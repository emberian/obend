module
/-
# Obend.Hardware.Synth — Verified Technology Mapping (`LUT3`/`CARRY8`/Barrel-Mux) & BEL Equivalence

Formalizes the synthesis & technology-mapping transformations from word-level `Obend.Hardware.HDL`
operations to physical FPGA/eFPGA primitives and retimed pipeline stages:
1. **Verified `LUT2` / `LUT3` Primitive Truth-Table Mapping**:
   - Proves `lut2_or_sound` (`INIT = 0xE`) and `lut3_mux_sound` (`INIT = 0xCA`),
   - Proves `evalLut3MuxBits_sound` over arbitrary-width bit lists.
2. **Verified `CARRY8` Two's-Complement Subtractor (`carrySubBel`)**:
   - Maps `a - b` onto `LUT2` + `CARRY8` by inverting `b` (`!b`) with initial carry-in `ci0 = true`
     ($a + \sim b + 1$), and proves `carrySubBel_eq_fullSubStageSpec`.
3. **Verified Pipeline Retiming & Critical-Path Splitting (`retime2Stage_sound`)**:
   - Splits a deep combinational tree `f (g x) (h y)` into a 2-stage pipeline closing 500 MHz timing.
4. **Verified `RtlModule` → `BelNetlist` Synthesis, 6-Stage Barrel Shifters & Universal Equivalence**:
   - Replaces buggy shift lowering with 6-stage logarithmic barrel-mux BEL networks (`shiftRoute` +
     `bitBroadcast` + `lut3 0xCA`, distances $1, 2, 4, 8, 16, 32$),
   - Defines operational `BelNetlist` semantics (`evalBelCell`, `evalCombBelCells`,
     `evalBelNetlistOutputs`, `stepBelNetlistRegs`),
   - Proves universal semantic equivalence (`evalBelNetlistOutputs_synthesizeModuleToBels`,
     `stepBelNetlistRegs_synthesizeModuleToBels`, `synthesizeModuleToBels_trace_equiv`) for every
     well-formed `m : RtlModule` (`checkRtlModule m = true`).
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

-- fixture kept (2026-11-04): a discriminating pair: the same path fails timing unretimed and closes retimed
example :
    checkTimingSignoff corner16nm_SS 2000 unretimedDeepPath = false ∧
    checkTimingSignoff corner16nm_SS 2000 retimedStagePath = true := by
  decide +kernel

/-! ## 4. General `RtlModule` → `BelNetlist` Technology Mapping, Barrel Shifters & Soundness -/

/-- Operating mode of a fast carry-chain BEL (`CARRY4` / `CARRY8`). -/
inductive CarryMode where
  | add     -- `a + b` (`cin = 0`)
  | sub     -- `a + ~b + 1` (`cin = 1`, fed `inv_b` from upstream `LUT1 0x1`)
  | ultCmp  -- Unsigned borrow-out comparator (`1#64` iff `a + ~b + 1 < 2^64`, i.e., `a <ᵤ b`)
  | sltCmp  -- Signed borrow-out comparator (`1#64` iff MSB-flipped `a + ~b + 1 < 2^64`, i.e., `a <ₛ b`)
  deriving DecidableEq, Repr

/-- Operating mode of a hard DSP multiplier slice (`DSP48E2` / `DSP58`). -/
inductive DspMulMode where
  | mul64   -- 64-bit integer product `(a * b)[63:0]`
  | qmul32  -- Signed Q32 fixed-point product `((sext128 a * sext128 b) >>> 32)[63:0]`
  deriving DecidableEq, Repr

/-- Direction/fill discipline of a fixed-offset shift wire permutation stage in a barrel shifter. -/
inductive ShiftDir where
  | shl   -- Left shift by fixed distance `dist`, zero-filling low `dist` bits
  | lshr  -- Logical right shift by fixed distance `dist`, zero-filling high `dist` bits
  | ashr  -- Arithmetic right shift by fixed distance `dist`, sign-filling high `dist` bits
  deriving DecidableEq, Repr

/-- Physical FPGA Basic Element of Logic (BEL) primitive kinds targeted by technology mapping. -/
inductive BelKind where
  | constBel     (val : BitVec 64)
  | portIn       (portIdx : Nat)
  | wireTap      (wireIdx : Nat)
  | regTap       (regIdx : Nat)
  | lut1         (initMask : Nat)               -- 64-lane 1-input LUT (`0x1` NOT, `0x2` buffer)
  | lut2         (initMask : Nat)               -- 64-lane 2-input LUT (`0x8` AND, `0xE` OR, `0x6` XOR)
  | lut3         (initMask : Nat)               -- 64-lane 3-input LUT (`0xCA` 2:1 MUX)
  | orReduce                                    -- Wide OR-reduction tree broadcasting `(a != 0#64)` across 64 lanes
  | zeroDetect                                  -- Wide NOR zero-detector (`1#64` iff `a == 0#64`, else `0#64`)
  | shiftRoute   (dir : ShiftDir) (dist : Nat)  -- Fixed-offset shift wiring (`dist ∈ {1,2,4,8,16,32}`)
  | bitBroadcast (bitIdx : Nat)                 -- Broadcast bit `bitIdx` across all 64 lanes
  | carry4       (mode : CarryMode := .add)     -- Fast lookahead carry chain primitive (`CARRY4` / `CARRY8`)
  | dspMul       (mode : DspMulMode := .mul64)  -- Hard DSP multiplier slice (`DSP48E2` / `DSP58`)
  | ff           (regIdx : Nat) (resetKind : ResetKind) -- Synchronous flip-flop BEL (`FDRE` / `FDPE`)
  | route        (op : RtlWidthOp)              -- Width slice/ext/trunc wire routing
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

theorem evalLut_inv (a : Bool) : evalLut 0x1 [a] = !a := by
  cases a <;> decide

theorem evalLut_buf (a : Bool) : evalLut 0x2 [a] = a := by
  cases a <;> decide

/-- Canonical collision-free root net name for internal RTL wire `idx` (contains no `'/'`). -/
def wireNetName (idx : Nat) : String :=
  String.ofList ('w' :: List.replicate idx '_' ++ ['='])

/-- Canonical collision-free root net name for register D-input `idx` (contains no `'/'`). -/
def regDinNetName (idx : Nat) : String :=
  String.ofList ('d' :: List.replicate idx '_' ++ ['='])

/-- Canonical collision-free root net name for module output `idx` (contains no `'/'`). -/
def outNetName (idx : Nat) : String :=
  String.ofList ('o' :: List.replicate idx '_' ++ ['='])

/-- Emit one stage of a 6-stage logarithmic barrel shifter (`dist = 2^bitIdx`):
1. `shiftRoute dir dist` (pure wire permutation + constant-0 / MSB sign fill),
2. `bitBroadcast bitIdx` (fanout bit `bitIdx` of shift amount `bName` to all 64 mux select pins),
3. `lut3 0xCA` (64-lane 2:1 multiplexer selecting shifted vs unshifted word). -/
def barrelStageBels
    (dir : ShiftDir) (bitIdx dist : Nat)
    (shNet selNet inNet outNet bName : String) : List BelCell :=
  [ { dstName := shNet,  kind := .shiftRoute dir dist, inputs := [inNet] }
  , { dstName := selNet, kind := .bitBroadcast bitIdx, inputs := [bName] }
  , { dstName := outNet, kind := .lut3 0xCA,           inputs := [inNet, shNet, selNet] } ]

/-- Emit a full 6-stage 64-bit logarithmic barrel shifter (`distances = 1, 2, 4, 8, 16, 32`)
from `aName` and `bName` into `dstName`. -/
def synthesizeBarrelShiftBels (dir : ShiftDir) (dstName aName bName : String) : List BelCell :=
  barrelStageBels dir 0 1  (dstName ++ "/h0") (dstName ++ "/k0") aName              (dstName ++ "/0") bName ++
  barrelStageBels dir 1 2  (dstName ++ "/h1") (dstName ++ "/k1") (dstName ++ "/0")  (dstName ++ "/1") bName ++
  barrelStageBels dir 2 4  (dstName ++ "/h2") (dstName ++ "/k2") (dstName ++ "/1")  (dstName ++ "/2") bName ++
  barrelStageBels dir 3 8  (dstName ++ "/h3") (dstName ++ "/k3") (dstName ++ "/2")  (dstName ++ "/3") bName ++
  barrelStageBels dir 4 16 (dstName ++ "/h4") (dstName ++ "/k4") (dstName ++ "/3")  (dstName ++ "/4") bName ++
  barrelStageBels dir 5 32 (dstName ++ "/h5") (dstName ++ "/k5") (dstName ++ "/4")  dstName           bName

/-- Emit the operator-local BEL cells combining already-synthesized operand nets `aName` and `bName`
into `dstName`. Factored out of `synthesizeExprToBels` so `synthesizeExprToBels` has a flat
single-clause equation on `.alu`. -/
def synthesizeAluHeadBels (op : RtlAluOp) (dstName aName bName : String) : List BelCell :=
  match op with
  | .bitAnd =>
    [{ dstName := dstName, kind := .lut2 0x8, inputs := [aName, bName] }]
  | .bitOr =>
    [{ dstName := dstName, kind := .lut2 0xE, inputs := [aName, bName] }]
  | .bitXor =>
    [{ dstName := dstName, kind := .lut2 0x6, inputs := [aName, bName] }]
  | .add =>
    let propName := dstName ++ "/p"
    [ { dstName := propName, kind := .lut2 0x6,    inputs := [aName, bName] }
    , { dstName := dstName,  kind := .carry4 .add, inputs := [aName, bName, propName] } ]
  | .sub =>
    let invName  := dstName ++ "/n"
    let propName := dstName ++ "/p"
    [ { dstName := invName,  kind := .lut1 0x1,    inputs := [bName] }
    , { dstName := propName, kind := .lut2 0x6,    inputs := [aName, invName] }
    , { dstName := dstName,  kind := .carry4 .sub, inputs := [aName, invName, propName] } ]
  | .mul =>
    [{ dstName := dstName, kind := .dspMul .mul64, inputs := [aName, bName] }]
  | .eq =>
    let xorName := dstName ++ "/x"
    [ { dstName := xorName, kind := .lut2 0x6,   inputs := [aName, bName] }
    , { dstName := dstName, kind := .zeroDetect, inputs := [xorName] } ]
  | .ult =>
    let invName := dstName ++ "/n"
    [ { dstName := invName, kind := .lut1 0x1,       inputs := [bName] }
    , { dstName := dstName, kind := .carry4 .ultCmp, inputs := [aName, invName] } ]
  | .shl =>
    synthesizeBarrelShiftBels .shl dstName aName bName
  | .lshr =>
    synthesizeBarrelShiftBels .lshr dstName aName bName
  | .ashr =>
    synthesizeBarrelShiftBels .ashr dstName aName bName
  | .slt =>
    let invName := dstName ++ "/n"
    [ { dstName := invName, kind := .lut1 0x1,       inputs := [bName] }
    , { dstName := dstName, kind := .carry4 .sltCmp, inputs := [aName, invName] } ]
  | .qmul32 =>
    [{ dstName := dstName, kind := .dspMul .qmul32, inputs := [aName, bName] }]

/-- Synthesize a combinational `RtlExpr` driving net `dstName` into a topologically ordered list of
FPGA `BelCell` primitives:
* `.alu .bitAnd` $\mapsto$ `BelKind.lut2 0x8`,
* `.alu .bitOr` $\mapsto$ `BelKind.lut2 0xE`,
* `.alu .bitXor` $\mapsto$ `BelKind.lut2 0x6`,
* `.alu .add` $\mapsto$ `BelKind.lut2 0x6` (propagate XOR) + `BelKind.carry4 .add`,
* `.alu .sub` $\mapsto$ `BelKind.lut1 0x1` (`~b`) + `BelKind.lut2 0x6` + `BelKind.carry4 .sub`,
* `.alu .shl`/`.lshr`/`.ashr` $\mapsto$ 6-stage logarithmic barrel mux (`synthesizeBarrelShiftBels`),
* `.mux` $\mapsto$ `BelKind.orReduce` + `BelKind.lut3 0xCA`,
* `.bitNot` $\mapsto$ `BelKind.lut1 0x1`,
* `.resize` $\mapsto$ `BelKind.route` (slice, extension or truncation is wiring). -/
def synthesizeExprToBels (dstName : String) : RtlExpr → List BelCell
  | .const v       => [{ dstName := dstName, kind := .constBel v, inputs := [] }]
  | .inputPort idx => [{ dstName := dstName, kind := .portIn idx, inputs := [s!"in_{idx}"] }]
  | .wireRef idx   => [{ dstName := dstName, kind := .wireTap idx, inputs := [wireNetName idx] }]
  | .regRead idx   => [{ dstName := dstName, kind := .regTap idx, inputs := [s!"r_{idx}"] }]
  | .bitNot a      =>
    let aName := dstName ++ "/a"
    synthesizeExprToBels aName a ++
      [{ dstName := dstName, kind := .lut1 0x1, inputs := [aName] }]
  | .resize op a   =>
    let aName := dstName ++ "/a"
    synthesizeExprToBels aName a ++
      [{ dstName := dstName, kind := .route op, inputs := [aName] }]
  | .mux c t f     =>
    let fName   := dstName ++ "/f"
    let tName   := dstName ++ "/t"
    let cName   := dstName ++ "/c"
    let selName := dstName ++ "/s"
    synthesizeExprToBels fName f ++
      synthesizeExprToBels tName t ++
      synthesizeExprToBels cName c ++
      [ { dstName := selName, kind := .orReduce,  inputs := [cName] }
      , { dstName := dstName, kind := .lut3 0xCA, inputs := [fName, tName, selName] } ]
  | .alu op a b    =>
    let aName := dstName ++ "/a"
    let bName := dstName ++ "/b"
    synthesizeExprToBels aName a ++
      synthesizeExprToBels bName b ++
      synthesizeAluHeadBels op dstName aName bName

/-- Synthesize an entire synchronous `RtlModule` into a technology-mapped `BelNetlist`, mapping all
internal wires, register next-state trees, and output trees via `synthesizeExprToBels`, and mapping
each sequential `RegSpec` to a dedicated `BelKind.ff` flip-flop BEL. -/
def synthesizeModuleToBels (m : RtlModule) : BelNetlist :=
  let wireBels := m.wires.flatMap (fun w => synthesizeExprToBels (wireNetName w.wireIdx) w.expr)
  let regCombBels := m.regs.zipIdx.flatMap (fun (r, k) => synthesizeExprToBels (regDinNetName k) r.nextExpr)
  let outBels := m.outputs.zipIdx.flatMap (fun (o, k) => synthesizeExprToBels (outNetName k) o.expr)
  let ffBels : List BelCell :=
    m.regs.zipIdx.map (fun (r, k) =>
      { dstName := r.name, kind := .ff r.regIdx r.resetKind, inputs := [regDinNetName k] })
  { moduleName  := m.name
  , inputNames  := m.inputNames
  , cells       := wireBels ++ regCombBels ++ outBels ++ ffBels
  , outputNames := m.outputs.map (·.name) }

/-- Check whether a `BelCell` is a sequential flip-flop (`BelKind.ff`). -/
def isFfBel (c : BelCell) : Bool :=
  match c.kind with
  | .ff _ _ => true
  | _       => false

/-- Count the number of sequential flip-flop (`BelKind.ff`) cells in a `BelNetlist`. -/
def countFfBels (nl : BelNetlist) : Nat :=
  (nl.cells.filter isFfBel).length

/-- Check whether a `BelCell` has a valid input pin arity for its `BelKind`. -/
def checkBelCellValid (c : BelCell) : Bool :=
  match c.kind with
  | .constBel _     => c.inputs.length == 0
  | .portIn _       => c.inputs.length == 1
  | .wireTap _      => c.inputs.length == 1
  | .regTap _       => c.inputs.length == 1
  | .lut1 _         => c.inputs.length == 1
  | .lut2 _         => c.inputs.length == 2
  | .lut3 _         => c.inputs.length == 3
  | .orReduce       => c.inputs.length == 1
  | .zeroDetect     => c.inputs.length == 1
  | .shiftRoute _ _ => c.inputs.length == 1
  | .bitBroadcast _ => c.inputs.length == 1
  | .carry4 _       => c.inputs.length == 2 || c.inputs.length == 3
  | .dspMul _       => c.inputs.length == 2
  | .ff _ _         => c.inputs.length == 1
  | .route _        => c.inputs.length == 1

/-- Check that every cell in a `BelNetlist` satisfies `checkBelCellValid`. -/
def checkBelNetlistValid (nl : BelNetlist) : Bool :=
  nl.cells.all checkBelCellValid

theorem synthesizeBarrelShiftBels_no_ff (dir : ShiftDir) (dst a b : String) :
    (synthesizeBarrelShiftBels dir dst a b).filter isFfBel = [] :=
  rfl

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
    have hHead : (synthesizeAluHeadBels op dstName (dstName ++ "/a") (dstName ++ "/b")).filter isFfBel = [] := by
      cases op <;> rfl
    simp [synthesizeExprToBels, List.filter_append, iha, ihb, hHead]

theorem flatMap_synthesizeExprToBels_no_ff {α : Type}
    (f : α → String) (g : α → RtlExpr) (xs : List α) :
    (xs.flatMap (fun x => synthesizeExprToBels (f x) (g x))).filter isFfBel = [] := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    simp [List.flatMap_cons, List.filter_append, synthesizeExprToBels_no_ff, ih]

theorem map_reg_ff_filter (regs : List (RegSpec × Nat)) :
    (regs.map (fun (r, k) => ({ dstName := r.name, kind := .ff r.regIdx r.resetKind, inputs := [regDinNetName k] } : BelCell))).filter isFfBel =
      regs.map (fun (r, k) => { dstName := r.name, kind := .ff r.regIdx r.resetKind, inputs := [regDinNetName k] }) := by
  induction regs with
  | nil => rfl
  | cons rk rest ih =>
    simp [List.map_cons, List.filter_cons, isFfBel, ih]

theorem synthesizeBarrelShiftBels_valid (dir : ShiftDir) (dst a b : String) :
    (synthesizeBarrelShiftBels dir dst a b).all checkBelCellValid = true :=
  rfl

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
    have hHead : (synthesizeAluHeadBels op dstName (dstName ++ "/a") (dstName ++ "/b")).all checkBelCellValid = true := by
      cases op <;> rfl
    simp [synthesizeExprToBels, List.all_append, iha, ihb, hHead]

theorem flatMap_synthesizeExprToBels_valid {α : Type}
    (f : α → String) (g : α → RtlExpr) (xs : List α) :
    (xs.flatMap (fun x => synthesizeExprToBels (f x) (g x))).all checkBelCellValid = true := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    simp [List.flatMap_cons, List.all_append, synthesizeExprToBels_valid, ih]

theorem map_reg_ff_valid (regs : List (RegSpec × Nat)) :
    (regs.map (fun (r, k) => ({ dstName := r.name, kind := .ff r.regIdx r.resetKind, inputs := [regDinNetName k] } : BelCell))).all checkBelCellValid = true := by
  induction regs with
  | nil => rfl
  | cons rk rest ih =>
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
        flatMap_synthesizeExprToBels_valid (fun w : WireAssign => wireNetName w.wireIdx) (·.expr),
        flatMap_synthesizeExprToBels_valid (fun rk : RegSpec × Nat => regDinNetName rk.2) (fun rk => rk.1.nextExpr),
        flatMap_synthesizeExprToBels_valid (fun ok : OutputPort × Nat => outNetName ok.2) (fun ok => ok.1.expr),
        map_reg_ff_valid]
    rfl
  · simp [countFfBels, synthesizeModuleToBels, List.filter_append,
      flatMap_synthesizeExprToBels_no_ff (fun w : WireAssign => wireNetName w.wireIdx) (·.expr),
      flatMap_synthesizeExprToBels_no_ff (fun rk : RegSpec × Nat => regDinNetName rk.2) (fun rk => rk.1.nextExpr),
      flatMap_synthesizeExprToBels_no_ff (fun ok : OutputPort × Nat => outNetName ok.2) (fun ok => ok.1.expr),
      map_reg_ff_filter]

/-! ## 5. Operational Semantics of `BelNetlist` & Universal Equivalence to `RtlModule` -/

/-- Pack `w` lane booleans `(0 .. w-1)` into a `BitVec w` (`MSB = f (w-1)` down to `LSB = f 0`). -/
def packBitsW : (w : Nat) → (Nat → Bool) → BitVec w
  | 0,     _ => 0#0
  | w + 1, f => BitVec.cons (f w) (packBitsW w f)

theorem getLsbD_packBitsW : ∀ (w : Nat) (f : Nat → Bool) (i : Nat),
    i < w → (packBitsW w f).getLsbD i = f i
  | 0, _, _, hi => absurd hi (Nat.not_lt_zero _)
  | w + 1, f, i, hi => by
    simp only [packBitsW, BitVec.getLsbD_cons]
    by_cases hEq : i = w
    · subst hEq; simp
    · simp [hEq, getLsbD_packBitsW w f i (by omega)]

attribute [irreducible] packBitsW

/-- Evaluate a 64-lane 1-input LUT (`LUT1`) bit-by-bit via `evalLut`. -/
def evalLutWord1 (mask : Nat) (a : BitVec 64) : BitVec 64 :=
  packBitsW 64 (fun i => evalLut mask [a.getLsbD i])

/-- Evaluate a 64-lane 2-input LUT (`LUT2`) bit-by-bit via `evalLut`. -/
def evalLutWord2 (mask : Nat) (a b : BitVec 64) : BitVec 64 :=
  packBitsW 64 (fun i => evalLut mask [a.getLsbD i, b.getLsbD i])

/-- Evaluate a 64-lane 3-input LUT (`LUT3`) bit-by-bit via `evalLut`. -/
def evalLutWord3 (mask : Nat) (d0 d1 sel : BitVec 64) : BitVec 64 :=
  packBitsW 64 (fun i => evalLut mask [d0.getLsbD i, d1.getLsbD i, sel.getLsbD i])

/-- Evaluate a fixed-offset shift wire permutation (`shiftRoute`). -/
def evalShiftRoute (dir : ShiftDir) (dist : Nat) (a : BitVec 64) : BitVec 64 :=
  match dir with
  | .shl  => a <<< dist
  | .lshr => a >>> dist
  | .ashr => BitVec.sshiftRight a dist

/-- Broadcast bit `bitIdx` of `b` across all 64 lanes (`~~~0#64` if `1`, `0#64` if `0`). -/
def evalBitBroadcast (bitIdx : Nat) (b : BitVec 64) : BitVec 64 :=
  if b.getLsbD bitIdx then ~~~(0#64) else 0#64

/-- Evaluate a 64-bit `CARRY4`/`CARRY8` fast carry chain primitive:
* `.add` computes `a + b` (`cin = 0`),
* `.sub` computes `a + inv_b + 1` (`cin = 1` with `inv_b = ~~~b` from `LUT1 0x1`),
* `.ultCmp` computes borrow-out `< 2^64` of `a + inv_b + 1` (`1#64` iff `a <ᵤ b`),
* `.sltCmp` computes MSB-biased borrow-out `< 2^64` of `(a + 2^63) + (inv_b + 2^63) + 1` (`1#64` iff `a <ₛ b`). -/
def evalCarry4Bel (mode : CarryMode) (a in1 : BitVec 64) : BitVec 64 :=
  match mode with
  | .add    => a + in1
  | .sub    => a + in1 + 1#64
  | .ultCmp =>
    if a.toNat + in1.toNat + 1 < 2 ^ 64 then 1#64 else 0#64
  | .sltCmp =>
    let aBiased := (a.toNat + 2 ^ 63) % 2 ^ 64
    let bBiased := (in1.toNat + 2 ^ 63) % 2 ^ 64
    if aBiased + bBiased + 1 < 2 ^ 64 then 1#64 else 0#64

/-- Evaluate a single combinational `BelCell` under primary `inputs`, current `regState`, and
already-evaluated net environment `env`. -/
def evalBelCell
    (inputs regState : Nat → BitVec 64)
    (env : String → BitVec 64)
    (c : BelCell) : BitVec 64 :=
  match c.kind with
  | .constBel v         => v
  | .portIn idx         => inputs idx
  | .wireTap idx        => env (wireNetName idx)
  | .regTap idx         => regState idx
  | .lut1 mask          => evalLutWord1 mask (env (c.inputs.getD 0 ""))
  | .lut2 mask          => evalLutWord2 mask (env (c.inputs.getD 0 "")) (env (c.inputs.getD 1 ""))
  | .lut3 mask          =>
    evalLutWord3 mask (env (c.inputs.getD 0 "")) (env (c.inputs.getD 1 "")) (env (c.inputs.getD 2 ""))
  | .orReduce           =>
    if env (c.inputs.getD 0 "") != 0#64 then ~~~(0#64) else 0#64
  | .zeroDetect         =>
    if env (c.inputs.getD 0 "") == 0#64 then 1#64 else 0#64
  | .shiftRoute dir d   => evalShiftRoute dir d (env (c.inputs.getD 0 ""))
  | .bitBroadcast bitId => evalBitBroadcast bitId (env (c.inputs.getD 0 ""))
  | .carry4 mode        => evalCarry4Bel mode (env (c.inputs.getD 0 "")) (env (c.inputs.getD 1 ""))
  | .dspMul .mul64      => env (c.inputs.getD 0 "") * env (c.inputs.getD 1 "")
  | .dspMul .qmul32     => evalAluOp .qmul32 (env (c.inputs.getD 0 "")) (env (c.inputs.getD 1 ""))
  | .ff regIdx _        => regState regIdx
  | .route op           => evalWidthOp op (env (c.inputs.getD 0 ""))

/-- Propagate combinational BEL cells in topological list order starting from `initEnv`
(sequential `BelKind.ff` flip-flop cells update only on clock edges in `stepBelNetlistRegs`). -/
def evalCombBelCellsFrom
    (inputs regState : Nat → BitVec 64)
    (initEnv : String → BitVec 64)
    (cells : List BelCell) : String → BitVec 64 :=
  cells.foldl
    (fun env c =>
      if isFfBel c then env
      else
        let v := evalBelCell inputs regState env c
        fun k => if k == c.dstName then v else env k)
    initEnv

/-- Evaluate all combinational BEL cells of a `BelNetlist` starting from the zero net environment. -/
def evalCombBelCells
    (inputs regState : Nat → BitVec 64)
    (cells : List BelCell) : String → BitVec 64 :=
  evalCombBelCellsFrom inputs regState (fun _ => 0#64) cells

/-- Evaluate all module output ports of a `BelNetlist` for given `inputs` and `regState`. -/
def evalBelNetlistOutputs
    (nl : BelNetlist)
    (inputs regState : Nat → BitVec 64) : List (String × BitVec 64) :=
  let env := evalCombBelCells inputs regState nl.cells
  nl.outputNames.zipIdx.map (fun (name, k) => (name, env (outNetName k)))

/-- Step all sequential flip-flop (`BelKind.ff`) cells of a `BelNetlist` by one clock edge. -/
def stepBelNetlistRegs
    (nl : BelNetlist)
    (rst : Bool)
    (inputs regState : Nat → BitVec 64) : Nat → BitVec 64 :=
  let env := evalCombBelCells inputs regState nl.cells
  nl.cells.foldl
    (fun (nextSt : Nat → BitVec 64) c =>
      match c.kind with
      | .ff regIdx resetKind =>
        let din := env (c.inputs.getD 0 "")
        let v :=
          match resetKind with
          | .resetFree => din
          | .syncReset initVal => if rst then initVal else din
        fun i => if i == regIdx then v else nextSt i
      | _ => nextSt)
    regState

/-! ### 5a. Word-Level `LUT1`/`LUT2`/`LUT3`, `CARRY4`, and 6-Stage Barrel-Shifter Identities -/

theorem evalLutWord1_not (a : BitVec 64) : evalLutWord1 0x1 a = ~~~a := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [evalLutWord1, getLsbD_packBitsW 64 _ i hi, evalLut_inv]
  simp [hi]

theorem evalLutWord2_and (a b : BitVec 64) : evalLutWord2 0x8 a b = (a &&& b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [evalLutWord2, getLsbD_packBitsW 64 _ i hi, (lut2_bitwise_synth_sound _ _).1, BitVec.getLsbD_and]

theorem evalLutWord2_or (a b : BitVec 64) : evalLutWord2 0xE a b = (a ||| b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [evalLutWord2, getLsbD_packBitsW 64 _ i hi, (lut2_bitwise_synth_sound _ _).2.1, BitVec.getLsbD_or]

theorem evalLutWord2_xor (a b : BitVec 64) : evalLutWord2 0x6 a b = (a ^^^ b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [evalLutWord2, getLsbD_packBitsW 64 _ i hi, (lut2_bitwise_synth_sound _ _).2.2, BitVec.getLsbD_xor]

theorem evalLutWord3_mux_broadcast (d0 d1 : BitVec 64) (cond : Bool) :
    evalLutWord3 0xCA d0 d1 (if cond then ~~~(0#64) else 0#64) =
      (if cond then d1 else d0) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [evalLutWord3, getLsbD_packBitsW 64 _ i hi, lut3_mux_synth_sound]
  cases cond
  · simp
  · simp only [↓reduceIte]
    have hBit : (~~~(0#64)).getLsbD i = true := by
      rw [BitVec.getLsbD_not, BitVec.getLsbD_zero]
      simp [hi]
    rw [hBit]
    rfl

theorem evalCarry4Bel_sub_eq (a b : BitVec 64) :
    evalCarry4Bel .sub a (~~~b) = a - b := by
  apply BitVec.eq_of_toNat_eq
  have ha : a.toNat < 2 ^ 64 := a.isLt
  have hb : b.toNat < 2 ^ 64 := b.isLt
  simp only [evalCarry4Bel, BitVec.toNat_add, BitVec.toNat_not, BitVec.toNat_sub,
    BitVec.toNat_ofNat]
  omega

theorem evalZeroDetect_xor_eq (a b : BitVec 64) :
    (if (a ^^^ b) == 0#64 then 1#64 else 0#64) = evalAluOp .eq a b := by
  simp only [evalAluOp]
  by_cases h : a = b
  · subst h
    simp
  · have hNe : (a == b) = false := beq_false_of_ne h
    have hXorNe : (a ^^^ b) ≠ 0#64 := by
      intro hZero
      apply h
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      have hBit : (a ^^^ b).getLsbD i = (0#64).getLsbD i := congrArg (fun v => v.getLsbD i) hZero
      simp only [BitVec.getLsbD_xor, BitVec.getLsbD_zero] at hBit
      cases ha : a.getLsbD i <;> cases hb : b.getLsbD i <;> simp_all
    simp [hNe, beq_false_of_ne hXorNe]

theorem evalCarry4Bel_ult_eq (a b : BitVec 64) :
    evalCarry4Bel .ultCmp a (~~~b) = evalAluOp .ult a b := by
  have ha : a.toNat < 2 ^ 64 := a.isLt
  have hb : b.toNat < 2 ^ 64 := b.isLt
  simp only [evalCarry4Bel, evalAluOp, BitVec.ult, BitVec.toNat_not]
  by_cases hLt : a.toNat < b.toNat
  · have hCarry : a.toNat + (2 ^ 64 - 1 - b.toNat) + 1 < 2 ^ 64 := by omega
    simp [hLt, hCarry]
  · have hNoCarry : ¬ (a.toNat + (2 ^ 64 - 1 - b.toNat) + 1 < 2 ^ 64) := by omega
    simp [hLt, hNoCarry]

private theorem mod_2pow64_add_half (x : Nat) (hx : x < 2 ^ 64) :
    (x + 2 ^ 63) % 2 ^ 64 =
      if x < 2 ^ 63 then x + 2 ^ 63 else x - 2 ^ 63 := by
  by_cases hLt : x < 2 ^ 63
  · simp only [hLt, ↓reduceIte]
    exact Nat.mod_eq_of_lt (by omega)
  · simp only [hLt, ↓reduceIte]
    have hEq : x + 2 ^ 63 = (x - 2 ^ 63) + 2 ^ 64 := by omega
    rw [hEq, Nat.add_mod_right]
    exact Nat.mod_eq_of_lt (by omega)

theorem evalCarry4Bel_slt_eq (a b : BitVec 64) :
    evalCarry4Bel .sltCmp a (~~~b) = evalAluOp .slt a b := by
  have ha : a.toNat < 2 ^ 64 := a.isLt
  have hb : b.toNat < 2 ^ 64 := b.isLt
  have hNotB : 2 ^ 64 - 1 - b.toNat < 2 ^ 64 := by omega
  simp only [evalCarry4Bel, evalAluOp, BitVec.slt, BitVec.toInt, BitVec.toNat_not]
  rw [mod_2pow64_add_half a.toNat ha, mod_2pow64_add_half (2 ^ 64 - 1 - b.toNat) hNotB]
  by_cases haHalf : a.toNat < 2 ^ 63 <;> by_cases hbHalf : b.toNat < 2 ^ 63
  · have ha2 : 2 * a.toNat < 2 ^ 64 := by omega
    have hb2 : 2 * b.toNat < 2 ^ 64 := by omega
    have hNotBH : ¬ (2 ^ 64 - 1 - b.toNat < 2 ^ 63) := by omega
    simp only [haHalf, hNotBH, ↓reduceIte, ha2, hb2]
    split <;> split <;> first | rfl | (exfalso; simp only [decide_eq_true_eq] at *; omega)
  · have ha2 : 2 * a.toNat < 2 ^ 64 := by omega
    have hb2 : ¬ (2 * b.toNat < 2 ^ 64) := by omega
    have hNotBH : 2 ^ 64 - 1 - b.toNat < 2 ^ 63 := by omega
    simp only [haHalf, hNotBH, ↓reduceIte, ha2, hb2]
    split <;> split <;> first | rfl | (exfalso; simp only [decide_eq_true_eq] at *; omega)
  · have ha2 : ¬ (2 * a.toNat < 2 ^ 64) := by omega
    have hb2 : 2 * b.toNat < 2 ^ 64 := by omega
    have hNotBH : ¬ (2 ^ 64 - 1 - b.toNat < 2 ^ 63) := by omega
    simp only [haHalf, hNotBH, ↓reduceIte, ha2, hb2]
    split <;> split <;> first | rfl | (exfalso; simp only [decide_eq_true_eq] at *; omega)
  · have ha2 : ¬ (2 * a.toNat < 2 ^ 64) := by omega
    have hb2 : ¬ (2 * b.toNat < 2 ^ 64) := by omega
    have hNotBH : 2 ^ 64 - 1 - b.toNat < 2 ^ 63 := by omega
    simp only [haHalf, hNotBH, ↓reduceIte, ha2, hb2]
    split <;> split <;> first | rfl | (exfalso; simp only [decide_eq_true_eq] at *; omega)

theorem evalShiftRoute_zero (dir : ShiftDir) (a : BitVec 64) :
    evalShiftRoute dir 0 a = a := by
  cases dir <;>
    (apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [evalShiftRoute, hi])

theorem evalShiftRoute_compose (dir : ShiftDir) (d1 d2 : Nat) (a : BitVec 64) :
    evalShiftRoute dir d2 (evalShiftRoute dir d1 a) = evalShiftRoute dir (d1 + d2) a := by
  cases dir with
  | shl =>
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [evalShiftRoute, BitVec.getLsbD_shiftLeft, hi, decide_true, Bool.true_and]
    by_cases h2 : i < d2
    · have h12 : i < d1 + d2 := by omega
      simp [h2, h12]
    · have hiSub : i - d2 < 64 := by omega
      simp only [h2, hiSub, decide_true, Bool.true_and]
      by_cases h1 : i - d2 < d1
      · have h12 : i < d1 + d2 := by omega
        simp [h1, h12]
      · have h12 : ¬ (i < d1 + d2) := by omega
        have hEqSub : i - d2 - d1 = i - (d1 + d2) := by omega
        simp [h1, h12, hEqSub]
  | lshr =>
    apply BitVec.eq_of_getLsbD_eq
    intro i _
    simp only [evalShiftRoute, BitVec.getLsbD_ushiftRight]
    have hEqAdd : d1 + (d2 + i) = d1 + d2 + i := by omega
    rw [hEqAdd]
  | ashr =>
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have hNotGe : ¬ (64 ≤ i) := by omega
    simp only [evalShiftRoute, BitVec.getLsbD_sshiftRight, hNotGe, decide_false,
      Bool.not_false, Bool.true_and]
    by_cases hLt2 : d2 + i < 64
    · have hNotGe2 : ¬ (64 ≤ d2 + i) := by omega
      have hEqAdd : d1 + (d2 + i) = d1 + d2 + i := by omega
      simp only [hLt2, ↓reduceIte, hNotGe2, decide_false, Bool.not_false, Bool.true_and, hEqAdd]
    · have hNotLt12 : ¬ (d1 + d2 + i < 64) := by omega
      simp only [hLt2, hNotLt12, ↓reduceIte]
      rw [BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_sshiftRight]
      by_cases hd1 : d1 = 0
      · subst hd1
        simp [BitVec.msb_eq_getLsbD_last]
      · have hNotLt63 : ¬ (d1 + 63 < 64) := by omega
        simp [hNotLt63]

theorem barrelStage_step (dir : ShiftDir) (acc bitIdx dist : Nat) (a b : BitVec 64) :
    evalLutWord3 0xCA
      (evalShiftRoute dir acc a)
      (evalShiftRoute dir dist (evalShiftRoute dir acc a))
      (evalBitBroadcast bitIdx b) =
    evalShiftRoute dir (acc + (if b.getLsbD bitIdx then dist else 0)) a := by
  unfold evalBitBroadcast
  rw [evalLutWord3_mux_broadcast]
  cases b.getLsbD bitIdx with
  | false => simp
  | true =>
    simp only [↓reduceIte]
    exact evalShiftRoute_compose dir acc dist a

private theorem getLsbD_val (b : BitVec 64) (k d : Nat) (_hk : k < 64) :
    (if b.getLsbD k then d else 0) = ((b.toNat / 2 ^ k) % 2) * d := by
  simp only [BitVec.getLsbD, Nat.testBit, Nat.shiftRight_eq_div_pow]
  rw [Nat.and_comm 1 _, Nat.and_one_is_mod]
  have hMod : (b.toNat / 2 ^ k) % 2 = 0 ∨ (b.toNat / 2 ^ k) % 2 = 1 := by omega
  rcases hMod with h0 | h1
  · simp [h0]
  · simp [h1]

theorem bitVec_low6_sum (b : BitVec 64) :
    (if b.getLsbD 0 then 1 else 0) +
    (if b.getLsbD 1 then 2 else 0) +
    (if b.getLsbD 2 then 4 else 0) +
    (if b.getLsbD 3 then 8 else 0) +
    (if b.getLsbD 4 then 16 else 0) +
    (if b.getLsbD 5 then 32 else 0) = b.toNat % 64 := by
  rw [getLsbD_val b 0 1 (by decide),
      getLsbD_val b 1 2 (by decide),
      getLsbD_val b 2 4 (by decide),
      getLsbD_val b 3 8 (by decide),
      getLsbD_val b 4 16 (by decide),
      getLsbD_val b 5 32 (by decide)]
  omega

/-- **Universal 6-Stage Barrel-Shifter Equivalence (`barrelShift6_eq_shift_mod64`)**:
Composing the 6 fixed-distance (`1, 2, 4, 8, 16, 32`) barrel-mux stages controlled by bits `0..5`
of `b` equals `evalShiftRoute dir (b.toNat % 64) a` for every `a, b : BitVec 64`! -/
theorem barrelShift6_eq_shift_mod64 (dir : ShiftDir) (a b s0 s1 s2 s3 s4 s5 : BitVec 64)
    (hs0 : s0 = evalLutWord3 0xCA a  (evalShiftRoute dir 1 a)   (evalBitBroadcast 0 b))
    (hs1 : s1 = evalLutWord3 0xCA s0 (evalShiftRoute dir 2 s0)  (evalBitBroadcast 1 b))
    (hs2 : s2 = evalLutWord3 0xCA s1 (evalShiftRoute dir 4 s1)  (evalBitBroadcast 2 b))
    (hs3 : s3 = evalLutWord3 0xCA s2 (evalShiftRoute dir 8 s2)  (evalBitBroadcast 3 b))
    (hs4 : s4 = evalLutWord3 0xCA s3 (evalShiftRoute dir 16 s3) (evalBitBroadcast 4 b))
    (hs5 : s5 = evalLutWord3 0xCA s4 (evalShiftRoute dir 32 s4) (evalBitBroadcast 5 b)) :
    s5 = evalShiftRoute dir (b.toNat % 64) a := by
  let d0 := 0 + (if b.getLsbD 0 then 1 else 0)
  let d1 := d0 + (if b.getLsbD 1 then 2 else 0)
  let d2 := d1 + (if b.getLsbD 2 then 4 else 0)
  let d3 := d2 + (if b.getLsbD 3 then 8 else 0)
  let d4 := d3 + (if b.getLsbD 4 then 16 else 0)
  let d5 := d4 + (if b.getLsbD 5 then 32 else 0)
  have h0 : s0 = evalShiftRoute dir d0 a := by
    rw [hs0]
    have ha0 : a = evalShiftRoute dir 0 a := (evalShiftRoute_zero dir a).symm
    conv => lhs; arg 2; rw [ha0]
    conv => lhs; arg 3; arg 3; rw [ha0]
    exact barrelStage_step dir 0 0 1 a b
  have h1 : s1 = evalShiftRoute dir d1 a := by
    rw [hs1, h0]; exact barrelStage_step dir d0 1 2 a b
  have h2 : s2 = evalShiftRoute dir d2 a := by
    rw [hs2, h1]; exact barrelStage_step dir d1 2 4 a b
  have h3 : s3 = evalShiftRoute dir d3 a := by
    rw [hs3, h2]; exact barrelStage_step dir d2 3 8 a b
  have h4 : s4 = evalShiftRoute dir d4 a := by
    rw [hs4, h3]; exact barrelStage_step dir d3 4 16 a b
  have h5 : s5 = evalShiftRoute dir d5 a := by
    rw [hs5, h4]; exact barrelStage_step dir d4 5 32 a b
  rw [h5]
  dsimp only [d5, d4, d3, d2, d1, d0]
  simp only [Nat.zero_add]
  rw [bitVec_low6_sum b]

/-! ### 5b. Net-Namespace Non-Interference & Universal `RtlExpr` → `BelCell` Soundness -/

theorem evalCombBelCellsFrom_append
    (inputs regState : Nat → BitVec 64)
    (env : String → BitVec 64)
    (xs ys : List BelCell) :
    evalCombBelCellsFrom inputs regState env (xs ++ ys) =
      evalCombBelCellsFrom inputs regState (evalCombBelCellsFrom inputs regState env xs) ys := by
  unfold evalCombBelCellsFrom
  exact List.foldl_append

/-- If `k` is distinct from every `c.dstName` in `cells`, evaluating `cells` preserves `env k`. -/
theorem evalCombBelCellsFrom_preserve
    (inputs regState : Nat → BitVec 64)
    (env : String → BitVec 64)
    (cells : List BelCell)
    (k : String)
    (hAvoid : ∀ c ∈ cells, c.dstName ≠ k) :
    evalCombBelCellsFrom inputs regState env cells k = env k := by
  induction cells generalizing env with
  | nil => rfl
  | cons c rest ih =>
    have hNe : (k == c.dstName) = false :=
      beq_false_of_ne (Ne.symm (hAvoid c List.mem_cons_self))
    have hRest : ∀ c' ∈ rest, c'.dstName ≠ k :=
      fun c' hc' => hAvoid c' (List.mem_cons_of_mem _ hc')
    have hStep : evalCombBelCellsFrom inputs regState env (c :: rest) k =
        evalCombBelCellsFrom inputs regState
          (if isFfBel c then env else fun k' => if k' == c.dstName then evalBelCell inputs regState env c else env k')
          rest k := rfl
    rw [hStep, ih _ hRest]
    cases isFfBel c <;> simp [hNe]

/-- Every cell emitted by `synthesizeExprToBels dst e` either writes `dst` directly or writes
a strictly extended slash-path `dst.toList ++ '/' :: ch :: rest`. -/
theorem synthesizeExprToBels_dst_shape (dst : String) (e : RtlExpr) :
    ∀ c ∈ synthesizeExprToBels dst e,
      c.dstName = dst ∨ ∃ ch rest, c.dstName.toList = dst.toList ++ '/' :: ch :: rest := by
  have push_tag : ∀ (d : String) (ch : Char) (x : String),
      (x = d ++ String.ofList ['/', ch] ∨
        ∃ ch2 rest, x.toList = (d ++ String.ofList ['/', ch]).toList ++ '/' :: ch2 :: rest) →
      ∃ ch' rest', x.toList = d.toList ++ '/' :: ch' :: rest' := by
    intro d ch x hx
    rcases hx with rfl | ⟨ch2, rest, hList⟩
    · exact ⟨ch, [], by simp [String.toList_append]⟩
    · exact ⟨ch, '/' :: ch2 :: rest, by simpa [String.toList_append, List.append_assoc] using hList⟩
  induction e generalizing dst with
  | const _ =>
    intro c hc; simp [synthesizeExprToBels] at hc; exact Or.inl (by simp [hc])
  | inputPort _ =>
    intro c hc; simp [synthesizeExprToBels] at hc; exact Or.inl (by simp [hc])
  | wireRef _ =>
    intro c hc; simp [synthesizeExprToBels] at hc; exact Or.inl (by simp [hc])
  | regRead _ =>
    intro c hc; simp [synthesizeExprToBels] at hc; exact Or.inl (by simp [hc])
  | bitNot a iha =>
    intro c hc
    simp only [synthesizeExprToBels, List.mem_append, List.mem_singleton] at hc
    rcases hc with ha | rfl
    · exact Or.inr (push_tag dst 'a' c.dstName (by simpa using iha (dst ++ "/a") c ha))
    · exact Or.inl rfl
  | resize op a iha =>
    intro c hc
    simp only [synthesizeExprToBels, List.mem_append, List.mem_singleton] at hc
    rcases hc with ha | rfl
    · exact Or.inr (push_tag dst 'a' c.dstName (by simpa using iha (dst ++ "/a") c ha))
    · exact Or.inl rfl
  | mux cond t f ihc iht ihf =>
    intro c hc
    simp only [synthesizeExprToBels, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with ((hf | ht) | hcond) | (rfl | rfl)
    · exact Or.inr (push_tag dst 'f' c.dstName (by simpa using ihf (dst ++ "/f") c hf))
    · exact Or.inr (push_tag dst 't' c.dstName (by simpa using iht (dst ++ "/t") c ht))
    · exact Or.inr (push_tag dst 'c' c.dstName (by simpa using ihc (dst ++ "/c") c hcond))
    · exact Or.inr ⟨'s', [], by simp [String.toList_append]⟩
    · exact Or.inl rfl
  | alu op a b iha ihb =>
    intro c hc
    have hBarrel : ∀ (dir : ShiftDir) x,
        x ∈ synthesizeBarrelShiftBels dir dst (dst ++ "/a") (dst ++ "/b") →
        x.dstName = dst ∨ ∃ ch rest, x.dstName.toList = dst.toList ++ '/' :: ch :: rest := by
      intro dir x hx
      simp only [synthesizeBarrelShiftBels, barrelStageBels, List.mem_append,
        List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with ((((h0 | h1) | h2) | h3) | h4) | h5
      · rcases h0 with rfl | rfl | rfl
        · exact Or.inr ⟨'h', ['0'], by simp [String.toList_append]⟩
        · exact Or.inr ⟨'k', ['0'], by simp [String.toList_append]⟩
        · exact Or.inr ⟨'0', [],    by simp [String.toList_append]⟩
      · rcases h1 with rfl | rfl | rfl
        · exact Or.inr ⟨'h', ['1'], by simp [String.toList_append]⟩
        · exact Or.inr ⟨'k', ['1'], by simp [String.toList_append]⟩
        · exact Or.inr ⟨'1', [],    by simp [String.toList_append]⟩
      · rcases h2 with rfl | rfl | rfl
        · exact Or.inr ⟨'h', ['2'], by simp [String.toList_append]⟩
        · exact Or.inr ⟨'k', ['2'], by simp [String.toList_append]⟩
        · exact Or.inr ⟨'2', [],    by simp [String.toList_append]⟩
      · rcases h3 with rfl | rfl | rfl
        · exact Or.inr ⟨'h', ['3'], by simp [String.toList_append]⟩
        · exact Or.inr ⟨'k', ['3'], by simp [String.toList_append]⟩
        · exact Or.inr ⟨'3', [],    by simp [String.toList_append]⟩
      · rcases h4 with rfl | rfl | rfl
        · exact Or.inr ⟨'h', ['4'], by simp [String.toList_append]⟩
        · exact Or.inr ⟨'k', ['4'], by simp [String.toList_append]⟩
        · exact Or.inr ⟨'4', [],    by simp [String.toList_append]⟩
      · rcases h5 with rfl | rfl | rfl
        · exact Or.inr ⟨'h', ['5'], by simp [String.toList_append]⟩
        · exact Or.inr ⟨'k', ['5'], by simp [String.toList_append]⟩
        · exact Or.inl rfl
    simp only [synthesizeExprToBels, List.mem_append] at hc
    rcases hc with (hxa | hxb) | hcHead
    · exact Or.inr (push_tag dst 'a' c.dstName (by simpa using iha (dst ++ "/a") c hxa))
    · exact Or.inr (push_tag dst 'b' c.dstName (by simpa using ihb (dst ++ "/b") c hxb))
    · cases op with
      | bitAnd | bitOr | bitXor | mul | qmul32 =>
        simp only [synthesizeAluHeadBels, List.mem_singleton] at hcHead
        exact Or.inl (by simp [hcHead])
      | add =>
        simp only [synthesizeAluHeadBels, List.mem_cons, List.not_mem_nil, or_false] at hcHead
        rcases hcHead with rfl | rfl
        · exact Or.inr ⟨'p', [], by simp [String.toList_append]⟩
        · exact Or.inl rfl
      | sub =>
        simp only [synthesizeAluHeadBels, List.mem_cons, List.not_mem_nil, or_false] at hcHead
        rcases hcHead with rfl | rfl | rfl
        · exact Or.inr ⟨'n', [], by simp [String.toList_append]⟩
        · exact Or.inr ⟨'p', [], by simp [String.toList_append]⟩
        · exact Or.inl rfl
      | eq =>
        simp only [synthesizeAluHeadBels, List.mem_cons, List.not_mem_nil, or_false] at hcHead
        rcases hcHead with rfl | rfl
        · exact Or.inr ⟨'x', [], by simp [String.toList_append]⟩
        · exact Or.inl rfl
      | ult | slt =>
        simp only [synthesizeAluHeadBels, List.mem_cons, List.not_mem_nil, or_false] at hcHead
        rcases hcHead with rfl | rfl
        · exact Or.inr ⟨'n', [], by simp [String.toList_append]⟩
        · exact Or.inl rfl
      | shl =>
        exact hBarrel .shl c hcHead
      | lshr =>
        exact hBarrel .lshr c hcHead
      | ashr =>
        exact hBarrel .ashr c hcHead

private theorem not_slash_mem_replicate_underscore :
    ∀ n : Nat, '/' ∉ ('w' :: List.replicate n '_' ++ ['=']) ∧
               '/' ∉ ('d' :: List.replicate n '_' ++ ['=']) ∧
               '/' ∉ ('o' :: List.replicate n '_' ++ ['=']) := by
  intro n
  have hRep : '/' ∉ List.replicate n '_' := by
    induction n with
    | zero => simp
    | succ m ih => simp [List.replicate_succ, ih]
  refine ⟨?_, ?_, ?_⟩ <;> simp [hRep]

theorem slash_not_in_wireNetName (idx : Nat) : '/' ∉ (wireNetName idx).toList := by
  simp [wireNetName]

theorem slash_not_in_regDinNetName (idx : Nat) : '/' ∉ (regDinNetName idx).toList := by
  simp [regDinNetName]

theorem slash_not_in_outNetName (idx : Nat) : '/' ∉ (outNetName idx).toList := by
  simp [outNetName]

theorem wireNetName_injective {i j : Nat} (h : wireNetName i = wireNetName j) : i = j := by
  have hLen := congrArg (fun s => s.toList.length) h
  simp [wireNetName] at hLen
  omega

theorem regDinNetName_injective {i j : Nat} (h : regDinNetName i = regDinNetName j) : i = j := by
  have hLen := congrArg (fun s => s.toList.length) h
  simp [regDinNetName] at hLen
  omega

theorem outNetName_injective {i j : Nat} (h : outNetName i = outNetName j) : i = j := by
  have hLen := congrArg (fun s => s.toList.length) h
  simp [outNetName] at hLen
  omega

theorem wireNetName_ne_regDinNetName (i j : Nat) : wireNetName i ≠ regDinNetName j := by
  intro h
  have hHead := congrArg (fun s => s.toList.head?) h
  simp [wireNetName, regDinNetName] at hHead

theorem wireNetName_ne_outNetName (i j : Nat) : wireNetName i ≠ outNetName j := by
  intro h
  have hHead := congrArg (fun s => s.toList.head?) h
  simp [wireNetName, outNetName] at hHead

theorem regDinNetName_ne_outNetName (i j : Nat) : regDinNetName i ≠ outNetName j := by
  intro h
  have hHead := congrArg (fun s => s.toList.head?) h
  simp [regDinNetName, outNetName] at hHead

/-- Any net containing `'/'` cannot equal a slash-free root net `k`. -/
theorem append_slash_ne_slashFree {dst s k : String} (hk : '/' ∉ k.toList) :
    dst ++ "/" ++ s ≠ k := by
  intro hEq
  apply hk
  rw [← hEq]
  simp [String.toList_append]

theorem synthesizeExprToBels_avoids_sibling
    (dst : String) (c1 c2 : Char) (e : RtlExpr)
    (hNe : c1 ≠ c2) :
    ∀ cell ∈ synthesizeExprToBels (dst ++ String.ofList ['/', c1]) e,
      cell.dstName ≠ dst ++ String.ofList ['/', c2] := by
  intro cell hMem hEq
  rcases synthesizeExprToBels_dst_shape (dst ++ String.ofList ['/', c1]) e cell hMem with hDirect | ⟨ch, rest, hList⟩
  · rw [hDirect] at hEq
    have hL := congrArg String.toList hEq
    simp only [String.toList_append, String.toList_ofList] at hL
    have hTail := List.append_cancel_left hL
    injection hTail with _ hCons
    injection hCons with hChar _
    exact hNe hChar
  · rw [hEq] at hList
    simp only [String.toList_append, String.toList_ofList, List.append_assoc] at hList
    have hTail := List.append_cancel_left hList
    injection hTail with _ hCons
    injection hCons with hChar _
    exact hNe hChar.symm

theorem synthesizeExprToBels_avoids_slashFree
    (dst k : String) (e : RtlExpr)
    (hk : '/' ∉ k.toList)
    (hNe : dst ≠ k) :
    ∀ cell ∈ synthesizeExprToBels dst e, cell.dstName ≠ k := by
  intro cell hMem
  rcases synthesizeExprToBels_dst_shape dst e cell hMem with hDirect | ⟨ch, rest, hList⟩
  · rw [hDirect]; exact hNe
  · intro hEq
    apply hk
    rw [← hEq, hList]
    simp

private theorem evalBarrelStageBels_step
    (inputs regState : Nat → BitVec 64)
    (env envNext : String → BitVec 64)
    (dir : ShiftDir) (bitIdx dist : Nat)
    (shNet selNet inNet outNet bName : String)
    (vIn vb : BitVec 64)
    (hEnvNext : evalCombBelCellsFrom inputs regState env
      (barrelStageBels dir bitIdx dist shNet selNet inNet outNet bName) = envNext)
    (hIn : env inNet = vIn)
    (hB : env bName = vb)
    (hBNeSh : bName ≠ shNet)
    (hBNeSel : bName ≠ selNet)
    (hBNeOut : bName ≠ outNet)
    (hInNeSh : inNet ≠ shNet)
    (hInNeSel : inNet ≠ selNet)
    (hShNeSel : shNet ≠ selNet) :
    envNext outNet = evalLutWord3 0xCA vIn (evalShiftRoute dir dist vIn) (evalBitBroadcast bitIdx vb) ∧
    envNext bName = vb := by
  subst hEnvNext
  unfold barrelStageBels evalCombBelCellsFrom
  simp [List.foldl_cons, List.foldl_nil, isFfBel, evalBelCell, hIn, hB,
    hBNeSh, hBNeSel, hBNeOut, hInNeSh, hInNeSel, hShNeSel]

theorem evalBarrelShiftBels_correct
    (inputs regState : Nat → BitVec 64)
    (env : String → BitVec 64)
    (dir : ShiftDir) (dst : String)
    (va vb : BitVec 64)
    (ha : env (dst ++ "/a") = va)
    (hb : env (dst ++ "/b") = vb) :
    evalCombBelCellsFrom inputs regState env
      (synthesizeBarrelShiftBels dir dst (dst ++ "/a") (dst ++ "/b")) dst =
    evalShiftRoute dir (vb.toNat % 64) va := by
  have ne_str : ∀ (s1 s2 : String), s1 ≠ s2 → dst ++ s1 ≠ dst ++ s2 := by
    intro s1 s2 h hEq
    have hL := congrArg String.toList hEq
    simp only [String.toList_append] at hL
    have hT := List.append_cancel_left hL
    exact h (String.ext_iff.mpr hT)
  have ne_dst : dst ++ "/b" ≠ dst := by
    intro hEq
    have hLen := congrArg (fun s => s.toList.length) hEq
    simp [String.toList_append] at hLen
  unfold synthesizeBarrelShiftBels
  rw [evalCombBelCellsFrom_append, evalCombBelCellsFrom_append,
      evalCombBelCellsFrom_append, evalCombBelCellsFrom_append,
      evalCombBelCellsFrom_append]
  generalize he0 : evalCombBelCellsFrom inputs regState env
    (barrelStageBels dir 0 1 (dst ++ "/h0") (dst ++ "/k0") (dst ++ "/a") (dst ++ "/0") (dst ++ "/b")) = env0
  generalize he1 : evalCombBelCellsFrom inputs regState env0
    (barrelStageBels dir 1 2 (dst ++ "/h1") (dst ++ "/k1") (dst ++ "/0") (dst ++ "/1") (dst ++ "/b")) = env1
  generalize he2 : evalCombBelCellsFrom inputs regState env1
    (barrelStageBels dir 2 4 (dst ++ "/h2") (dst ++ "/k2") (dst ++ "/1") (dst ++ "/2") (dst ++ "/b")) = env2
  generalize he3 : evalCombBelCellsFrom inputs regState env2
    (barrelStageBels dir 3 8 (dst ++ "/h3") (dst ++ "/k3") (dst ++ "/2") (dst ++ "/3") (dst ++ "/b")) = env3
  generalize he4 : evalCombBelCellsFrom inputs regState env3
    (barrelStageBels dir 4 16 (dst ++ "/h4") (dst ++ "/k4") (dst ++ "/3") (dst ++ "/4") (dst ++ "/b")) = env4
  generalize he5 : evalCombBelCellsFrom inputs regState env4
    (barrelStageBels dir 5 32 (dst ++ "/h5") (dst ++ "/k5") (dst ++ "/4") dst (dst ++ "/b")) = env5
  obtain ⟨hv0, hb0⟩ := evalBarrelStageBels_step inputs regState env env0 dir 0 1
    (dst ++ "/h0") (dst ++ "/k0") (dst ++ "/a") (dst ++ "/0") (dst ++ "/b") va vb he0 ha hb
    (ne_str "/b" "/h0" (by decide)) (ne_str "/b" "/k0" (by decide)) (ne_str "/b" "/0" (by decide))
    (ne_str "/a" "/h0" (by decide)) (ne_str "/a" "/k0" (by decide)) (ne_str "/h0" "/k0" (by decide))
  obtain ⟨hv1, hb1⟩ := evalBarrelStageBels_step inputs regState env0 env1 dir 1 2
    (dst ++ "/h1") (dst ++ "/k1") (dst ++ "/0") (dst ++ "/1") (dst ++ "/b") (env0 (dst ++ "/0")) vb he1 rfl hb0
    (ne_str "/b" "/h1" (by decide)) (ne_str "/b" "/k1" (by decide)) (ne_str "/b" "/1" (by decide))
    (ne_str "/0" "/h1" (by decide)) (ne_str "/0" "/k1" (by decide)) (ne_str "/h1" "/k1" (by decide))
  obtain ⟨hv2, hb2⟩ := evalBarrelStageBels_step inputs regState env1 env2 dir 2 4
    (dst ++ "/h2") (dst ++ "/k2") (dst ++ "/1") (dst ++ "/2") (dst ++ "/b") (env1 (dst ++ "/1")) vb he2 rfl hb1
    (ne_str "/b" "/h2" (by decide)) (ne_str "/b" "/k2" (by decide)) (ne_str "/b" "/2" (by decide))
    (ne_str "/1" "/h2" (by decide)) (ne_str "/1" "/k2" (by decide)) (ne_str "/h2" "/k2" (by decide))
  obtain ⟨hv3, hb3⟩ := evalBarrelStageBels_step inputs regState env2 env3 dir 3 8
    (dst ++ "/h3") (dst ++ "/k3") (dst ++ "/2") (dst ++ "/3") (dst ++ "/b") (env2 (dst ++ "/2")) vb he3 rfl hb2
    (ne_str "/b" "/h3" (by decide)) (ne_str "/b" "/k3" (by decide)) (ne_str "/b" "/3" (by decide))
    (ne_str "/2" "/h3" (by decide)) (ne_str "/2" "/k3" (by decide)) (ne_str "/h3" "/k3" (by decide))
  obtain ⟨hv4, hb4⟩ := evalBarrelStageBels_step inputs regState env3 env4 dir 4 16
    (dst ++ "/h4") (dst ++ "/k4") (dst ++ "/3") (dst ++ "/4") (dst ++ "/b") (env3 (dst ++ "/3")) vb he4 rfl hb3
    (ne_str "/b" "/h4" (by decide)) (ne_str "/b" "/k4" (by decide)) (ne_str "/b" "/4" (by decide))
    (ne_str "/3" "/h4" (by decide)) (ne_str "/3" "/k4" (by decide)) (ne_str "/h4" "/k4" (by decide))
  obtain ⟨hv5, _⟩ := evalBarrelStageBels_step inputs regState env4 env5 dir 5 32
    (dst ++ "/h5") (dst ++ "/k5") (dst ++ "/4") dst (dst ++ "/b") (env4 (dst ++ "/4")) vb he5 rfl hb4
    (ne_str "/b" "/h5" (by decide)) (ne_str "/b" "/k5" (by decide)) ne_dst
    (ne_str "/4" "/h5" (by decide)) (ne_str "/4" "/k5" (by decide)) (ne_str "/h5" "/k5" (by decide))
  exact barrelShift6_eq_shift_mod64 dir va vb
    (env0 (dst ++ "/0")) (env1 (dst ++ "/1")) (env2 (dst ++ "/2"))
    (env3 (dst ++ "/3")) (env4 (dst ++ "/4")) (env5 dst)
    hv0 hv1 hv2 hv3 hv4 hv5

/-- **Universal Combinational `RtlExpr` → `BelCell` Equivalence (`synthesizeExprToBels_sound`)**:
For ANY `e : RtlExpr` referencing wires `< wireBound`, evaluating `synthesizeExprToBels dst e`
from any net environment `env` whose wire roots `wireNetName i` (`i < wireBound`) match `wireEnv i`
drives `dst` to the exact 64-bit word `evalRtlExpr inputs wireEnv regState e`! -/
theorem synthesizeExprToBels_sound
    (numInputs numRegs wireBound : Nat)
    (inputs wireEnv regState : Nat → BitVec 64)
    (e : RtlExpr)
    (hDag : checkExprDAG numInputs numRegs wireBound e = true) :
    ∀ (dst : String) (env : String → BitVec 64),
      (∀ i < wireBound, wireNetName i ≠ dst) →
      (∀ i < wireBound, env (wireNetName i) = wireEnv i) →
      evalCombBelCellsFrom inputs regState env (synthesizeExprToBels dst e) dst =
        evalRtlExpr inputs wireEnv regState e := by
  induction e with
  | const v =>
    intro dst env _ _
    simp [synthesizeExprToBels, evalCombBelCellsFrom, isFfBel, evalBelCell, evalRtlExpr]
  | inputPort idx =>
    intro dst env _ _
    simp [synthesizeExprToBels, evalCombBelCellsFrom, isFfBel, evalBelCell, evalRtlExpr]
  | wireRef idx =>
    intro dst env _ hWires
    simp only [checkExprDAG, decide_eq_true_eq] at hDag
    simp [synthesizeExprToBels, evalCombBelCellsFrom, isFfBel, evalBelCell, evalRtlExpr, hWires idx hDag]
  | regRead idx =>
    intro dst env _ _
    simp [synthesizeExprToBels, evalCombBelCellsFrom, isFfBel, evalBelCell, evalRtlExpr]
  | bitNot a iha =>
    intro dst env _ hWires
    simp only [checkExprDAG] at hDag
    have hSubNoSlash : ∀ i < wireBound, wireNetName i ≠ dst ++ "/a" :=
      fun i _ h => append_slash_ne_slashFree (s := "a") (slash_not_in_wireNetName i) (by simpa [String.append_assoc] using h.symm)
    let envA := evalCombBelCellsFrom inputs regState env (synthesizeExprToBels (dst ++ "/a") a)
    have ha : envA (dst ++ "/a") = evalRtlExpr inputs wireEnv regState a :=
      iha hDag (dst ++ "/a") env hSubNoSlash hWires
    simp only [synthesizeExprToBels, evalCombBelCellsFrom_append]
    change evalCombBelCellsFrom inputs regState envA
      [{ dstName := dst, kind := .lut1 0x1, inputs := [dst ++ "/a"] }] dst = _
    simp [evalCombBelCellsFrom, isFfBel, evalBelCell, ha, evalLutWord1_not, evalRtlExpr]
  | resize op a iha =>
    intro dst env _ hWires
    simp only [checkExprDAG] at hDag
    have hSubNoSlash : ∀ i < wireBound, wireNetName i ≠ dst ++ "/a" :=
      fun i _ h => append_slash_ne_slashFree (s := "a") (slash_not_in_wireNetName i) (by simpa [String.append_assoc] using h.symm)
    let envA := evalCombBelCellsFrom inputs regState env (synthesizeExprToBels (dst ++ "/a") a)
    have ha : envA (dst ++ "/a") = evalRtlExpr inputs wireEnv regState a :=
      iha hDag (dst ++ "/a") env hSubNoSlash hWires
    simp only [synthesizeExprToBels, evalCombBelCellsFrom_append]
    change evalCombBelCellsFrom inputs regState envA
      [{ dstName := dst, kind := .route op, inputs := [dst ++ "/a"] }] dst = _
    simp [evalCombBelCellsFrom, isFfBel, evalBelCell, ha, evalRtlExpr]
  | mux c t f ihc iht ihf =>
    intro dst env _ hWires
    simp only [checkExprDAG, Bool.and_eq_true] at hDag
    rcases hDag with ⟨⟨hDc, hDt⟩, hDf⟩
    have hNoSlashTag : ∀ (tag : String) i, i < wireBound → wireNetName i ≠ dst ++ "/" ++ tag :=
      fun tag i _ h => (append_slash_ne_slashFree (slash_not_in_wireNetName i)) h.symm
    let envF := evalCombBelCellsFrom inputs regState env (synthesizeExprToBels (dst ++ "/f") f)
    let envT := evalCombBelCellsFrom inputs regState envF (synthesizeExprToBels (dst ++ "/t") t)
    let envC := evalCombBelCellsFrom inputs regState envT (synthesizeExprToBels (dst ++ "/c") c)
    have hfVal : envF (dst ++ "/f") = evalRtlExpr inputs wireEnv regState f :=
      ihf hDf (dst ++ "/f") env (by intro i hi; simpa [String.append_assoc] using hNoSlashTag "f" i hi) hWires
    have hWiresF : ∀ i < wireBound, envF (wireNetName i) = wireEnv i := by
      intro i hi
      exact (evalCombBelCellsFrom_preserve inputs regState env _ (wireNetName i)
        (synthesizeExprToBels_avoids_slashFree _ _ f (slash_not_in_wireNetName i)
          (Ne.symm (by simpa [String.append_assoc] using hNoSlashTag "f" i hi)))).trans (hWires i hi)
    have htVal : envT (dst ++ "/t") = evalRtlExpr inputs wireEnv regState t :=
      iht hDt (dst ++ "/t") envF (by intro i hi; simpa [String.append_assoc] using hNoSlashTag "t" i hi) hWiresF
    have hfPresT : envT (dst ++ "/f") = evalRtlExpr inputs wireEnv regState f :=
      (evalCombBelCellsFrom_preserve inputs regState envF _ (dst ++ "/f")
        (by simpa using synthesizeExprToBels_avoids_sibling dst 't' 'f' t (by decide))).trans hfVal
    have hWiresT : ∀ i < wireBound, envT (wireNetName i) = wireEnv i := by
      intro i hi
      exact (evalCombBelCellsFrom_preserve inputs regState envF _ (wireNetName i)
        (synthesizeExprToBels_avoids_slashFree _ _ t (slash_not_in_wireNetName i)
          (Ne.symm (by simpa [String.append_assoc] using hNoSlashTag "t" i hi)))).trans (hWiresF i hi)
    have hcVal : envC (dst ++ "/c") = evalRtlExpr inputs wireEnv regState c :=
      ihc hDc (dst ++ "/c") envT (by intro i hi; simpa [String.append_assoc] using hNoSlashTag "c" i hi) hWiresT
    have hfPresC : envC (dst ++ "/f") = evalRtlExpr inputs wireEnv regState f :=
      (evalCombBelCellsFrom_preserve inputs regState envT _ (dst ++ "/f")
        (by simpa using synthesizeExprToBels_avoids_sibling dst 'c' 'f' c (by decide))).trans hfPresT
    have htPresC : envC (dst ++ "/t") = evalRtlExpr inputs wireEnv regState t :=
      (evalCombBelCellsFrom_preserve inputs regState envT _ (dst ++ "/t")
        (by simpa using synthesizeExprToBels_avoids_sibling dst 'c' 't' c (by decide))).trans htVal
    have ne_str : ∀ (s1 s2 : String), s1 ≠ s2 → dst ++ s1 ≠ dst ++ s2 := by
      intro s1 s2 h hEq
      have hL := congrArg String.toList hEq
      simp only [String.toList_append] at hL
      exact h (String.ext_iff.mpr (List.append_cancel_left hL))
    simp only [synthesizeExprToBels, List.append_assoc, evalCombBelCellsFrom_append]
    change evalCombBelCellsFrom inputs regState envC
        [ { dstName := dst ++ "/s", kind := .orReduce, inputs := [dst ++ "/c"] }
        , { dstName := dst, kind := .lut3 0xCA, inputs := [dst ++ "/f", dst ++ "/t", dst ++ "/s"] } ] dst = _
    simp only [evalCombBelCellsFrom, List.foldl_cons, List.foldl_nil, isFfBel, Bool.false_eq_true,
      ↓reduceIte, evalBelCell, List.getD_cons_zero, List.getD_cons_succ, hcVal, hfPresC, htPresC,
      beq_false_of_ne (ne_str "/f" "/s" (by decide)),
      beq_false_of_ne (ne_str "/t" "/s" (by decide)),
      beq_self_eq_true, evalLutWord3_mux_broadcast, evalRtlExpr]
  | alu op a b iha ihb =>
    intro dst env _ hWires
    simp only [checkExprDAG, Bool.and_eq_true] at hDag
    rcases hDag with ⟨hDa, hDb⟩
    have hNoSlashTag : ∀ (tag : String) i, i < wireBound → wireNetName i ≠ dst ++ "/" ++ tag :=
      fun tag i _ h => (append_slash_ne_slashFree (slash_not_in_wireNetName i)) h.symm
    let envA := evalCombBelCellsFrom inputs regState env (synthesizeExprToBels (dst ++ "/a") a)
    let envB := evalCombBelCellsFrom inputs regState envA (synthesizeExprToBels (dst ++ "/b") b)
    have haVal : envA (dst ++ "/a") = evalRtlExpr inputs wireEnv regState a :=
      iha hDa (dst ++ "/a") env (by intro i hi; simpa [String.append_assoc] using hNoSlashTag "a" i hi) hWires
    have hWiresA : ∀ i < wireBound, envA (wireNetName i) = wireEnv i := by
      intro i hi
      exact (evalCombBelCellsFrom_preserve inputs regState env _ (wireNetName i)
        (synthesizeExprToBels_avoids_slashFree _ _ a (slash_not_in_wireNetName i)
          (Ne.symm (by simpa [String.append_assoc] using hNoSlashTag "a" i hi)))).trans (hWires i hi)
    have hbVal : envB (dst ++ "/b") = evalRtlExpr inputs wireEnv regState b :=
      ihb hDb (dst ++ "/b") envA (by intro i hi; simpa [String.append_assoc] using hNoSlashTag "b" i hi) hWiresA
    have haPresB : envB (dst ++ "/a") = evalRtlExpr inputs wireEnv regState a :=
      (evalCombBelCellsFrom_preserve inputs regState envA _ (dst ++ "/a")
        (by simpa using synthesizeExprToBels_avoids_sibling dst 'b' 'a' b (by decide))).trans haVal
    simp only [synthesizeExprToBels, List.append_assoc, evalCombBelCellsFrom_append]
    change evalCombBelCellsFrom inputs regState envB
      (synthesizeAluHeadBels op dst (dst ++ "/a") (dst ++ "/b")) dst = _
    cases op with
    | bitAnd =>
      simp [synthesizeAluHeadBels, evalCombBelCellsFrom, isFfBel, evalBelCell, haPresB, hbVal, evalLutWord2_and, evalRtlExpr, evalAluOp]
    | bitOr =>
      simp [synthesizeAluHeadBels, evalCombBelCellsFrom, isFfBel, evalBelCell, haPresB, hbVal, evalLutWord2_or, evalRtlExpr, evalAluOp]
    | bitXor =>
      simp [synthesizeAluHeadBels, evalCombBelCellsFrom, isFfBel, evalBelCell, haPresB, hbVal, evalLutWord2_xor, evalRtlExpr, evalAluOp]
    | add =>
      simp [synthesizeAluHeadBels, evalCombBelCellsFrom, isFfBel, evalBelCell, haPresB, hbVal,
        evalCarry4Bel, evalRtlExpr, evalAluOp]
    | sub =>
      simp [synthesizeAluHeadBels, evalCombBelCellsFrom, isFfBel, evalBelCell, haPresB, hbVal,
        evalLutWord1_not, evalCarry4Bel_sub_eq, evalRtlExpr, evalAluOp]
    | mul =>
      simp [synthesizeAluHeadBels, evalCombBelCellsFrom, isFfBel, evalBelCell, haPresB, hbVal, evalRtlExpr, evalAluOp]
    | eq =>
      simp [synthesizeAluHeadBels, evalCombBelCellsFrom, isFfBel, evalBelCell, haPresB, hbVal,
        evalLutWord2_xor, evalRtlExpr, evalAluOp]
    | ult =>
      simp [synthesizeAluHeadBels, evalCombBelCellsFrom, isFfBel, evalBelCell, haPresB, hbVal,
        evalLutWord1_not, evalCarry4Bel_ult_eq, evalRtlExpr]
    | slt =>
      simp [synthesizeAluHeadBels, evalCombBelCellsFrom, isFfBel, evalBelCell, haPresB, hbVal,
        evalLutWord1_not, evalCarry4Bel_slt_eq, evalRtlExpr]
    | qmul32 =>
      simp [synthesizeAluHeadBels, evalCombBelCellsFrom, isFfBel, evalBelCell, haPresB, hbVal, evalRtlExpr]
    | shl =>
      simp only [synthesizeAluHeadBels]
      rw [evalBarrelShiftBels_correct inputs regState envB .shl dst _ _ haPresB hbVal]
      rfl
    | lshr =>
      simp only [synthesizeAluHeadBels]
      rw [evalBarrelShiftBels_correct inputs regState envB .lshr dst _ _ haPresB hbVal]
      rfl
    | ashr =>
      simp only [synthesizeAluHeadBels]
      rw [evalBarrelShiftBels_correct inputs regState envB .ashr dst _ _ haPresB hbVal]
      rfl

/-! ### 5c. Wire-Table, Output-Port & Register-Step Equivalence (`synthesizeModuleToBels` == `RtlModule`) -/

private theorem wireTable_go_sound
    (numInputs numRegs : Nat)
    (inputs regState : Nat → BitVec 64) :
    ∀ (assigns : List WireAssign) (expectedIdx : Nat)
      (wEnv : Nat → BitVec 64) (bEnv : String → BitVec 64),
      checkWireTableDAG.go numInputs numRegs expectedIdx assigns = true →
      (∀ i < expectedIdx, bEnv (wireNetName i) = wEnv i) →
      let wFinal := assigns.foldl
        (fun (env : Nat → BitVec 64) a =>
          let v := evalRtlExpr inputs env regState a.expr
          fun i => if i == a.wireIdx then v else env i) wEnv
      let bFinal := evalCombBelCellsFrom inputs regState bEnv
        (assigns.flatMap (fun w => synthesizeExprToBels (wireNetName w.wireIdx) w.expr))
      ∀ i < expectedIdx + assigns.length, bFinal (wireNetName i) = wFinal i := by
  intro assigns
  induction assigns with
  | nil =>
    intro expectedIdx wEnv bEnv _ hAgree _ _ i hi
    exact hAgree i (by omega)
  | cons a rest ih =>
    intro expectedIdx wEnv bEnv hGo hAgree
    simp only [checkWireTableDAG.go, Bool.and_eq_true, beq_iff_eq] at hGo
    rcases hGo with ⟨⟨hIdx, hDag⟩, hRestGo⟩
    subst hIdx
    let wEnv1 : Nat → BitVec 64 :=
      fun i => if i == a.wireIdx then evalRtlExpr inputs wEnv regState a.expr else wEnv i
    let bEnv1 := evalCombBelCellsFrom inputs regState bEnv
      (synthesizeExprToBels (wireNetName a.wireIdx) a.expr)
    have hAgree1 : ∀ i < a.wireIdx + 1, bEnv1 (wireNetName i) = wEnv1 i := by
      intro i hi
      by_cases hEq : i = a.wireIdx
      · subst hEq
        simp only [wEnv1, beq_self_eq_true, ↓reduceIte]
        exact synthesizeExprToBels_sound numInputs numRegs a.wireIdx inputs wEnv regState a.expr hDag
          (wireNetName a.wireIdx) bEnv
          (fun j hj hName => Nat.ne_of_lt hj (wireNetName_injective hName))
          hAgree
      · have hLt : i < a.wireIdx := by omega
        have hBeq : (i == a.wireIdx) = false := beq_false_of_ne hEq
        simp only [wEnv1, hBeq, Bool.false_eq_true, ↓reduceIte]
        exact (evalCombBelCellsFrom_preserve inputs regState bEnv _ (wireNetName i)
          (synthesizeExprToBels_avoids_slashFree _ _ a.expr (slash_not_in_wireNetName i)
            (fun hName => hEq (wireNetName_injective hName.symm)))).trans (hAgree i hLt)
    simp only [List.flatMap_cons, evalCombBelCellsFrom_append, List.foldl_cons, List.length_cons]
    intro i hi
    exact ih (a.wireIdx + 1) wEnv1 bEnv1 hRestGo hAgree1 i (by omega)

private theorem flatMap_indexed_sound {α : Type}
    (numInputs numRegs wireBound : Nat)
    (inputs wireEnv regState : Nat → BitVec 64)
    (rootFn : Nat → String)
    (hSlashFree : ∀ k, '/' ∉ (rootFn k).toList)
    (hRootInj : ∀ {k1 k2}, rootFn k1 = rootFn k2 → k1 = k2)
    (hDisjWire : ∀ i k, wireNetName i ≠ rootFn k)
    (exprOf : α → RtlExpr) :
    ∀ (xs : List α) (base : Nat) (bEnv : String → BitVec 64),
      (∀ x ∈ xs, checkExprDAG numInputs numRegs wireBound (exprOf x) = true) →
      (∀ i < wireBound, bEnv (wireNetName i) = wireEnv i) →
      let cells := (xs.zipIdx base).flatMap (fun (x, k) => synthesizeExprToBels (rootFn k) (exprOf x))
      let bFinal := evalCombBelCellsFrom inputs regState bEnv cells
      (∀ i < wireBound, bFinal (wireNetName i) = wireEnv i) ∧
      (∀ k < base, bFinal (rootFn k) = bEnv (rootFn k)) ∧
      (∀ (idx : Nat) (hIdx : idx < xs.length),
        bFinal (rootFn (base + idx)) = evalRtlExpr inputs wireEnv regState (exprOf xs[idx])) := by
  intro xs
  induction xs with
  | nil =>
    intro base bEnv _ hWires
    refine ⟨hWires, fun _ _ => rfl, fun idx hIdx => absurd hIdx (Nat.not_lt_zero _)⟩
  | cons x rest ih =>
    intro base bEnv hAllDag hWires
    have hDagX : checkExprDAG numInputs numRegs wireBound (exprOf x) = true :=
      hAllDag x List.mem_cons_self
    have hDagRest : ∀ y ∈ rest, checkExprDAG numInputs numRegs wireBound (exprOf y) = true :=
      fun y hy => hAllDag y (List.mem_cons_of_mem _ hy)
    let bEnv1 := evalCombBelCellsFrom inputs regState bEnv (synthesizeExprToBels (rootFn base) (exprOf x))
    have hValX : bEnv1 (rootFn base) = evalRtlExpr inputs wireEnv regState (exprOf x) :=
      synthesizeExprToBels_sound numInputs numRegs wireBound inputs wireEnv regState (exprOf x) hDagX
        (rootFn base) bEnv (fun i _ => hDisjWire i base) hWires
    have hWires1 : ∀ i < wireBound, bEnv1 (wireNetName i) = wireEnv i := by
      intro i hi
      exact (evalCombBelCellsFrom_preserve inputs regState bEnv _ (wireNetName i)
        (synthesizeExprToBels_avoids_slashFree _ _ (exprOf x) (slash_not_in_wireNetName i)
          (Ne.symm (hDisjWire i base)))).trans (hWires i hi)
    have hPrev1 : ∀ k < base, bEnv1 (rootFn k) = bEnv (rootFn k) := by
      intro k hk
      exact evalCombBelCellsFrom_preserve inputs regState bEnv _ (rootFn k)
        (synthesizeExprToBels_avoids_slashFree _ _ (exprOf x) (hSlashFree k)
          (fun hEq => Nat.ne_of_gt hk (hRootInj hEq)))
    obtain ⟨hWiresFinal, hPrevFinal, hRestVals⟩ := ih (base + 1) bEnv1 hDagRest hWires1
    simp only [List.zipIdx_cons, List.flatMap_cons, evalCombBelCellsFrom_append]
    refine ⟨hWiresFinal, ?_, ?_⟩
    · intro k hk
      rw [hPrevFinal k (by omega), hPrev1 k hk]
    · intro idx hIdx
      cases idx with
      | zero =>
        simp only [Nat.add_zero, List.getElem_cons_zero]
        rw [hPrevFinal base (by omega)]
        exact hValX
      | succ j =>
        simp only [List.length_cons] at hIdx
        have hj : j < rest.length := by omega
        have hAdd : base + (j + 1) = (base + 1) + j := by omega
        rw [hAdd]
        simpa [List.getElem_cons_succ] using hRestVals j hj

private theorem evalCombBelCellsFrom_ff_noop
    (inputs regState : Nat → BitVec 64)
    (bEnv : String → BitVec 64)
    (regs : List (RegSpec × Nat)) :
    evalCombBelCellsFrom inputs regState bEnv
      (regs.map (fun (r, k) => { dstName := r.name, kind := .ff r.regIdx r.resetKind, inputs := [regDinNetName k] })) =
    bEnv := by
  induction regs generalizing bEnv with
  | nil => rfl
  | cons rk rest ih =>
    unfold evalCombBelCellsFrom
    simp only [List.map_cons, List.foldl_cons, isFfBel, ↓reduceIte]
    exact ih bEnv

private theorem flatMap_preserves_foreign_root {α : Type}
    (inputs regState : Nat → BitVec 64)
    (rootFn : Nat → String)
    (exprOf : α → RtlExpr)
    (k : String)
    (hkSlash : '/' ∉ k.toList)
    (hDisj : ∀ n, rootFn n ≠ k) :
    ∀ (xs : List (α × Nat)) (bEnv : String → BitVec 64),
      evalCombBelCellsFrom inputs regState bEnv
        (xs.flatMap (fun (x, n) => synthesizeExprToBels (rootFn n) (exprOf x))) k = bEnv k := by
  intro xs
  induction xs with
  | nil => intro bEnv; rfl
  | cons xn rest ih =>
    intro bEnv
    simp only [List.flatMap_cons, evalCombBelCellsFrom_append]
    rw [ih]
    exact evalCombBelCellsFrom_preserve inputs regState bEnv _ k
      (synthesizeExprToBels_avoids_slashFree _ k (exprOf xn.1) hkSlash (hDisj xn.2))

/-- Core environment agreement theorem for `synthesizeModuleToBels m`:
for any well-formed `m : RtlModule` (`checkRtlModule m = true`), `evalCombBelCells` evaluates every
output root `outNetName k` and every register next-state root `regDinNetName k` to the exact
64-bit value of `evalRtlExpr` under `evalWireTable inputs regState m.wires`! -/
theorem evalCombBelCells_synthesizeModuleToBels
    (m : RtlModule)
    (inputs regState : Nat → BitVec 64)
    (hWf : checkRtlModule m = true) :
    let wireEnv := evalWireTable inputs regState m.wires
    let belEnv := evalCombBelCells inputs regState (synthesizeModuleToBels m).cells
    (∀ (k : Nat) (hk : k < m.outputs.length),
      belEnv (outNetName k) = evalRtlExpr inputs wireEnv regState m.outputs[k].expr) ∧
    (∀ (k : Nat) (hk : k < m.regs.length),
      belEnv (regDinNetName k) = evalRtlExpr inputs wireEnv regState m.regs[k].nextExpr) := by
  simp only [checkRtlModule, Bool.and_eq_true, List.all_eq_true] at hWf
  rcases hWf with ⟨⟨⟨hWiresDag, hRegsDag⟩, hOutsDag⟩, _⟩
  let wireEnv := evalWireTable inputs regState m.wires
  let wireBels := m.wires.flatMap (fun w => synthesizeExprToBels (wireNetName w.wireIdx) w.expr)
  let regCombBels := m.regs.zipIdx.flatMap (fun (r, k) => synthesizeExprToBels (regDinNetName k) r.nextExpr)
  let outBels := m.outputs.zipIdx.flatMap (fun (o, k) => synthesizeExprToBels (outNetName k) o.expr)
  let ffBels : List BelCell :=
    m.regs.zipIdx.map (fun (r, k) => { dstName := r.name, kind := .ff r.regIdx r.resetKind, inputs := [regDinNetName k] })
  let env1 := evalCombBelCellsFrom inputs regState (fun _ => 0#64) wireBels
  let env2 := evalCombBelCellsFrom inputs regState env1 regCombBels
  let env3 := evalCombBelCellsFrom inputs regState env2 outBels
  have hEnv1Wires : ∀ i < m.wires.length, env1 (wireNetName i) = wireEnv i := by
    have h := wireTable_go_sound m.inputNames.length m.regs.length inputs regState m.wires 0
      (fun _ => 0#64) (fun _ => 0#64) hWiresDag (fun _ hi => absurd hi (Nat.not_lt_zero _))
    intro i hi
    exact h i (by omega)
  obtain ⟨hEnv2Wires, _, hRegVals⟩ :=
    flatMap_indexed_sound m.inputNames.length m.regs.length m.wires.length inputs wireEnv regState
      regDinNetName slash_not_in_regDinNetName (@regDinNetName_injective) wireNetName_ne_regDinNetName
      (·.nextExpr) m.regs 0 env1 hRegsDag hEnv1Wires
  obtain ⟨_, _, hOutVals⟩ :=
    flatMap_indexed_sound m.inputNames.length m.regs.length m.wires.length inputs wireEnv regState
      outNetName slash_not_in_outNetName (@outNetName_injective) wireNetName_ne_outNetName
      (·.expr) m.outputs 0 env2 hOutsDag hEnv2Wires
  have hCellsEq :
      evalCombBelCells inputs regState (synthesizeModuleToBels m).cells = env3 := by
    dsimp only [evalCombBelCells, synthesizeModuleToBels]
    rw [evalCombBelCellsFrom_append, evalCombBelCellsFrom_append, evalCombBelCellsFrom_append,
        evalCombBelCellsFrom_ff_noop]
  refine ⟨?_, ?_⟩
  · intro k hk
    change evalCombBelCells inputs regState (synthesizeModuleToBels m).cells (outNetName k) = _
    rw [hCellsEq]
    simpa [Nat.zero_add] using hOutVals k hk
  · intro k hk
    change evalCombBelCells inputs regState (synthesizeModuleToBels m).cells (regDinNetName k) = _
    rw [hCellsEq]
    have hPresOut : env3 (regDinNetName k) = env2 (regDinNetName k) :=
      flatMap_preserves_foreign_root inputs regState outNetName (·.expr) (regDinNetName k)
        (slash_not_in_regDinNetName k) (fun n => Ne.symm (regDinNetName_ne_outNetName k n))
        m.outputs.zipIdx env2
    rw [hPresOut]
    simpa [Nat.zero_add] using hRegVals k hk

private theorem map_zipIdx_outputs_eq
    (outs : List OutputPort) (base : Nat)
    (fBel : Nat → BitVec 64) (fRtl : OutputPort → BitVec 64)
    (hEq : ∀ (idx : Nat) (hIdx : idx < outs.length), fBel (base + idx) = fRtl outs[idx]) :
    ((outs.map (·.name)).zipIdx base).map (fun (name, k) => (name, fBel k)) =
      outs.map (fun o => (o.name, fRtl o)) := by
  induction outs generalizing base with
  | nil => rfl
  | cons o rest ih =>
    simp only [List.map_cons, List.zipIdx_cons]
    have h0 := hEq 0 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero] at h0
    rw [h0, ih (base + 1)]
    intro idx hIdx
    have hSucc := hEq (idx + 1) (by simp; omega)
    have hAdd : (base + 1) + idx = base + (idx + 1) := by omega
    rw [hAdd]
    simpa [List.getElem_cons_succ] using hSucc

/-- **Universal Combinational Output Equivalence (`evalBelNetlistOutputs_synthesizeModuleToBels`)**:
For EVERY well-formed `m : RtlModule` (`checkRtlModule m = true`) and ALL 64-bit input/register
environments `inputs, regState : Nat → BitVec 64`, evaluating the synthesized `BelNetlist`
produces the exact output port list of `evalModuleOutputs m inputs regState`! -/
theorem evalBelNetlistOutputs_synthesizeModuleToBels
    (m : RtlModule)
    (inputs regState : Nat → BitVec 64)
    (hWf : checkRtlModule m = true) :
    evalBelNetlistOutputs (synthesizeModuleToBels m) inputs regState =
      evalModuleOutputs m inputs regState := by
  have hOut := (evalCombBelCells_synthesizeModuleToBels m inputs regState hWf).1
  unfold evalBelNetlistOutputs evalModuleOutputs
  have hNames : (synthesizeModuleToBels m).outputNames = m.outputs.map (·.name) := rfl
  rw [hNames]
  exact map_zipIdx_outputs_eq m.outputs 0
    (fun k => evalCombBelCells inputs regState (synthesizeModuleToBels m).cells (outNetName k))
    (fun o => evalRtlExpr inputs (evalWireTable inputs regState m.wires) regState o.expr)
    (fun idx hIdx => by simpa [Nat.zero_add] using hOut idx hIdx)

private theorem foldl_nonFf_noop
    (rst : Bool) (env : String → BitVec 64)
    (cells : List BelCell) (hNoFf : cells.filter isFfBel = [])
    (st : Nat → BitVec 64) :
    cells.foldl
      (fun (nextSt : Nat → BitVec 64) c =>
        match c.kind with
        | .ff regIdx resetKind =>
          let din := env (c.inputs.getD 0 "")
          let v := match resetKind with
            | .resetFree => din
            | .syncReset initVal => if rst then initVal else din
          fun i => if i == regIdx then v else nextSt i
        | _ => nextSt)
      st = st := by
  induction cells generalizing st with
  | nil => rfl
  | cons c rest ih =>
    cases hKind : c.kind <;>
      simp only [List.filter_cons, isFfBel, hKind, ↓reduceIte] at hNoFf
    case ff => nomatch hNoFf
    all_goals
      simp only [List.foldl_cons, hKind]
      exact ih hNoFf st

private theorem foldl_ffBels_step_eq
    (rst : Bool) (env : String → BitVec 64)
    (regs : List RegSpec) (base : Nat)
    (fRtl : RegSpec → BitVec 64)
    (hEq : ∀ (idx : Nat) (hIdx : idx < regs.length), env (regDinNetName (base + idx)) = fRtl regs[idx])
    (st : Nat → BitVec 64) :
    ((regs.zipIdx base).map (fun (r, k) =>
      ({ dstName := r.name, kind := .ff r.regIdx r.resetKind, inputs := [regDinNetName k] } : BelCell))).foldl
      (fun (nextSt : Nat → BitVec 64) c =>
        match c.kind with
        | .ff regIdx resetKind =>
          let din := env (c.inputs.getD 0 "")
          let v := match resetKind with
            | .resetFree => din
            | .syncReset initVal => if rst then initVal else din
          fun i => if i == regIdx then v else nextSt i
        | _ => nextSt)
      st =
    regs.foldl
      (fun (nextSt : Nat → BitVec 64) r =>
        let v := match r.resetKind with
          | .resetFree => fRtl r
          | .syncReset initVal => if rst then initVal else fRtl r
        fun i => if i == r.regIdx then v else nextSt i)
      st := by
  induction regs generalizing base st with
  | nil => rfl
  | cons r rest ih =>
    simp only [List.zipIdx_cons, List.map_cons, List.foldl_cons, List.getD_cons_zero]
    have h0 := hEq 0 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero] at h0
    rw [h0]
    apply ih (base + 1)
    intro idx hIdx
    have hSucc := hEq (idx + 1) (by simp; omega)
    have hAdd : (base + 1) + idx = base + (idx + 1) := by omega
    rw [hAdd]
    simpa [List.getElem_cons_succ] using hSucc

/-- **Universal Sequential Register-Step Equivalence (`stepBelNetlistRegs_synthesizeModuleToBels`)**:
For EVERY well-formed `m : RtlModule` (`checkRtlModule m = true`), reset signal `rst : Bool`,
and 64-bit input/register environments `inputs, regState : Nat → BitVec 64`, stepping the
synthesized `BelNetlist` by one clock edge produces the exact next register state of
`stepModuleRegs m rst inputs regState`! -/
theorem stepBelNetlistRegs_synthesizeModuleToBels
    (m : RtlModule)
    (rst : Bool)
    (inputs regState : Nat → BitVec 64)
    (hWf : checkRtlModule m = true) :
    stepBelNetlistRegs (synthesizeModuleToBels m) rst inputs regState =
      stepModuleRegs m rst inputs regState := by
  have hReg := (evalCombBelCells_synthesizeModuleToBels m inputs regState hWf).2
  let env := evalCombBelCells inputs regState (synthesizeModuleToBels m).cells
  have hStep : stepBelNetlistRegs (synthesizeModuleToBels m) rst inputs regState =
      ((synthesizeModuleToBels m).cells).foldl
        (fun (nextSt : Nat → BitVec 64) c =>
          match c.kind with
          | .ff regIdx resetKind =>
            let din := env (c.inputs.getD 0 "")
            let v := match resetKind with
              | .resetFree => din
              | .syncReset initVal => if rst then initVal else din
            fun i => if i == regIdx then v else nextSt i
          | _ => nextSt)
        regState := rfl
  rw [hStep]
  have hCells : (synthesizeModuleToBels m).cells =
      m.wires.flatMap (fun w => synthesizeExprToBels (wireNetName w.wireIdx) w.expr) ++
      m.regs.zipIdx.flatMap (fun (r, k) => synthesizeExprToBels (regDinNetName k) r.nextExpr) ++
      m.outputs.zipIdx.flatMap (fun (o, k) => synthesizeExprToBels (outNetName k) o.expr) ++
      m.regs.zipIdx.map (fun (r, k) =>
        ({ dstName := r.name, kind := .ff r.regIdx r.resetKind, inputs := [regDinNetName k] } : BelCell)) := rfl
  rw [hCells, List.foldl_append, List.foldl_append, List.foldl_append]
  rw [foldl_nonFf_noop rst env _ (flatMap_synthesizeExprToBels_no_ff (fun w : WireAssign => wireNetName w.wireIdx) (·.expr) m.wires),
      foldl_nonFf_noop rst env _ (flatMap_synthesizeExprToBels_no_ff (fun rk : RegSpec × Nat => regDinNetName rk.2) (fun rk => rk.1.nextExpr) m.regs.zipIdx),
      foldl_nonFf_noop rst env _ (flatMap_synthesizeExprToBels_no_ff (fun ok : OutputPort × Nat => outNetName ok.2) (fun ok => ok.1.expr) m.outputs.zipIdx)]
  exact foldl_ffBels_step_eq rst env m.regs 0
    (fun r => evalRtlExpr inputs (evalWireTable inputs regState m.wires) regState r.nextExpr)
    (fun idx hIdx => by simpa [Nat.zero_add] using hReg idx hIdx) regState

/-- Multi-cycle synchronous trace evaluation of a `BelNetlist` over a stream of `(rst, inputs)` cycles. -/
def runBelNetlistTrace
    (nl : BelNetlist)
    (regState : Nat → BitVec 64) :
    List (Bool × (Nat → BitVec 64)) → List (List (String × BitVec 64))
  | [] => []
  | (rst, ins) :: rest =>
    evalBelNetlistOutputs nl ins regState ::
      runBelNetlistTrace nl (stepBelNetlistRegs nl rst ins regState) rest

/-- Multi-cycle synchronous trace evaluation of an `RtlModule` over a stream of `(rst, inputs)` cycles. -/
def runRtlModuleTrace
    (m : RtlModule)
    (regState : Nat → BitVec 64) :
    List (Bool × (Nat → BitVec 64)) → List (List (String × BitVec 64))
  | [] => []
  | (rst, ins) :: rest =>
    evalModuleOutputs m ins regState ::
      runRtlModuleTrace m (stepModuleRegs m rst ins regState) rest

/-- **Universal Multi-Cycle Synchronous `BelNetlist` ↔ `RtlModule` Trace Equivalence
(`synthesizeModuleToBels_trace_equiv`)**:
Across ANY initial register state `regState₀` and ANY multi-cycle input/reset stimulus trace,
`synthesizeModuleToBels m` produces the exact cycle-by-cycle output stream of `m`! -/
theorem synthesizeModuleToBels_trace_equiv
    (m : RtlModule)
    (hWf : checkRtlModule m = true)
    (regState₀ : Nat → BitVec 64)
    (trace : List (Bool × (Nat → BitVec 64))) :
    runBelNetlistTrace (synthesizeModuleToBels m) regState₀ trace =
      runRtlModuleTrace m regState₀ trace := by
  induction trace generalizing regState₀ with
  | nil => rfl
  | cons cyc rest ih =>
    rcases cyc with ⟨rst, ins⟩
    simp only [runBelNetlistTrace, runRtlModuleTrace,
      evalBelNetlistOutputs_synthesizeModuleToBels m ins regState₀ hWf,
      stepBelNetlistRegs_synthesizeModuleToBels m rst ins regState₀ hWf,
      ih]

/-! ## 6. Verified RTL-to-BEL Signoff Gate (`checkSynthesizedRtlSignoff`) & Retimed MAC RTL Module -/

/-- Verify both `RtlModule` DAG/CDC well-formedness (`checkRtlModule`) and synthesized `BelNetlist`
cell-arity validity (`checkBelNetlistValid`). -/
def checkSynthesizedRtlSignoff (m : RtlModule) : Bool :=
  checkRtlModule m && checkBelNetlistValid (synthesizeModuleToBels m)

/-- **Theorem (`checkSynthesizedRtlSignoff_sound`)**:
Any `m : RtlModule` passing `checkSynthesizedRtlSignoff` satisfies `checkRtlModule m = true`,
produces a valid `BelNetlist`, preserves exact sequential flip-flop count (`countFfBels = m.regs.length`),
and is cycle-for-cycle semantically equivalent to `m` across all inputs and register states! -/
theorem checkSynthesizedRtlSignoff_sound (m : RtlModule)
    (hOk : checkSynthesizedRtlSignoff m = true) :
    checkRtlModule m = true ∧
    checkBelNetlistValid (synthesizeModuleToBels m) = true ∧
    countFfBels (synthesizeModuleToBels m) = m.regs.length ∧
    (∀ inputs regState,
      evalBelNetlistOutputs (synthesizeModuleToBels m) inputs regState =
        evalModuleOutputs m inputs regState) ∧
    (∀ rst inputs regState,
      stepBelNetlistRegs (synthesizeModuleToBels m) rst inputs regState =
        stepModuleRegs m rst inputs regState) := by
  simp only [checkSynthesizedRtlSignoff, Bool.and_eq_true] at hOk
  exact ⟨hOk.1, hOk.2, (synthesizeModuleToBels_valid_and_ff_count m).2,
    fun ins st => evalBelNetlistOutputs_synthesizeModuleToBels m ins st hOk.1,
    fun rst ins st => stepBelNetlistRegs_synthesizeModuleToBels m rst ins st hOk.1⟩

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
