module
/-
# Obend.Apps.ObendRisc — Flagship App #1: 3-Layer Open-Recursive RISC Softcore

Elaborates and proves the 3-layer open-recursive RISC softcore (`apps/obend-risc/`):
1. `BaseRiscCore.obend`: In-core instruction bit-slice decoders (`decodeOpcode`, `decodeRd`,
   `decodeFunct3`, `decodeRs1`, `decodeRs2`, `decodeFunct7`, sign-extended `decodeImmI` & `decodeImmS`)
   using `.obend` bitwise/shift/signed primitives (`&`, `|`, `^`, `<<`, `>>>`, `>>`, `<s`), plus
   two's-complement RV64I/M ALU execution.
2. `PrivilegeCsrOverride.obend`: Machine-mode CSR synchronous trap (`ECALL`), `CSRRS` readback, and
   trap return (`MRET`) override layer preempting base/extension execution on trap entry and
   redirecting `pc` to `mtvec = 0x50`.
3. `CustomSimdZkExt.obend`: Custom opcode `0x2B` (`43`) SIMD/ZK Goldilocks multiply-accumulate
   extension delegating non-extension opcodes to `super`.
4. `ComposedRiscCpu.obend`: Complete 3-layer open-recursive composition + Fibonacci/MAC/cross-layer
   test points, compiled to hardware via `compileRichBookToRtl`.

Also formalizes both the Layer-1 `baseRiscCpuRtlModule : RtlModule` and the 3-layer sequential
`always_ff @(posedge clk)` SystemVerilog softcore `obendRiscCpuRtlModule : RtlModule` (holding
`pc`, `mstatus`, `mepc`, `mcause`, `cycle_cnt`, and `x1..x15` in synchronous hardware registers and
driving `imem_addr` and `dmem_addr`/`dmem_wdata`/`dmem_we`), whose exact `emitModuleSV` output is
compiled by Verilator in `apps/obend-risc/verilator/obend_risc_cpu.sv`.
-/
public import Lean
public import Obend.Spec.FrontEnd
public import Obend.Spec.Capture
public import Obend.Spec.Sha256
public import Obend.Logic.Program
public import Obend.Logic.Obligation
public import Obend.Leaf.Emit
public import Obend.Leaf.Specialize
public import Obend.Leaf.Futamura
public import Obend.Spec.CrossPackage
public import Obend.Hardware.HDL
public import Obend.Hardware.Types
public import Obend.Hardware.Compiler
public import Obend.Hardware.Synth
public import Obend.Tactic.Weave
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
namespace Obend.Apps.ObendRisc

open Lean (Json toJson Name Ident Syntax TSyntax Quote quote mkIdent)
open Lean.Elab.Command (CommandElabM elabCommand)
open Obend.Core.Term
open Obend.Equiv
open Obend.Logic
open Obend.Leaf
open Obend.Leaf.Futamura
open Obend.Spec.CrossPackage
open Obend.Hardware
open Obend.Hardware.HDL
open Obend.Hardware.Types
open Obend.Hardware.Compiler
open Obend.Hardware.Synth
open Obend.Tactic.Weave

set_option autoImplicit false

/-- Local alias allowing `by weave` alongside `by weave_chain` and `by obend_law`. -/
macro "weave" : tactic => `(tactic| weave_chain)

/-! ## 0. `#import_obend` is `Obend.Elab.Workbook`'s (the one importer, 2026-11-04); this module
only consumes the constants it emits (`<def>_comp`, `<def>_book`, `<def>_val`, `claim_*_{obj,just,holds}`,
`laws_count`). -/

/-! ## 1. Elaborating the 3-Layer `.obend` RISC Softcore Hierarchy & Lowering Books to RTL -/

#import_obend "apps/obend-risc/BaseRiscCore.obend" as BaseRisc
#import_obend "apps/obend-risc/PrivilegeCsrOverride.obend" as PrivRisc
#import_obend "apps/obend-risc/CustomSimdZkExt.obend" as ExtRisc
#import_obend "apps/obend-risc/ComposedRiscCpu.obend" as ComposedRisc

/-- Theorem: Evaluating the 8-element Fibonacci sequence sum (`1+1+2+3+5+8+13+21 = 54`),
    the 4-instruction custom SIMD/ZK MAC chain (`1282`), and cross-module imported layer
    consistency (`true`) on `composedRiscCpu()` in `.obend` reduces to their exact expected values. -/
theorem obend_risc_workbook_fibonacci_and_mac_eval :
    ComposedRisc.evalFibonacci8Sum_val = .nat 54 ∧
    ComposedRisc.evalCustomSimdMac4_val = .nat 1282 ∧
    ComposedRisc.evalCrossLayerConsistency_val = .boolean true ∧
    PrivRisc.verifyBaseAddMatchesPriv_val = .boolean true ∧
    ExtRisc.verifyExtCrossModuleConsistency_val = .boolean true :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Theorem: All four elaborated `.obend` RISC books (`BaseRiscCore`, `PrivilegeCsrOverride`,
    `CustomSimdZkExt`, and `ComposedRiscCpu`) compile directly through `compileRichBookToRtl`
    into DAG-valid, CDC-safe `RtlModule`s (`checkRtlModule = true`). -/
theorem obend_risc_books_compile_to_valid_rtl :
    ((compileRichBookToRtl "base_risc_book_rtl" {} BaseRisc.baseRiscCore_book).map checkRtlModule) = some true ∧
    ((compileRichBookToRtl "priv_risc_book_rtl" {} PrivRisc.privilegeRiscCore_book).map checkRtlModule) = some true ∧
    ((compileRichBookToRtl "ext_risc_book_rtl" {} ExtRisc.customSimdZkRiscCore_book).map checkRtlModule) = some true ∧
    ((compileRichBookToRtl "composed_risc_book_rtl" {} ComposedRisc.composedRiscCpu_book).map checkRtlModule) = some true := by
  decide +kernel

/-! ## 2. Sequential `always_ff @(posedge clk)` SystemVerilog RISC Softcore (`obendRiscCpuRtlModule`) -/

/-- Clock domain for the sequential RISC softcore. -/
def riscClkDomain : ClkDomain :=
  .coreClk

/-- Build a 15-way register file read mux tree over `x1..x15` (registers `5..19`),
    returning `64'd0` for `x0` (`idx == 0`). -/
def buildRegReadMux (selWire : Nat) : List (Nat × Nat) → RtlExpr
  | [] => .const 0#64
  | (regNum, regSlot) :: rest =>
    .mux (.alu .eq (.wireRef selWire) (.const (BitVec.ofNat 64 regNum)))
      (.regRead regSlot)
      (buildRegReadMux selWire rest)

/-- Standard mapping from architectural register numbers `1..15` to `RtlModule` register slots `5..19`. -/
def archRegSlots : List (Nat × Nat) :=
  [(1, 5), (2, 6), (3, 7), (4, 8), (5, 9), (6, 10), (7, 11), (8, 12),
   (9, 13), (10, 14), (11, 15), (12, 16), (13, 17), (14, 18), (15, 19)]

/-- Build the architectural register writeback `RegSpec` for `x_k` at slot `4 + k`. -/
def buildArchRegSpec (k : Nat) : RegSpec :=
  let slot := 4 + k
  { regIdx := slot
    name := s!"x{k}"
    domain := riscClkDomain
    resetKind := .syncReset 0#64
    isSynchronizer := false
    nextExpr :=
      .mux (.alu .bitAnd (.wireRef 21) (.alu .eq (.wireRef 1) (.const (BitVec.ofNat 64 k))))
        (.wireRef 20)
        (.regRead slot) }

/-- Shared register table (`pc`, `mstatus`, `mepc`, `mcause`, `cycle_cnt`, and `x1..x15`) for both
    the Layer-1 `baseRiscCpuRtlModule` and the 3-layer `obendRiscCpuRtlModule`. -/
def riscCpuRegs : List RegSpec :=
  [ { regIdx := 0, name := "pc", domain := riscClkDomain,
      resetKind := .syncReset 0#64, isSynchronizer := false, nextExpr := .wireRef 23 },
    { regIdx := 1, name := "mstatus", domain := riscClkDomain,
      resetKind := .syncReset 0#64, isSynchronizer := false,
      nextExpr := .mux (.wireRef 12) (.const 24#64)
                    (.mux (.wireRef 13) (.const 8#64) (.regRead 1)) },
    { regIdx := 2, name := "mepc", domain := riscClkDomain,
      resetKind := .syncReset 0#64, isSynchronizer := false,
      nextExpr := .mux (.wireRef 12) (.alu .add (.regRead 0) (.const 4#64)) (.regRead 2) },
    { regIdx := 3, name := "mcause", domain := riscClkDomain,
      resetKind := .syncReset 0#64, isSynchronizer := false,
      nextExpr := .mux (.wireRef 12) (.const 11#64) (.regRead 3) },
    { regIdx := 4, name := "cycle_cnt", domain := riscClkDomain,
      resetKind := .syncReset 0#64, isSynchronizer := false,
      nextExpr := .alu .add (.regRead 4) (.const 1#64) }
  ] ++ (List.range 15).map (fun i => buildArchRegSpec (i + 1))

/-- Shared output port table for `baseRiscCpuRtlModule` and `obendRiscCpuRtlModule`. -/
def riscCpuOutputs : List OutputPort :=
  [ { name := "imem_addr", expr := .regRead 0 },
    { name := "dmem_addr", expr := .wireRef 24 },
    { name := "dmem_wdata", expr := .wireRef 11 },
    { name := "dmem_we", expr := .wireRef 25 },
    { name := "pc_out", expr := .regRead 0 },
    { name := "mstatus_out", expr := .regRead 1 },
    { name := "mepc_out", expr := .regRead 2 },
    { name := "mcause_out", expr := .regRead 3 },
    { name := "cycle_cnt_out", expr := .regRead 4 },
    { name := "x1_out", expr := .regRead 5 },
    { name := "x2_out", expr := .regRead 6 },
    { name := "x3_out", expr := .regRead 7 },
    { name := "x4_out", expr := .regRead 8 },
    { name := "x5_out", expr := .regRead 9 },
    { name := "x6_out", expr := .regRead 10 },
    { name := "x7_out", expr := .regRead 11 },
    { name := "x8_out", expr := .regRead 12 },
    { name := "x9_out", expr := .regRead 13 },
    { name := "x10_out", expr := .regRead 14 },
    { name := "x11_out", expr := .regRead 15 },
    { name := "x12_out", expr := .regRead 16 },
    { name := "x13_out", expr := .regRead 17 },
    { name := "x14_out", expr := .regRead 18 },
    { name := "x15_out", expr := .regRead 19 } ]

/-- Stage A wires (`w_0..w_11`): In-core instruction bit-slice & sign-extended immediate decoders
    plus architectural register read muxes (`rs1_val`, `rs2_val`). -/
def riscDecodeAndReadWires : List WireAssign :=
  [ { wireIdx := 0, name := "opcode",
      expr := .alu .bitAnd (.inputPort 0) (.const 127#64) },
    { wireIdx := 1, name := "rd",
      expr := .alu .bitAnd (.alu .lshr (.inputPort 0) (.const 7#64)) (.const 31#64) },
    { wireIdx := 2, name := "funct3",
      expr := .alu .bitAnd (.alu .lshr (.inputPort 0) (.const 12#64)) (.const 7#64) },
    { wireIdx := 3, name := "rs1",
      expr := .alu .bitAnd (.alu .lshr (.inputPort 0) (.const 15#64)) (.const 31#64) },
    { wireIdx := 4, name := "rs2",
      expr := .alu .bitAnd (.alu .lshr (.inputPort 0) (.const 20#64)) (.const 31#64) },
    { wireIdx := 5, name := "imm_u12",
      expr := .alu .bitAnd (.alu .lshr (.inputPort 0) (.const 20#64)) (.const 4095#64) },
    { wireIdx := 6, name := "funct7",
      expr := .alu .bitAnd (.alu .lshr (.inputPort 0) (.const 25#64)) (.const 127#64) },
    { wireIdx := 7, name := "imm_i",
      expr := .alu .ashr (.alu .shl (.inputPort 0) (.const 32#64)) (.const 52#64) },
    { wireIdx := 8, name := "imm_s",
      expr := .alu .ashr
                (.alu .shl
                  (.alu .bitOr (.alu .shl (.wireRef 6) (.const 5#64)) (.wireRef 1))
                  (.const 52#64))
                (.const 52#64) },
    { wireIdx := 9, name := "imm_b",
      expr := .alu .ashr
                (.alu .shl
                  (.alu .bitOr
                    (.alu .bitOr
                      (.alu .shl (.alu .bitAnd (.alu .lshr (.inputPort 0) (.const 31#64)) (.const 1#64)) (.const 12#64))
                      (.alu .shl (.alu .bitAnd (.alu .lshr (.inputPort 0) (.const 7#64)) (.const 1#64)) (.const 11#64)))
                    (.alu .bitOr
                      (.alu .shl (.alu .bitAnd (.alu .lshr (.inputPort 0) (.const 25#64)) (.const 63#64)) (.const 5#64))
                      (.alu .shl (.alu .bitAnd (.alu .lshr (.inputPort 0) (.const 8#64)) (.const 15#64)) (.const 1#64))))
                  (.const 51#64))
                (.const 51#64) },
    { wireIdx := 10, name := "rs1_val",
      expr := buildRegReadMux 3 archRegSlots },
    { wireIdx := 11, name := "rs2_val",
      expr := buildRegReadMux 4 archRegSlots } ]

/-- Stage B wires (`w_12..w_16`): Layer 2 (`PrivilegeCsrOverride`) & Layer 3 (`CustomSimdZkExt`)
    decode strobes (`enablePrivAndExt = false` disables Layer 2 & Layer 3 overrides). -/
def riscLayerStrobeWires (enablePrivAndExt : Bool) : List WireAssign :=
  [ { wireIdx := 12, name := "is_trap",
      expr := if enablePrivAndExt then
                .alu .bitAnd
                  (.alu .bitAnd (.alu .eq (.wireRef 0) (.const 115#64))
                                (.alu .eq (.wireRef 2) (.const 0#64)))
                  (.alu .eq (.wireRef 5) (.const 0#64))
              else .const 0#64 },
    { wireIdx := 13, name := "is_mret",
      expr := if enablePrivAndExt then
                .alu .bitAnd
                  (.alu .bitAnd (.alu .eq (.wireRef 0) (.const 115#64))
                                (.alu .eq (.wireRef 2) (.const 0#64)))
                  (.alu .eq (.wireRef 5) (.const 770#64))
              else .const 0#64 },
    { wireIdx := 14, name := "is_csrrs",
      expr := if enablePrivAndExt then
                .alu .bitAnd (.alu .eq (.wireRef 0) (.const 115#64))
                             (.alu .eq (.wireRef 2) (.const 2#64))
              else .const 0#64 },
    { wireIdx := 15, name := "csr_rdata",
      expr := .mux (.alu .eq (.wireRef 5) (.const 768#64))
                (.regRead 1)
                (.mux (.alu .eq (.wireRef 5) (.const 833#64))
                  (.regRead 2)
                  (.mux (.alu .eq (.wireRef 5) (.const 834#64))
                    (.regRead 3)
                    (.const 80#64))) },
    { wireIdx := 16, name := "is_custom_ext",
      expr := if enablePrivAndExt then
                .alu .eq (.wireRef 0) (.const 43#64)
              else .const 0#64 } ]

/-- Stage C wires (`w_17..w_25`): Standard RV64I/M ALU, CustomSimdZkExt MAC/Goldilocks datapath,
    writeback mux/enable, branch comparator, `next_pc`, and `dmem` interface. -/
def riscDatapathAndControlWires : List WireAssign :=
  [ { wireIdx := 17, name := "base_alu_rhs",
      expr := .mux (.alu .eq (.wireRef 0) (.const 19#64)) (.wireRef 7) (.wireRef 11) },
    { wireIdx := 18, name := "base_alu_out",
      expr := .mux (.alu .eq (.wireRef 2) (.const 0#64))
                (.mux (.alu .bitAnd (.alu .eq (.wireRef 0) (.const 51#64)) (.alu .eq (.wireRef 6) (.const 32#64)))
                  (.alu .sub (.wireRef 10) (.wireRef 17))
                  (.mux (.alu .bitAnd (.alu .eq (.wireRef 0) (.const 51#64)) (.alu .eq (.wireRef 6) (.const 1#64)))
                    (.alu .mul (.wireRef 10) (.wireRef 17))
                    (.alu .add (.wireRef 10) (.wireRef 17))))
                (.mux (.alu .eq (.wireRef 2) (.const 1#64))
                  (.alu .shl (.wireRef 10) (.wireRef 17))
                  (.mux (.alu .eq (.wireRef 2) (.const 2#64))
                    (.alu .slt (.wireRef 10) (.wireRef 17))
                    (.mux (.alu .eq (.wireRef 2) (.const 3#64))
                      (.alu .ult (.wireRef 10) (.wireRef 17))
                      (.mux (.alu .eq (.wireRef 2) (.const 4#64))
                        (.alu .bitXor (.wireRef 10) (.wireRef 17))
                        (.mux (.alu .eq (.wireRef 2) (.const 5#64))
                          (.mux (.alu .eq (.alu .lshr (.wireRef 6) (.const 1#64)) (.const 16#64))
                            (.alu .ashr (.wireRef 10) (.wireRef 17))
                            (.alu .lshr (.wireRef 10) (.wireRef 17)))
                          (.mux (.alu .eq (.wireRef 2) (.const 6#64))
                            (.alu .bitOr (.wireRef 10) (.wireRef 17))
                            (.alu .bitAnd (.wireRef 10) (.wireRef 17)))))))) },
    { wireIdx := 19, name := "custom_ext_out",
      expr := .mux (.alu .eq (.wireRef 2) (.const 0#64))
                (.alu .add (.alu .mul (.wireRef 10) (.wireRef 11)) (.wireRef 6))
                (.mux (.alu .eq (.wireRef 2) (.const 1#64))
                  (.alu .add
                    (.alu .sub
                      (.alu .shl (.alu .bitAnd (.wireRef 10) (.const 4294967295#64)) (.const 32#64))
                      (.alu .bitAnd (.wireRef 10) (.const 4294967295#64)))
                    (.wireRef 11))
                  (.alu .add (.wireRef 10) (.alu .shl (.wireRef 11) (.const 1#64)))) },
    { wireIdx := 20, name := "wb_val",
      expr := .mux (.wireRef 14)
                (.wireRef 15)
                (.mux (.wireRef 16)
                  (.wireRef 19)
                  (.mux (.alu .eq (.wireRef 0) (.const 3#64))
                    (.inputPort 1)
                    (.mux (.alu .eq (.wireRef 0) (.const 111#64))
                      (.alu .add (.regRead 0) (.const 4#64))
                      (.wireRef 18)))) },
    { wireIdx := 21, name := "wb_en",
      expr := .mux (.wireRef 12)
                (.const 0#64)
                (.alu .bitOr
                  (.alu .bitOr
                    (.alu .bitOr
                      (.alu .bitOr
                        (.alu .bitOr (.wireRef 14) (.wireRef 16))
                        (.alu .eq (.wireRef 0) (.const 19#64)))
                      (.alu .eq (.wireRef 0) (.const 51#64)))
                    (.alu .eq (.wireRef 0) (.const 3#64)))
                  (.alu .eq (.wireRef 0) (.const 111#64))) },
    { wireIdx := 22, name := "branch_taken",
      expr := .mux (.alu .eq (.wireRef 2) (.const 0#64))
                (.alu .eq (.wireRef 10) (.wireRef 11))
                (.mux (.alu .eq (.wireRef 2) (.const 1#64))
                  (.mux (.alu .eq (.wireRef 10) (.wireRef 11)) (.const 0#64) (.const 1#64))
                  (.mux (.alu .eq (.wireRef 2) (.const 4#64))
                    (.alu .slt (.wireRef 10) (.wireRef 11))
                    (.mux (.alu .slt (.wireRef 10) (.wireRef 11)) (.const 0#64) (.const 1#64)))) },
    { wireIdx := 23, name := "next_pc",
      expr := .mux (.wireRef 12)
                (.const 80#64)
                (.mux (.wireRef 13)
                  (.regRead 2)
                  (.mux (.alu .eq (.wireRef 0) (.const 99#64))
                    (.mux (.wireRef 22)
                      (.alu .add (.regRead 0) (.wireRef 9))
                      (.alu .add (.regRead 0) (.const 4#64)))
                    (.mux (.alu .eq (.wireRef 0) (.const 111#64))
                      (.alu .add (.regRead 0) (.alu .shl (.wireRef 7) (.const 1#64)))
                      (.alu .add (.regRead 0) (.const 4#64))))) },
    { wireIdx := 24, name := "dmem_addr_w",
      expr := .mux (.alu .eq (.wireRef 0) (.const 35#64))
                (.alu .add (.wireRef 10) (.wireRef 8))
                (.alu .add (.wireRef 10) (.wireRef 7)) },
    { wireIdx := 25, name := "dmem_we_w",
      expr := .mux (.wireRef 12)
                (.const 0#64)
                (.mux (.alu .eq (.wireRef 0) (.const 35#64)) (.const 1#64) (.const 0#64)) } ]

/-- Parameterized wire table constructor: `enablePrivAndExt = false` yields the pure Layer-1
    `BaseRiscCore` softcore (`baseRiscCpuRtlModule`), while `enablePrivAndExt = true` yields the
    full 3-layer composed softcore (`obendRiscCpuRtlModule`). -/
def mkRiscCpuWires (enablePrivAndExt : Bool) : List WireAssign :=
  riscDecodeAndReadWires ++ riscLayerStrobeWires enablePrivAndExt ++ riscDatapathAndControlWires

/-- Layer-1 (`BaseRiscCore`) sequential RV64I/M softcore `RtlModule` (without Layer 2 or Layer 3). -/
def baseRiscCpuRtlModule : RtlModule :=
  { name := "base_risc_cpu"
    inputNames := ["imem_rdata", "dmem_rdata"]
    wires := mkRiscCpuWires false
    regs := riscCpuRegs
    outputs := riscCpuOutputs }

/-- Complete 3-layer sequential `always_ff @(posedge clk)` SystemVerilog RISC softcore (`obend_risc_cpu`).
    Performs in-core bit-slice & sign-extended instruction decode from raw `imem_rdata` (`inputPort 0`),
    holds `pc`, `mstatus`, `mepc`, `mcause`, `cycle_cnt`, and `x1..x15` in synchronous registers,
    and drives `imem_addr` and `dmem_addr`/`dmem_wdata`/`dmem_we`. -/
def obendRiscCpuRtlModule : RtlModule :=
  { name := "obend_risc_cpu"
    inputNames := ["imem_rdata", "dmem_rdata"]
    wires := mkRiscCpuWires true
    regs := riscCpuRegs
    outputs := riscCpuOutputs }

/-- Theorem: Both `baseRiscCpuRtlModule` and `obendRiscCpuRtlModule` are well-formed topological DAGs
    and pass CDC checks (`checkRtlModule = true`). -/
theorem obendRiscCpuRtlModule_valid :
    checkRtlModule baseRiscCpuRtlModule = true ∧
    checkRtlModule obendRiscCpuRtlModule = true := by
  decide +kernel

/-- Theorem: `obendRiscCpuRtlModule` synthesizes cleanly to a valid FPGA BEL netlist (`LUT6`/`CARRY8`/`FDRE`)
    with exactly 20 `FDRE` flip-flop BELs (`pc`, `mstatus`, `mepc`, `mcause`, `cycle_cnt`, and `x1..x15`). -/
theorem obendRiscCpuRtlModule_bel_valid :
    checkBelNetlistValid (synthesizeModuleToBels obendRiscCpuRtlModule) = true ∧
    countFfBels (synthesizeModuleToBels obendRiscCpuRtlModule) = 20 :=
  ⟨(synthesizeModuleToBels_valid_and_ff_count obendRiscCpuRtlModule).1,
   (synthesizeModuleToBels_valid_and_ff_count obendRiscCpuRtlModule).2.trans (by decide +kernel)⟩

/-- Firmware ROM lookup matching `apps/obend-risc/firmware/test_prog.hex` (indexed by `pc >> 2`). -/
def riscFirmwareRom : Nat → BitVec 64
  | 0  => 0x00100093#64 -- 0x00: ADDI x1, x0, 1
  | 1  => 0x00100113#64 -- 0x04: ADDI x2, x0, 1
  | 2  => 0x002081B3#64 -- 0x08: ADD  x3, x1, x2
  | 3  => 0x00310233#64 -- 0x0C: ADD  x4, x2, x3
  | 4  => 0x004182B3#64 -- 0x10: ADD  x5, x3, x4
  | 5  => 0x00520333#64 -- 0x14: ADD  x6, x4, x5
  | 6  => 0x006283B3#64 -- 0x18: ADD  x7, x5, x6
  | 7  => 0x00730433#64 -- 0x1C: ADD  x8, x6, x7
  | 8  => 0x00000073#64 -- 0x20: ECALL (standard RISC-V trap -> MTVEC=0x50)
  | 9  => 0x027305AB#64 -- 0x24: ZK.MAC x11, x6, x7, 1
  | 10 => 0x0435862B#64 -- 0x28: ZK.MAC x12, x11, x3, 2
  | 11 => 0x064606AB#64 -- 0x2C: ZK.MAC x13, x12, x4, 3
  | 12 => 0x0836872B#64 -- 0x30: ZK.MAC x14, x13, x3, 4
  | 13 => 0x00A407B3#64 -- 0x34: ADD  x15, x8, x10
  | 14 => 0x00E787B3#64 -- 0x38: ADD  x15, x15, x14
  | 15 => 0x00F02023#64 -- 0x3C: SW   x15, 0(x0)  -> dmem[0] <= 1345
  | 16 => 0x00E02423#64 -- 0x40: SW   x14, 8(x0)  -> dmem[8] <= 1282
  | 17 => 0x00802483#64 -- 0x44: LW   x9,  8(x0)  -> x9 <= dmem[8] = 1282
  | 18 => 0x00000013#64 -- 0x48: NOP
  | 19 => 0x00000013#64 -- 0x4C: NOP
  | 20 => 0x342024F3#64 -- 0x50: CSRRS x9, mcause, x0 (MTVEC handler: x9 <= 11)
  | 21 => 0x01F48513#64 -- 0x54: ADDI  x10, x9, 31    (x10 <= 42)
  | 22 => 0x30200073#64 -- 0x58: MRET                 (pc <= mepc = 0x24, mstatus <= 8)
  | _  => 0x00000013#64

/-- Step `obendRiscCpuRtlModule` coupled to `riscFirmwareRom` AND stateful `dmem` for `n` clock cycles. -/
def runRiscFirmwareSocCycles :
    Nat → (Nat → BitVec 64) → (Nat → BitVec 64) → (Nat → BitVec 64) × (Nat → BitVec 64)
  | 0, st, dmem => (st, dmem)
  | k + 1, st, dmem =>
    let pcIdx := (st 0).toNat / 4
    let inst := riscFirmwareRom pcIdx
    -- Combinational evaluation of dmem_addr before dmem_rdata lookup
    let preInputs : Nat → BitVec 64 := fun p => if p == 0 then inst else 0#64
    let preWires := evalWireTable preInputs st obendRiscCpuRtlModule.wires
    let dAddr := (preWires 24 &&& 63#64).toNat
    let inputs : Nat → BitVec 64 := fun p =>
      if p == 0 then inst
      else if p == 1 then dmem dAddr
      else 0#64
    let postWires := evalWireTable inputs st obendRiscCpuRtlModule.wires
    let dmemWe := postWires 25
    let dmemWdata := postWires 11
    let dmem' : Nat → BitVec 64 :=
      if dmemWe != 0#64 then
        fun addr => if addr == dAddr then dmemWdata else dmem addr
      else
        dmem
    let st' := stepModuleRegs obendRiscCpuRtlModule false inputs st
    runRiscFirmwareSocCycles k st' dmem'

/-- Theorem: Running 21 cycles of `riscFirmwareRom` (`test_prog.hex`) on `obendRiscCpuRtlModule`
    inside Lean produces the exact same cycle-accurate architectural register and `dmem` state as
    the Verilator simulation (`x8 = 21`, `mepc = 36`, `mcause = 11`, `mstatus = 8`, `x10 = 42`,
    `x11 = 105`, `x12 = 212`, `x13 = 639`, `x14 = 1282`, `x15 = 1345`, `dmem[0] = 1345`,
    `dmem[8] = 1282`, and `x9 = 1282` read back via `LW x9, 8(x0)`). -/
theorem obendRiscCpuRtlModule_firmware_sim_sound :
    let (finalSt, finalDmem) := runRiscFirmwareSocCycles 21 (fun _ => 0#64) (fun _ => 0#64)
    finalSt 1 = 8#64 ∧       -- mstatus = 8 after MRET
    finalSt 2 = 36#64 ∧      -- mepc = 0x24
    finalSt 3 = 11#64 ∧      -- mcause = 11
    finalSt 4 = 21#64 ∧      -- cycle_cnt = 21
    finalSt 12 = 21#64 ∧     -- x8 = Fib(8) = 21
    finalSt 13 = 1282#64 ∧   -- x9 = LW readback from dmem[8] = 1282
    finalSt 14 = 42#64 ∧     -- x10 = CSRRS mcause (11) + 31 = 42
    finalSt 15 = 105#64 ∧    -- x11 = ZK_MAC #1 = 105
    finalSt 16 = 212#64 ∧    -- x12 = ZK_MAC #2 = 212
    finalSt 17 = 639#64 ∧    -- x13 = ZK_MAC #3 = 639
    finalSt 18 = 1282#64 ∧   -- x14 = ZK_MAC #4 = 1282
    finalSt 19 = 1345#64 ∧   -- x15 = final checksum = 1345
    finalDmem 0 = 1345#64 ∧  -- SW x15, 0(x0)
    finalDmem 8 = 1282#64    -- SW x14, 8(x0) (non-zero S-type offset)
    := by
  decide +kernel

/-! ## 3. Core Deliverable Theorems (`risc_base_opcode_non_interference`, `risc_privilege_trap_preempts_base_and_ext`, `risc_read_set_monotonicity`, `risc_inCore_futamura2`) -/

/-- Single wire-assignment step matching `evalWireTable`'s `foldl` body. -/
def wireFoldStep (inputs regs env : Nat → BitVec 64) (a : WireAssign) (i : Nat) : BitVec 64 :=
  if i == a.wireIdx then evalRtlExpr inputs env regs a.expr else env i

theorem evalWireTable_eq_foldl (inputs regs : Nat → BitVec 64) (assigns : List WireAssign) :
    evalWireTable inputs regs assigns = assigns.foldl (wireFoldStep inputs regs) (fun _ => 0#64) :=
  rfl

/-- Index-preservation lemma: folding wires whose `wireIdx` never equals `k` leaves `env k` untouched
    without evaluating any wire expression! -/
theorem foldl_wireFoldStep_preserve
    (inputs regs : Nat → BitVec 64) (k : Nat) :
    ∀ (ws : List WireAssign) (env : Nat → BitVec 64),
      (ws.all fun a => a.wireIdx != k) = true →
      (ws.foldl (wireFoldStep inputs regs) env) k = env k
  | [], _, _ => rfl
  | a :: rest, env, hAll => by
    simp only [List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq] at hAll
    have hBeq : (k == a.wireIdx) = false := beq_false_of_ne (Ne.symm hAll.1)
    rw [List.foldl_cons, foldl_wireFoldStep_preserve inputs regs k rest _ hAll.2]
    simp [wireFoldStep, hBeq]

/-- Single register-step function matching `stepModuleRegs`'s `foldl` body. -/
def regFoldStep (rst : Bool) (inputs wireEnv regState nextSt : Nat → BitVec 64) (r : RegSpec) (i : Nat) :
    BitVec 64 :=
  let v :=
    match r.resetKind with
    | .resetFree => evalRtlExpr inputs wireEnv regState r.nextExpr
    | .syncReset initVal =>
      if rst then initVal else evalRtlExpr inputs wireEnv regState r.nextExpr
  if i == r.regIdx then v else nextSt i

theorem stepModuleRegs_eq_foldl (m : RtlModule) (rst : Bool) (inputs regState : Nat → BitVec 64) :
    stepModuleRegs m rst inputs regState =
      m.regs.foldl (regFoldStep rst inputs (evalWireTable inputs regState m.wires) regState) regState :=
  rfl

/-- Index-preservation lemma for `regFoldStep`: folding registers whose `regIdx ≠ k` leaves `nextSt k` untouched! -/
theorem foldl_regFoldStep_preserve
    (rst : Bool) (inputs wireEnv regState : Nat → BitVec 64) (k : Nat) :
    ∀ (rs : List RegSpec) (st : Nat → BitVec 64),
      (rs.all fun r => r.regIdx != k) = true →
      (rs.foldl (regFoldStep rst inputs wireEnv regState) st) k = st k
  | [], _, _ => rfl
  | r :: rest, st, hAll => by
    simp only [List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq] at hAll
    have hBeq : (k == r.regIdx) = false := beq_false_of_ne (Ne.symm hAll.1)
    rw [List.foldl_cons, foldl_regFoldStep_preserve rst inputs wireEnv regState k rest _ hAll.2]
    simp [regFoldStep, hBeq]

/-- Decode-stage wire extraction lemma (`w_0`, `w_2`, `w_5`) without unfolding `w_7..w_11`. -/
theorem riscDecodeAndReadWires_vals (inputs regState : Nat → BitVec 64) :
    let env12 := riscDecodeAndReadWires.foldl (wireFoldStep inputs regState) (fun _ => 0#64)
    env12 0 = (inputs 0 &&& 127#64) ∧
    env12 2 = ((inputs 0 >>> 12) &&& 7#64) ∧
    env12 5 = ((inputs 0 >>> 20) &&& 4095#64) := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · change ([riscDecodeAndReadWires[0]] ++ riscDecodeAndReadWires.drop 1).foldl
      (wireFoldStep inputs regState) (fun _ => 0#64) 0 = _
    rw [List.foldl_append, foldl_wireFoldStep_preserve inputs regState 0 _ _ (by decide +kernel)]
    rfl
  · change ((riscDecodeAndReadWires.take 3) ++ (riscDecodeAndReadWires.drop 3)).foldl
      (wireFoldStep inputs regState) (fun _ => 0#64) 2 = _
    rw [List.foldl_append, foldl_wireFoldStep_preserve inputs regState 2 _ _ (by decide +kernel)]
    rfl
  · change ((riscDecodeAndReadWires.take 6) ++ (riscDecodeAndReadWires.drop 6)).foldl
      (wireFoldStep inputs regState) (fun _ => 0#64) 5 = _
    rw [List.foldl_append, foldl_wireFoldStep_preserve inputs regState 5 _ _ (by decide +kernel)]
    rfl

/-- Lemma: For any non-privilege (`opcode != 115`) and non-custom-extension (`opcode != 43`)
    instruction word `inputs 0`, the entire 26-wire table of `obendRiscCpuRtlModule` evaluates
    identically to the Layer-1 `baseRiscCpuRtlModule` wire table across all register states! -/
theorem risc_wireTable_non_interference
    (inputs regState : Nat → BitVec 64)
    (hNotExt : (inputs 0 &&& 127#64 == 43#64) = false)
    (hNotTrapOp : (inputs 0 &&& 127#64 == 115#64) = false) :
    evalWireTable inputs regState obendRiscCpuRtlModule.wires =
      evalWireTable inputs regState baseRiscCpuRtlModule.wires := by
  rw [evalWireTable_eq_foldl, evalWireTable_eq_foldl]
  unfold obendRiscCpuRtlModule baseRiscCpuRtlModule mkRiscCpuWires
  simp only [List.foldl_append]
  have hDec := riscDecodeAndReadWires_vals inputs regState
  generalize riscDecodeAndReadWires.foldl (wireFoldStep inputs regState) (fun _ => 0#64) = env12 at hDec ⊢
  rcases hDec with ⟨h0, _, _⟩
  suffices hStrobes :
      (riscLayerStrobeWires true).foldl (wireFoldStep inputs regState) env12 =
      (riscLayerStrobeWires false).foldl (wireFoldStep inputs regState) env12 by
    rw [hStrobes]
  unfold riscLayerStrobeWires
  simp only [List.foldl_cons, List.foldl_nil]
  have step12 :
      wireFoldStep inputs regState env12
        { wireIdx := 12, name := "is_trap",
          expr := .alu .bitAnd (.alu .bitAnd (.alu .eq (.wireRef 0) (.const 115#64))
                                             (.alu .eq (.wireRef 2) (.const 0#64)))
                               (.alu .eq (.wireRef 5) (.const 0#64)) } =
      wireFoldStep inputs regState env12
        { wireIdx := 12, name := "is_trap", expr := .const 0#64 } := by
    funext i
    simp [wireFoldStep, evalRtlExpr, evalAluOp, h0, hNotTrapOp]
  rw [step12]
  generalize hE13 : wireFoldStep inputs regState env12 { wireIdx := 12, name := "is_trap", expr := .const 0#64 } = e13
  have hE13_0 : e13 0 = inputs 0 &&& 127#64 := by rw [← hE13]; simp [wireFoldStep, h0]
  have step13 :
      wireFoldStep inputs regState e13
        { wireIdx := 13, name := "is_mret",
          expr := .alu .bitAnd (.alu .bitAnd (.alu .eq (.wireRef 0) (.const 115#64))
                                             (.alu .eq (.wireRef 2) (.const 0#64)))
                               (.alu .eq (.wireRef 5) (.const 770#64)) } =
      wireFoldStep inputs regState e13
        { wireIdx := 13, name := "is_mret", expr := .const 0#64 } := by
    funext i
    simp [wireFoldStep, evalRtlExpr, evalAluOp, hE13_0, hNotTrapOp]
  rw [step13]
  generalize hE14 : wireFoldStep inputs regState e13 { wireIdx := 13, name := "is_mret", expr := .const 0#64 } = e14
  have hE14_0 : e14 0 = inputs 0 &&& 127#64 := by rw [← hE14]; simp [wireFoldStep, hE13_0]
  have step14 :
      wireFoldStep inputs regState e14
        { wireIdx := 14, name := "is_csrrs",
          expr := .alu .bitAnd (.alu .eq (.wireRef 0) (.const 115#64))
                               (.alu .eq (.wireRef 2) (.const 2#64)) } =
      wireFoldStep inputs regState e14
        { wireIdx := 14, name := "is_csrrs", expr := .const 0#64 } := by
    funext i
    simp [wireFoldStep, evalRtlExpr, evalAluOp, hE14_0, hNotTrapOp]
  rw [step14]
  generalize hE16 :
    wireFoldStep inputs regState
      (wireFoldStep inputs regState e14 { wireIdx := 14, name := "is_csrrs", expr := .const 0#64 })
      { wireIdx := 15, name := "csr_rdata",
        expr := .mux (.alu .eq (.wireRef 5) (.const 768#64)) (.regRead 1)
                  (.mux (.alu .eq (.wireRef 5) (.const 833#64)) (.regRead 2)
                    (.mux (.alu .eq (.wireRef 5) (.const 834#64)) (.regRead 3) (.const 80#64))) } = e16
  have hE16_0 : e16 0 = inputs 0 &&& 127#64 := by rw [← hE16]; simp [wireFoldStep, hE14_0]
  funext i
  simp [wireFoldStep, evalRtlExpr, evalAluOp, hE16_0, hNotExt]

/-- Deliverable Theorem 1: `risc_base_opcode_non_interference`.
    Proves that adding `PrivilegeCsrOverride` (`0x73`) and `CustomSimdZkExt` (`0x2B`) preserves:
    1. All `.obend` `by weave` base instruction claims across `BaseRisc`, `PrivRisc`, `ExtRisc`, and `ComposedRisc`, AND
    2. Universal cycle-accurate hardware equivalence (`stepModuleRegs` and `evalModuleOutputs`)
       between the 3-layer `obendRiscCpuRtlModule` and the Layer-1 `baseRiscCpuRtlModule` across ALL
       64-bit instruction/data inputs `inputs`, ALL reset flags `rst`, and ALL 20-register states
       `regState` whenever `opcode ≠ 43#64` and `opcode ≠ 115#64`! -/
theorem risc_base_opcode_non_interference
    (rst : Bool)
    (inputs regState : Nat → BitVec 64)
    (hNotExt : (inputs 0 &&& 127#64 == 43#64) = false)
    (hNotTrapOp : (inputs 0 &&& 127#64 == 115#64) = false) :
    Obend.Logic.obligationMeaningWithJudges Obend.Logic.defaultExternalFormats
      BaseRisc.claim_base_exec_add_obj BaseRisc.claim_base_exec_add_just ∧
    Obend.Logic.obligationMeaningWithJudges Obend.Logic.defaultExternalFormats
      PrivRisc.claim_priv_preserves_base_add_obj PrivRisc.claim_priv_preserves_base_add_just ∧
    Obend.Logic.obligationMeaningWithJudges Obend.Logic.defaultExternalFormats
      ExtRisc.claim_custom_ext_non_interference_add_obj ExtRisc.claim_custom_ext_non_interference_add_just ∧
    Obend.Logic.obligationMeaningWithJudges Obend.Logic.defaultExternalFormats
      ComposedRisc.claim_composed_base_non_interference_obj ComposedRisc.claim_composed_base_non_interference_just ∧
    stepModuleRegs obendRiscCpuRtlModule rst inputs regState =
      stepModuleRegs baseRiscCpuRtlModule rst inputs regState ∧
    evalModuleOutputs obendRiscCpuRtlModule inputs regState =
      evalModuleOutputs baseRiscCpuRtlModule inputs regState := by
  have hWires := risc_wireTable_non_interference inputs regState hNotExt hNotTrapOp
  refine ⟨BaseRisc.claim_base_exec_add_holds,
          PrivRisc.claim_priv_preserves_base_add_holds,
          ExtRisc.claim_custom_ext_non_interference_add_holds,
          ComposedRisc.claim_composed_base_non_interference_holds,
          ?_, ?_⟩
  · unfold stepModuleRegs
    rw [hWires]
    rfl
  · unfold evalModuleOutputs
    rw [hWires]
    rfl

/-- Trap-mode wire values lemma (`w_12`, `w_13`, `w_21`, `w_23`, `w_25`) without unfolding `w_17..w_20`. -/
theorem risc_wireTable_on_trap
    (inputs regState : Nat → BitVec 64)
    (hTrapOp : (inputs 0 &&& 127#64 == 115#64) = true)
    (hTrapF3 : ((inputs 0 >>> 12) &&& 7#64 == 0#64) = true)
    (hTrapImm : ((inputs 0 >>> 20) &&& 4095#64 == 0#64) = true) :
    let w := evalWireTable inputs regState obendRiscCpuRtlModule.wires
    w 12 = 1#64 ∧
    w 13 = 0#64 ∧
    w 21 = 0#64 ∧
    w 23 = 80#64 ∧
    w 25 = 0#64 := by
  dsimp only
  rw [evalWireTable_eq_foldl]
  unfold obendRiscCpuRtlModule mkRiscCpuWires
  simp only [List.foldl_append]
  have hDec := riscDecodeAndReadWires_vals inputs regState
  generalize riscDecodeAndReadWires.foldl (wireFoldStep inputs regState) (fun _ => 0#64) = env12 at hDec ⊢
  rcases hDec with ⟨h0, h2, h5⟩
  have hImmZero : (inputs 0 >>> 20) &&& 4095#64 = 0#64 := eq_of_beq hTrapImm
  have hEnv17_12 : ((riscLayerStrobeWires true).foldl (wireFoldStep inputs regState) env12) 12 = 1#64 := by
    change ([ (riscLayerStrobeWires true)[0] ] ++ (riscLayerStrobeWires true).drop 1).foldl
      (wireFoldStep inputs regState) env12 12 = 1#64
    rw [List.foldl_append, foldl_wireFoldStep_preserve inputs regState 12 _ _ (by decide +kernel)]
    simp [riscLayerStrobeWires, wireFoldStep, evalRtlExpr, evalAluOp, h0, h2, h5, hTrapOp, hTrapF3, hTrapImm]
  have hEnv17_13 : ((riscLayerStrobeWires true).foldl (wireFoldStep inputs regState) env12) 13 = 0#64 := by
    change ((riscLayerStrobeWires true).take 2 ++ (riscLayerStrobeWires true).drop 2).foldl
      (wireFoldStep inputs regState) env12 13 = 0#64
    rw [List.foldl_append, foldl_wireFoldStep_preserve inputs regState 13 _ _ (by decide +kernel)]
    simp [riscLayerStrobeWires, wireFoldStep, evalRtlExpr, evalAluOp, h0, h2, h5, hImmZero]
  generalize (riscLayerStrobeWires true).foldl (wireFoldStep inputs regState) env12 = env17 at hEnv17_12 hEnv17_13 ⊢
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (foldl_wireFoldStep_preserve inputs regState 12 riscDatapathAndControlWires env17 (by decide +kernel)).trans hEnv17_12
  · exact (foldl_wireFoldStep_preserve inputs regState 13 riscDatapathAndControlWires env17 (by decide +kernel)).trans hEnv17_13
  · change (riscDatapathAndControlWires.take 4 ++ [riscDatapathAndControlWires[4]] ++ riscDatapathAndControlWires.drop 5).foldl
      (wireFoldStep inputs regState) env17 21 = 0#64
    simp only [List.foldl_append]
    rw [foldl_wireFoldStep_preserve inputs regState 21 (riscDatapathAndControlWires.drop 5) _ (by decide +kernel)]
    have hPre12 : (riscDatapathAndControlWires.take 4).foldl (wireFoldStep inputs regState) env17 12 = 1#64 :=
      (foldl_wireFoldStep_preserve inputs regState 12 _ env17 (by decide +kernel)).trans hEnv17_12
    generalize (riscDatapathAndControlWires.take 4).foldl (wireFoldStep inputs regState) env17 = e20 at hPre12 ⊢
    simp [riscDatapathAndControlWires, wireFoldStep, evalRtlExpr, hPre12]
  · change (riscDatapathAndControlWires.take 6 ++ [riscDatapathAndControlWires[6]] ++ riscDatapathAndControlWires.drop 7).foldl
      (wireFoldStep inputs regState) env17 23 = 80#64
    simp only [List.foldl_append]
    rw [foldl_wireFoldStep_preserve inputs regState 23 (riscDatapathAndControlWires.drop 7) _ (by decide +kernel)]
    have hPre12 : (riscDatapathAndControlWires.take 6).foldl (wireFoldStep inputs regState) env17 12 = 1#64 :=
      (foldl_wireFoldStep_preserve inputs regState 12 _ env17 (by decide +kernel)).trans hEnv17_12
    generalize (riscDatapathAndControlWires.take 6).foldl (wireFoldStep inputs regState) env17 = e22 at hPre12 ⊢
    simp [riscDatapathAndControlWires, wireFoldStep, evalRtlExpr, hPre12]
  · change (riscDatapathAndControlWires.take 8 ++ [riscDatapathAndControlWires[8]]).foldl
      (wireFoldStep inputs regState) env17 25 = 0#64
    simp only [List.foldl_append]
    have hPre12 : (riscDatapathAndControlWires.take 8).foldl (wireFoldStep inputs regState) env17 12 = 1#64 :=
      (foldl_wireFoldStep_preserve inputs regState 12 _ env17 (by decide +kernel)).trans hEnv17_12
    generalize (riscDatapathAndControlWires.take 8).foldl (wireFoldStep inputs regState) env17 = e24 at hPre12 ⊢
    simp [riscDatapathAndControlWires, wireFoldStep, evalRtlExpr, hPre12]

/-- GPR preservation helper: when `w 21 = 0#64` (`wb_en == 0`), every architectural register `5..19`
    steps to `regState slot`! -/
theorem foldl_archRegs_wb_disabled
    (inputs w regState : Nat → BitVec 64)
    (hWbOff : w 21 = 0#64) :
    ∀ (ks : List Nat) (st : Nat → BitVec 64) (slot : Nat),
      (∀ k ∈ ks, 4 + k = slot → st slot = regState slot) →
      ((ks.map buildArchRegSpec).foldl (regFoldStep false inputs w regState) st) slot = st slot
  | [], _, _, _ => rfl
  | k :: rest, st, slot, _ => by
    simp only [List.map_cons, List.foldl_cons]
    have hStepEq : regFoldStep false inputs w regState st (buildArchRegSpec k) = st := by
      funext i
      simp [regFoldStep, buildArchRegSpec, evalRtlExpr, evalAluOp, hWbOff]
    rw [hStepEq]
    exact foldl_archRegs_wb_disabled inputs w regState hWbOff rest st slot (fun _ _ _ => rfl)

/-- Deliverable Theorem 2: `risc_privilege_trap_preempts_base_and_ext`.
    Proves directly over `stepModuleRegs` and `evalModuleOutputs` of `obendRiscCpuRtlModule`
    (alongside the `.obend` `by weave` trap preemption claims) that for EVERY synchronous trap
    instruction (`opcode == 115#64`, `funct3 == 0#64`, `imm_u12 == 0#64`) and EVERY 20-register
    state `regState`:
    1. `pc` (`reg 0`) transitions to `mtvec = 80#64` (`0x50`),
    2. `mstatus` (`reg 1`) transitions to `24#64`,
    3. `mepc` (`reg 2`) saves `pc + 4#64`,
    4. `mcause` (`reg 3`) records `11#64`,
    5. Every architectural GPR `x1..x15` (`reg 5..19`) is strictly preserved (writeback preempted),
    6. Data memory write enable `dmem_we` (`output 3`) is forced to `0#64`! -/
theorem risc_privilege_trap_preempts_base_and_ext
    (inputs regState : Nat → BitVec 64)
    (hTrapOp : (inputs 0 &&& 127#64 == 115#64) = true)
    (hTrapF3 : ((inputs 0 >>> 12) &&& 7#64 == 0#64) = true)
    (hTrapImm : ((inputs 0 >>> 20) &&& 4095#64 == 0#64) = true) :
    let nextSt := stepModuleRegs obendRiscCpuRtlModule false inputs regState
    let outs := evalModuleOutputs obendRiscCpuRtlModule inputs regState
    Obend.Logic.obligationMeaningWithJudges Obend.Logic.defaultExternalFormats
      PrivRisc.claim_priv_ecall_redirects_to_mtvec_obj PrivRisc.claim_priv_ecall_redirects_to_mtvec_just ∧
    Obend.Logic.obligationMeaningWithJudges Obend.Logic.defaultExternalFormats
      ExtRisc.claim_custom_ext_respects_trap_preemption_obj ExtRisc.claim_custom_ext_respects_trap_preemption_just ∧
    Obend.Logic.obligationMeaningWithJudges Obend.Logic.defaultExternalFormats
      ComposedRisc.claim_composed_trap_preempts_pc_obj ComposedRisc.claim_composed_trap_preempts_pc_just ∧
    nextSt 0 = 80#64 ∧
    nextSt 1 = 24#64 ∧
    nextSt 2 = regState 0 + 4#64 ∧
    nextSt 3 = 11#64 ∧
    (∀ slot, 5 ≤ slot → slot ≤ 19 → nextSt slot = regState slot) ∧
    outs[3]? = some ("dmem_we", 0#64) := by
  dsimp only
  have hTrapWires := risc_wireTable_on_trap inputs regState hTrapOp hTrapF3 hTrapImm
  rw [stepModuleRegs_eq_foldl]
  unfold evalModuleOutputs
  generalize evalWireTable inputs regState obendRiscCpuRtlModule.wires = w at hTrapWires ⊢
  rcases hTrapWires with ⟨hw12, hw13, hw21, hw23, hw25⟩
  have hArchId : ∀ (st : Nat → BitVec 64) (slot : Nat),
      (((List.range 15).map (fun i => buildArchRegSpec (i + 1))).foldl
        (regFoldStep false inputs w regState) st) slot = st slot := by
    intro st slot
    have hMap : (List.range 15).map (fun i => buildArchRegSpec (i + 1)) =
        ((List.range 15).map (· + 1)).map buildArchRegSpec := by simp [List.map_map]
    rw [hMap]
    exact foldl_archRegs_wb_disabled inputs w regState hw21 _ st slot (fun _ _ _ => rfl)
  refine ⟨PrivRisc.claim_priv_ecall_redirects_to_mtvec_holds,
          ExtRisc.claim_custom_ext_respects_trap_preemption_holds,
          ComposedRisc.claim_composed_trap_preempts_pc_holds,
          ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change riscCpuRegs.foldl (regFoldStep false inputs w regState) regState 0 = 80#64
    unfold riscCpuRegs
    rw [List.foldl_append, hArchId]
    simp [regFoldStep, evalRtlExpr, hw23]
  · change riscCpuRegs.foldl (regFoldStep false inputs w regState) regState 1 = 24#64
    unfold riscCpuRegs
    rw [List.foldl_append, hArchId]
    simp [regFoldStep, evalRtlExpr, hw12, hw13]
  · change riscCpuRegs.foldl (regFoldStep false inputs w regState) regState 2 = regState 0 + 4#64
    unfold riscCpuRegs
    rw [List.foldl_append, hArchId]
    simp [regFoldStep, evalRtlExpr, evalAluOp, hw12]
  · change riscCpuRegs.foldl (regFoldStep false inputs w regState) regState 3 = 11#64
    unfold riscCpuRegs
    rw [List.foldl_append, hArchId]
    simp [regFoldStep, evalRtlExpr, hw12]
  · intro slot hLo hHi
    change riscCpuRegs.foldl (regFoldStep false inputs w regState) regState slot = regState slot
    unfold riscCpuRegs
    rw [List.foldl_append, hArchId]
    have hNe0 : (slot == 0) = false := by omega
    have hNe1 : (slot == 1) = false := by omega
    have hNe2 : (slot == 2) = false := by omega
    have hNe3 : (slot == 3) = false := by omega
    have hNe4 : (slot == 4) = false := by omega
    simp [regFoldStep, hNe0, hNe1, hNe2, hNe3, hNe4]
  · simp [obendRiscCpuRtlModule, riscCpuOutputs, evalRtlExpr, hw25]

/-- Extract the inner method body (under the outer `λself.` binder) from a `Leaf.Book` slot. -/
def extractRiscBookMethodInner (B : Book) (m : String) : Term :=
  match lookupBookCode B m with
  | some (.lam inner) => inner
  | _ => .nat 0

def privStepPcBody : Term :=
  extractRiscBookMethodInner PrivRisc.privilegeRiscCore_book "stepPc"

def privExecBody : Term :=
  extractRiscBookMethodInner PrivRisc.privilegeRiscCore_book "execInstruction"

def composedExecStepBody : Term :=
  extractRiscBookMethodInner ComposedRisc.composedRiscCpu_book "execStep"

def composedNextPcBody : Term :=
  extractRiscBookMethodInner ComposedRisc.composedRiscCpu_book "nextPc"

/-- Deliverable Theorem 3: `risc_read_set_monotonicity`.
    Proves that:
    1. Every member read by `PrivRisc` (`"mtvecAddr"` in `stepPc`, and `"trapCauseCode"`, `"mtvecAddr"`, `"aluExec"` in `execInstruction`)
       is preserved in the 3-layer `ComposedRiscCpu` read-member cone (`composedNextPcBody` and `composedExecStepBody`),
    2. By `extractReadMembers_mutation_invariant`, mutating any disjoint member (`"customExtOpcode"` for `nextPc`,
       or `"decodeImmS"` for `execStep`) leaves `substMemberEnv` identically unchanged. -/
theorem risc_read_set_monotonicity (env : String → Option Term) (newVal : Option Term) :
    "mtvecAddr" ∈ extractReadMembers privStepPcBody ∧
    "trapCauseCode" ∈ extractReadMembers privExecBody ∧
    (∀ m ∈ extractReadMembers privStepPcBody ++ extractReadMembers privExecBody,
      m ∈ extractReadMembers composedNextPcBody ++ extractReadMembers composedExecStepBody) ∧
    substMemberEnv (mutateMemberEnv env "customExtOpcode" newVal) composedNextPcBody =
      substMemberEnv env composedNextPcBody ∧
    substMemberEnv (mutateMemberEnv env "decodeImmS" newVal) composedExecStepBody =
      substMemberEnv env composedExecStepBody := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_⟩
  · exact (extractReadMembers_mutation_invariant composedNextPcBody env newVal (by decide +kernel)).1
  · exact (extractReadMembers_mutation_invariant composedExecStepBody env newVal (by decide +kernel)).1

/-- Deliverable Theorem 4: `risc_inCore_futamura2`.
    Proves that all four open-recursive RISC softcore layer books (`BaseRiscCore`,
    `PrivilegeCsrOverride`, `CustomSimdZkExt`, and `ComposedRiscCpu`) specialize in-core via both
    `inCoreBookCompiler` (`inCoreBookCompiler_specializes_from_pinsOnly`) and
    `futamura2BookCompiler` (`futamura2BookCompiler_specializes_in_core`). -/
theorem risc_inCore_futamura2 (pins : List LeafPin) :
    let B1 := BaseRisc.baseRiscCore_book
    let B2 := PrivRisc.privilegeRiscCore_book
    let B3 := ExtRisc.customSimdZkRiscCore_book
    let B4 := ComposedRisc.composedRiscCpu_book
    dataPinSpecialize (.app (inCoreBookCompiler B1) (encodePinsOnly pins)) =
      encodeBookTerm (inCoreSpecializeBook B1 pins) ∧
    dataPinSpecialize (.app (inCoreBookCompiler B2) (encodePinsOnly pins)) =
      encodeBookTerm (inCoreSpecializeBook B2 pins) ∧
    dataPinSpecialize (.app (inCoreBookCompiler B3) (encodePinsOnly pins)) =
      encodeBookTerm (inCoreSpecializeBook B3 pins) ∧
    dataPinSpecialize (.app (inCoreBookCompiler B4) (encodePinsOnly pins)) =
      encodeBookTerm (inCoreSpecializeBook B4 pins) ∧
    dataPinSpecialize (.app (futamura2BookCompiler B1) (encodePinsRecordForBook B1 pins)) =
      encodeBookTerm (specializeBook B1 pins) ∧
    dataPinSpecialize (.app (futamura2BookCompiler B2) (encodePinsRecordForBook B2 pins)) =
      encodeBookTerm (specializeBook B2 pins) ∧
    dataPinSpecialize (.app (futamura2BookCompiler B3) (encodePinsRecordForBook B3 pins)) =
      encodeBookTerm (specializeBook B3 pins) ∧
    dataPinSpecialize (.app (futamura2BookCompiler B4) (encodePinsRecordForBook B4 pins)) =
      encodeBookTerm (specializeBook B4 pins) :=
  ⟨(inCoreBookCompiler_specializes_from_pinsOnly BaseRisc.baseRiscCore_book pins).1,
   (inCoreBookCompiler_specializes_from_pinsOnly PrivRisc.privilegeRiscCore_book pins).1,
   (inCoreBookCompiler_specializes_from_pinsOnly ExtRisc.customSimdZkRiscCore_book pins).1,
   (inCoreBookCompiler_specializes_from_pinsOnly ComposedRisc.composedRiscCpu_book pins).1,
   futamura2BookCompiler_specializes_in_core BaseRisc.baseRiscCore_book pins,
   futamura2BookCompiler_specializes_in_core PrivRisc.privilegeRiscCore_book pins,
   futamura2BookCompiler_specializes_in_core ExtRisc.customSimdZkRiscCore_book pins,
   futamura2BookCompiler_specializes_in_core ComposedRisc.composedRiscCpu_book pins⟩

end Obend.Apps.ObendRisc
end
