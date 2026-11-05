import Obend.Hardware.VerilateRunner
/-!
# Widths and clock domains in `RtlExpr` (rung 3 of HARDWARE.md)

Tests, not theorems: the refusals `checkWidths` gives, the widths `inferWidthE` assigns, and the
text `emitModuleSV` prints for narrow signals and for two clock domains. The theorems these
exercise are in `Obend.Hardware.HDL` §4c-§4d.
-/
open Obend.Hardware.HDL Obend.Hardware.VerilateRunner

/-- A 16-bit output port driven by a 64-bit difference. -/
def badPort : RtlModule :=
  { name := "bad_port", inputNames := ["a", "b"], wires := [], regs := []
    outputs := [{ name := "y", width := 16, expr := .alu .sub (.inputPort 0) (.inputPort 1) }] }

#guard widthErrors badPort ==
  ["output port `y` is 16 bits wide but is driven by a 64-bit expression (narrow it with trunc or slice)"]
#guard !checkWidths badPort
#guard !checkRtlModuleW badPort

-- The same port, narrowed by `trunc 16`, is accepted.
#guard checkRtlModuleW { badPort with
  outputs := [{ name := "y", width := 16, expr := .resize (.trunc 16) (.alu .sub (.inputPort 0) (.inputPort 1)) }] }

/-- A slice above the top of an 8-bit input. -/
def badSlice : RtlModule :=
  { name := "bad_slice", inputNames := ["a"], inputWidths := [8], regs := [], outputs := []
    wires := [{ wireIdx := 0, name := "w_top", width := 2, expr := .resize (.slice 9 8) (.inputPort 0) }] }

#guard widthErrors badSlice == ["wire `w_top`: slice [9:8] is outside its 8-bit source"]

-- A register whose reset value does not fit its 4 bits, and a wire declared 0 bits wide.
#guard widthErrors
  { name := "bad_decl", inputNames := [], outputs := []
    wires := [{ wireIdx := 0, name := "w0", width := 0, expr := .const 0#64 }]
    regs := [{ regIdx := 0, name := "r", domain := .coreClk, resetKind := .syncReset 17#64
               isSynchronizer := false, width := 4, nextExpr := .const 3#64 }] } ==
  [ "wire `w0` declares width 0; widths are 1..64"
  , "wire `w0` is 0 bits wide but is driven by a 1-bit expression (narrow it with trunc or slice)"
  , "register `r` resets to 17, which does not fit its 4 bits" ]

/-- Inferred widths: an 8+8 sum is 9 bits, an 8x8 product 16, a 16-into-8 concatenation 24,
a comparison 1, a subtraction 64. -/
def env8 : WidthEnv := ⟨fun i => [8, 8, 16].getD i 64, fun _ => 64, fun _ => 64⟩
#guard inferWidth env8 (.alu .add (.inputPort 0) (.inputPort 1)) == some 9
#guard inferWidth env8 (.alu .mul (.inputPort 0) (.inputPort 1)) == some 16
#guard inferWidth env8 (RtlExpr.concat (.inputPort 2) (.inputPort 0) 8) == some 24
#guard inferWidth env8 (.alu .ult (.inputPort 0) (.inputPort 1)) == some 1
#guard inferWidth env8 (.alu .sub (.inputPort 0) (.inputPort 1)) == some 64
#guard inferWidth env8 (.resize (.zext 4) (.inputPort 0)) == none

-- The semantics of the width operators on the carrier.
#guard evalWidthOp (.slice 7 4) 0xAB#64 == 0xA#64
#guard evalWidthOp (.sext 8 16) 0x80#64 == 0xFF80#64
#guard evalWidthOp (.sext 8 16) 0x7F#64 == 0x7F#64
#guard evalWidthOp (.trunc 4) 0xAB#64 == 0xB#64
#guard evalRtlExpr (fun i => [0x12#64, 0x34#64].getD i 0) (fun _ => 0) (fun _ => 0)
    (RtlExpr.concat (.inputPort 0) (.inputPort 1) 8) == 0x1234#64

-- The probe module: two domains, narrow signals, a two-flop synchronizer; it passes the gate.
#guard checkRtlModuleW goldenWidthProbeRtl
#guard moduleDomains goldenWidthProbeRtl == [.coreClk, .axiIoClk]

def probeSV : String := emitModuleSV goldenWidthProbeRtl
#guard (probeSV.splitOn "input  logic        clk_core").length == 2
#guard (probeSV.splitOn "input  logic        clk_axi").length == 2
#guard (probeSV.splitOn "always_ff @(posedge clk_axi)").length == 2
#guard (probeSV.splitOn "(* ASYNC_REG = \"TRUE\" *) logic [0:0] flag_s1;").length == 2
#guard (probeSV.splitOn "(* ASYNC_REG = \"TRUE\" *) logic [0:0] flag_s2;").length == 2
#guard (probeSV.splitOn "logic [8:0] w_0; // w_sum").length == 2
#guard (probeSV.splitOn "output logic [23:0] cat_out").length == 2
#guard (probeSV.splitOn "[63:0]").length == 1

-- A synchronizer that is one flop, not two, is refused by the emission gate.
#guard !checkRtlModuleW { goldenWidthProbeRtl with
  regs := goldenWidthProbeRtl.regs.map fun r =>
    if r.name == "flag_s2" then { r with isSynchronizer := false } else r }

-- An all-64 module still declares `[63:0]` and one `clk`.
#guard ((emitModuleSV goldenMultiInputSeqAluRtl).splitOn "input  logic        clk,").length == 2
