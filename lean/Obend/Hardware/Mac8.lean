module
/-
# Obend.Hardware.Mac8 — the 8x8+16 multiply-accumulate the physical flows build

`iceStickMac8` is emitted to `hardware/ice40/obend_ice40_mac8.sv` (`obend-emit-sv ice40-mac8`), placed on
the iCEstick by `hardware/ice40/`, and configured onto a FABulous fabric by `hardware/fabulous/`, where
`Obend.Hardware.Fabulous.Mac8` proves the bitstream's logic realizes it.
-/
public import Obend.Hardware.HDL
@[expose] public section

namespace Obend.Hardware

open Obend.Hardware.HDL

/-- The first physical target: an 8x8+16 multiply-accumulate with port widths, for the iCEstick
(`hardware/ice40/`). Same shape as `Synth.goldenRetimedMacRtl`, with every signal at its width:
the 16-bit product and addend registers, and the sum truncated to the 16-bit output register. -/
def iceStickMac8 : RtlModule :=
  { name       := "obend_ice40_mac8"
    inputNames := ["a", "b", "c"]
    inputWidths := [8, 8, 16]
    wires      :=
      [ { wireIdx := 0, name := "w_mul", width := 16, expr := .alu .mul (.inputPort 0) (.inputPort 1) }
      , { wireIdx := 1, name := "w_add", width := 16,
          expr := .resize (.trunc 16) (.alu .add (.regRead 0) (.regRead 1)) } ]
    regs       :=
      [ { regIdx := 0, name := "mulReg", domain := .coreClk, resetKind := .syncReset 0#64, isSynchronizer := false, width := 16, nextExpr := .wireRef 0 }
      , { regIdx := 1, name := "cReg",   domain := .coreClk, resetKind := .syncReset 0#64, isSynchronizer := false, width := 16, nextExpr := .inputPort 2 }
      , { regIdx := 2, name := "outReg", domain := .coreClk, resetKind := .syncReset 0#64, isSynchronizer := false, width := 16, nextExpr := .wireRef 1 } ]
    outputs    := [ { name := "mac_out", expr := .regRead 2, width := 16 } ] }

end Obend.Hardware
