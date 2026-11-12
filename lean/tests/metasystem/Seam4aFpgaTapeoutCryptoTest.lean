import Obend.Hardware.AwsF2Shell
import Obend.AssertAxioms
import Obend.Tactic.Tooth

/-!
# `tests/metasystem/Seam4aFpgaTapeoutCryptoTest.lean` — seam 4a: FPGA shell, tapeout, accelerators, crypto

1. AWS F2 wrapper: duplicate-free bindings, exact core port correspondence, the wired `u_core` instance, and
   the `"vivado-sta@1"` / `"openpdk-drc-sta@1"` token-wire codecs.
-/

namespace Obend.Tests.Seam4aFpgaTapeoutCryptoTest

/-! ## 1. AWS F2 shell wrapper -/
section AwsF2
open Obend.Hardware.HDL Obend.Hardware.AwsF2Shell

def adderCore : RtlModule where
  name := "obend_f2_core"
  inputNames := ["a", "b"]
  wires := [{ wireIdx := 0, name := "w_sum", expr := .alu .add (.inputPort 0) (.inputPort 1) }]
  regs := []
  outputs := [{ name := "y", expr := .wireRef 0 }]

#guard validateF2CorePortBindings defaultAwsF2WrapperConfig adderCore
#guard f2CoreConnections defaultAwsF2WrapperConfig adderCore ==
  ["    .clk(clk_main_a0)", "    .rst(rst_core_sync)", "    .a(sh_cl_dma_pcis_awaddr)",
   "    .b(sh_cl_dma_pcis_araddr)", "    .y(cl_sh_pcim_awaddr)"]
-- The emitted text is the core module, then the CL module that instantiates it before `endmodule`.
#guard (emitAwsF2ClWrapperSV defaultAwsF2WrapperConfig adderCore).any fun sv =>
  sv.startsWith (emitModuleSV adderCore) &&
  sv.endsWith ("  obend_f2_core u_core (\n    .clk(clk_main_a0),\n    .rst(rst_core_sync),\n" ++
    "    .a(sh_cl_dma_pcis_awaddr),\n    .b(sh_cl_dma_pcis_araddr),\n    .y(cl_sh_pcim_awaddr)\n  );\nendmodule\n")

-- A shell port bound twice, or a CL signal bound twice, is refused.
#guard validateF2WrapperPortBinding { defaultAwsF2WrapperConfig with portBindings :=
  { shellPortName := "sh_cl_dma_pcis_awaddr", clSignalName := "a2", dir := .shToCl, width := 64 } ::
    defaultAwsF2WrapperConfig.portBindings } == false
#guard validateF2WrapperPortBinding { defaultAwsF2WrapperConfig with portBindings :=
  { shellPortName := "sh_cl_dma_pcis_wstrb", clSignalName := "a", dir := .shToCl, width := 64 } ::
    defaultAwsF2WrapperConfig.portBindings } == false
-- A core with an unbound input, a width mismatch, a port named `clk`, or an output on `cl_sh_flr_done` is refused.
#guard validateF2CorePortBindings defaultAwsF2WrapperConfig { adderCore with inputNames := ["a", "c"] } == false
#guard validateF2CorePortBindings defaultAwsF2WrapperConfig { adderCore with inputWidths := [64, 32] } == false
#guard validateF2CorePortBindings defaultAwsF2WrapperConfig
  { adderCore with outputs := [{ name := "y", expr := .wireRef 0, width := 32 }] } == false
#guard validateF2CorePortBindings defaultAwsF2WrapperConfig
  { adderCore with outputs := [{ name := "flr_done", expr := .wireRef 0, width := 1 }] } == false
#guard validateF2CorePortBindings defaultAwsF2WrapperConfig
  { adderCore with outputs := [{ name := "y", expr := .wireRef 0 }, { name := "y", expr := .wireRef 0 }] } == false
#guard (emitAwsF2ClWrapperSV defaultAwsF2WrapperConfig { adderCore with inputNames := ["a", "c"] }).isNone

/-- The pre-repair validator: canonical bindings, no duplicate check. -/
def validateWithoutDuplicateCheck (cfg : F2WrapperConfig) : Bool :=
  (cfg.targetDevice == awsF2TargetDevice) && cfg.rstActiveLow && (!cfg.usesCustomerIcap) &&
  decide (cfg.hbmChannelsUsed ≤ 32) && (!cfg.portBindings.isEmpty) &&
  cfg.portBindings.all checkSingleF2PortBinding

#tooth Obend.Hardware.AwsF2Shell.validateF2WrapperPortBinding_sound
  by mutation Obend.Hardware.AwsF2Shell.validateF2WrapperPortBinding := validateWithoutDuplicateCheck
-- Accepting a core port without a binding of its width.
#tooth Obend.Hardware.AwsF2Shell.validateF2CorePortBindings_sound
  by mutation Obend.Hardware.AwsF2Shell.checkF2CorePort := fun _ _ _ _ => true
-- Wiring every core port to the clock instead of its bound shell port.
#tooth Obend.Hardware.AwsF2Shell.emitAwsF2ClWrapperSV_instantiates_wired_core
  by mutation Obend.Hardware.AwsF2Shell.boundF2ShellPort := fun _ _ _ => "clk_main_a0"
-- Omitting the core's outputs from the instance.
#tooth Obend.Hardware.AwsF2Shell.emitAwsF2ClWrapperSV_instantiates_wired_core
  by mutation Obend.Hardware.AwsF2Shell.f2CoreConnections := fun cfg m =>
    (coreInputPorts m).map (fun p => "    ." ++ p.1 ++ "(" ++ boundF2ShellPort cfg .shToCl p.1 ++ ")")

-- Byte codecs: encode then decode is the identity on the samples, and the registered formats judge bytes.
#guard (decodeVivadoStaObj (encodeVivadoStaObj sampleVivadoStaObj)).toOption == some sampleVivadoStaObj
#guard (decodeVivadoStaCert (encodeVivadoStaCert sampleVivadoStaCert)).toOption == some sampleVivadoStaCert
#guard (decodeVivadoStaCert (encodeVivadoStaCert ⟨-12, -3, 2⟩)).toOption == some ⟨-12, -3, 2⟩
#guard (decodeOpenPdkSignoffObj (encodeOpenPdkSignoffObj sampleSky130SignoffObj)).toOption == some sampleSky130SignoffObj
#guard (decodeOpenPdkSignoffObj (encodeOpenPdkSignoffObj sky130SpacingViolationObj)).toOption ==
  some sky130SpacingViolationObj
#guard (decodeOpenPdkSignoffCert (encodeOpenPdkSignoffCert sampleSky130SignoffCert)).toOption ==
  some sampleSky130SignoffCert
#guard encodeVivadoStaObj sampleVivadoStaObj ==
  "xcvu47p-fsvh2892-2-e 4000 35 680 1 slr0_to_slr1_reg 0 1 2950 335 190 110 45 2400"
#guard match vivadoStaByteJudge.checkBytes 8 (encodeVivadoStaObj sampleVivadoStaObj)
  (encodeVivadoStaCert sampleVivadoStaCert) with | .ok => true | _ => false
#guard match openpdkDrcStaByteJudge.checkBytes 20 (encodeOpenPdkSignoffObj sampleSky130SignoffObj)
  (encodeOpenPdkSignoffCert sampleSky130SignoffCert) with | .ok => true | _ => false
-- The planted reports are refused through the byte path, by the judge (not as malformed), at their own path.
#guard match vivadoStaByteJudge.checkBytes 8 (encodeVivadoStaObj vivadoStaByteJudge.bad.1)
  (encodeVivadoStaCert sampleVivadoStaCert) with | .refused (.judge _) p => p == [1] | _ => false
#guard match openpdkDrcStaByteJudge.checkBytes 20 (encodeOpenPdkSignoffObj sky130SpacingViolationObj)
  (encodeOpenPdkSignoffCert sampleSky130SignoffCert) with | .refused (.judge _) p => p == [2] | _ => false
#guard match vivadoStaByteJudge.checkBytes 8 "not a report" "335 45 1" with | .refused (.malformed _) _ => true | _ => false
-- Truncated, trailing-garbage, non-numeric and bad-enum wires are refused as malformed.
#guard (decodeVivadoStaCert "335 45").toOption.isNone
#guard (decodeVivadoStaCert "335 45 1 7").toOption.isNone
#guard (decodeVivadoStaCert "335 4x 1").toOption.isNone
#guard (decodeVivadoStaObj "xcvu47p-fsvh2892-2-e 4000 35 680 1 p 0 3 2950 335 190 110 45 2400").toOption.isNone
#guard (decodeVivadoStaObj "xcvu47p-fsvh2892-2-e 4000 35 680 2 p 0 1 2950 335 190 110 45 2400").toOption.isNone
#guard (decodeOpenPdkSignoffObj "").toOption.isNone
-- The kernel runs the decoder on a literal wire.
theorem vivadoStaCert_wire_decodes : (decodeVivadoStaCert "335 45 1").toOption = some sampleVivadoStaCert := by decide +kernel

end AwsF2

end Obend.Tests.Seam4aFpgaTapeoutCryptoTest
