import Obend.Hardware.AwsF2Shell
import Obend.Hardware.TapeoutPipeline
import Obend.AssertAxioms
import Obend.Tactic.Tooth

/-!
# `tests/metasystem/Seam4aFpgaTapeoutCryptoTest.lean` — seam 4a: FPGA shell, tapeout, accelerators, crypto

1. AWS F2 wrapper: duplicate-free bindings, exact core port correspondence, the wired `u_core` instance, and
   the `"vivado-sta@1"` / `"openpdk-drc-sta@1"` token-wire codecs.
2. Tapeout: artifact-bound physical signoff derived from the netlist and its PnR certificate; a timing defect in
   the RTL and a geometry defect in the placement are refused while every `TapeoutConfig` sample input is clean.
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

/-! ## 2. Artifact-bound tapeout signoff -/
section Tapeout
open Obend.Hardware.HDL Obend.Hardware.Synth Obend.Hardware.PlaceRoute Obend.Hardware.Process Obend.Hardware.DRC
open Obend.Hardware.TapeoutPipeline

/-- `n` chained 64-bit adders between input and output: `n` LUT levels and `n` carry chains, no register. -/
def adderChain (n : Nat) : RtlModule where
  name := "adder_chain"
  inputNames := ["a", "b"]
  wires := (List.range n).map fun i =>
    { wireIdx := i, name := "s", expr := .alu .add (if i = 0 then .inputPort 0 else .wireRef (i - 1)) (.inputPort 1) }
  regs := []
  outputs := [{ name := "y", expr := .wireRef (n - 1) }]

def chainNl (n : Nat) : BelNetlist := synthesizeModuleToBels (adderChain n)

-- A shallow chain signs off from its RTL alone; the returned checks are the derived ones.
#guard (compileRtlModuleArtifactBoundTapeout envelope7nm 2000 default7nmDrcDeck (adderChain 3)).isSome
#guard (deriveCriticalTimingPathFromPnr corner7nm_SS (chainNl 3) (synthesizeGridPnrCert (chainNl 3))).logicLevels == 3
#guard (deriveCriticalTimingPathFromPnr corner7nm_SS (chainNl 3) (synthesizeGridPnrCert (chainNl 3))).carryBits == 24
-- The timing graph has one register-free edge per fan-in edge and no flip-flop edge.
#guard (deriveSyncGraphFromBelNetlist corner7nm_SS (chainNl 3) (synthesizeGridPnrCert (chainNl 3))).edges.length ==
  (belFanIn (chainNl 3)).length
-- Timing defect in the RTL: nine chained adders need more than 2000 ps at SS. The emission gate, the netlist, the
-- netlist-bound PnR certificate and the configured sample path all pass; the derived signoff refuses.
#guard checkRtlModuleW (adderChain 9)
#guard checkPnrCertificate (chainNl 9) corner7nm_SS 2000 (synthesizeGridPnrCert (chainNl 9))
#guard checkEnvelopeTimingSignoff envelope7nm 2000 ({ moduleName := "m" } : TapeoutConfig).timingPath
#guard checkArtifactBoundTapeout envelope7nm 2000 default7nmDrcDeck (chainNl 9) (synthesizeGridPnrCert (chainNl 9)) == false
#guard (compileRtlModuleArtifactBoundTapeout envelope7nm 2000 default7nmDrcDeck (adderChain 9)).isNone
#guard (compileRtlModuleArtifactBoundTapeout envelope7nm 4000 default7nmDrcDeck (adderChain 9)).isSome

/-- The reference design's netlist, as the pipeline synthesizes it. -/
def referenceNl : BelNetlist :=
  ((compileBookByMode goldenTapeoutConfig.compileMode goldenTapeoutConfig.moduleName
    (specializeBookDict goldenTapeoutConfig.dictInlinePasses (Obend.Leaf.emit goldenCleanroomTcadComp))).map
      synthesizeModuleToBels).getD validAdderBelNetlist
/-- The grid certificate with cell 1 moved from slot 1 to slot 2 of its tile: still an injective placement, but its
pad lands on the pad of the next tile's slot 0. -/
def overlappingPadCert : PnrCertificate :=
  { synthesizeGridPnrCert referenceNl with
    placedCells := (synthesizeGridPnrCert referenceNl).placedCells.map fun c =>
      if c.cellId = 1 then { c with belSlot := 2 } else c }
/-- The grid certificate with its last routed net dropped. -/
def unroutedEdgeCert : PnrCertificate :=
  { synthesizeGridPnrCert referenceNl with routedNets := (synthesizeGridPnrCert referenceNl).routedNets.dropLast }

#guard checkArtifactBoundTapeout envelope7nm 2000 default7nmDrcDeck referenceNl (synthesizeGridPnrCert referenceNl)
#guard checkPnrCertificate referenceNl corner7nm_SS 2000 overlappingPadCert
#guard checkArtifactBoundTapeout envelope7nm 2000 default7nmDrcDeck referenceNl overlappingPadCert == false
#guard checkPnrCertificate referenceNl corner7nm_SS 2000 unroutedEdgeCert
#guard checkArtifactBoundTapeout envelope7nm 2000 default7nmDrcDeck referenceNl unroutedEdgeCert == false

/-- **Geometry defect through the whole pipeline.** With every configured sample box, tree, graph and path left at
its clean default, a PnR certificate whose pads overlap is refused at the artifact-bound stage. -/
theorem overlapping_pads_refused_under_clean_config :
    (match compileCompositionToSiliconTapeout { goldenTapeoutConfig with pnrCert? := some overlappingPadCert }
        goldenCleanroomTcadComp [goldenTapeoutIsarCert] with
     | .error (.artifactBoundSignoffRefused _) => true
     | _ => false) = true := by decide +kernel
/-- **Timing defect through the whole pipeline.** At 1300 ps the configured sample path and graph still pass, the
reference design's own register-to-register paths (1263 ps of logic and wire at SS) do not. -/
theorem slow_paths_refused_under_clean_config :
    (match compileCompositionToSiliconTapeout { goldenTapeoutConfig with clockPeriodPs := 1300 }
        goldenCleanroomTcadComp [goldenTapeoutIsarCert] with
     | .error (.artifactBoundSignoffRefused _) => true
     | _ => false) = true := by decide +kernel

#tooth Obend.Hardware.TapeoutPipeline.checkArtifactBoundTapeout_sound
  by mutation Obend.Hardware.TapeoutPipeline.checkArtifactBoundTapeout := fun _ _ _ _ _ => true
-- Accepting any arrival certificate.
#tooth Obend.Hardware.TapeoutPipeline.checkArtifactBoundTapeout_sound
  by mutation Obend.Hardware.TapeoutPipeline.checkGraphArrivals := fun _ _ _ => true
-- Accepting any pad spacing.
#tooth Obend.Hardware.TapeoutPipeline.checkArtifactBoundTapeout_sound
  by mutation Obend.Hardware.DRC.checkBoxSpacing2D := fun _ _ _ => true
#tooth Obend.Hardware.TapeoutPipeline.runArtifactBoundTapeoutSignoff_sound
  by mutation Obend.Hardware.TapeoutPipeline.runArtifactBoundTapeoutSignoff :=
    fun env _ deck nl pnr => some (derivePhysicalChecksFromBelNetlist env.slowCorner deck nl pnr)

-- JSON for the reference artifact.
def referenceJson (render : SiliconTapeoutArtifact → String) : Option Lean.Json :=
  match compileCompositionToSiliconTapeout goldenTapeoutConfig goldenCleanroomTcadComp [goldenTapeoutIsarCert] with
  | .ok art => (Lean.Json.parse (render art)).toOption
  | .error _ => none
#guard ((referenceJson renderLibrelaneConfigJson).bind fun j => (j.getObjValAs? String "DESIGN_NAME").toOption) ==
  some "CleanroomTcadStack"
#guard ((referenceJson renderLibrelaneConfigJson).bind fun j => (j.getObjValAs? String "CLOCK_PORT").toOption) == some "clk"
#guard ((referenceJson renderLibrelaneConfigJson).bind fun j => (j.getObjValAs? Float "CLOCK_PERIOD").toOption) == some 2.0
#guard ((referenceJson renderLibrelaneConfigJson).bind fun j => (j.getObjValAs? (Array String) "VERILOG_FILES").toOption) ==
  some #["dir::CleanroomTcadStack.sv"]
#guard ((referenceJson renderTapeoutReceiptJson).bind fun j => (j.getObjValAs? String "verdict").toOption) == some "ok"
#guard ((referenceJson renderTapeoutReceiptJson).bind fun j => (j.getObjValAs? Nat "belCells").toOption) == some 44
#guard ((referenceJson renderTapeoutReceiptJson).bind fun j => (j.getObjValAs? Nat "routedNets").toOption) == some 55
#guard ((referenceJson renderTapeoutReceiptJson).bind fun j => (j.getObjVal? "openings").toOption.bind fun o =>
  (o.getObjValAs? Bool "checkArtifactBoundTapeout").toOption) == some true
#guard ((referenceJson renderTapeoutReceiptJson).bind fun j => (j.getObjVal? "criticalPath").toOption.bind fun o =>
  (o.getObjValAs? Nat "logicLevels").toOption) == some 7

end Tapeout

end Obend.Tests.Seam4aFpgaTapeoutCryptoTest
