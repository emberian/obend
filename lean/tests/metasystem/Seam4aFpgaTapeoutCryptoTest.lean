import Obend.Hardware.AwsF2Shell
import Obend.Hardware.TapeoutPipeline
import Obend.Hardware.Tpu.CryptoSystolic
import Obend.Hardware.Gpu.Rdna2.AsyncRefinement
import Obend.Hardware.Gpu.Rdna2.DppShuffle
import Obend.Crypto.Poseidon2Goldilocks
import Obend.Crypto.BinaryTower256
import Obend.Crypto.DarkBazaar
import Obend.AssertAxioms
import Obend.Tactic.Tooth

/-!
# `tests/metasystem/Seam4aFpgaTapeoutCryptoTest.lean` — seam 4a: FPGA shell, tapeout, accelerators, crypto

1. AWS F2 wrapper: duplicate-free bindings, exact core port correspondence, the wired `u_core` instance, and
   the `"vivado-sta@1"` / `"openpdk-drc-sta@1"` token-wire codecs.
2. Tapeout: artifact-bound physical signoff derived from the netlist and its PnR certificate; a timing defect in
   the RTL and a geometry defect in the placement are refused while every `TapeoutConfig` sample input is clean.
3. Accelerators: TPU allocation bounds and validated GEMM/Bailey tile layouts; RDNA2 kernels checked from their
   machine words; the DPP16 modifier dword against LLVM MC encodings.
4. Crypto: SplitMix64 Poseidon2 round constants and the vectors shared with the Rust twin
   (`crates/obend-crypto-exec/src/goldilocks.rs`); NIST SP 800-38D GHASH; the statistical smudging bound.
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

/-! ## 3. TPU tile layouts and RDNA2 machine words -/
section Tpu
open Obend.Hardware.Tpu Obend.Crypto.Fast

-- The layout of the existing GEMM test is accepted; aliasing and out-of-range layouts are refused.
#guard validateGemmTileLayout 7 7 2 0 1 3
#guard validateGemmTileLayout 7 7 2 0 0 3
#guard validateGemmTileLayout 7 7 0 0 1 3 == false      -- dst = lhs
#guard validateGemmTileLayout 7 7 1 0 1 3 == false      -- dst = rhs
#guard validateGemmTileLayout 7 7 2 0 4 3 == false      -- rhs inside scratch
#guard validateGemmTileLayout 7 7 5 0 1 3 == false      -- dst inside scratch
#guard validateGemmTileLayout 6 7 2 0 1 3 == false      -- scratch + 3 out of range
#guard validateGemmTileLayout 7 6 2 0 1 3 == false      -- six VREGs
#guard goldilocksGemmChecked 7 7 2 0 1 3 == some (goldilocksGemmProgram 2 0 1 3)
#guard (goldilocksGemmChecked 7 7 0 0 1 3).isNone
#guard checkProgramBounds 0 7 0 7 0 (goldilocksGemmProgram 2 0 1 3)
#guard checkProgramBounds 0 6 0 7 0 (goldilocksGemmProgram 2 0 1 3) == false
#guard validateBaileyNttTileLayout 12 7 5 0 1 2 3 6
#guard validateBaileyNttTileLayout 12 7 5 0 1 2 7 6 == false   -- twiddle inside scratch
#guard validateBaileyNttTileLayout 12 7 0 0 1 2 3 6 == false   -- dst = input
#guard validateBaileyNttTileLayout 11 7 5 0 1 2 3 6 == false   -- scratch + 5 out of range
#guard (baileyNttChecked 12 7 5 0 1 2 3 6).isSome

/-- Seven tiles of `p - 1`. -/
def fullTiles : TpuCoreState :=
  { TpuCoreState.initial 0 7 0 7 0 with
    vmem := Array.replicate 7 (Sized.ofFn fun _ => UInt64.ofNat (Obend.Apps.ZkNtt.goldilocksPrime - 1)) }
-- What the validator prevents: with `dst = lhs` the first seventeen instructions already zero the left input.
#guard (runSync fullTiles ((goldilocksGemmProgram 0 0 1 3).take 17)).vmem[0]? != fullTiles.vmem[0]?
#guard (runSync fullTiles ((goldilocksGemmProgram 2 0 1 3).take 17)).vmem[0]? == fullTiles.vmem[0]?

-- The checked emitter needs the allocation; the plain emitter refuses an out-of-range block.
#guard (emitCheckedPallasTpuKernel 0 7 0 7 (goldilocksGemmProgram 2 0 1 3 ++ [.finish])).isSome
#guard (emitCheckedPallasTpuKernel 0 6 0 7 (goldilocksGemmProgram 2 0 1 3 ++ [.finish])).isNone
#guard (emitPallasTpuKernel [.loadVReg 0 0 16, .finish]).startsWith "raise ValueError"
#guard (emitPallasTpuKernel [.loadVReg 0 0 15, .finish]).startsWith "raise ValueError" == false

/-- The pre-repair contract: bounds only, aliasing left to the caller. -/
def validateGemmBoundsOnly (vmemTiles vregCount dst lhs rhs scratch : Nat) : Bool :=
  decide (dst < vmemTiles) && decide (lhs < vmemTiles) && decide (rhs < vmemTiles) &&
  decide (scratch + 3 < vmemTiles) && decide (7 ≤ vregCount)

#tooth Obend.Hardware.Tpu.validateGemmTileLayout_sound
  by mutation Obend.Hardware.Tpu.validateGemmTileLayout := validateGemmBoundsOnly
#tooth Obend.Hardware.Tpu.validateBaileyNttTileLayout_sound
  by mutation Obend.Hardware.Tpu.validateBaileyNttTileLayout := fun _ _ _ _ _ _ _ _ => true
#tooth Obend.Hardware.Tpu.checkProgramBounds_sound
  by mutation Obend.Hardware.Tpu.checkInstrBounds := fun _ _ _ _ _ _ => true
#tooth Obend.Hardware.Tpu.runSync_vmem_frame
  by mutation Obend.Hardware.Tpu.TpuInstr.mayWriteVmem := fun _ _ => false

end Tpu

section Rdna2
open Obend.Hardware.Gpu.Rdna2 Obend.Hardware.Gpu.Rdna2.Async Obend.Hardware.Gpu.Rdna2.Dpp

-- `s_load_dword s8, s[0:1], 0`; `s_waitcnt 0`; `s_mov_b32 s10, s8`: the load-wait-use block, from its words.
#guard (decodeKernelWords 4 [0xf4000200, 0xfa000000, 0xbf8c0000, 0xbe8a0308]).map (·.map (·.name)) ==
  some ["S_LOAD_DWORD", "S_WAITCNT", "S_MOV_B32"]
#guard verifyAsyncTraceWords 0 [0xf4000200, 0xfa000000, 0xbf8c0000, 0xbe8a0308]
-- Using `s8` before the wait is refused; so are a truncated load and a word that is no instruction.
#guard verifyAsyncTraceWords 0 [0xf4000200, 0xfa000000, 0xbe8a0308] == false
#guard verifyAsyncTraceWords 0 [0xf4000200] == false
#guard verifyAsyncTraceWords 0 [0xffffffff] == false
#guard ((decodeKernelWords 4 [0xf4000200, 0xfa000000, 0xbf8c0000, 0xbe8a0308]).map kernelFootprint).map
  (fun f => (f.vgprs, f.scalarLoads, f.ldsAccesses)) == some ([], 1, 0)
-- `v_mov_b32 v5, v70` names VGPR 70: inside a 128-VGPR allocation, outside a 64-VGPR one.
#guard (decodeKernelWords 1 [0x7e0a0346]).map (·.map (·.name)) == some ["V_MOV_B32"]
#guard ((decodeKernelWords 1 [0x7e0a0346]).map kernelFootprint).map (·.vgprs) == some [70, 5]
#guard verifyAsyncTraceWords 128 [0x7e0a0346]
#guard verifyAsyncTraceWords 64 [0x7e0a0346] == false

#tooth Obend.Hardware.Gpu.Rdna2.Async.decodeAndVerifyAsyncKernel_sound
  by mutation Obend.Hardware.Gpu.Rdna2.Async.verifyAsyncTraceWords := fun _ _ => true
#tooth Obend.Hardware.Gpu.Rdna2.Async.decodeAndVerifyAsyncKernel_sound
  by mutation Obend.Hardware.Gpu.Rdna2.Async.checkVgprFootprint := fun _ _ => true

-- DPP16 modifier dwords from LLVM's MC tests (`llvm/test/MC/AMDGPU/dpp.s`), second dword little-endian:
-- `v_mov_b32_dpp v0, v0 quad_perm:[0,2,1,1] row_mask:0xf bank_mask:0xf`  ; [0x00,0x58,0x00,0xff]
-- `v_mov_b32_dpp v0, v0 row_shl:1 row_mask:0xf bank_mask:0xf`            ; [0x00,0x01,0x01,0xff]
-- `v_mov_b32_dpp v0, v0 row_shr:1 row_mask:0xf bank_mask:0xf`            ; [0x00,0x11,0x01,0xff]
-- `v_mov_b32_dpp v0, v0 row_mirror row_mask:0xf bank_mask:0xf`           ; [0x00,0x40,0x01,0xff]
-- `v_mov_b32_dpp v0, v0 wave_shl:1 row_mask:0x0 bank_mask:0x0 bound_ctrl:0` ; [0x00,0x30,0x09,0x00]
#guard decodeDppModifierWord 0xff005800 == some (0, { op := .quad_perm 0 2 1 1 })
#guard decodeDppModifierWord 0xff010100 == some (0, { op := .row_shl 1 })
#guard decodeDppModifierWord 0xff011100 == some (0, { op := .row_shr 1 })
#guard decodeDppModifierWord 0xff014000 == some (0, { op := .row_mirror })
#guard decodeDppModifierWord 0x00093000 ==
  some (0, { op := .wave_shl1, row_mask := 0, bank_mask := 0, bound_ctrl := true })
#guard encodeDppWord32 0 { op := .quad_perm 0 2 1 1 } == 0xff005800
#guard encodeDppWord32 0 { op := .row_shr 1 } == 0xff011100
#guard encodeDppWord32 0 { op := .wave_shl1, row_mask := 0, bank_mask := 0, bound_ctrl := true } == 0x00093000
#guard encodeDppWord32 7 { op := .row_half_mirror, fetch_inactive := true } == 0xff054107
-- Reserved bit 17, a float modifier, and an unassigned control code are refused.
#guard (decodeDppModifierWord 0xff025800).isNone
#guard (decodeDppModifierWord 0xff105800).isNone
#guard (decodeDppModifierWord 0xff015000).isNone
-- RDNA2 has no wave shift or row broadcast: the word decodes but the shuffle is refused.
#guard (verifyDppWordShuffle 0x00093000 allExec (Vector.replicate 64 7) (Vector.replicate 64 0)).isNone
#guard (verifyDppWordShuffle 0xff014200 allExec (Vector.replicate 64 7) (Vector.replicate 64 0)).isNone
-- `row_mirror` on lanes `0..63` reverses each row of sixteen.
#guard (verifyDppWordShuffle 0xff014000 allExec (Vector.ofFn fun i => i.val.toUInt32) (Vector.replicate 64 0)).map
  (·.toList.take 18) == some [15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0, 31, 30]

#tooth Obend.Hardware.Gpu.Rdna2.Dpp.decodeDppModifierWord_encode
  by mutation Obend.Hardware.Gpu.Rdna2.Dpp.encodeDppOp := fun _ => 0
#tooth Obend.Hardware.Gpu.Rdna2.Dpp.verifyDppWordShuffle_sound
  by mutation Obend.Hardware.Gpu.Rdna2.Dpp.verifyDppWordShuffle := fun _ _ src _ => some src

end Rdna2

/-! ## 4. Poseidon2 constants and vectors, NIST GHASH, smudging -/
section Crypto
open Obend.Crypto Obend.Apps.ZkNtt

-- SplitMix64 reference stream from state 0 (Vigna, `splitmix64.c`).
theorem splitMix64_reference_stream :
    splitMix64Mix 0 = 0xE220A8397B1DCDAF ∧ splitMix64Mix 0x9E3779B97F4A7C15 = 0x6E789E6AA1B965F4 ∧
    splitMix64Mix 0x3C6EF372FE94F82A = 0x06C45D188009454F := by decide
/-- Number of set bits. -/
def popcount64 (x : UInt64) : Nat := (List.range 64).countP fun i => (x >>> i.toUInt64) &&& 1 == 1
-- Avalanche: flipping any single input bit of `0` flips between 20 and 44 of the 64 output bits.
#guard (List.range 64).all fun i =>
  let flipped := popcount64 (splitMix64Mix 0 ^^^ splitMix64Mix (1 <<< i.toUInt64))
  20 ≤ flipped && flipped ≤ 44
-- Round-constant words shared with `test_poseidon2_round_constants_match_lean`.
theorem poseidon2_const_words :
    [poseidon2ConstWord 0 0 0, poseidon2ConstWord 1 0 0, poseidon2ConstWord 1 1 0, poseidon2ConstWord 1 2 0,
     poseidon2ConstWord 2 3 11] =
    [18276600331543306333, 17812178848501694915, 2688800452358182541, 4196640518521023400,
     7448626387614558066] := by decide
-- All 48 + 22 + 48 round constants are distinct.
#guard (((List.range 4).flatMap fun r => (List.range 12).map fun l => (poseidon2ConstAt 0 r l).val) ++
  ((List.range 22).map fun r => (poseidon2ConstAt 1 r 0).val) ++
  ((List.range 4).flatMap fun r => (List.range 12).map fun l => (poseidon2ConstAt 2 r l).val)).eraseDups.length == 118

/-- The state `0, 1, …, 11`. -/
def countingState : Poseidon2State12 :=
  ⟨⟨Goldilocks.ofNat 0, Goldilocks.ofNat 1, Goldilocks.ofNat 2, Goldilocks.ofNat 3⟩,
   ⟨Goldilocks.ofNat 4, Goldilocks.ofNat 5, Goldilocks.ofNat 6, Goldilocks.ofNat 7⟩,
   ⟨Goldilocks.ofNat 8, Goldilocks.ofNat 9, Goldilocks.ofNat 10, Goldilocks.ofNat 11⟩⟩

-- The vectors of `test_poseidon2_perm12_matches_lean` and `test_poseidon2_hash32_matches_lean`.
theorem poseidon2Perm12_zero_kat :
    (poseidon2Perm12 ⟨lane4Zero, lane4Zero, lane4Zero⟩).toList.map (·.val) =
    [444626622888223479, 10486189390627733761, 5399253379101132897, 5052010181030417489, 6267397916963039069,
     9245911245446346418, 9661705423445490201, 787089484585814203, 14953692268052641311, 11458212182116269477,
     16934754160153525625, 6948793053817514326] := by decide +kernel
theorem poseidon2Perm12_counting_kat :
    (poseidon2Perm12 countingState).toList.map (·.val) =
    [12427618818045938679, 15603055080602884714, 13440107678219667309, 8886947539732114456, 14710374340000099479,
     10111918623281920586, 1604190142837255372, 14400339433171367428, 13181657164602338457, 12801330883977696413,
     8886499513080244401, 2541968083255470153] := by decide +kernel
theorem poseidon2Hash32_empty_kat : poseidon2Hash32 [] =
    [138, 190, 114, 201, 171, 117, 245, 165, 115, 111, 42, 219, 119, 171, 10, 76, 186, 173, 182, 128, 209, 69, 108,
     220, 169, 239, 117, 130, 81, 43, 90, 65] := by decide +kernel
theorem poseidon2Hash32_zero_byte_kat : poseidon2Hash32 [0x00] =
    [233, 139, 182, 115, 89, 72, 21, 126, 245, 149, 62, 120, 26, 254, 106, 209, 111, 96, 153, 251, 141, 207, 186,
     100, 74, 174, 87, 99, 85, 43, 117, 48] := by decide +kernel
theorem poseidon2Hash32_three_byte_kat : poseidon2Hash32 [0x01, 0x02, 0x03] =
    [196, 180, 177, 170, 216, 21, 133, 248, 62, 149, 42, 39, 133, 17, 81, 112, 144, 59, 209, 93, 95, 26, 110, 112,
     237, 219, 50, 120, 128, 103, 142, 202] := by decide +kernel
theorem poseidon2Hash32_two_block_kat : poseidon2Hash32 ((List.range 65).map UInt8.ofNat) =
    [39, 156, 89, 149, 6, 55, 81, 19, 223, 99, 122, 54, 228, 229, 22, 100, 172, 170, 142, 201, 25, 219, 70, 102,
     137, 73, 207, 135, 141, 48, 175, 71] := by decide +kernel
#guard (poseidon2PadBytes [0x01, 0x02, 0x03]).map (·.val) == [283686901645312, 1, 0, 0, 0, 0, 0, 72057594037927936]
#guard poseidon2Perm12Inv (poseidon2Perm12 countingState) == countingState

-- Without the mixing step the internal constants are `v, v + 1, v + 2`: an arithmetic progression.
#tooth Obend.Crypto.poseidon2ConstAt_not_affine by mutation Obend.Crypto.splitMix64Mix := fun x => x
-- An affine generator.
#tooth Obend.Crypto.poseidon2ConstAt_not_affine
  by mutation Obend.Crypto.poseidon2ConstAt := fun _ round _ => Goldilocks.ofNat (5 + 3 * round)

open Obend.Crypto.BinaryTower256 in
/-- McGrew–Viega / SP 800-38D AES-128 test case 2: `H`, `C`, the length block, `X₁` and `GHASH`. -/
theorem nist_gcm_test_case_2_ghash :
    nistGhashMul 0x0388dace60b6a392f328c2b971b2fe78#128 0x66e94bd4ef8a2c3b884cfa59ca342b2e#128 =
      0x5e2ec746917062882c85b0685353deb7#128 ∧
    nistGhash 0x66e94bd4ef8a2c3b884cfa59ca342b2e#128 [0x0388dace60b6a392f328c2b971b2fe78#128, 0x80#128] =
      0xf38cbb1ad69223dcc3457ae5b6b0f885#128 := by decide +kernel
open Obend.Crypto.BinaryTower256 in
-- The block `80 00 … 00` is the polynomial `1`, the identity of the block product; `40 00 … 00` is `x`.
#guard ghashBlockToGF128 0x80000000000000000000000000000000#128 == 1#128 &&
  nistGhashMul 0x0388dace60b6a392f328c2b971b2fe78#128 0x80000000000000000000000000000000#128 ==
    0x0388dace60b6a392f328c2b971b2fe78#128 &&
  ghashBlockToGF128 0x40000000000000000000000000000000#128 == 2#128
open Obend.Crypto.BinaryTower256 in
-- The product is commutative and associative on the test-case blocks.
#guard
  let h := 0x66e94bd4ef8a2c3b884cfa59ca342b2e#128
  let c := 0x0388dace60b6a392f328c2b971b2fe78#128
  let t := 0xf38cbb1ad69223dcc3457ae5b6b0f885#128
  nistGhashMul h c == nistGhashMul c h && nistGhashMul (nistGhashMul h c) t == nistGhashMul h (nistGhashMul c t)

-- Dropping the reduction by `x⁷ + x² + x + 1`.
#tooth Obend.Crypto.BinaryTower256.gf128Mul_pow_split
  by mutation Obend.Crypto.BinaryTower256.gf128MulX := fun a => a <<< 1
-- Dropping the bit reflection.
#tooth Obend.Crypto.BinaryTower256.nistGhashMul_one
  by mutation Obend.Crypto.BinaryTower256.ghashBlockToGF128 := fun b => b

/-- A configuration whose smudging range is `2^44`. -/
def smudgeCfg : ThresholdDecryptConfig :=
  { params := ⟨4, 2 ^ 54, 256⟩, quorum := 3, encNoiseBound := 8, smudgeBound := 2 ^ 43, secBits := 40 }
-- Sensitivity 16 is covered (16 · 2^40 = 2^44 ≤ 2^44 + 1); sensitivity 17 is not.
#guard checkRenyiSmudgeSecurity smudgeCfg 16
#guard checkRenyiSmudgeSecurity smudgeCfg 17 == false
#guard smudgedOverlapMass 5 10 13 == 8        -- [5, 15] ∩ [8, 18] = [8, 15]
#guard smudgedOverlapMass 5 10 30 == 0        -- disjoint ranges

#tooth Obend.Crypto.renyiSmudgingBound_sound
  by mutation Obend.Crypto.checkRenyiSmudgeSecurity := fun _ _ => true
-- A bound that forgets `secBits`.
#tooth Obend.Crypto.renyiSmudgingBound_sound
  by mutation Obend.Crypto.checkRenyiSmudgeSecurity :=
    fun cfg seatSensitivity => decide (seatSensitivity ≤ 2 * cfg.smudgeBound + 1)

end Crypto

end Obend.Tests.Seam4aFpgaTapeoutCryptoTest
