import Obend.Hardware.TapeoutPipeline
import Obend.Hardware.AwsF2Shell
import Obend.AssertAxioms
import Obend.Tactic.Tooth

/-!
# `tests/silicon_elab/TapeoutAwsF2OpenPdkTest.lean` — Wave-5 Lane C2 Silicon Verification Suite

Exercises and mutation-tests all Wave-5 Lane C2 physical implementation & cloud-FPGA shell layers:
1. **Netlist-Derived `TapeoutPipeline.synthesizeGridPnrCert` & `synthesizeGridPnrCert_valid_for_netlist`**:
   - Multi-cell `BelNetlist` (`LUT1`, `LUT2`, `LUT3`, `CARRY4`, `DSP48E2`, `FF`) producing genuine
     `BelKind`-derived `lutInit` truth tables and disjoint Manhattan X-then-Y switch-box `RoutedNet`s,
   - Accepted when `clockPeriodPs` fits the longest Manhattan Elmore RC arrival delay, and **strictly
     refused** (`= false`) when `clockPeriodPs` is `1 ps` tighter than the real Elmore RC arrival!
2. **Authentic AWS EC2 F2 (`xcvu47p-fsvh2892-2-e`) `cl_ports.vh` Interface & BAR0 `FABulous` Hot-Swap**:
   - Authentic 512-bit AXI4 MM `sh_cl_dma_pcis_*` / `cl_sh_pcim_*` + 32-bit BAR0 `ocl_cl_*` + 32-ch HBM +
     active-low `rst_main_n` accepted; fictional `"sh_pcis_h2c_tdata"` and customer `ICAP` refused,
   - `< 50 µs` verified PCIe BAR0 `FABulous` overlay swap (`f2_pcie_fabulous_hotswap_stutter_safe`),
     256-bit `HashBytes.Hash` commitment binding, and tampered-digest / bad-CRC quarantine.
3. **Pre-Placed UltraScale+ / RapidWright Locked Macro & `XDC` Emitter**:
   - `mapPnrCertToRapidWright`, `emitRapidWrightMacroJson`, `emitUltraScalePblockXdc`, and universal
     `rapidWrightPlacement_collision_free` across `SLICE_X*Y*` (`A6LUT..H6LUT`, `AFF..HFF`) & `DSP48E2_X*Y*`.
4. **Untrusted EDA Signoff Ingestion `Judge`s (`"vivado-sta@1"` & `"openpdk-drc-sta@1"`)**:
   - `vivadoPostRouteStaJudge`: clean `[FF, TT, SS]` multi-SLR `VU47P` report accepted; planted `WHS < 0`
     hold violation and multi-SLR Laguna setup violation refused with `vivadoStaRefutes = true`,
   - `openPdkSignoffJudge`: clean Sky130 (`130nm`) & ASAP7 (`7nm`) layouts + pin-to-DEF port bijection
     accepted; planted Sky130 `met1` `< 140nm` spacing violation, `SS` setup violation, via overhang,
     and broken pin bijection refused.
5. **5 `#tooth` Kernel Mutation Kills & `#assert_axioms_tree` Purity Census (`0 sorryAx`)**.
-/

namespace Obend.Tests.SiliconElab.TapeoutAwsF2OpenPdkTest

open Obend.Category
open Obend.Hardware.Process
open Obend.Hardware.HDL
open Obend.Hardware.Synth
open Obend.Hardware.PlaceRoute
open Obend.Hardware.DRC
open Obend.Hardware.DprStutter
open Obend.Hardware.TapeoutPipeline
open Obend.Hardware.AwsF2Shell

set_option autoImplicit false

-- ============================================================================
-- 0. Whole-Tree Axiom Purity Audit (`0 sorryAx`, `0` custom `axiom`s)
-- ============================================================================

#assert_axioms_tree

-- ============================================================================
-- 1. Netlist-Derived `synthesizeGridPnrCert` & Elmore Tightness Refusal
-- ============================================================================

/-- Multi-cell heterogeneous `BelNetlist` spanning multiple grid tiles (`tileX = 0..3`):
exercises `.portIn`, `.lut1`, `.lut2`, `.lut3`, `.carry4`, `.dspMul`, and `.ff`. -/
def multiCellDatapathNetlist : BelNetlist where
  moduleName  := "multicell_f2_datapath"
  inputNames  := ["a_in", "b_in", "sel_in"]
  cells :=
    [ { dstName := "p_a",     kind := .portIn 0,          inputs := ["a_in"] }
    , { dstName := "inv_a",   kind := .lut1 0x0001,       inputs := ["p_a"] }
    , { dstName := "and_ab",  kind := .lut2 0x0008,       inputs := ["inv_a", "b_in"] }
    , { dstName := "mux_out", kind := .lut3 0x00CA,       inputs := ["p_a", "and_ab", "sel_in"] }
    , { dstName := "sum_c4",  kind := .carry4 .add,       inputs := ["mux_out", "b_in"] }
    , { dstName := "prod_64", kind := .dspMul .mul64,     inputs := ["sum_c4", "and_ab"] }
    , { dstName := "reg_out", kind := .ff 0 .resetFree,   inputs := ["prod_64"] } ]
  outputNames := ["reg_out"]

def multiCellSynthesizedCert : PnrCertificate :=
  synthesizeGridPnrCert multiCellDatapathNetlist 5

/-- Exact worst-case Elmore RC arrival + setup/skew budget (in ps) across all Manhattan-routed
nets of `multiCellSynthesizedCert` at `corner7nm_SS`. -/
def multiCellWorstArrivalPs : Nat :=
  multiCellSynthesizedCert.routedNets.foldl
    (fun acc r =>
      max acc
        (corner7nm_SS.tCqMaxPs + corner7nm_SS.tGateMaxPs +
         computeElmoreDelayPs 5 r.hops +
         corner7nm_SS.tSetupPs + corner7nm_SS.tSkewPs))
    0

-- Extracted LUT truth tables reflect each `BelKind` (NOT hardcoded `0x6`!).
#guard multiCellSynthesizedCert.placedCells.map (·.lutInit) ==
  [0x1000, 0x0001, 0x0008, 0x00CA, 0x0096, 0xD580, 0xFF00]

-- Synthesized `RoutedNet`s come from `multiCellDatapathNetlist`'s 12 real producer-consumer edges
-- (NOT hardcoded `validAdderPnrCert.routedNets`!), are pairwise wire-disjoint, and endpoint-contiguous.
#guard multiCellSynthesizedCert.routedNets != validAdderPnrCert.routedNets
#guard multiCellSynthesizedCert.routedNets.length == 12
#guard checkRoutingDisjoint multiCellSynthesizedCert.routedNets == true
#guard multiCellSynthesizedCert.routedNets.all checkNetConnectivity == true

-- Multi-tile edges produce multi-hop X-then-Y Manhattan switch-box paths (`hops.length > 1`).
#guard multiCellSynthesizedCert.routedNets.any (fun r => decide (r.hops.length ≥ 4)) == true

-- `checkPnrCertificate` ACCEPTS at `multiCellWorstArrivalPs` and REFUSES 1 ps tighter!
#guard checkPnrCertificate multiCellDatapathNetlist corner7nm_SS multiCellWorstArrivalPs multiCellSynthesizedCert == true
#guard checkPnrCertificate multiCellDatapathNetlist corner7nm_SS (multiCellWorstArrivalPs - 1) multiCellSynthesizedCert == false

example :
    checkPnrCertificate multiCellDatapathNetlist corner7nm_SS multiCellWorstArrivalPs multiCellSynthesizedCert = true ∧
    checkPnrCertificate multiCellDatapathNetlist corner7nm_SS (multiCellWorstArrivalPs - 1) multiCellSynthesizedCert = false := by
  have hSuite := synthesizeGridPnrCert_valid_for_netlist
    multiCellDatapathNetlist corner7nm_SS (multiCellWorstArrivalPs - 1) 5 (by decide)
  refine ⟨by decide +kernel, hSuite.2 ?_⟩
  decide +kernel

-- ============================================================================
-- 2. Authentic AWS EC2 F2 (`VU47P`) `cl_ports.vh` & BAR0 `FABulous` Hot-Swap
-- ============================================================================

def sampleF2CoreRtlMod : RtlModule where
  name := "obend_f2_core"
  inputNames := ["a", "b"]
  wires := [{ wireIdx := 0, name := "w_sum", expr := .alu .add (.inputPort 0) (.inputPort 1) }]
  regs := []
  outputs := [{ name := "y", expr := .wireRef 0 }]

-- Authentic `xcvu47p-fsvh2892-2-e` wrapper passes validation and emits `cl_ports.vh` SystemVerilog.
#guard validateF2WrapperPortBinding defaultAwsF2WrapperConfig == true
#guard (emitAwsF2ClWrapperSV defaultAwsF2WrapperConfig sampleF2CoreRtlMod).isSome == true

-- Fictional AXI-Stream DMA port `"sh_pcis_h2c_tdata"` is strictly refused.
def fictionalStreamF2Config : F2WrapperConfig :=
  { defaultAwsF2WrapperConfig with
    portBindings :=
      { shellPortName := "sh_pcis_h2c_tdata", clSignalName := "h2c_stream", dir := .shToCl, width := 512 } ::
        defaultAwsF2WrapperConfig.portBindings }

#guard validateF2WrapperPortBinding fictionalStreamF2Config == false
#guard (emitAwsF2ClWrapperSV fictionalStreamF2Config sampleF2CoreRtlMod).isNone == true

-- Customer ICAP usage (`usesCustomerIcap := true` or `"icap_i"` port) and active-high reset are refused.
#guard validateF2WrapperPortBinding { defaultAwsF2WrapperConfig with usesCustomerIcap := true } == false
#guard validateF2WrapperPortBinding { defaultAwsF2WrapperConfig with rstActiveLow := false } == false
#guard validateF2WrapperPortBinding
  { defaultAwsF2WrapperConfig with
    portBindings := { shellPortName := "icap_i", clSignalName := "icap_din", dir := .clToSh, width := 32 } ::
      defaultAwsF2WrapperConfig.portBindings } == false

-- Wrong AXI4 DMA bus width (`256` instead of `512` on `sh_cl_dma_pcis_wdata`) is refused.
#guard validateF2WrapperPortBinding
  { defaultAwsF2WrapperConfig with
    portBindings := { shellPortName := "sh_cl_dma_pcis_wdata", clSignalName := "bad_w", dir := .shToCl, width := 256 } ::
      defaultAwsF2WrapperConfig.portBindings } == false

example :
    validateF2WrapperPortBinding fictionalStreamF2Config = false ∧
    validateF2WrapperPortBinding { defaultAwsF2WrapperConfig with usesCustomerIcap := true } = false :=
  fictional_pcis_stream_port_refused defaultAwsF2WrapperConfig "h2c_stream" .shToCl 512

/-- Fast 32-byte deterministic rolling sponge for concrete `#guard` / kernel trace execution. -/
def testSpongeHash256 (msg : List UInt8) : List UInt8 :=
  let s0 : UInt64 := msg.foldl (fun acc b => acc * 1099511628211 + b.toUInt64 + 0x9E3779B97F4A7C15) 14695981039346656037
  (List.range 32).map fun i =>
    let mixed := s0 ^^^ ((s0 >>> ((i % 8) * 8).toUInt64) + (i * 131 + msg.length).toUInt64)
    UInt8.ofNat (mixed.toNat % 256)

/-- Initial 2-tile embedded `FABulous` overlay state (`LUT4` buffer + zero tile). -/
def initOverlayTiles : Array TechmappedTile :=
  #[ { lut := 0xAAAA#16, registered := false, a := ⟨0, by decide⟩, b := ⟨1, by decide⟩, c := ⟨2, by decide⟩, d := ⟨3, by decide⟩ }
   , { lut := 0x0000#16, registered := false, a := ⟨0, by decide⟩, b := ⟨1, by decide⟩, c := ⟨2, by decide⟩, d := ⟨3, by decide⟩ } ]

/-- Hot-swapped 2-tile embedded `FABulous` overlay (`LUT4` 2-input `XOR = 0x6666` + 2-input `AND = 0x8888`). -/
def swappedXorAndTiles : Array TechmappedTile :=
  #[ { lut := 0x6666#16, registered := false, a := ⟨0, by decide⟩, b := ⟨1, by decide⟩, c := ⟨2, by decide⟩, d := ⟨3, by decide⟩ }
   , { lut := 0x8888#16, registered := false, a := ⟨0, by decide⟩, b := ⟨1, by decide⟩, c := ⟨2, by decide⟩, d := ⟨3, by decide⟩ } ]

def initF2OverlayState : F2FabulousOverlayState where
  fabric :=
    { specSlot := 0, phase := .active, activeTiles := initOverlayTiles,
      sram := encodeTileFrames initOverlayTiles, pending := none, clampedOut := false,
      inputs := #[true, false, false, false], targetRegs := #[false, false],
      neighbors := { tiles := #[], regs := #[], packets := #[⟨3, 0xCAFE#64, 1⟩], sampledBoundary := false } }
  overlayPhase := .active
  stagedFrames := #[]
  expectedDigest256 := 0#256
  bar0CyclesSpent := 0

-- BAR0 hot-swap latency stays strictly below `50 µs` (`50,000 ns`) at 250 MHz (`clk_main_a0`).
#guard bar0HotSwapLatencyNs 2 == 432
#guard bar0HotSwapLatencyNs 64 == 8368
#guard bar0HotSwapLatencyNs 380 < 50000

def validBar0Frames : Array TileFrame := encodeTileFrames swappedXorAndTiles
def validBar0Digest : BitVec 256 := digestTileFrames256 testSpongeHash256 validBar0Frames

def committedOverlayState : F2FabulousOverlayState :=
  runF2Bar0Schedule testSpongeHash256 initF2OverlayState
    [ .bar0FreezeIsolate
    , .bar0WriteExpectedDigest validBar0Digest
    , .bar0StreamFrames validBar0Frames
    , .bar0AuthenticateCommit ]

-- Valid BAR0 hot-swap commits `swappedXorAndTiles`, advances neighbor NoC hops without stutter (`1 -> 5`),
-- and evaluates `(a=1, b=1) -> (1 XOR 1 = 0, 1 AND 1 = 1)` and `(a=1, b=0) -> (1 XOR 0 = 1, 1 AND 0 = 0)`.
#guard committedOverlayState.overlayPhase == .active
#guard committedOverlayState.fabric.phase == .active
#guard committedOverlayState.fabric.activeTiles == swappedXorAndTiles
#guard committedOverlayState.bar0CyclesSpent == bar0HotSwapCycles 2
#guard committedOverlayState.fabric.neighbors.packets == #[⟨3, 0xCAFE#64, 5⟩]
#guard evalDecodedFabric committedOverlayState.fabric.activeTiles #[true, true, false, false] #[false, false] == #[false, true]
#guard evalDecodedFabric committedOverlayState.fabric.activeTiles #[true, false, false, false] #[false, false] == #[true, false]

-- Tampered 256-bit BAR0 digest (`validBar0Digest ^^^ 1#256`) is quarantined and keeps old `initOverlayTiles`!
def tamperedDigestOverlayState : F2FabulousOverlayState :=
  runF2Bar0Schedule testSpongeHash256 initF2OverlayState
    [ .bar0FreezeIsolate
    , .bar0WriteExpectedDigest (validBar0Digest ^^^ 1#256)
    , .bar0StreamFrames validBar0Frames
    , .bar0AuthenticateCommit ]

#guard tamperedDigestOverlayState.overlayPhase == .quarantined
#guard tamperedDigestOverlayState.fabric.phase == .isolateClamped
#guard tamperedDigestOverlayState.fabric.activeTiles == initOverlayTiles
#guard observedBoundaryPort tamperedDigestOverlayState.fabric == tamperedDigestOverlayState.fabric.clampedOut

-- Corrupted 64-bit frame CRC is ALSO quarantined even when paired with its recomputed 256-bit digest!
def crcFlippedFrames : Array TileFrame :=
  validBar0Frames.map fun f => { f with crc := f.crc ^^^ 1#64 }

def crcCorruptedOverlayState : F2FabulousOverlayState :=
  runF2Bar0Schedule testSpongeHash256 initF2OverlayState
    [ .bar0FreezeIsolate
    , .bar0WriteExpectedDigest (digestTileFrames256 testSpongeHash256 crcFlippedFrames)
    , .bar0StreamFrames crcFlippedFrames
    , .bar0AuthenticateCommit ]

#guard crcCorruptedOverlayState.overlayPhase == .quarantined
#guard crcCorruptedOverlayState.fabric.phase == .isolateClamped
#guard crcCorruptedOverlayState.fabric.activeTiles == initOverlayTiles

-- ============================================================================
-- 3. Pre-Placed UltraScale+ / RapidWright Hard Macro & `XDC` Emitter
-- ============================================================================

def multiCellRapidWrightCells : List RapidWrightCellPlacement :=
  mapPnrCertToRapidWright multiCellDatapathNetlist multiCellSynthesizedCert

#guard multiCellRapidWrightCells.length == 7
#guard checkPlacedBelSlotsBounded multiCellSynthesizedCert.placedCells == true
#guard multiCellRapidWrightCells.all (fun c => c.isLocFixed && c.isBelFixed) == true
#guard (multiCellRapidWrightCells.map (·.siteName)) ==
  ["SLICE_X0Y0", "SLICE_X0Y0", "SLICE_X32Y0", "SLICE_X32Y0", "SLICE_X64Y0", "DSP48E2_X513Y0", "SLICE_X96Y0"]
#guard (multiCellRapidWrightCells.map (·.belName)) ==
  ["A6LUT", "B6LUT", "A6LUT", "B6LUT", "A6LUT", "DSP_ALU", "AFF"]

def sampleRapidWrightJson : String :=
  emitRapidWrightMacroJson "obend_f2_datapath_macro" "pblock_obend_slr0" multiCellRapidWrightCells

def sampleUltraScaleXdc : String :=
  emitUltraScalePblockXdc "pblock_obend_slr0" .slr0 multiCellRapidWrightCells

#guard (sampleRapidWrightJson.splitOn "xcvu47p-fsvh2892-2-e").length == 2
#guard (sampleRapidWrightJson.splitOn "DSP48E2_X513Y0").length == 2
#guard (sampleUltraScaleXdc.splitOn "CONTAIN_ROUTING 1").length == 2
#guard (sampleUltraScaleXdc.splitOn "IS_LOC_FIXED 1").length == 8

example (i j : Nat)
    (hi : i < multiCellRapidWrightCells.length)
    (hj : j < multiCellRapidWrightCells.length)
    (hNe : i ≠ j) :
    multiCellRapidWrightCells[i].physKey ≠ multiCellRapidWrightCells[j].physKey := by
  have hPnr : checkPnrCertificate multiCellDatapathNetlist corner7nm_SS multiCellWorstArrivalPs multiCellSynthesizedCert = true := by
    decide +kernel
  have hSlots : checkPlacedBelSlotsBounded multiCellSynthesizedCert.placedCells = true := by
    decide +kernel
  exact (rapidWrightPlacement_collision_free
    multiCellDatapathNetlist corner7nm_SS multiCellWorstArrivalPs multiCellSynthesizedCert hPnr hSlots).2.2
    i j hi hj hNe

-- ============================================================================
-- 4. Untrusted EDA Signoff `Judge`s (`"vivado-sta@1"` & `"openpdk-drc-sta@1"`)
-- ============================================================================

-- 4.1 Clean multi-SLR `VU47P` `[FF, TT, SS]` post-route STA report passes `vivadoPostRouteStaJudge`.
#guard checkVivadoStaSignoff 8 sampleVivadoStaObj sampleVivadoStaCert == .ok

-- 4.2 Planted `FF`-corner hold violation (`WHS = -12 ps < 0`, `holdArrivalFfPs = 130 < 110 + 35`) is REFUSED!
def holdViolatingVivadoObj : VivadoStaSignoffObj :=
  { sampleVivadoStaObj with
    paths :=
      [ { pathName := "slr0_fast_hold_race", srcSlr := .slr0, dstSlr := .slr0,
          setupArrivalSsPs := 1800, setupSlackReportedSsPs := 2165,
          holdArrivalFfPs := 130, holdReqFfPs := 110, holdSlackReportedFfPs := -12,
          ttArrivalPs := 1450 } ] }

#guard checkVivadoStaSignoff 8 holdViolatingVivadoObj sampleVivadoStaCert == .refused .holdViolationFF [1]
#guard vivadoStaRefutes .holdViolationFF == true

-- 4.3 Planted `SLR0 -> SLR2` double Laguna crossing (`2 * 680 = 1360 ps` SLL penalty exceeding `4000 ps`) is REFUSED!
def slrSetupViolatingVivadoObj : VivadoStaSignoffObj :=
  { sampleVivadoStaObj with
    paths :=
      [ { pathName := "slr0_to_slr2_unpipelined", srcSlr := .slr0, dstSlr := .slr2,
          setupArrivalSsPs := 2700, setupSlackReportedSsPs := 10,
          holdArrivalFfPs := 210, holdReqFfPs := 110, holdSlackReportedFfPs := 65,
          ttArrivalPs := 2200 } ] }

#guard checkVivadoStaSignoff 8 slrSetupViolatingVivadoObj { sampleVivadoStaCert with maxSlrCrossings := 2 } ==
  .refused .setupViolationSS [0]
#guard vivadoStaRefutes .setupViolationSS == true

-- 4.4 Clean Sky130 (`130nm`) and ASAP7 (`7nm`) signoff reports pass `openPdkSignoffJudge`.
#guard checkOpenPdkSignoff 20 sampleSky130SignoffObj sampleSky130SignoffCert == .ok

def sampleAsap7SignoffObj : OpenPdkSignoffObj where
  deck := asap7PdkDeck
  netlistPins := ["clk", "din", "dout"]
  defPorts := ["din", "dout", "clk"]
  metalShapes :=
    [ (0, { layerId := 1, xMinNm := 0,  yMinNm := 0, xMaxNm := 24, yMaxNm := 60 })
    , (1, { layerId := 1, xMinNm := 44, yMinNm := 0, xMaxNm := 68, yMaxNm := 60 }) ]
  viaCuts :=
    [ ( { layerId := 10, xMinNm := 4, yMinNm := 4, xMaxNm := 20, yMaxNm := 20 }
      , { layerId := 1,  xMinNm := 0, yMinNm := 0, xMaxNm := 24, yMaxNm := 60 } ) ]
  cornerReports :=
    [ { pathGroup := "asap7_core", ffWnsPs := 85, ffWhsPs := 12,
        ttWnsPs := 54, ttWhsPs := 18, ssWnsPs := 21, ssWhsPs := 25 } ]

def sampleAsap7SignoffCert : OpenPdkSignoffCert where
  pinToDefIdx := [2, 0, 1]
  defToPinIdx := [1, 2, 0]
  minWnsPs := 21
  minWhsPs := 12

#guard checkOpenPdkSignoff 20 sampleAsap7SignoffObj sampleAsap7SignoffCert == .ok

-- 4.5 Planted Sky130 `met1` spacing violation (`320 - 200 = 120nm < 140nm` Sky130 `met1` spacing rule) is REFUSED!
def sky130SpacingViolatingObj : OpenPdkSignoffObj :=
  { sampleSky130SignoffObj with
    metalShapes :=
      [ (0, { layerId := 1, xMinNm := 0,   yMinNm := 0, xMaxNm := 200, yMaxNm := 200 })
      , (1, { layerId := 1, xMinNm := 320, yMinNm := 0, xMaxNm := 520, yMaxNm := 200 }) ] }

#guard checkOpenPdkSignoff 20 sky130SpacingViolatingObj sampleSky130SignoffCert ==
  .refused .metalSpacingViolation [2]
#guard openPdkRefutes .metalSpacingViolation == true

-- 4.6 Planted OpenSTA `SS` setup violation (`ssWnsPs = -9 ps`), Sky130 via overhang (`< 55nm`),
-- and broken synthesized-netlist-pin to DEF-port bijection are ALL refused!
#guard checkOpenPdkSignoff 20
  { sampleSky130SignoffObj with
    cornerReports := [ { pathGroup := "reg2reg", ffWnsPs := 420, ffWhsPs := 45,
                         ttWnsPs := 290, ttWhsPs := 60, ssWnsPs := -9, ssWhsPs := 85 } ] }
  sampleSky130SignoffCert == .refused .multiCornerStaViolation [0]

#guard checkOpenPdkSignoff 20
  { sampleSky130SignoffObj with
    viaCuts := [ ( { layerId := 10, xMinNm := 20, yMinNm := 60, xMaxNm := 130, yMaxNm := 130 }
                 , { layerId := 1,  xMinNm := 0,  yMinNm := 0,  xMaxNm := 200, yMaxNm := 200 } ) ] }
  sampleSky130SignoffCert == .refused .viaEnclosureViolation [3]

#guard checkOpenPdkSignoff 20
  { sampleSky130SignoffObj with defPorts := ["rst_n", "wrong_port", "clk"] }
  sampleSky130SignoffCert == .refused .bijectionOrSlackCertInvalid [5]

-- ============================================================================
-- 5. `#tooth` Kernel Mutation-Killing Probes (`≥ 5` Universal Theorem Kills)
-- ============================================================================

-- Tooth 1: Collapsing Manhattan PnR cell coordinates to `(0, 0, 0)` kills `synthesizeGridPnrCert_valid_for_netlist`.
def buildGridPlacedCellsColliding (idx : Nat) : List BelCell → List PlacedCell
  | [] => []
  | c :: rest =>
    { cellId := idx, tileX := 0, tileY := 0, belSlot := 0,
      lutInit := extractBelCellLutInit c.kind } :: buildGridPlacedCellsColliding (idx + 1) rest

#tooth Obend.Hardware.TapeoutPipeline.synthesizeGridPnrCert_valid_for_netlist
  by mutation Obend.Hardware.TapeoutPipeline.buildGridPlacedCells := buildGridPlacedCellsColliding

-- Tooth 2: Accepting unverified / fictional AWS F2 shell port bindings kills `validateF2WrapperPortBinding_sound`.
#tooth Obend.Hardware.AwsF2Shell.validateF2WrapperPortBinding_sound
  by mutation Obend.Hardware.AwsF2Shell.validateF2WrapperPortBinding := fun _ => true

-- Tooth 3: Skipping `DprFabric` isolation during BAR0 freeze kills `f2FabulousOverlayStep_preserves_isolationInv`.
def f2FabulousOverlayStepBrokenFreeze
    (_H : Obend.Digest.HashBytes.Hash) (st : F2FabulousOverlayState) (_act : F2Bar0Action) :
    F2FabulousOverlayState :=
  { st with fabric := { st.fabric with phase := .active }, overlayPhase := .frozenIsolated }

#tooth Obend.Hardware.AwsF2Shell.f2FabulousOverlayStep_preserves_isolationInv
  by mutation Obend.Hardware.AwsF2Shell.f2FabulousOverlayStep := f2FabulousOverlayStepBrokenFreeze

-- Tooth 4: Emitting unlocked RapidWright cells (`isLocFixed := false`) kills `rapidWrightPlacement_collision_free`.
def mapPlacedCellToRapidWrightUnlocked (bc : BelCell) (pc : PlacedCell) : RapidWrightCellPlacement :=
  { cellId := pc.cellId, cellName := bc.dstName, slr := .slr0,
    siteKind := .sliceL, siteX := 0, siteY := 0, belPin := .lut6 ⟨0, by decide⟩,
    lutInit := pc.lutInit, isLocFixed := false, isBelFixed := false }

#tooth Obend.Hardware.AwsF2Shell.rapidWrightPlacement_collision_free
  by mutation Obend.Hardware.AwsF2Shell.mapPlacedCellToRapidWright := mapPlacedCellToRapidWrightUnlocked

-- Tooth 5: Waiving same-layer metal spacing DRC kills `openPdkSignoff_same_layer_disjoint`.
#tooth Obend.Hardware.AwsF2Shell.openPdkSignoff_same_layer_disjoint
  by mutation Obend.Hardware.AwsF2Shell.checkShapePairSpacingB := fun _ _ _ => true

end Obend.Tests.SiliconElab.TapeoutAwsF2OpenPdkTest
