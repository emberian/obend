module
/-
# Obend.Hardware.WaferSpace — `wafer.space` (GF180MCU / Sky130 / IHP SG13G2) MPW Shuttle Signoff, IO Padring/ESD, Plasma Antenna Rules, CMP Density & LVS

Formalizes the physical foundry tapeout and Multi-Project Wafer (MPW) shuttle signoff checks required
for open-source ASIC fabrication on **`wafer.space`** (`GF180MCU` 180nm 3.3V/5.0V MCU process,
`Sky130` 130nm, and `IHP SG13G2` 130nm SiGe BiCMOS):

1. **Mixed-Signal 5V/3.3V IO Padring & ESD Clamp Continuity (`PadringSpec`, `checkPadringComplete`)**:
   - Verifies that the chip perimeter contains all 4 corner ring-continuity cells, core & I/O power/ground
     pads (`vddCore`, `vssCore`, `vddIo`, `vssIo`), dedicated rail-to-rail ESD clamps, and per-pad ESD
     diodes on every digital and analog signal pad (`padring_esd_and_power_complete`).
2. **Plasma-Etch Antenna Ratio & Tie-Down Diode Checker (`AntennaNetCheck`, `checkAntennaNet`)**:
   - Prevents gate-oxide Fowler–Nordheim tunneling damage during plasma metal RIE by enforcing
     foundry metal-to-gate area limits (`200:1` un-dioded, `4000:1` with tie-down diode on `GF180MCU`),
   - Proves `antennaSafe_no_gate_oxide_damage`.
3. **Chemical-Mechanical Planarization (CMP) Metal Density Window `[30%, 70%]` (`checkLayerCmpDensity`)**:
   - Prevents CMP oxide dishing (`< 30%`) and copper/aluminum erosion (`> 70%`) across metal layers
     `Metal1..Metal5` (including automated waffling / dummy metal fill `dummyFillUm2`),
   - Proves `cmpDensity_within_foundry_window`.
4. **Layout-Versus-Schematic (LVS) Graph Signature Checker (`LvsNetlistSig`, `checkLvsMatch`)**:
   - Verifies exact device-count, parameter, and net-connectivity agreement between extracted GDSII
     layout and golden schematic (`lvsMatch_sound`).
5. **LibreLane / OpenLane 2 `GF180MCU` Configuration Generator (`emitLibreLaneGf180Json`)**.
-/
public import Obend.Hardware.Silicon
public import Obend.Hardware.Process
public import Obend.Hardware.HDL
public import Obend.Hardware.Synth
public import Obend.Hardware.Retiming
public import Obend.Hardware.PlaceRoute
public import Obend.Hardware.FabuBlox
public import Obend.Hardware.DRC
public import Obend.Hardware.Analog
@[expose] public section

namespace Obend.Hardware.WaferSpace
open Obend.Hardware.Silicon Obend.Hardware.Process Obend.Hardware.HDL
open Obend.Hardware.Synth Obend.Hardware.Retiming Obend.Hardware.PlaceRoute
open Obend.Hardware.FabuBlox Obend.Hardware.DRC Obend.Hardware.Analog
set_option autoImplicit false

/-! ## 1. Open-Source MPW Foundry Process Profiles (`WaferSpacePdk`) -/

/-- Open-source silicon foundry PDKs supported for `wafer.space` / TinyTapeout / Europractice MPW shuttles. -/
inductive WaferSpacePdk where
  | gf180mcuD   -- GlobalFoundries 180nm MCU (5LM, 3.3V/5.0V dual-oxide, MIM cap, high-R poly)
  | sky130A     -- SkyWater 130nm CMOS (5LM, 1.8V core / 5.0V I/O)
  | ihpSg13g2   -- IHP 130nm SiGe BiCMOS (7LM, 1.2V core / 3.3V I/O, 300 GHz HBT)
  deriving DecidableEq, Repr

/-- Maximum allowed un-dioded plasma-etch antenna ratio ($A_{\text{metal}} / A_{\text{gate}}$) per PDK. -/
def maxUnprotectedAntennaRatio : WaferSpacePdk → Nat
  | .gf180mcuD => 200
  | .sky130A   => 400
  | .ihpSg13g2 => 300

/-- Maximum allowed plasma-etch antenna ratio when a reverse-biased tie-down diode is attached. -/
def maxDiodeProtectedAntennaRatio : WaferSpacePdk → Nat
  | .gf180mcuD => 4000
  | .sky130A   => 4000
  | .ihpSg13g2 => 3000

/-! ## 2. Mixed-Signal IO Padring & ESD Clamp Continuity Checker (`checkPadringComplete`) -/

/-- Pad cell classification in a `gf180mcu_fd_io` / `sky130_fd_io` chip perimeter padring. -/
inductive PadCellKind where
  | digitalBidirect
  | analogPassThrough
  | vddCore
  | vssCore
  | vddIo
  | vssIo
  | esdRailClamp
  deriving DecidableEq, Repr

/-- Descriptor for an individual pad instance in the perimeter padring. -/
structure IoPadSpec where
  padName     : String
  kind        : PadCellKind
  voltageMv   : Nat
  hasEsdDiode : Bool
  deriving DecidableEq, Repr

/-- Complete chip perimeter padring specification for a `wafer.space` die (`e.g. 3.0mm x 3.0mm`). -/
structure PadringSpec where
  chipName       : String
  numCornerCells : Nat
  pads           : List IoPadSpec
  deriving DecidableEq, Repr

/-- Verify that a `PadringSpec` satisfies all foundry I/O and Electrostatic Discharge (ESD) rules:
1. All 4 corner seal/rail-continuity cells are placed (`numCornerCells == 4`),
2. Core and I/O power/ground domains are powered (`vddCore`, `vssCore`, `vddIo`, `vssIo` present),
3. At least one dedicated rail-to-rail `esdRailClamp` is present,
4. Every pad in `pads` carries active local ESD diode protection (`hasEsdDiode = true`). -/
def checkPadringComplete (ring : PadringSpec) : Bool :=
  (ring.numCornerCells == 4) &&
  ring.pads.any (fun p => p.kind == .vddCore) &&
  ring.pads.any (fun p => p.kind == .vssCore) &&
  ring.pads.any (fun p => p.kind == .vddIo) &&
  ring.pads.any (fun p => p.kind == .vssIo) &&
  ring.pads.any (fun p => p.kind == .esdRailClamp) &&
  ring.pads.all (fun p => p.hasEsdDiode)

/-- Theorem (`padring_esd_and_power_complete`):
If `checkPadringComplete ring = true`, then `ring` has exactly 4 corner continuity cells and every
pad `p ∈ ring.pads` has local ESD protection (`p.hasEsdDiode = true`). -/
theorem padring_esd_and_power_complete
    (ring : PadringSpec)
    (hOk : checkPadringComplete ring = true) :
    ring.numCornerCells = 4 ∧ (∀ p ∈ ring.pads, p.hasEsdDiode = true) := by
  simp only [checkPadringComplete, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hOk
  exact ⟨hOk.1.1.1.1.1.1, hOk.2⟩

/-! ## 3. Plasma-Etch Antenna Ratio & Tie-Down Diode Verifier (`checkAntennaNet`) -/

/-- Per-net antenna area audit record extracted from physical routing:
* `metalAreaUm2`: exposed metal perimeter/top area on the current RIE etch layer ($\mu\text{m}^2$),
* `gateAreaUm2`: total connected thin/thick MOSFET gate polysilicon area ($\mu\text{m}^2$),
* `hasTieDownDiode`: whether a reverse-biased `n+/p-sub` antenna tie-down diode is attached to bleed
  plasma charge to substrate during etching. -/
structure AntennaNetCheck where
  netName         : String
  metalAreaUm2    : Nat
  gateAreaUm2     : Nat
  hasTieDownDiode : Bool
  deriving DecidableEq, Repr

/-- Check a single routed net against the foundry's plasma-etch antenna rule for `pdk`. -/
def checkAntennaNet (pdk : WaferSpacePdk) (net : AntennaNetCheck) : Bool :=
  decide (net.gateAreaUm2 > 0) &&
  if net.hasTieDownDiode then
    decide (net.metalAreaUm2 ≤ maxDiodeProtectedAntennaRatio pdk * net.gateAreaUm2)
  else
    decide (net.metalAreaUm2 ≤ maxUnprotectedAntennaRatio pdk * net.gateAreaUm2)

/-- Check all nets in a physical layout for antenna violations. -/
def checkAllAntennaNets (pdk : WaferSpacePdk) (nets : List AntennaNetCheck) : Bool :=
  nets.all (checkAntennaNet pdk)

/-- Theorem (`antennaSafe_no_gate_oxide_damage`):
If `checkAntennaNet pdk net = true`, then `net.gateAreaUm2 > 0`, and if `net` exceeds the
unprotected plasma-etch antenna ratio (`maxUnprotectedAntennaRatio pdk * net.gateAreaUm2 < net.metalAreaUm2`),
it is guaranteed to be protected by a tie-down antenna diode (`net.hasTieDownDiode = true`) within
the diode-protected ratio! -/
theorem antennaSafe_no_gate_oxide_damage
    (pdk : WaferSpacePdk) (net : AntennaNetCheck)
    (hSafe : checkAntennaNet pdk net = true) :
    net.gateAreaUm2 > 0 ∧
    (maxUnprotectedAntennaRatio pdk * net.gateAreaUm2 < net.metalAreaUm2 →
      net.hasTieDownDiode = true ∧
      net.metalAreaUm2 ≤ maxDiodeProtectedAntennaRatio pdk * net.gateAreaUm2) := by
  simp only [checkAntennaNet, Bool.and_eq_true, decide_eq_true_eq] at hSafe
  refine ⟨hSafe.1, ?_⟩
  intro hExceed
  cases hDiode : net.hasTieDownDiode with
  | false =>
    rw [hDiode] at hSafe
    simp only [Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq] at hSafe
    omega
  | true =>
    rw [hDiode] at hSafe
    simp only [↓reduceIte, decide_eq_true_eq] at hSafe
    exact ⟨rfl, hSafe.2⟩

/-! ## 4. CMP Metal Density Window `[30%, 70%]` & Dummy Metal Fill Verifier -/

/-- Metal density audit record for a metal layer (`Metal1..Metal5`) across a die window of area `windowAreaUm2`. -/
structure MetalLayerDensity where
  layerName       : String
  routedMetalUm2  : Nat
  dummyFillUm2    : Nat
  windowAreaUm2   : Nat
  deriving DecidableEq, Repr

/-- Total metal area (`routedMetalUm2 + dummyFillUm2`) on the layer. -/
def totalMetalAreaUm2 (m : MetalLayerDensity) : Nat :=
  m.routedMetalUm2 + m.dummyFillUm2

/-- Check that a metal layer's total density lies strictly within the `[30%, 70%]` CMP planarization
window (`30 * windowArea ≤ 100 * totalMetalArea ≤ 70 * windowArea`). -/
def checkLayerCmpDensity (m : MetalLayerDensity) : Bool :=
  decide (m.windowAreaUm2 > 0) &&
  decide (30 * m.windowAreaUm2 ≤ 100 * totalMetalAreaUm2 m) &&
  decide (100 * totalMetalAreaUm2 m ≤ 70 * m.windowAreaUm2)

/-- Check all metal layers in the BEOL stack for CMP density compliance. -/
def checkAllCmpDensity (layers : List MetalLayerDensity) : Bool :=
  layers.all checkLayerCmpDensity

/-- Theorem (`cmpDensity_within_foundry_window`):
Any metal layer passing `checkLayerCmpDensity` satisfies both the `≥ 30%` anti-dishing bound and the
`≤ 70%` anti-erosion bound. -/
theorem cmpDensity_within_foundry_window
    (m : MetalLayerDensity)
    (hOk : checkLayerCmpDensity m = true) :
    m.windowAreaUm2 > 0 ∧
    30 * m.windowAreaUm2 ≤ 100 * (m.routedMetalUm2 + m.dummyFillUm2) ∧
    100 * (m.routedMetalUm2 + m.dummyFillUm2) ≤ 70 * m.windowAreaUm2 := by
  simp only [checkLayerCmpDensity, Bool.and_eq_true, decide_eq_true_eq] at hOk
  simp only [totalMetalAreaUm2] at hOk
  exact ⟨hOk.1.1, hOk.1.2, hOk.2⟩

/-! ## 5. Layout-Versus-Schematic (LVS) Graph Signature Checker (`checkLvsMatch`) -/

/-- Canonical LVS netlist signature summarizing device counts, total MOSFET width/length, MIM
capacitance, and sorted `(devicePin, netName)` connectivity edges. -/
structure LvsNetlistSig where
  moduleName     : String
  nfetCount      : Nat
  pfetCount      : Nat
  mimCapCount    : Nat
  totalCapFf     : Nat
  pinConnections : List (String × String)
  deriving DecidableEq, Repr

/-- Verify Layout-Versus-Schematic (LVS) equivalence between golden schematic `schem` and GDS
extracted layout `layout`. -/
def checkLvsMatch (schem layout : LvsNetlistSig) : Bool :=
  schem == layout

/-- Theorem (`lvsMatch_sound`):
If `checkLvsMatch schem layout = true`, then the extracted layout netlist signature is identical
in every device count, capacitance, and pin-to-net connection to the golden schematic. -/
theorem lvsMatch_sound (schem layout : LvsNetlistSig)
    (hLvs : checkLvsMatch schem layout = true) :
    schem = layout := by
  simp only [checkLvsMatch, beq_iff_eq] at hLvs
  exact hLvs

/-! ## 6. Complete `wafer.space` MPW Shuttle Signoff Certificate & Checker (`checkWaferSpaceSignoff`) -/

/-- Complete `wafer.space` MPW tapeout signoff certificate combining IO padring/ESD, plasma-etch
antenna ratios, CMP metal density (`Metal1..Metal5`), multi-voltage UPF oxide safety, and LVS. -/
structure WaferSpaceSignoffCert where
  projectName   : String
  pdk           : WaferSpacePdk
  padring       : PadringSpec
  antennaNets   : List AntennaNetCheck
  metalLayers   : List MetalLayerDensity
  voltageChecks : List FetVoltageCheck
  schematicSig  : LvsNetlistSig
  layoutSig     : LvsNetlistSig
  deriving DecidableEq, Repr

/-- Complete kernel signoff checker for a `wafer.space` MPW shuttle submission. -/
def checkWaferSpaceSignoff (cert : WaferSpaceSignoffCert) : Bool :=
  checkPadringComplete cert.padring &&
  checkAllAntennaNets cert.pdk cert.antennaNets &&
  checkAllCmpDensity cert.metalLayers &&
  checkAmsPowerSafe cert.voltageChecks &&
  checkLvsMatch cert.schematicSig cert.layoutSig

/-- Golden `GF180MCU` (`wafer.space`) mixed-signal Objective Bend co-processor signoff certificate. -/
def goldenGf180SignoffCert : WaferSpaceSignoffCert where
  projectName := "obend_gf180mcu_ams_coproc"
  pdk         := .gf180mcuD
  padring     :=
    { chipName := "obend_gf180_top"
    , numCornerCells := 4
    , pads :=
        [ { padName := "PAD_VDD_CORE", kind := .vddCore,         voltageMv := 3300, hasEsdDiode := true }
        , { padName := "PAD_VSS_CORE", kind := .vssCore,         voltageMv := 0,    hasEsdDiode := true }
        , { padName := "PAD_VDD_IO",   kind := .vddIo,           voltageMv := 5000, hasEsdDiode := true }
        , { padName := "PAD_VSS_IO",   kind := .vssIo,           voltageMv := 0,    hasEsdDiode := true }
        , { padName := "PAD_ESD_CLMP", kind := .esdRailClamp,    voltageMv := 5000, hasEsdDiode := true }
        , { padName := "PAD_CLK_IN",   kind := .digitalBidirect, voltageMv := 3300, hasEsdDiode := true }
        , { padName := "PAD_ADC_VIN",  kind := .analogPassThrough, voltageMv := 5000, hasEsdDiode := true } ] }
  antennaNets :=
    [ { netName := "clk_tree_m3", metalAreaUm2 := 180,  gateAreaUm2 := 2, hasTieDownDiode := false }
    , { netName := "long_bus_m4", metalAreaUm2 := 2400, gateAreaUm2 := 1, hasTieDownDiode := true  } ]
  metalLayers :=
    [ { layerName := "Metal1", routedMetalUm2 := 3500, dummyFillUm2 := 1000, windowAreaUm2 := 10000 }
    , { layerName := "Metal2", routedMetalUm2 := 2800, dummyFillUm2 := 1200, windowAreaUm2 := 10000 }
    , { layerName := "Metal3", routedMetalUm2 := 2000, dummyFillUm2 := 1500, windowAreaUm2 := 10000 }
    , { layerName := "Metal4", routedMetalUm2 := 1500, dummyFillUm2 := 2000, windowAreaUm2 := 10000 }
    , { layerName := "Metal5", routedMetalUm2 := 1800, dummyFillUm2 := 1600, windowAreaUm2 := 10000 } ]
  voltageChecks :=
    [ { deviceName := "M_core_alu", srcDomainMv := 3300, dstDomainMv := 3300, appliedSwingMv := 3300, oxideRatingMv := 3600, hasLevelShifter := false }
    , { deviceName := "M_io_adc",   srcDomainMv := 5000, dstDomainMv := 3300, appliedSwingMv := 5000, oxideRatingMv := 5500, hasLevelShifter := true  } ]
  schematicSig :=
    { moduleName := "obend_gf180_top", nfetCount := 128, pfetCount := 128, mimCapCount := 16, totalCapFf := 1600
    , pinConnections := [("ADC_IN", "vin_net"), ("CLK", "clk_net"), ("DOUT0", "dout0_net")] }
  layoutSig :=
    { moduleName := "obend_gf180_top", nfetCount := 128, pfetCount := 128, mimCapCount := 16, totalCapFf := 1600
    , pinConnections := [("ADC_IN", "vin_net"), ("CLK", "clk_net"), ("DOUT0", "dout0_net")] }

/-- Bad signoff certificate with an unprotected 2400:1 antenna net (`hasTieDownDiode = false`). -/
def badAntennaSignoffCert : WaferSpaceSignoffCert :=
  { goldenGf180SignoffCert with
    antennaNets :=
      [ { netName := "long_bus_m4", metalAreaUm2 := 2400, gateAreaUm2 := 1, hasTieDownDiode := false } ] }

/-- Bad signoff certificate with under-dense `15%` Metal1 (`< 30%` CMP dishing threshold, dummy fill omitted). -/
def badCmpDensitySignoffCert : WaferSpaceSignoffCert :=
  { goldenGf180SignoffCert with
    metalLayers :=
      [ { layerName := "Metal1", routedMetalUm2 := 1500, dummyFillUm2 := 0, windowAreaUm2 := 10000 } ] }

/-- Theorem: `checkWaferSpaceSignoff` accepts `goldenGf180SignoffCert` and refuses both plasma
antenna violations (`badAntennaSignoffCert`) and CMP under-density (`badCmpDensitySignoffCert`)! -/
theorem waferspace_gf180mcu_signoff_poles :
    checkWaferSpaceSignoff goldenGf180SignoffCert = true ∧
    checkWaferSpaceSignoff badAntennaSignoffCert = false ∧
    checkWaferSpaceSignoff badCmpDensitySignoffCert = false :=
  ⟨rfl, rfl, rfl⟩

/-- Generate a LibreLane / OpenLane 2 `config.json` for taping out an Objective Bend RTL module
on `wafer.space` (`gf180mcuD`). -/
def emitLibreLaneGf180Json (designName verilogFile : String) (clockPeriodNs : Nat) : String :=
  "{\n" ++
  s!"  \"DESIGN_NAME\": \"{designName}\",\n" ++
  "  \"PDK\": \"gf180mcuD\",\n" ++
  "  \"STD_CELL_LIBRARY\": \"gf180mcu_fd_sc_mcu7t5v0\",\n" ++
  s!"  \"VERILOG_FILES\": [\"{verilogFile}\"],\n" ++
  "  \"CLOCK_PORT\": \"clk\",\n" ++
  s!"  \"CLOCK_PERIOD\": {clockPeriodNs},\n" ++
  "  \"VDD_NETS\": [\"VDD\"],\n" ++
  "  \"GND_NETS\": [\"VSS\"],\n" ++
  "  \"RUN_ANTENNA_REPAIR\": true,\n" ++
  "  \"RUN_FILL_INSERTION\": true,\n" ++
  "  \"RUN_KLAYOUT_DRC\": true,\n" ++
  "  \"RUN_NETGEN_LVS\": true\n" ++
  "}\n"

/-! ## 7. Unified End-to-End Silicon Physical Implementation Spine (`EndToEndTapeoutPipeline`) -/

/-- Unified end-to-end physical silicon implementation & tapeout pipeline welding:
1. `Synth`: `RtlModule` $\to$ `BelNetlist` synthesis & FF count preservation,
2. `Retiming`: `SyncGraph` + Leiserson–Saxe `RetimingCert` timing closure,
3. `PlaceRoute` & `Silicon`: `PnrCertificate` + multi-sink `SteinerTree` Elmore RC delay + `PlacedChannel` SLR floorplan,
4. `DRC`: 1D `CutlineDrcFeature` + 2D Manhattan `LayoutBox2D` spacing & via enclosure,
5. `FabuBlox`: `WaferState` + `List FabStep` cleanroom damascene flow + process corner extraction,
6. `WaferSpace`: `WaferSpaceSignoffCert` (`GF180MCU` / `Sky130` / `IHP SG13G2` padring + antenna + CMP + LVS). -/
structure EndToEndTapeoutPipeline where
  rtlModule      : RtlModule
  syncGraph      : SyncGraph
  retimingCert   : RetimingCert
  clockPeriodPs  : Nat
  pnrCert        : PnrCertificate
  steinerTrees   : List SteinerTree
  placedChannels : List PlacedChannel
  drcDeck        : FoundryDrcDeck
  cutlineFeature : CutlineDrcFeature
  metalBoxA      : LayoutBox2D
  metalBoxB      : LayoutBox2D
  viaBox         : LayoutBox2D
  viaPadBox      : LayoutBox2D
  initialWafer   : WaferState
  fabSteps       : List FabStep
  waferSpaceCert : WaferSpaceSignoffCert
  deriving DecidableEq, Repr

/-- Unified kernel checker for the end-to-end RTL-to-GDS physical silicon implementation spine:
chains `FabuBlox` process & RC extraction $\to$ `Synth` $\to$ `Retiming` $\to$ `PlaceRoute` (with
multi-sink `SteinerTree` Elmore delay and `PlacedChannel` floorplan) $\to$ `DRC` (`LayoutBox2D` +
`CutlineDrcFeature`) $\to$ `WaferSpace` signoff. -/
def checkEndToEndSiliconSignoff (pipe : EndToEndTapeoutPipeline) : Bool :=
  match runFabFlow pipe.initialWafer pipe.fabSteps with
  | .error _ => false
  | .ok finalWafer =>
    let corner := extractCornerFromWafer finalWafer
    finalWafer.columns.all (fun c => decide ((extractInterconnectRCFromCutline c).1 ≤ 500)) &&
    checkSynthesizedRtlSignoff pipe.rtlModule &&
    checkRetimingCert pipe.syncGraph pipe.retimingCert corner pipe.clockPeriodPs &&
    checkPnrCertificate corner pipe.clockPeriodPs pipe.pnrCert &&
    pipe.steinerTrees.all (checkSteinerTimingClosure corner pipe.clockPeriodPs) &&
    checkAllChannelHops pipe.placedChannels &&
    checkCutlineDRC pipe.drcDeck pipe.cutlineFeature &&
    checkBoxSpacing2D pipe.drcDeck.minMetalSpacingNm pipe.metalBoxA pipe.metalBoxB &&
    checkViaEnclosure2D pipe.drcDeck.minViaEnclosureNm pipe.viaBox pipe.viaPadBox &&
    checkWaferSpaceSignoff pipe.waferSpaceCert

/-- **Theorem (`checkEndToEndSiliconSignoff_sound`)**:
If `checkEndToEndSiliconSignoff pipe = true`, then EVERY physical stage of the RTL-to-GDS spine
is simultaneously verified:
1. The `FabuBlox` cleanroom recipe succeeds (`∃ finalWafer, ...`), every fabricated cutline column
   meets sheet-resistance signoff (`(extractInterconnectRCFromCutline c).1 ≤ 500`), and every
   multi-sink `SteinerTree` closes Elmore RC setup timing at `extractCornerFromWafer finalWafer`,
2. `pipe.rtlModule` is a valid combinational DAG + CDC-safe module whose synthesized `BelNetlist`
   is valid and preserves exact flip-flop count (`countFfBels = pipe.rtlModule.regs.length`),
3. Every edge `e ∈ pipe.syncGraph.edges` has non-negative Leiserson–Saxe retimed register weight
   `0 ≤ retimedEdgeWeight (lookupLag pipe.retimingCert) e`,
4. BEL placement is injective (`checkPlacementInjective pipe.pnrCert.placedCells = true`), routing
   is short-free (`checkRoutingDisjoint pipe.pnrCert.routedNets = true`), and every `PlacedChannel`
   satisfies tile-local / 2-stage Laguna SLR rules,
5. The 1D cutline feature satisfies minimum foundry metal pitch (`drc_clean_implies_min_pitch`),
   the 2D layout boxes `metalBoxA` and `metalBoxB` are point-wise disjoint (`¬ (metalBoxA.containsPoint x y ∧ metalBoxB.containsPoint x y)`),
   and every point in `viaBox` is strictly enclosed inside `viaPadBox`,
6. The `wafer.space` MPW shuttle submission has 4 corner continuity cells, complete per-pad ESD
   protection, and exact Layout-Versus-Schematic (`schematicSig = layoutSig`) equivalence! -/
theorem checkEndToEndSiliconSignoff_sound (pipe : EndToEndTapeoutPipeline)
    (hOk : checkEndToEndSiliconSignoff pipe = true) :
    (∃ finalWafer,
      runFabFlow pipe.initialWafer pipe.fabSteps = .ok finalWafer ∧
      (∀ c ∈ finalWafer.columns, (extractInterconnectRCFromCutline c).1 ≤ 500) ∧
      (∀ t ∈ pipe.steinerTrees,
        checkSteinerTimingClosure (extractCornerFromWafer finalWafer) pipe.clockPeriodPs t = true)) ∧
    checkRtlModule pipe.rtlModule = true ∧
    checkBelNetlistValid (synthesizeModuleToBels pipe.rtlModule) = true ∧
    countFfBels (synthesizeModuleToBels pipe.rtlModule) = pipe.rtlModule.regs.length ∧
    (∀ e ∈ pipe.syncGraph.edges, 0 ≤ retimedEdgeWeight (lookupLag pipe.retimingCert) e) ∧
    checkPlacementInjective pipe.pnrCert.placedCells = true ∧
    checkRoutingDisjoint pipe.pnrCert.routedNets = true ∧
    (∀ ch ∈ pipe.placedChannels, checkChannelHop ch = .ok ()) ∧
    pipe.drcDeck.minMetalWidthNm + pipe.drcDeck.minMetalSpacingNm ≤
      pipe.cutlineFeature.metalWidthNm + pipe.cutlineFeature.metalSpacingNm ∧
    (∀ x y, ¬ (pipe.metalBoxA.containsPoint x y ∧ pipe.metalBoxB.containsPoint x y)) ∧
    (∀ x y, pipe.viaBox.containsPoint x y → pipe.viaPadBox.containsPoint x y) ∧
    pipe.waferSpaceCert.padring.numCornerCells = 4 ∧
    pipe.waferSpaceCert.schematicSig = pipe.waferSpaceCert.layoutSig := by
  unfold checkEndToEndSiliconSignoff at hOk
  cases hFab : runFabFlow pipe.initialWafer pipe.fabSteps with
  | error err => rw [hFab] at hOk; cases hOk
  | ok finalWafer =>
    rw [hFab] at hOk
    dsimp only at hOk
    simp only [Bool.and_eq_true] at hOk
    rcases hOk with ⟨⟨⟨⟨⟨⟨⟨⟨⟨hRc, hSynth⟩, hRet⟩, hPnr⟩, hSteiner⟩, hChan⟩, hCutDrc⟩, hBoxSpace⟩, hViaEnc⟩, hWs⟩
    have hRcAll : ∀ c ∈ finalWafer.columns, (extractInterconnectRCFromCutline c).1 ≤ 500 := by
      intro c hMem
      simp only [List.all_eq_true, decide_eq_true_eq] at hRc
      exact hRc c hMem
    have hSteinerAll : ∀ t ∈ pipe.steinerTrees,
        checkSteinerTimingClosure (extractCornerFromWafer finalWafer) pipe.clockPeriodPs t = true := by
      intro t hMem
      simp only [List.all_eq_true] at hSteiner
      exact hSteiner t hMem
    have hSynthSound := checkSynthesizedRtlSignoff_sound pipe.rtlModule hSynth
    have hRetNonneg : ∀ e ∈ pipe.syncGraph.edges, 0 ≤ retimedEdgeWeight (lookupLag pipe.retimingCert) e := by
      simp only [checkRetimingCert, Bool.and_eq_true] at hRet
      exact retimed_weights_nonneg (lookupLag pipe.retimingCert) pipe.syncGraph.edges hRet.1.1
    have hPnrParts : checkPlacementInjective pipe.pnrCert.placedCells = true ∧
        checkRoutingDisjoint pipe.pnrCert.routedNets = true := by
      simp only [checkPnrCertificate, Bool.and_eq_true] at hPnr
      exact ⟨hPnr.1.1.1.1, hPnr.1.1.2⟩
    have hChanSound : ∀ ch ∈ pipe.placedChannels, checkChannelHop ch = .ok () := by
      intro ch hMem
      exact (checkAllChannelHops_sound pipe.placedChannels hChan ch hMem).1
    have hPitch := drc_clean_implies_min_pitch pipe.drcDeck pipe.cutlineFeature hCutDrc
    have hWsParts : pipe.waferSpaceCert.padring.numCornerCells = 4 ∧
        pipe.waferSpaceCert.schematicSig = pipe.waferSpaceCert.layoutSig := by
      simp only [checkWaferSpaceSignoff, Bool.and_eq_true] at hWs
      exact ⟨(padring_esd_and_power_complete pipe.waferSpaceCert.padring hWs.1.1.1.1).1,
             lvsMatch_sound pipe.waferSpaceCert.schematicSig pipe.waferSpaceCert.layoutSig hWs.2⟩
    refine ⟨⟨finalWafer, rfl, hRcAll, hSteinerAll⟩,
            hSynthSound.1,
            hSynthSound.2.1,
            hSynthSound.2.2,
            hRetNonneg,
            hPnrParts.1,
            hPnrParts.2,
            hChanSound,
            hPitch,
            fun x y => boxSpacing2D_disjoint pipe.drcDeck.minMetalSpacingNm pipe.metalBoxA pipe.metalBoxB x y hBoxSpace,
            fun x y hIn => (viaEnclosure2D_contained pipe.drcDeck.minViaEnclosureNm pipe.viaBox pipe.viaPadBox x y hViaEnc hIn).1,
            hWsParts.1,
            hWsParts.2⟩

/-- Golden end-to-end silicon physical implementation pipeline on `corner7nm_SS` / `GF180MCU`. -/
def goldenEndToEndSiliconPipeline : EndToEndTapeoutPipeline where
  rtlModule      := goldenRetimedMacRtl
  syncGraph      := macUnretimedGraph
  retimingCert   := balancedRetimingCert
  clockPeriodPs  := 2000
  pnrCert        := validAdderPnrCert
  steinerTrees   := [bufferedFanoutTree]
  placedChannels := goldenPlacedChannels
  drcDeck        :=
    { deckName          := "FabuBlox-7nm-BEOL"
    , minMetalWidthNm   := 40
    , minMetalSpacingNm := 40
    , minViaWidthNm     := 36
    , minViaEnclosureNm := 10
    , maxResistAspect   := 4 }
  cutlineFeature :=
    { metalWidthNm    := 100
    , metalSpacingNm  := 80
    , viaWidthNm      := 40
    , viaEnclosureNm  := 20
    , resistHeightNm  := 120
    , resistOpeningNm := 40
    , ildThicknessNm  := 100 }
  metalBoxA      := { layerId := 1, xMinNm := 0,   yMinNm := 0,  xMaxNm := 100, yMaxNm := 200 }
  metalBoxB      := { layerId := 1, xMinNm := 160, yMinNm := 0,  xMaxNm := 260, yMaxNm := 200 }
  viaBox         := { layerId := 2, xMinNm := 20,  yMinNm := 20, xMaxNm := 60,  yMaxNm := 60  }
  viaPadBox      := { layerId := 1, xMinNm := 0,   yMinNm := 0,  xMaxNm := 100, yMaxNm := 100 }
  initialWafer   := initialCmosWafer
  fabSteps       := cmosDamasceneFlow
  waferSpaceCert := goldenGf180SignoffCert

/-- Theorem: `goldenEndToEndSiliconPipeline` passes the unified `checkEndToEndSiliconSignoff` gate! -/
-- fixture kept (2026-11-04): would delete (a preset passing its own signoff) but cited by tests/metasystem/PhysicalSiliconSpineTest.lean:338
theorem goldenEndToEndSiliconPipeline_verified :
    checkEndToEndSiliconSignoff goldenEndToEndSiliconPipeline = true := by
  decide +kernel

end Obend.Hardware.WaferSpace
