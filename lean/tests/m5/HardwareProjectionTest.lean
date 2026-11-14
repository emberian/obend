module
import all Obend.Hardware.NotebookProjection
meta import all Obend.Hardware.NotebookProjection
import Obend.Doc.Structured
import Obend.Doc.Graph
import Obend.Hardware.HDL
import Obend.Hardware.Process
import Obend.Hardware.PlaceRoute
import Obend.Hardware.DRC
import Obend.Hardware.Synth
import Obend.Hardware.Circuits
meta import Obend.Doc.Structured
meta import Obend.Doc.Graph
meta import Obend.Hardware.HDL
meta import Obend.Hardware.Process
meta import Obend.Hardware.PlaceRoute
meta import Obend.Hardware.DRC
meta import Obend.Hardware.Synth
meta import Obend.Hardware.Circuits

open Obend.Vault.HardwareProjection
open Obend.Doc
open Obend.Hardware.HDL
open Obend.Hardware.Process
open Obend.Hardware.PlaceRoute
open Obend.Hardware.DRC
open Obend.Hardware.Synth
open Obend.Hardware.Circuits

set_option autoImplicit false

/-! # Milestone 5 Feature 36: Read-Only Hardware Projection Test Suite -/

-- Test 1: RTL Circuit Projection to Content.cell
def test_project_circuit : Bool :=
  let m : Circuit := {
    name       := "adder_cell"
    inputNames := ["a", "b"]
    wires      := [{ wireIdx := 0, name := "w0", expr := .alu .add (.inputPort 0) (.inputPort 1) }]
    regs       := []
    outputs    := [{ name := "sum", expr := .wireRef 0 }]
  }
  let c := projectCircuit "cell_rtl_0" m
  match c with
  | .cell id kind _ast pins receipt =>
    (id == "cell_rtl_0") &&
    (kind == .hardwareSchematic) &&
    (pins.isEmpty == true) &&
    (receipt.isNone == true)
  | _ => false

#guard test_project_circuit == true

-- Test 2: BEL Netlist Projection & Congruence
def test_project_netlist_congruence : Bool :=
  let golden : Netlist := validAdderBelNetlist
  let layout := golden
  let cGolden := projectNetlist "netlist_0" golden
  let cLayout := projectNetlist "netlist_0" layout
  (checkBelNetlistValid golden == true) &&
  (cGolden == cLayout)

#guard test_project_netlist_congruence == true

-- Test 3: Static Timing Analysis Projection (Setup & Hold Closure)
def test_project_timing_closed : Bool :=
  let corner := corner7nm_SS
  let path : TimingPath := {
    name        := "alu_critical_path"
    logicLevels := 2
    minLevels   := 1
    carryBits   := 4
    tileHops    := 1
  }
  let clockPeriodPs := 2000 -- 500 MHz = 2000 ps
  let c := projectTiming "timing_0" corner path clockPeriodPs
  let closed := checkTimingSignoff corner clockPeriodPs path
  match c with
  | .cell _ kind _ _ _ =>
    (kind == .hardwareTiming) &&
    (closed == true)
  | _ => false

#guard test_project_timing_closed == true

-- Test 4: Physical Placement & PnR Bitstream Projection
def test_project_gdsii_pnr : Bool :=
  let pnr : GdsLayout := {
    designName      := "tiny_alu"
    placedCells     := [⟨0, 0, 0, 0, 0xAA⟩]
    routedNets      := []
    expectedConfigs := [⟨0, 0, 0, 0xAA, 0⟩]
    bitstreamFrames := [⟨0, 0xAA0000⟩]
    sinkCapFf       := 10
  }
  let c := projectGdsii "pnr_0" pnr
  match c with
  | .cell _ kind _ _ _ => kind == .hardwareLayout
  | _ => false

#guard test_project_gdsii_pnr == true

-- Test 5: Cutline DRC Projection & Pitch Check
def test_project_cutline_drc : Bool :=
  let deck : FoundryDrcDeck := {
    deckName          := "Sky130_DRC"
    minMetalWidthNm   := 140
    minMetalSpacingNm := 140
    minViaWidthNm     := 170
    minViaEnclosureNm := 60
    maxResistAspect   := 3
  }
  let feat : CutlineDrcFeature := {
    metalWidthNm    := 200
    metalSpacingNm  := 200
    viaWidthNm      := 180
    viaEnclosureNm  := 80
    resistHeightNm  := 300
    resistOpeningNm := 150
    ildThicknessNm  := 800
  }
  let c := projectDrc "drc_0" deck feat
  let clean := checkCutlineDRC deck feat
  match c with
  | .cell _ kind _ _ _ =>
    (kind == .hardwareLayout) &&
    (clean == true)
  | _ => false

#guard test_project_cutline_drc == true

-- Test 6: Routing/frame projection retains a nonempty hardware payload.
example : ∃ c : PnrCertificate, c.routedNets ≠ [] ∧ c.bitstreamFrames ≠ [] ∧
    ∀ d, pnrLayoutToData c = pnrLayoutToData d →
      c.routedNets = d.routedNets ∧ c.bitstreamFrames = d.bitstreamFrames :=
  pnr_projection_inhabited

-- Test 7: Document Graph Non-Interference
def test_doc_atom_noninterference : Bool :=
  let G0 : Graph := {
    atoms := [(1, .text "First paragraph"), (2, .field "status" "draft")]
    dead  := []
    edges := [(1, 2)]
  }
  let hwCell := projectTiming "t_cell" corner16nm_SS ⟨"p", 1, 1, 0, 0⟩ 5000
  let G1 : Graph := { G0 with atoms := (3, hwCell) :: G0.atoms }
  (G1.label 1 == some (.text "First paragraph")) &&
  (G1.label 2 == some (.field "status" "draft")) &&
  (G1.label 3 == some hwCell)

#guard test_doc_atom_noninterference == true

namespace RouteFrameProjectionAudit
open Obend.Vault.HardwareProjection
open Obend.Core.Data

example : match pnrLayoutToData projectionWitness with
    | .record fs => (fs.find? (fun f => f.1 == "route_frame_commitment")).map Prod.snd =
        some (dataSeq (fun b => .natural b.toNat) (pnrRouteFrameBytes projectionWitness))
    | _ => False := by rfl

end RouteFrameProjectionAudit
