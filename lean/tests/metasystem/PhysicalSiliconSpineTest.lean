module

public import Obend.Tactic.Tooth
public import Obend.Hardware.Silicon
public import Obend.Hardware.Synth
public import Obend.Hardware.Retiming
public import Obend.Hardware.PlaceRoute
public import Obend.Hardware.FabuBlox
public import Obend.Hardware.DRC
public import Obend.Hardware.WaferSpace
import all Obend.Hardware.Silicon
import all Obend.Hardware.Synth
import all Obend.Hardware.Retiming
import all Obend.Hardware.PlaceRoute
import all Obend.Hardware.FabuBlox
import all Obend.Hardware.DRC
import all Obend.Hardware.WaferSpace

/-!
# Metasystem Test Suite — End-to-End Silicon Physical Implementation Spine (`WS-I`)

Comprehensive universal theorem checks, boundary & negative refutation poles, `#tooth`
kernel mutation-killing probes, and `#print axioms` verification (`0 sorryAx`) across:
1. `Obend.Hardware.Retiming` & `Obend.Hardware.Synth`:
   - `solveRetimingFuel`, `solveVerifiedRetiming?`, `solveVerifiedRetiming_sound`,
   - `applyRetimingCertToGraph`, `applyRetimingCertToGraph_preserves_cycle_weight`,
   - `checkSynthesizedRtlSignoff`, `checkSynthesizedRtlSignoff_sound`.
2. `Obend.Hardware.PlaceRoute`:
   - `SteinerTree`, `downstreamCapFf`, `maxSteinerElmoreDelayFsOhm`, `maxSteinerElmoreDelayPs`,
   - `downstreamCapFf_monotone_load`, `maxSteinerElmoreDelay_nonneg`,
   - `steiner_fanout_buffer_insertion_reduces_elmore_delay`.
3. `Obend.Hardware.DRC` & `Obend.Hardware.FabuBlox`:
   - `LayoutBox2D`, `checkBoxSpacing2D`, `checkViaEnclosure2D`,
   - `boxSpacing2D_disjoint`, `viaEnclosure2D_contained`,
   - (`extractInterconnectRC_*` monotonicity deleted 2026-11-04 with `FabuBlox` §6; the function is tested through `WaferSpace`.)
4. `Obend.Hardware.Silicon` & `Obend.Hardware.WaferSpace`:
   - `checkAllChannelHops`, `checkAllChannelHops_sound`,
   - `EndToEndTapeoutPipeline`, `checkEndToEndSiliconSignoff`, `checkEndToEndSiliconSignoff_sound`,
   - `goldenEndToEndSiliconPipeline_verified` & stage-by-stage negative refusal poles.
-/

@[expose] public section
namespace Obend.Tests.Metasystem.PhysicalSiliconSpineTest

open Obend.Hardware.Process
open Obend.Hardware.HDL
open Obend.Hardware.Silicon
open Obend.Hardware.Synth
open Obend.Hardware.Retiming
open Obend.Hardware.PlaceRoute
open Obend.Hardware.FabuBlox
open Obend.Hardware.DRC
open Obend.Hardware.WaferSpace
set_option autoImplicit false

/-! ## 1. Deliverable 1 Tests: Constructive Leiserson–Saxe Retiming Solver & Cycle Weight Invariance -/

/-- 1.1 Universal soundness of `solveVerifiedRetiming?`: every edge in any accepted certificate has
non-negative retimed register weight $w_r(e) \ge 0$. -/
theorem test_solveVerifiedRetiming_sound
    (fuel : Nat) (g : SyncGraph) (maxDelay : Nat) (cert : RetimingCert)
    (hSome : solveVerifiedRetiming? fuel g maxDelay = some cert) :
    ∀ e ∈ g.edges, 0 ≤ retimedEdgeWeight (lookupLag cert) e :=
  solveVerifiedRetiming_sound fuel g maxDelay cert hSome

/-- 1.2 Universal cycle register weight preservation under `applyRetimingCertToGraph`. -/
theorem test_applyRetimingCertToGraph_preserves_cycle_weight
    (g : SyncGraph) (cert : RetimingCert) (startVtx : Nat)
    (hCycle : checkContiguousSyncEdges startVtx startVtx g.edges = true)
    (hNonneg : checkAllEdgesNonneg (lookupLag cert) g.edges = true) :
    origPathWeight (edgesToPathHops (applyRetimingCertToGraph g cert).edges) =
      origPathWeight (edgesToPathHops g.edges) :=
  applyRetimingCertToGraph_preserves_cycle_weight g cert startVtx hCycle hNonneg

/-- 3-vertex feedback loop graph `0 → 1 → 2 → 0` with `3` total loop registers. -/
def testFeedbackCycleGraph : SyncGraph where
  name           := "feedback_3cycle"
  primaryInputs  := []
  primaryOutputs := []
  edges          :=
    [ { src := 0, dst := 1, origRegs := 0, combDelayPs := 1900 }
    , { src := 1, dst := 2, origRegs := 2, combDelayPs := 800  }
    , { src := 2, dst := 0, origRegs := 1, combDelayPs := 700  } ]

/-- 1.3 Concrete solver + cycle weight invariance verification on:
* `macUnretimedGraph` (backward retiming `r(1) = 1`),
* `dualMacUnretimedGraph` (forward retiming `r(1) = -1` pushing a register toward a pinned output),
* `multiHopChainGraph` (multi-hop zero-register combinational chain `1100 + 1100 = 2200 > 1800 ps`),
* `testFeedbackCycleGraph` (3-vertex feedback loop cycle weight preservation),
plus negative-pole refusals on `testUnretimeableGraph` and `directIoSlowGraph`. -/
def testUnretimeableGraph : SyncGraph where
  name           := "unretimeable_zero_regs"
  primaryInputs  := [0]
  primaryOutputs := [2]
  edges          :=
    [ { src := 0, dst := 1, origRegs := 0, combDelayPs := 2500 }
    , { src := 1, dst := 2, origRegs := 0, combDelayPs := 900  } ]

def directIoSlowGraph : SyncGraph where
  name           := "direct_io_slow"
  primaryInputs  := [0]
  primaryOutputs := [1]
  edges          :=
    [ { src := 0, dst := 1, origRegs := 0, combDelayPs := 2500 } ]

def dualMacUnretimedGraph : SyncGraph where
  name           := "mac_forward_2stage"
  primaryInputs  := [0]
  primaryOutputs := [2]
  edges          :=
    [ { src := 0, dst := 1, origRegs := 2, combDelayPs := 900  }
    , { src := 1, dst := 2, origRegs := 0, combDelayPs := 2200 } ]

def multiHopChainGraph : SyncGraph where
  name           := "chain_3stage"
  primaryInputs  := [0]
  primaryOutputs := [3]
  edges          :=
    [ { src := 0, dst := 1, origRegs := 0, combDelayPs := 1100 }
    , { src := 1, dst := 2, origRegs := 0, combDelayPs := 1100 }
    , { src := 2, dst := 3, origRegs := 2, combDelayPs := 700  } ]

example :
    (match solveVerifiedRetiming? 2 macUnretimedGraph 1800 with
     | some cert =>
       decide (lookupLag cert 0 = 0) &&
       decide (lookupLag cert 1 = 1) &&
       decide (lookupLag cert 2 = 0) &&
       checkRetimingCert macUnretimedGraph cert corner7nm_SS 2000 &&
       decide ((applyRetimingCertToGraph macUnretimedGraph cert).edges.map (·.origRegs) = [1, 1])
     | none => false) = true ∧
    (match solveVerifiedRetiming? 2 dualMacUnretimedGraph 1800 with
     | some cert =>
       decide (lookupLag cert 0 = 0) &&
       decide (lookupLag cert 1 = -1) &&
       decide (lookupLag cert 2 = 0) &&
       checkRetimingCert dualMacUnretimedGraph cert corner7nm_SS 2000 &&
       decide ((applyRetimingCertToGraph dualMacUnretimedGraph cert).edges.map (·.origRegs) = [1, 1])
     | none => false) = true ∧
    (match solveVerifiedRetiming? 3 multiHopChainGraph 1800 with
     | some cert =>
       decide (lookupLag cert 2 = 1) &&
       checkRetimingCert multiHopChainGraph cert corner7nm_SS 2000 &&
       decide ((applyRetimingCertToGraph multiHopChainGraph cert).edges.map (·.origRegs) = [0, 1, 1])
     | none => false) = true ∧
    (match solveVerifiedRetiming? 3 testFeedbackCycleGraph 1500 with
     | some cert =>
       checkContiguousSyncEdges 0 0 testFeedbackCycleGraph.edges &&
       decide (origPathWeight (edgesToPathHops (applyRetimingCertToGraph testFeedbackCycleGraph cert).edges) =
         origPathWeight (edgesToPathHops testFeedbackCycleGraph.edges)) &&
       decide (origPathWeight (edgesToPathHops (applyRetimingCertToGraph testFeedbackCycleGraph cert).edges) = 3)
     | none => false) = true ∧
    solveVerifiedRetiming? 2 testUnretimeableGraph 1800 = none ∧
    solveVerifiedRetiming? 2 directIoSlowGraph 1800 = none := by
  decide +kernel

/-! ## 2. Deliverable 2 Tests: Multi-Sink `SteinerTree` Elmore RC Delay & Repeater Buffer Insertion -/

/-- 2.1 Universal load monotonicity and non-negativity of `downstreamCapFf` and `maxSteinerElmoreDelayFsOhm`. -/
theorem test_steiner_elmore_monotone_and_nonneg
    (deltaCapFf : Nat) (t : SteinerTree) :
    downstreamCapFf t ≤ downstreamCapFf (inflateSinkLoads deltaCapFf t) ∧
    maxSteinerElmoreDelayFsOhm t ≤ maxSteinerElmoreDelayFsOhm (inflateSinkLoads deltaCapFf t) ∧
    0 ≤ maxSteinerElmoreDelayFsOhm t :=
  ⟨(downstreamCapFf_monotone_load deltaCapFf t).1,
   (downstreamCapFf_monotone_load deltaCapFf t).2,
   (maxSteinerElmoreDelay_nonneg t).1⟩

/-- 2.2 Concrete & universal repeater buffer insertion theorem (`steiner_fanout_buffer_insertion_reduces_elmore_delay`),
plus boundary check on a single leaf `.sink`. -/
example :
    downstreamCapFf (.sink 0 25) = 25 ∧
    maxSteinerElmoreDelayFsOhm (.sink 0 25) = 0 ∧
    downstreamCapFf unbufferedFanoutTree = 1050 ∧
    downstreamCapFf bufferedFanoutTree = 175 ∧
    maxSteinerElmoreDelayFsOhm unbufferedFanoutTree = 3450000 ∧
    maxSteinerElmoreDelayFsOhm bufferedFanoutTree = 350000 ∧
    checkSteinerTimingClosure corner7nm_SS 2000 unbufferedFanoutTree = false ∧
    checkSteinerTimingClosure corner7nm_SS 2000 bufferedFanoutTree = true ∧
    downstreamCapFf bufferedFanoutTree < downstreamCapFf unbufferedFanoutTree ∧
    maxSteinerElmoreDelayFsOhm bufferedFanoutTree < maxSteinerElmoreDelayFsOhm unbufferedFanoutTree := by
  decide +kernel

/-! ## 3. Deliverable 3A & 3B Tests: 2D `LayoutBox2D` DRC & `FabuBlox` Cutline RC Extraction -/

/-- 3.1 Universal 2D Manhattan box disjointness (`boxSpacing2D_disjoint`) and via enclosure containment
(`viaEnclosure2D_contained`). -/
theorem test_drc_2d_box_soundness
    (minSpacingNm minEncNm : Nat) (b1 b2 viaBox padBox : LayoutBox2D) (x y : Nat)
    (hSpace : checkBoxSpacing2D minSpacingNm b1 b2 = true)
    (hEnc   : checkViaEnclosure2D minEncNm viaBox padBox = true) :
    ¬ (b1.containsPoint x y ∧ b2.containsPoint x y) ∧
    (viaBox.containsPoint x y → padBox.containsPoint x y) :=
  ⟨boxSpacing2D_disjoint minSpacingNm b1 b2 x y hSpace,
   fun hIn => (viaEnclosure2D_contained minEncNm viaBox padBox x y hEnc hIn).1⟩

/-- 3.2 Concrete 2D `LayoutBox2D` positive & negative boundary poles (overlapping boxes, insufficient spacing,
degenerate zero-width box, and overhanging via). -/
example :
    let boxA : LayoutBox2D := { layerId := 1, xMinNm := 0,   yMinNm := 0,  xMaxNm := 100, yMaxNm := 100 }
    let boxB : LayoutBox2D := { layerId := 1, xMinNm := 150, yMinNm := 0,  xMaxNm := 250, yMaxNm := 100 }
    let boxOverlap : LayoutBox2D := { layerId := 1, xMinNm := 80, yMinNm := 0, xMaxNm := 180, yMaxNm := 100 }
    let boxDegen : LayoutBox2D := { layerId := 1, xMinNm := 200, yMinNm := 0, xMaxNm := 200, yMaxNm := 100 }
    let viaOk : LayoutBox2D := { layerId := 2, xMinNm := 20, yMinNm := 20, xMaxNm := 80, yMaxNm := 80 }
    let viaOverhang : LayoutBox2D := { layerId := 2, xMinNm := 5, yMinNm := 20, xMaxNm := 80, yMaxNm := 80 }
    checkBoxSpacing2D 40 boxA boxB = true ∧
    checkBoxSpacing2D 60 boxA boxB = false ∧
    checkBoxSpacing2D 0 boxA boxOverlap = false ∧
    checkBoxSpacing2D 10 boxA boxDegen = false ∧
    checkViaEnclosure2D 15 viaOk boxA = true ∧
    checkViaEnclosure2D 15 viaOverhang boxA = false := by
  decide +kernel

/-! ## 4. Deliverable 3C Tests: Unified `EndToEndTapeoutPipeline` & Stage-by-Stage Negative Poles -/

/-- 4.1 Universal soundness of `checkEndToEndSiliconSignoff`. -/
theorem test_checkEndToEndSiliconSignoff_sound
    (pipe : EndToEndTapeoutPipeline)
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
    pipe.waferSpaceCert.schematicSig = pipe.waferSpaceCert.layoutSig :=
  checkEndToEndSiliconSignoff_sound pipe hOk

/-- 4.2 Stage-by-stage negative refusal poles across the entire RTL-to-GDS spine:
1. Golden pipeline passes (`= true`),
2. Unretimed critical path (`identityRetimingCert`) fails at 500 MHz (`= false`),
3. Negative retiming lag (`negativeWeightBadCert`) fails (`= false`),
4. BEL placement collision (`collidingBelPnrCert`) fails (`= false`),
5. Unbuffered high-fanout Steiner tree (`unbufferedFanoutTree`, `3450 ps > 2000 ps`) fails (`= false`),
6. Unregistered SLR crossing (`regStages = 1 < 2`) fails (`= false`),
7. Overlapping 2D metal bounding boxes fail (`= false`),
8. Unenclosed 2D via overhangs metal landing pad and fails (`= false`),
9. Post-Cu FEOL furnace contamination step in `fabSteps` fails (`= false`),
10. Unprotected `2400:1` plasma-etch antenna net in `waferSpaceCert` fails (`= false`). -/
example :
    checkEndToEndSiliconSignoff goldenEndToEndSiliconPipeline = true ∧
    checkEndToEndSiliconSignoff { goldenEndToEndSiliconPipeline with retimingCert := identityRetimingCert } = false ∧
    checkEndToEndSiliconSignoff { goldenEndToEndSiliconPipeline with retimingCert := negativeWeightBadCert } = false ∧
    checkEndToEndSiliconSignoff { goldenEndToEndSiliconPipeline with pnrCert := collidingBelPnrCert } = false ∧
    checkEndToEndSiliconSignoff { goldenEndToEndSiliconPipeline with steinerTrees := [unbufferedFanoutTree] } = false ∧
    checkEndToEndSiliconSignoff
      { goldenEndToEndSiliconPipeline with
        placedChannels := [{ name := "bad_slr", src := ⟨0, 0, 0⟩, dst := ⟨1, 0, 0⟩, bitWidth := 64, regStages := 1 }] } = false ∧
    checkEndToEndSiliconSignoff
      { goldenEndToEndSiliconPipeline with
        metalBoxB := { layerId := 1, xMinNm := 50, yMinNm := 0, xMaxNm := 150, yMaxNm := 200 } } = false ∧
    checkEndToEndSiliconSignoff
      { goldenEndToEndSiliconPipeline with
        viaBox := { layerId := 2, xMinNm := 2, yMinNm := 20, xMaxNm := 60, yMaxNm := 60 } } = false ∧
    checkEndToEndSiliconSignoff
      { goldenEndToEndSiliconPipeline with
        fabSteps := cmosDamasceneFlow ++ [.feolThermalAnneal 600 10] } = false ∧
    checkEndToEndSiliconSignoff
      { goldenEndToEndSiliconPipeline with
        waferSpaceCert := badAntennaSignoffCert } = false := by
  decide +kernel

/-! ## 5. `#tooth` Kernel Mutation-Killing Probes & Axiom Audit -/

/-- Broken `solveVerifiedRetiming?` that skips `checkAllEdgesNonneg` and returns `negativeWeightBadCert`. -/
def solveVerifiedRetimingBrokenSkipCheck (_fuel : Nat) (_g : SyncGraph) (_maxCombDelayPs : Nat) : Option RetimingCert :=
  some negativeWeightBadCert

#tooth Obend.Hardware.Retiming.solveVerifiedRetiming_sound
  by mutation Obend.Hardware.Retiming.solveVerifiedRetiming? := solveVerifiedRetimingBrokenSkipCheck

/-- Broken `downstreamCapFf` on `SteinerTree` that ignores right-branch capacitance `downstreamCapFf right`. -/
def downstreamCapFfDropRight : SteinerTree → Nat
  | .sink _ loadCapFf => loadCapFf
  | .branch _ _ segCapFf left _right => segCapFf + downstreamCapFfDropRight left

#tooth Obend.Hardware.PlaceRoute.steiner_fanout_buffer_insertion_reduces_elmore_delay
  by mutation Obend.Hardware.PlaceRoute.downstreamCapFf := downstreamCapFfDropRight

/-- Broken `checkBoxSpacing2D` that accepts any pair of boxes without checking coordinate separation. -/
def checkBoxSpacing2DAcceptAll (_minSpacingNm : Nat) (b1 b2 : LayoutBox2D) : Bool :=
  b1.wf && b2.wf

#tooth Obend.Hardware.DRC.boxSpacing2D_disjoint
  by mutation Obend.Hardware.DRC.checkBoxSpacing2D := checkBoxSpacing2DAcceptAll


#print axioms Obend.Hardware.Retiming.solveVerifiedRetiming_sound
#print axioms Obend.Hardware.Retiming.applyRetimingCertToGraph_preserves_cycle_weight
#print axioms Obend.Hardware.PlaceRoute.downstreamCapFf_monotone_load
#print axioms Obend.Hardware.PlaceRoute.maxSteinerElmoreDelay_nonneg
#print axioms Obend.Hardware.PlaceRoute.steiner_fanout_buffer_insertion_reduces_elmore_delay
#print axioms Obend.Hardware.DRC.boxSpacing2D_disjoint
#print axioms Obend.Hardware.DRC.viaEnclosure2D_contained
#print axioms Obend.Hardware.WaferSpace.checkEndToEndSiliconSignoff_sound
#print axioms Obend.Hardware.WaferSpace.goldenEndToEndSiliconPipeline_verified

end Obend.Tests.Metasystem.PhysicalSiliconSpineTest
end
