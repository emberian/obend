module

public import Obend.Tactic.Tooth
public import Obend.Hardware.Silicon
public import Obend.Hardware.Synth
public import Obend.Hardware.Retiming
public import Obend.Hardware.PlaceRoute
public import Obend.Hardware.DRC
public import Obend.Hardware.TapeoutPipeline
import all Obend.Hardware.Silicon
import all Obend.Hardware.Synth
import all Obend.Hardware.Retiming
import all Obend.Hardware.PlaceRoute
import all Obend.Hardware.DRC
import all Obend.Hardware.TapeoutPipeline

/-!
# Metasystem Test Suite — End-to-End Silicon Physical Implementation Spine (`WS-I`)

Comprehensive universal theorem checks, boundary & negative refutation poles, `#tooth`
kernel mutation-killing probes, and `#print axioms` verification (`0 sorryAx`) across:
1. `Obend.Hardware.Retiming` & `Obend.Hardware.Synth`:
   - `solveRetimingFuel`, `solveVerifiedRetiming?`, `solveVerifiedRetiming_sound`,
   - `checkAllCombPathsMeetDelay`, `checkAllCombPathsMeetDelay_sound` (order-independent DAG longest path),
   - `applyRetimingCertToGraph`, `applyRetimingCertToGraph_preserves_cycle_weight`,
   - `synthesizeModuleToBels`, `synthesizeModuleToBels_trace_equiv` (including 6-stage barrel-shift BELs!).
2. `Obend.Hardware.PlaceRoute`:
   - `checkPlacementInjective_sound`, `checkRoutingDisjoint_sound`, `checkPnrCertificate_sound` (netlist-bound),
   - `SteinerTree`, `downstreamCapFf`, `maxSteinerElmoreDelayFsOhm`,
   - `downstreamCapFf_monotone_load`, `maxSteinerElmoreDelay_nonneg`,
   - `steiner_fanout_buffer_insertion_reduces_elmore_delay`.
3. `Obend.Hardware.DRC`:
   - `LayoutBox2D`, `checkBoxSpacing2D`, `checkViaEnclosure2D`,
   - `boxSpacing2D_disjoint`, `viaEnclosure2D_contained`.
4. `Obend.Hardware.Silicon` & `Obend.Hardware.TapeoutPipeline`:
   - `checkAllChannelHops`, `checkAllChannelHops_sound`,
   - `compileCompositionToSiliconTapeout`, `compileCompositionToSiliconTapeout_sound`,
   - `golden_obend_module_silicon_tapeout_verified` & stage-by-stage negative refusal poles.
-/

@[expose] public section
namespace Obend.Tests.Metasystem.PhysicalSiliconSpineTest

open Obend.Hardware.Process
open Obend.Hardware.HDL
open Obend.Hardware.Silicon
open Obend.Hardware.Synth
open Obend.Hardware.Retiming
open Obend.Hardware.PlaceRoute
open Obend.Hardware.DRC
open Obend.Hardware.TapeoutPipeline
set_option autoImplicit false

/-! ## 1. Constructive Leiserson–Saxe Retiming, Order-Independent DAG Longest Path & Cycle Invariance -/

/-- 1.1 Universal soundness of `solveVerifiedRetiming?` and `checkAllCombPathsMeetDelay_sound`. -/
theorem test_solveVerifiedRetiming_sound
    (fuel : Nat) (g : SyncGraph) (maxDelay : Nat) (cert : RetimingCert)
    (hSome : solveVerifiedRetiming? fuel g maxDelay = some cert) :
    ∀ e ∈ g.edges, 0 ≤ retimedEdgeWeight (lookupLag cert) e :=
  (solveVerifiedRetiming_sound fuel g maxDelay cert hSome).1

/-- 1.2 Universal cycle register weight preservation under `applyRetimingCertToGraph`. -/
theorem test_applyRetimingCertToGraph_preserves_cycle_weight
    (g : SyncGraph) (cert : RetimingCert) (startVtx : Nat)
    (hCycle : checkContiguousSyncEdges startVtx startVtx g.edges = true)
    (hNonneg : checkAllEdgesNonneg (lookupLag cert) g.edges = true) :
    origPathWeight (edgesToPathHops (applyRetimingCertToGraph g cert).edges) =
      origPathWeight (edgesToPathHops g.edges) :=
  applyRetimingCertToGraph_preserves_cycle_weight g cert startVtx hCycle hNonneg

def testFeedbackCycleGraph : SyncGraph where
  name           := "feedback_3cycle"
  primaryInputs  := []
  primaryOutputs := []
  edges          :=
    [ { src := 0, dst := 1, origRegs := 0, combDelayPs := 1900 }
    , { src := 1, dst := 2, origRegs := 2, combDelayPs := 800  }
    , { src := 2, dst := 0, origRegs := 1, combDelayPs := 700  } ]

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

/-- Reverse-topological multi-hop combinational chain (`1 -> 2` listed BEFORE `0 -> 1`):
verifies `checkAllCombPathsMeetDelay` catches `1100 + 1100 = 2200 > 1800 ps` independent of edge order! -/
def reverseOrderSlowCombEdges : List SyncEdge :=
  [ { src := 1, dst := 2, origRegs := 0, combDelayPs := 1100 }
  , { src := 0, dst := 1, origRegs := 0, combDelayPs := 1100 } ]

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
    checkAllCombPathsMeetDelay identityRetimingCert 1800 reverseOrderSlowCombEdges = false ∧
    solveVerifiedRetiming? 2 testUnretimeableGraph 1800 = none ∧
    solveVerifiedRetiming? 2 directIoSlowGraph 1800 = none := by
  decide +kernel

/-! ## 2. Netlist-Bound `PlaceRoute` List-Wide Soundness & Multi-Sink `SteinerTree` Elmore RC Delay -/

/-- 2.1 Universal list-wide placement injectivity (`checkPlacementInjective_sound`) and routing
disjointness (`checkRoutingDisjoint_sound`) for all `i ≠ j`. -/
theorem test_pnr_list_wide_soundness
    (net : BelNetlist) (corner : ProcessCorner) (periodPs : Nat) (cert : PnrCertificate)
    (hOk : checkPnrCertificate net corner periodPs cert = true) :
    cert.designName = net.moduleName ∧
    cert.placedCells.length = net.cells.length ∧
    (∀ (i j : Nat) (hi : i < cert.placedCells.length) (hj : j < cert.placedCells.length),
      i ≠ j → cellLocation cert.placedCells[i] ≠ cellLocation cert.placedCells[j]) ∧
    (∀ (i j : Nat) (hi : i < cert.routedNets.length) (hj : j < cert.routedNets.length),
      i ≠ j → ∀ u ∈ netWires cert.routedNets[i], u ∉ netWires cert.routedNets[j]) :=
  let h := checkPnrCertificate_sound net corner periodPs cert hOk
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

/-- 2.2 Universal load monotonicity and non-negativity of `downstreamCapFf` and `maxSteinerElmoreDelayFsOhm`. -/
theorem test_steiner_elmore_monotone_and_nonneg
    (deltaCapFf : Nat) (t : SteinerTree) :
    downstreamCapFf t ≤ downstreamCapFf (inflateSinkLoads deltaCapFf t) ∧
    maxSteinerElmoreDelayFsOhm t ≤ maxSteinerElmoreDelayFsOhm (inflateSinkLoads deltaCapFf t) ∧
    0 ≤ maxSteinerElmoreDelayFsOhm t :=
  ⟨(downstreamCapFf_monotone_load deltaCapFf t).1,
   (downstreamCapFf_monotone_load deltaCapFf t).2,
   (maxSteinerElmoreDelay_nonneg t).1⟩

example :
    downstreamCapFf (.sink 0 25) = 25 ∧
    maxSteinerElmoreDelayFsOhm (.sink 0 25) = 0 ∧
    downstreamCapFf unbufferedFanoutTree = 1050 ∧
    downstreamCapFf bufferedFanoutTree = 175 ∧
    maxSteinerElmoreDelayFsOhm unbufferedFanoutTree = 3450000 ∧
    maxSteinerElmoreDelayFsOhm bufferedFanoutTree = 350000 ∧
    checkSteinerTimingClosure corner7nm_SS 2000 unbufferedFanoutTree = false ∧
    checkSteinerTimingClosure corner7nm_SS 2000 bufferedFanoutTree = true := by
  decide +kernel

/-! ## 3. 2D `LayoutBox2D` Manhattan DRC Soundness -/

theorem test_drc_2d_box_soundness
    (minSpacingNm minEncNm : Nat) (b1 b2 viaBox padBox : LayoutBox2D) (x y : Nat)
    (hSpace : checkBoxSpacing2D minSpacingNm b1 b2 = true)
    (hEnc   : checkViaEnclosure2D minEncNm viaBox padBox = true) :
    ¬ (b1.containsPoint x y ∧ b2.containsPoint x y) ∧
    (viaBox.containsPoint x y → padBox.containsPoint x y) :=
  ⟨boxSpacing2D_disjoint minSpacingNm b1 b2 x y hSpace,
   fun hIn => (viaEnclosure2D_contained minEncNm viaBox padBox x y hEnc hIn).1⟩

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

/-! ## 4. Barrel-Shift `Synth` Equivalence & Netlist-Bound `TapeoutPipeline` Negative Poles -/

/-- Concrete barrel-shift `RtlModule` testing `.shl`, `.lshr`, `.ashr` (including ≥ 64 saturating shifts!)
under `synthesizeModuleToBels` vs `evalModuleOutputs`. -/
def barrelShiftTestRtl : RtlModule where
  name       := "barrel_shift_test"
  inputNames := ["x", "sh"]
  wires      :=
    [ { wireIdx := 0, name := "w_shl",  expr := .alu .shl  (.inputPort 0) (.inputPort 1) }
    , { wireIdx := 1, name := "w_lshr", expr := .alu .lshr (.inputPort 0) (.inputPort 1) }
    , { wireIdx := 2, name := "w_ashr", expr := .alu .ashr (.inputPort 0) (.inputPort 1) } ]
  regs       := []
  outputs    :=
    [ { name := "out_shl",  expr := .wireRef 0 }
    , { name := "out_lshr", expr := .wireRef 1 }
    , { name := "out_ashr", expr := .wireRef 2 } ]

example :
    let nl := synthesizeModuleToBels barrelShiftTestRtl
    let inSmall : Nat → BitVec 64 := fun i => if i == 0 then 0x80000000000000F0#64 else 4#64
    let in63 : Nat → BitVec 64 := fun i => if i == 0 then 0x80000000000000F0#64 else 63#64
    checkRtlModule barrelShiftTestRtl = true ∧
    checkBelNetlistValid nl = true ∧
    evalBelNetlistOutputs nl inSmall (fun _ => 0#64) = evalModuleOutputs barrelShiftTestRtl inSmall (fun _ => 0#64) ∧
    evalBelNetlistOutputs nl in63 (fun _ => 0#64) = evalModuleOutputs barrelShiftTestRtl in63 (fun _ => 0#64) ∧
    evalBelNetlistOutputs nl in63 (fun _ => 0#64) =
      [ ("out_shl",  0#64)
      , ("out_lshr", 1#64)
      , ("out_ashr", 0xFFFFFFFFFFFFFFFF#64) ] := by
  have hWf : checkRtlModule barrelShiftTestRtl = true := by decide +kernel
  have hSmall := evalBelNetlistOutputs_synthesizeModuleToBels barrelShiftTestRtl
    (fun i => if i == 0 then 0x80000000000000F0#64 else 4#64) (fun _ => 0#64) hWf
  have h63 := evalBelNetlistOutputs_synthesizeModuleToBels barrelShiftTestRtl
    (fun i => if i == 0 then 0x80000000000000F0#64 else 63#64) (fun _ => 0#64) hWf
  have hRtl63 :
      evalModuleOutputs barrelShiftTestRtl
        (fun i => if i == 0 then 0x80000000000000F0#64 else 63#64) (fun _ => 0#64) =
      [ ("out_shl",  0#64)
      , ("out_lshr", 1#64)
      , ("out_ashr", 0xFFFFFFFFFFFFFFFF#64) ] := by decide +kernel
  exact ⟨hWf, (synthesizeModuleToBels_valid_and_ff_count barrelShiftTestRtl).1,
    hSmall, h63, h63.trans hRtl63⟩

/-- Stage-by-stage negative refusal poles across `compileCompositionToSiliconTapeout`:
1. `goldenCleanroomTcadComp` passes (`.isOk = true`),
2. Unretimeable graph (`testUnretimeableGraph`) is refused,
3. Colliding BEL PnR certificate (`collidingBelPnrCert`) is refused,
4. Netlist cell-count mismatch (`validAdderPnrCert` with 2 cells vs synthesized >2 BELs) is refused,
5. Overlapping 2D metal boxes are refused,
6. Overhanging 2D via is refused,
7. Overclocked 10 GHz (`clockPeriodPs = 100 ps`) envelope timing is refused. -/
example :
    (compileCompositionToSiliconTapeout goldenTapeoutConfig goldenCleanroomTcadComp [goldenTapeoutIsarCert]).isOk = true ∧
    (compileCompositionToSiliconTapeout { goldenTapeoutConfig with syncGraph := testUnretimeableGraph } goldenCleanroomTcadComp []).isOk = false ∧
    (compileCompositionToSiliconTapeout { goldenTapeoutConfig with pnrCert? := some collidingBelPnrCert } goldenCleanroomTcadComp []).isOk = false ∧
    (compileCompositionToSiliconTapeout { goldenTapeoutConfig with pnrCert? := some validAdderPnrCert } goldenCleanroomTcadComp []).isOk = false ∧
    (compileCompositionToSiliconTapeout
      { goldenTapeoutConfig with metalBoxB := { layerId := 1, xMinNm := 20, yMinNm := 0, xMaxNm := 120, yMaxNm := 100 } }
      goldenCleanroomTcadComp []).isOk = false ∧
    (compileCompositionToSiliconTapeout
      { goldenTapeoutConfig with viaBox := { layerId := 2, xMinNm := 2, yMinNm := 10, xMaxNm := 46, yMaxNm := 46 } }
      goldenCleanroomTcadComp []).isOk = false ∧
    (compileCompositionToSiliconTapeout { goldenTapeoutConfig with clockPeriodPs := 100 } goldenCleanroomTcadComp []).isOk = false := by
  decide +kernel

/-! ## 5. `#tooth` Kernel Mutation-Killing Probes & Axiom Audit -/

def solveVerifiedRetimingBrokenSkipCheck (_fuel : Nat) (_g : SyncGraph) (_maxCombDelayPs : Nat) : Option RetimingCert :=
  some negativeWeightBadCert

#tooth Obend.Hardware.Retiming.solveVerifiedRetiming_sound
  by mutation Obend.Hardware.Retiming.solveVerifiedRetiming? := solveVerifiedRetimingBrokenSkipCheck

def downstreamCapFfDropRight : SteinerTree → Nat
  | .sink _ loadCapFf => loadCapFf
  | .branch _ _ segCapFf left _right => segCapFf + downstreamCapFfDropRight left

#tooth Obend.Hardware.PlaceRoute.steiner_fanout_buffer_insertion_reduces_elmore_delay
  by mutation Obend.Hardware.PlaceRoute.downstreamCapFf := downstreamCapFfDropRight

def checkBoxSpacing2DAcceptAll (_minSpacingNm : Nat) (b1 b2 : LayoutBox2D) : Bool :=
  b1.wf && b2.wf

#tooth Obend.Hardware.DRC.boxSpacing2D_disjoint
  by mutation Obend.Hardware.DRC.checkBoxSpacing2D := checkBoxSpacing2DAcceptAll

#print axioms Obend.Hardware.Synth.synthesizeModuleToBels_trace_equiv
#print axioms Obend.Hardware.Retiming.solveVerifiedRetiming_sound
#print axioms Obend.Hardware.Retiming.checkAllCombPathsMeetDelay_sound
#print axioms Obend.Hardware.Retiming.applyRetimingCertToGraph_preserves_cycle_weight
#print axioms Obend.Hardware.PlaceRoute.checkPnrCertificate_sound
#print axioms Obend.Hardware.PlaceRoute.downstreamCapFf_monotone_load
#print axioms Obend.Hardware.PlaceRoute.maxSteinerElmoreDelay_nonneg
#print axioms Obend.Hardware.PlaceRoute.steiner_fanout_buffer_insertion_reduces_elmore_delay
#print axioms Obend.Hardware.DRC.boxSpacing2D_disjoint
#print axioms Obend.Hardware.DRC.viaEnclosure2D_contained
#print axioms Obend.Hardware.TapeoutPipeline.compileCompositionToSiliconTapeout_sound

end Obend.Tests.Metasystem.PhysicalSiliconSpineTest
end
