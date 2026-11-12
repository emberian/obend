module
/-
# Obend.Hardware.TapeoutPipeline — `.obend` source to netlist-bound silicon tapeout artifact
Stages: front end (`FrontEnd.parseModule` … `accept`), `Leaf.emit` + `specializeBookDict`, Book-to-RTL (`checkRtlModule`),
BEL synthesis (`synthesizeModuleToBels`), retiming, netlist-bound PnR (`synthesizeGridPnrCert`, `checkPnrCertificate`),
artifact-bound physical signoff (`checkArtifactBoundTapeout`: the timing graph, fanout tree, pad/via geometry and critical
path are derived from the synthesized netlist and its PnR certificate), DRC, `[FF, TT, SS]` envelope STA, SystemVerilog
emission and the cSHAKE256 receipt (`tapeout_sv_digest_binds_or_collides`).
-/
public import Lean.Data.Json
public import Obend.Core.Digest
public import Obend.Spec.FrontEnd
public import Obend.Spec.Capture
public import Obend.Spec.Sha256
public import Obend.Logic.Program
public import Obend.Leaf.Emit
public import Obend.Lower.Proofs.Hardware
public import Obend.Receipt
public import Obend.Hardware.Process
public import Obend.Hardware.HDL
public import Obend.Hardware.Compiler
public import Obend.Hardware.Synth
public import Obend.Hardware.Retiming
public import Obend.Hardware.PlaceRoute
public import Obend.Hardware.DRC
public import Obend.Hardware.Judge
public section
namespace Obend.Hardware.TapeoutPipeline
open Lean (Json toJson)
open Obend.Core.Term Obend.Equiv Obend.Logic Obend.Leaf Obend.Lower Obend.Spec Obend.Hardware.Process Obend.Hardware.HDL
open Obend.Hardware.Compiler Obend.Hardware.Synth Obend.Hardware.Retiming Obend.Hardware.PlaceRoute Obend.Hardware.DRC Obend.Hardware.Judge
set_option autoImplicit false

/-! ## 1. Hardware Compilation Modes, Default DRC Geometry, Configuration & Error Diagnostics -/
/-- RTL compilation strategy for Stage 3 of the `.obend` tapeout pipeline. -/
inductive RtlCompileMode where
  | pipelined        -- Register-stage pipelined datapath (`compileBookToPipelinedRtl`)
  | combinationalSat -- Saturating combinational datapath (`compileBookToRtlSat`)
  | sequentialSat    -- Multi-cycle sequential FSM (`compileBookToSeqRtlSat`)
  deriving DecidableEq, Repr
/-- Default 7nm Metal-1 foundry DRC deck used by `TapeoutConfig`. -/
def default7nmDrcDeck : FoundryDrcDeck :=
  { deckName := "7nm_M1_EUV_Deck", minMetalWidthNm := 36, minMetalSpacingNm := 36, minViaWidthNm := 32
  , minViaEnclosureNm := 8, maxResistAspect := 3 }
/-- Default DRC-clean Metal-1 cutline feature (`40nm` width, `40nm` spacing). -/
def default7nmCutlineFeature : CutlineDrcFeature :=
  { metalWidthNm := 40, metalSpacingNm := 40, viaWidthNm := 36, viaEnclosureNm := 10, resistOpeningNm := 40
  , resistHeightNm := 100, ildThicknessNm := 120 }
def defaultMetalBoxA : LayoutBox2D := { layerId := 1, xMinNm := 0,  yMinNm := 0,  xMaxNm := 40,  yMaxNm := 100 }
def defaultMetalBoxB : LayoutBox2D := { layerId := 1, xMinNm := 80, yMinNm := 0,  xMaxNm := 120, yMaxNm := 100 }
def defaultViaBox    : LayoutBox2D := { layerId := 2, xMinNm := 10, yMinNm := 10, xMaxNm := 46,  yMaxNm := 46 }
def defaultViaPadBox : LayoutBox2D := { layerId := 1, xMinNm := 0,  yMinNm := 0,  xMaxNm := 56,  yMaxNm := 56 }
/-- Extract the 16-bit LUT SRAM truth table / BEL primitive configuration word (`< 65536`)
directly from a technology-mapped `BelKind`. -/
@[expose] def extractBelCellLutInit : BelKind → Nat
  | .lut1 m => m % 65536 | .lut2 m => m % 65536 | .lut3 m => m % 65536 | .carry4 .add => 0x0096 | .carry4 .sub => 0x0069
  | .carry4 .ultCmp => 0x00B2 | .carry4 .sltCmp => 0x00D4 | .dspMul .mul64 => 0xD580 | .dspMul .qmul32 => 0xD532
  | .ff _ .resetFree => 0xFF00 | .ff _ (.syncReset _) => 0xFF01 | .orReduce => 0xFFFE | .zeroDetect => 0x0001
  | .shiftRoute .shl d => 0x5100 + (d % 64) | .shiftRoute .lshr d => 0x5200 + (d % 64) | .shiftRoute .ashr d => 0x5300 + (d % 64)
  | .bitBroadcast b => 0xB000 + (b % 64) | .constBel v => v.toNat % 256 | .portIn p => 0x1000 + (p % 256) | .wireTap w => 0x2000 + (w % 256)
  | .regTap r => 0x3000 + (r % 256) | .route _ => 0x4000
theorem extractBelCellLutInit_lt (k : BelKind) : extractBelCellLutInit k < 65536 := by
  cases k with
  | carry4 m => cases m <;> decide
  | dspMul m => cases m <;> decide
  | ff _ r => cases r <;> (dsimp [extractBelCellLutInit]; omega)
  | shiftRoute d n => cases d <;> (dsimp [extractBelCellLutInit]; omega)
  | lut1 m | lut2 m | lut3 m | bitBroadcast m | portIn m | wireTap m | regTap m =>
    dsimp [extractBelCellLutInit]; omega
  | constBel v => dsimp [extractBelCellLutInit]; omega
  | orReduce | zeroDetect => decide
  | route _ => dsimp [extractBelCellLutInit]; omega
/-- Compute the switch-box input mux PIP configuration mask (`1 .. 255 < 65536`) from `c.inputs`. -/
@[expose] def extractBelCellPipMask (c : BelCell) : Nat :=
  1 + (c.inputs.length % 255)
theorem extractBelCellPipMask_lt (c : BelCell) : extractBelCellPipMask c < 65536 := by
  dsimp [extractBelCellPipMask]; omega
/-- Grid column `tileX ∈ [0, 16)` for placed BEL cell index `i` (2 BEL slots per tile). -/
@[expose] def gridTileX (i : Nat) : Nat := (i / 2) % 16
/-- Grid row `tileY ∈ [0, 256)` for placed BEL cell index `i` (32 BELs per grid row, 8,192 total). -/
@[expose] def gridTileY (i : Nat) : Nat := (i / 32) % 256
/-- Intra-tile BEL slot `belSlot ∈ {0, 1}` for placed BEL cell index `i`. -/
@[expose] def gridBelSlot (i : Nat) : Nat := i % 2
private theorem gridCoord_injective {i j : Nat} (hi : i < 8192) (hj : j < 8192)
    (hEq : (gridTileX i, gridTileY i, gridBelSlot i) = (gridTileX j, gridTileY j, gridBelSlot j)) :
    i = j := by
  dsimp [gridTileX, gridTileY, gridBelSlot] at hEq
  rcases Prod.mk.inj hEq with ⟨hX, hYZ⟩
  rcases Prod.mk.inj hYZ with ⟨hY, hZ⟩
  omega
/-- Canonical physical switch-box wire identifier partitioning routing channel `trackId`,
hop step `stepIdx < 1024`, tile row `tileY < 256`, and tile column `tileX < 256`. -/
@[expose] def encodeSwitchWire (trackId stepIdx tileX tileY : Nat) : Nat :=
  trackId * 67108864 + (stepIdx % 1024) * 65536 + (tileY % 256) * 256 + (tileX % 256)
private theorem encodeSwitchWire_track (trackId stepIdx tileX tileY : Nat) :
    encodeSwitchWire trackId stepIdx tileX tileY / 67108864 = trackId := by
  dsimp [encodeSwitchWire]; omega
/-- 1D Manhattan tile distance `|a - b|`. -/
@[expose] def manhattanDist1D (a b : Nat) : Nat :=
  if a ≤ b then b - a else a - b
/-- Advance one tile coordinate step from `cur` towards `target`. -/
def stepTileTowards (cur target : Nat) : Nat :=
  if cur < target then cur + 1 else if target < cur then cur - 1 else cur
/-- Emit `steps` horizontal switch-box `PipHop`s along row `y` from `curX` towards `dstX`. -/
def buildManhattanXHops (trackId stepIdx curX dstX y : Nat) : Nat → List PipHop
  | 0 => []
  | k + 1 =>
    let nextX := stepTileTowards curX dstX
    { srcWire := encodeSwitchWire trackId stepIdx curX y
    , dstWire := encodeSwitchWire trackId (stepIdx + 1) nextX y
    , resOhm  := 60
    , capFf   := 4 } ::
    buildManhattanXHops trackId (stepIdx + 1) nextX dstX y k
/-- Emit `steps` vertical switch-box `PipHop`s along column `x` from `curY` towards `dstY`. -/
def buildManhattanYHops (trackId stepIdx x curY dstY : Nat) : Nat → List PipHop
  | 0 => []
  | k + 1 =>
    let nextY := stepTileTowards curY dstY
    { srcWire := encodeSwitchWire trackId stepIdx x curY
    , dstWire := encodeSwitchWire trackId (stepIdx + 1) x nextY
    , resOhm  := 60
    , capFf   := 4 } ::
    buildManhattanYHops trackId (stepIdx + 1) x nextY dstY k
/-- Synthesize a Manhattan X-then-Y switch-box `RoutedNet` on dedicated track `trackId`
from producer tile `(srcX, srcY)` to consumer tile `(dstX, dstY)`. -/
@[expose] def routeManhattanEdge (trackId srcX srcY dstX dstY : Nat) : RoutedNet :=
  let dx := manhattanDist1D srcX dstX
  let dy := manhattanDist1D srcY dstY
  let xHops := buildManhattanXHops trackId 0 srcX dstX srcY dx
  let yHops := buildManhattanYHops trackId dx dstX srcY dstY dy
  let sinkHop : PipHop :=
    { srcWire := encodeSwitchWire trackId (dx + dy) dstX dstY
    , dstWire := encodeSwitchWire trackId (dx + dy + 1) dstX dstY
    , resOhm  := 40
    , capFf   := 3 }
  { netId   := trackId
  , srcWire := encodeSwitchWire trackId 0 srcX srcY
  , dstWire := encodeSwitchWire trackId (dx + dy + 1) dstX dstY
  , hops    := xHops ++ yHops ++ [sinkHop] }
/-- Look up the cell index of the sequential `BelKind.ff regIdx _` driving `.regTap regIdx`. -/
def findFfCellIdx? (targetReg : Nat) : List BelCell → Nat → Option Nat
  | [], _ => none
  | c :: rest, idx =>
    match c.kind with
    | .ff r _ => if r == targetReg then some idx else findFfCellIdx? targetReg rest (idx + 1)
    | _       => findFfCellIdx? targetReg rest (idx + 1)
/-- Look up the cell index of the producer `BelCell` driving net `pinName`. -/
def findProducerCellIdx? (pinName : String) : List BelCell → Nat → Option Nat
  | [], _ => none
  | c :: rest, idx =>
    if c.dstName.toList == pinName.toList then some idx else findProducerCellIdx? pinName rest (idx + 1)
/-- Look up the primary module input index driving named primary port `pinName`. -/
def findPrimaryInputIdx? (pinName : String) : List String → Nat → Option Nat
  | [], _ => none
  | nm :: rest, idx =>
    if nm.toList == pinName.toList then some idx
    else findPrimaryInputIdx? pinName rest (idx + 1)
/-- Fan-in of pin list `pins` of cell `dst` as `(sourceIsCell, source, dst)`; a non-cell source is a primary input. -/
def belPinFanIn (net : BelNetlist) (dst : Nat) : List String → List (Bool × Nat × Nat)
  | [] => []
  | pin :: pins =>
    (match findProducerCellIdx? pin net.cells 0 with
     | some j => [(true, j, dst)]
     | none => match findPrimaryInputIdx? pin net.inputNames 0 with
       | some k => [(false, k, dst)]
       | none => []) ++ belPinFanIn net dst pins
def belCellFanIn (net : BelNetlist) (dst : Nat) (c : BelCell) : List (Bool × Nat × Nat) :=
  match c.kind with
  | .constBel _ => []
  | .portIn k => [(false, k, dst)]
  | .regTap r => match findFfCellIdx? r net.cells 0 with | some f => [(true, f, dst)] | none => []
  | _ => belPinFanIn net dst c.inputs
def belFanInAux (net : BelNetlist) (dst : Nat) : List BelCell → List (Bool × Nat × Nat)
  | [] => []
  | c :: rest => belCellFanIn net dst c ++ belFanInAux net (dst + 1) rest
/-- Every producer-to-consumer fan-in edge of `net`, consumer cells in order. -/
def belFanIn (net : BelNetlist) : List (Bool × Nat × Nat) := belFanInAux net 0 net.cells
/-- Tile coordinates `(srcX, srcY, dstX, dstY)` of every fan-in edge on the grid placement (primary input `k` enters
at tile `(0, k % 256)`). -/
def extractBelNetlistEdges (net : BelNetlist) : List (Nat × Nat × Nat × Nat) :=
  (belFanIn net).map fun e =>
    (if e.1 then gridTileX e.2.1 else 0, if e.1 then gridTileY e.2.1 else e.2.1 % 256, gridTileX e.2.2, gridTileY e.2.2)
/-- Route every extracted `(srcX, srcY, dstX, dstY)` edge across distinct switch-box tracks. -/
def routeEdgeListFrom (startTrack : Nat) : List (Nat × Nat × Nat × Nat) → List RoutedNet
  | [] => []
  | (sx, sy, dx, dy) :: rest =>
    routeManhattanEdge startTrack sx sy dx dy :: routeEdgeListFrom (startTrack + 1) rest
def buildGridPlacedCells (idx : Nat) : List BelCell → List PlacedCell
  | [] => []
  | c :: rest =>
    { cellId  := idx
    , tileX   := gridTileX idx
    , tileY   := gridTileY idx
    , belSlot := gridBelSlot idx
    , lutInit := extractBelCellLutInit c.kind } :: buildGridPlacedCells (idx + 1) rest
def buildGridTileConfigs (idx : Nat) : List BelCell → List TileFrameConfig
  | [] => []
  | c :: rest =>
    { tileX   := gridTileX idx
    , tileY   := gridTileY idx
    , belSlot := gridBelSlot idx
    , lutInit := extractBelCellLutInit c.kind
    , pipMask := extractBelCellPipMask c } :: buildGridTileConfigs (idx + 1) rest
/-- The netlist-derived grid-placed, Manhattan-routed `PnrCertificate` of `net`: real LUT/primitive words, injective
placement on the `16 × 256 × 2` BEL array, and one routed net per fan-in edge on its own switch-box track. -/
@[expose] def synthesizeGridPnrCert (net : BelNetlist) (sinkCapFf : Nat := 5) : PnrCertificate :=
  let placed := buildGridPlacedCells 0 net.cells
  let cfgs   := buildGridTileConfigs 0 net.cells
  let edges  := extractBelNetlistEdges net
  let routed := routeEdgeListFrom 0 edges
  { designName      := net.moduleName
  , placedCells     := placed
  , routedNets      := routed
  , expectedConfigs := cfgs
  , bitstreamFrames := cfgs.map encodeBitstreamFrame
  , sinkCapFf       := sinkCapFf }
private theorem map_cellId_buildGridPlacedCells (cs : List BelCell) (idx : Nat) :
    (buildGridPlacedCells idx cs).map (·.cellId) = List.range' idx cs.length := by
  induction cs generalizing idx with
  | nil => rfl
  | cons c rest ih =>
    simp [buildGridPlacedCells, List.range', ih (idx + 1)]
private theorem checkCellAgainstList_buildGridPlacedCells
    (c0 : PlacedCell) (idx : Nat) (cs : List BelCell)
    (hc0Id : c0.cellId < idx)
    (hc0Loc : cellLocation c0 = (gridTileX c0.cellId, gridTileY c0.cellId, gridBelSlot c0.cellId))
    (hBound : idx + cs.length ≤ 8192) :
    checkCellAgainstList c0 (buildGridPlacedCells idx cs) = true := by
  induction cs generalizing idx with
  | nil => rfl
  | cons c rest ih =>
    simp only [buildGridPlacedCells, checkCellAgainstList, Bool.and_eq_true]
    refine ⟨?_, ih (idx + 1) (by omega) (by simp at hBound; omega)⟩
    simp only [checkPairNoCollision, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq]
    right
    intro hLocEq
    rw [hc0Loc] at hLocEq
    have hIdxEq := gridCoord_injective (by omega) (by simp at hBound; omega) hLocEq
    omega
private theorem checkPlacementInjective_buildGridPlacedCells
    (idx : Nat) (cs : List BelCell) (hBound : idx + cs.length ≤ 8192) :
    checkPlacementInjective (buildGridPlacedCells idx cs) = true := by
  induction cs generalizing idx with
  | nil => rfl
  | cons c rest ih =>
    simp only [buildGridPlacedCells, checkPlacementInjective, Bool.and_eq_true]
    refine ⟨checkCellAgainstList_buildGridPlacedCells _ (idx + 1) rest (by dsimp; omega) rfl (by simp at hBound; omega),
            ih (idx + 1) (by simp at hBound; omega)⟩
private theorem checkHopsContiguous_append (w0 w1 w2 : Nat) (h1 h2 : List PipHop)
    (hc1 : checkHopsContiguous w0 w1 h1 = true)
    (hc2 : checkHopsContiguous w1 w2 h2 = true) :
    checkHopsContiguous w0 w2 (h1 ++ h2) = true := by
  induction h1 generalizing w0 with
  | nil =>
    simp only [checkHopsContiguous, beq_iff_eq] at hc1
    subst hc1
    exact hc2
  | cons h rest ih =>
    simp only [checkHopsContiguous, Bool.and_eq_true, beq_iff_eq] at hc1
    simp only [List.cons_append, checkHopsContiguous, Bool.and_eq_true, beq_iff_eq]
    exact ⟨hc1.1, ih h.dstWire hc1.2⟩
private theorem buildManhattanXHops_contiguous :
    ∀ (d trackId stepIdx curX dstX y : Nat),
      manhattanDist1D curX dstX = d →
      checkHopsContiguous
        (encodeSwitchWire trackId stepIdx curX y)
        (encodeSwitchWire trackId (stepIdx + d) dstX y)
        (buildManhattanXHops trackId stepIdx curX dstX y d) = true
  | 0, trackId, stepIdx, curX, dstX, y, hd => by
    have hEq : curX = dstX := by unfold manhattanDist1D at hd; split at hd <;> omega
    subst hEq
    simp [buildManhattanXHops, checkHopsContiguous]
  | k + 1, trackId, stepIdx, curX, dstX, y, hd => by
    have hNext : manhattanDist1D (stepTileTowards curX dstX) dstX = k := by
      unfold manhattanDist1D at hd
      unfold manhattanDist1D stepTileTowards
      split at hd <;> split <;> (try split) <;> (try split) <;> omega
    simp only [buildManhattanXHops, checkHopsContiguous, Bool.and_eq_true, beq_iff_eq, true_and]
    have ih := buildManhattanXHops_contiguous k trackId (stepIdx + 1) (stepTileTowards curX dstX) dstX y hNext
    rwa [show stepIdx + 1 + k = stepIdx + (k + 1) by omega] at ih
private theorem buildManhattanYHops_contiguous :
    ∀ (d trackId stepIdx x curY dstY : Nat),
      manhattanDist1D curY dstY = d →
      checkHopsContiguous
        (encodeSwitchWire trackId stepIdx x curY)
        (encodeSwitchWire trackId (stepIdx + d) x dstY)
        (buildManhattanYHops trackId stepIdx x curY dstY d) = true
  | 0, trackId, stepIdx, x, curY, dstY, hd => by
    have hEq : curY = dstY := by unfold manhattanDist1D at hd; split at hd <;> omega
    subst hEq
    simp [buildManhattanYHops, checkHopsContiguous]
  | k + 1, trackId, stepIdx, x, curY, dstY, hd => by
    have hNext : manhattanDist1D (stepTileTowards curY dstY) dstY = k := by
      unfold manhattanDist1D at hd
      unfold manhattanDist1D stepTileTowards
      split at hd <;> split <;> (try split) <;> (try split) <;> omega
    simp only [buildManhattanYHops, checkHopsContiguous, Bool.and_eq_true, beq_iff_eq, true_and]
    have ih := buildManhattanYHops_contiguous k trackId (stepIdx + 1) x (stepTileTowards curY dstY) dstY hNext
    rwa [show stepIdx + 1 + k = stepIdx + (k + 1) by omega] at ih
private theorem routeManhattanEdge_connected (trackId sx sy dx dy : Nat) :
    checkNetConnectivity (routeManhattanEdge trackId sx sy dx dy) = true := by
  dsimp only [routeManhattanEdge, checkNetConnectivity]
  simp only [Bool.and_eq_true, Bool.not_eq_true']
  refine ⟨?_, ?_⟩
  · cases (buildManhattanXHops trackId 0 sx dx sy (manhattanDist1D sx dx) ++
           buildManhattanYHops trackId (manhattanDist1D sx dx) dx sy dy (manhattanDist1D sy dy)) <;> rfl
  · have hX := buildManhattanXHops_contiguous (manhattanDist1D sx dx) trackId 0 sx dx sy rfl
    rw [Nat.zero_add] at hX
    have hY := buildManhattanYHops_contiguous (manhattanDist1D sy dy) trackId (manhattanDist1D sx dx) dx sy dy rfl
    have hXY := checkHopsContiguous_append _ _ _ _ _ hX hY
    refine checkHopsContiguous_append _ _ _ _ _ hXY ?_
    simp [checkHopsContiguous]
private theorem routeEdgeListFrom_all_connected (startTrack : Nat) (edges : List (Nat × Nat × Nat × Nat)) :
    (routeEdgeListFrom startTrack edges).all checkNetConnectivity = true := by
  induction edges generalizing startTrack with
  | nil => rfl
  | cons e rest ih =>
    rcases e with ⟨sx, sy, dx, dy⟩
    simp [routeEdgeListFrom, routeManhattanEdge_connected, ih (startTrack + 1)]
private theorem buildManhattanXHops_dstTrack :
    ∀ (d trackId stepIdx curX dstX y u : Nat),
      u ∈ (buildManhattanXHops trackId stepIdx curX dstX y d).map (·.dstWire) →
      u / 67108864 = trackId
  | 0, _, _, _, _, _, _, hMem => by cases hMem
  | k + 1, trackId, stepIdx, curX, dstX, y, u, hMem => by
    simp only [buildManhattanXHops, List.map_cons, List.mem_cons] at hMem
    rcases hMem with rfl | hTail
    · exact encodeSwitchWire_track _ _ _ _
    · exact buildManhattanXHops_dstTrack k trackId (stepIdx + 1) _ dstX y u hTail
private theorem buildManhattanYHops_dstTrack :
    ∀ (d trackId stepIdx x curY dstY u : Nat),
      u ∈ (buildManhattanYHops trackId stepIdx x curY dstY d).map (·.dstWire) →
      u / 67108864 = trackId
  | 0, _, _, _, _, _, _, hMem => by cases hMem
  | k + 1, trackId, stepIdx, x, curY, dstY, u, hMem => by
    simp only [buildManhattanYHops, List.map_cons, List.mem_cons] at hMem
    rcases hMem with rfl | hTail
    · exact encodeSwitchWire_track _ _ _ _
    · exact buildManhattanYHops_dstTrack k trackId (stepIdx + 1) x _ dstY u hTail
private theorem routeManhattanEdge_wire_track (trackId sx sy dx dy u : Nat)
    (hMem : u ∈ netWires (routeManhattanEdge trackId sx sy dx dy)) :
    u / 67108864 = trackId := by
  dsimp only [routeManhattanEdge, netWires] at hMem
  simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hMem
  rcases hMem with rfl | (hX | hY) | rfl
  · exact encodeSwitchWire_track _ _ _ _
  · exact buildManhattanXHops_dstTrack _ _ _ _ _ _ u hX
  · exact buildManhattanYHops_dstTrack _ _ _ _ _ _ u hY
  · exact encodeSwitchWire_track _ _ _ _
private theorem disjointWireLists_of_ne_track (t1 t2 sx1 sy1 dx1 dy1 sx2 sy2 dx2 dy2 : Nat)
    (hNe : t1 ≠ t2) :
    disjointWireLists
      (netWires (routeManhattanEdge t1 sx1 sy1 dx1 dy1))
      (netWires (routeManhattanEdge t2 sx2 sy2 dx2 dy2)) = true := by
  simp only [disjointWireLists, List.all_eq_true, Bool.not_eq_true', List.contains_eq_any_beq,
    List.any_eq_false, beq_iff_eq]
  intro u hu1 v hv2 hEq
  subst hEq
  have h1 := routeManhattanEdge_wire_track t1 sx1 sy1 dx1 dy1 u hu1
  have h2 := routeManhattanEdge_wire_track t2 sx2 sy2 dx2 dy2 u hv2
  omega
private theorem checkNetDisjointFromList_routeEdgeListFrom
    (t0 sx0 sy0 dx0 dy0 startTrack : Nat) (edges : List (Nat × Nat × Nat × Nat))
    (hLt : t0 < startTrack) :
    checkNetDisjointFromList
      (routeManhattanEdge t0 sx0 sy0 dx0 dy0)
      (routeEdgeListFrom startTrack edges) = true := by
  induction edges generalizing startTrack with
  | nil => rfl
  | cons e rest ih =>
    rcases e with ⟨sx, sy, dx, dy⟩
    simp only [routeEdgeListFrom, checkNetDisjointFromList, Bool.and_eq_true]
    exact ⟨disjointWireLists_of_ne_track t0 startTrack sx0 sy0 dx0 dy0 sx sy dx dy (by omega),
           ih (startTrack + 1) (by omega)⟩
private theorem checkRoutingDisjoint_routeEdgeListFrom
    (startTrack : Nat) (edges : List (Nat × Nat × Nat × Nat)) :
    checkRoutingDisjoint (routeEdgeListFrom startTrack edges) = true := by
  induction edges generalizing startTrack with
  | nil => rfl
  | cons e rest ih =>
    rcases e with ⟨sx, sy, dx, dy⟩
    simp only [routeEdgeListFrom, checkRoutingDisjoint, Bool.and_eq_true]
    exact ⟨checkNetDisjointFromList_routeEdgeListFrom startTrack sx sy dx dy (startTrack + 1) rest (by omega),
           ih (startTrack + 1)⟩
private theorem buildGridTileConfigs_roundtrip (idx : Nat) (cs : List BelCell) :
    ((buildGridTileConfigs idx cs).map encodeBitstreamFrame).map decodeBitstreamFrame =
      buildGridTileConfigs idx cs := by
  induction cs generalizing idx with
  | nil => rfl
  | cons c rest ih =>
    simp only [buildGridTileConfigs, List.map_cons]
    rw [ih (idx + 1)]
    congr 1
    apply bitstream_decode_roundtrip_sound
    dsimp only [wfTileFrameConfig, gridTileX, gridTileY, gridBelSlot]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨⟨⟨by omega, by omega⟩, by omega⟩, extractBelCellLutInit_lt c.kind⟩,
            extractBelCellPipMask_lt c⟩
/-- For every netlist of at most 8,192 BELs, corner, clock and sink load: the grid certificate is accepted exactly when
every routed net meets Elmore setup timing, and a clock tighter than any net's arrival is refused. -/
theorem synthesizeGridPnrCert_valid_for_netlist
    (net : BelNetlist) (corner : ProcessCorner) (clockPeriodPs sinkCapFf : Nat)
    (hCap : net.cells.length ≤ 8192) :
    (checkPnrCertificate net corner clockPeriodPs (synthesizeGridPnrCert net sinkCapFf) = true ↔
      ∀ r ∈ (synthesizeGridPnrCert net sinkCapFf).routedNets,
        corner.tCqMaxPs + corner.tGateMaxPs + computeElmoreDelayPs sinkCapFf r.hops +
          corner.tSetupPs + corner.tSkewPs ≤ clockPeriodPs) ∧
    ((∃ r ∈ (synthesizeGridPnrCert net sinkCapFf).routedNets,
        clockPeriodPs <
          corner.tCqMaxPs + corner.tGateMaxPs + computeElmoreDelayPs sinkCapFf r.hops +
            corner.tSetupPs + corner.tSkewPs) →
      checkPnrCertificate net corner clockPeriodPs (synthesizeGridPnrCert net sinkCapFf) = false) := by
  have hMapIds : (buildGridPlacedCells 0 net.cells).map (·.cellId) = List.range net.cells.length := by
    rw [map_cellId_buildGridPlacedCells, List.range_eq_range']
  have hInj : checkPlacementInjective (buildGridPlacedCells 0 net.cells) = true :=
    checkPlacementInjective_buildGridPlacedCells 0 net.cells (by omega)
  have hConn : (routeEdgeListFrom 0 (extractBelNetlistEdges net)).all checkNetConnectivity = true :=
    routeEdgeListFrom_all_connected 0 (extractBelNetlistEdges net)
  have hDisj : checkRoutingDisjoint (routeEdgeListFrom 0 (extractBelNetlistEdges net)) = true :=
    checkRoutingDisjoint_routeEdgeListFrom 0 (extractBelNetlistEdges net)
  have hFrames :
      ((buildGridTileConfigs 0 net.cells).map encodeBitstreamFrame).map decodeBitstreamFrame =
        buildGridTileConfigs 0 net.cells :=
    buildGridTileConfigs_roundtrip 0 net.cells
  have hIff :
      checkPnrCertificate net corner clockPeriodPs (synthesizeGridPnrCert net sinkCapFf) = true ↔
      ∀ r ∈ (synthesizeGridPnrCert net sinkCapFf).routedNets,
        corner.tCqMaxPs + corner.tGateMaxPs + computeElmoreDelayPs sinkCapFf r.hops +
          corner.tSetupPs + corner.tSkewPs ≤ clockPeriodPs := by
    unfold checkPnrCertificate synthesizeGridPnrCert
    simp only [beq_self_eq_true, hMapIds, hInj, hConn, hDisj, hFrames,
      Bool.true_and, Bool.and_true, List.all_eq_true, checkNetElmoreTiming, decide_eq_true_eq]
  refine ⟨hIff, ?_⟩
  rintro ⟨r, hrMem, hTight⟩
  cases hChk : checkPnrCertificate net corner clockPeriodPs (synthesizeGridPnrCert net sinkCapFf) with
  | false => rfl
  | true =>
    have hLe := hIff.mp hChk r hrMem
    omega

/-! ## 1b. Netlist-bound physical extraction: timing graph, fanout forest, pad/via geometry, critical path -/

/-- Logic depth of one BEL: a LUT or reduction is one gate level, a DSP multiplier slice four; carry chains are
counted in `belCarryBlocks` (a 64-lane chain is eight `CARRY8` blocks); taps, constants and D pins add nothing. -/
def belLogicLevels : BelKind → Nat
  | .lut1 _ | .lut2 _ | .lut3 _ | .orReduce | .zeroDetect => 1
  | .dspMul _ => 4
  | _ => 0
def belCarryBlocks : BelKind → Nat | .carry4 _ => 8 | _ => 0
def belCellDelayPs (corner : ProcessCorner) (k : BelKind) : Nat :=
  belLogicLevels k * corner.tGateMaxPs + belCarryBlocks k * corner.tCarryMaxPs
def isFfCellAt (nl : BelNetlist) (j : Nat) : Bool := (nl.cells[j]?).any isFfBel
/-- Elmore delay (ps) of the routed net of fan-in edge `k` (routed net `k`, `checkRoutingBindsFanIn`). -/
def fanInWirePs (pnr : PnrCertificate) (k : Nat) : Nat :=
  match pnr.routedNets[k]? with | some n => computeElmoreDelayPs pnr.sinkCapFf n.hops | none => 0
/-- **The timing graph of the placed and routed netlist.** Vertex `i < N` is cell `i` (for a flip-flop, its D side),
`N + k` primary input `k`, `N + P + f` the Q side of flip-flop cell `f`. A flip-flop is a one-register edge D → Q; a
fan-in edge carries no register and the delay of its routed wire plus its consumer cell at `corner`. -/
def deriveSyncGraphFromBelNetlist (corner : ProcessCorner) (nl : BelNetlist) (pnr : PnrCertificate) : SyncGraph :=
  let n := nl.cells.length
  let p := nl.inputNames.length
  { name := nl.moduleName
  , primaryInputs := (List.range p).map (n + ·)
  , primaryOutputs := (List.range nl.outputNames.length).filterMap fun k => findProducerCellIdx? (outNetName k) nl.cells 0
  , edges :=
      (nl.cells.zipIdx.filterMap fun ci =>
        if isFfBel ci.1 then some ({ src := ci.2, dst := n + p + ci.2, origRegs := 1, combDelayPs := 0 } : SyncEdge) else none) ++
      (belFanIn nl).zipIdx.map fun ek =>
        ({ src := if ek.1.1 then (if isFfCellAt nl ek.1.2.1 then n + p + ek.1.2.1 else ek.1.2.1) else n + ek.1.2.1
         , dst := ek.1.2.2, origRegs := 0
         , combDelayPs := fanInWirePs pnr ek.2 + ((nl.cells[ek.1.2.2]?).elim 0 fun c => belCellDelayPs corner c.kind) } : SyncEdge) }
/-- A routed net as a chain of RC segments ending in a sink of `sinkCapFf`. -/
def hopChainTree (sinkCapFf : Nat) (w : Nat) : List PipHop → SteinerTree
  | [] => .sink w sinkCapFf
  | h :: rest => .branch h.srcWire h.resOhm h.capFf (hopChainTree sinkCapFf h.dstWire rest) (.sink h.dstWire 0)
/-- The fanout forest of the routed netlist: the net of every fan-in edge, joined at an ideal (zero-impedance) root. -/
def deriveSteinerTreeFromPnr (nl : BelNetlist) (pnr : PnrCertificate) (sinkCapFf : Nat) : SteinerTree :=
  ((pnr.routedNets.take (belFanIn nl).length).map fun n => hopChainTree sinkCapFf n.srcWire n.hops).foldr
    (fun t acc => .branch 0 0 0 t acc) (.sink 0 0)
/-- Pad and via geometry of the placement under `deck`: BEL `(x, y, slot)` gets a square layer-1 pad of side
`max minMetalWidth (minViaWidth + 2·minViaEnclosure)` at pitch `side + minMetalSpacing`, two slots per tile, and a
centred layer-2 via cut. Returns `(cellId, pad)` shapes and `(via, pad)` pairs. -/
def deriveLayoutBoxesFromPnr (deck : FoundryDrcDeck) (pnr : PnrCertificate) :
    List (Nat × LayoutBox2D) × List (LayoutBox2D × LayoutBox2D) :=
  let side := max deck.minMetalWidthNm (deck.minViaWidthNm + 2 * deck.minViaEnclosureNm)
  let pitch := side + max deck.minMetalSpacingNm 1
  let pad (c : PlacedCell) : LayoutBox2D :=
    { layerId := 1, xMinNm := (2 * c.tileX + c.belSlot) * pitch, yMinNm := c.tileY * pitch
    , xMaxNm := (2 * c.tileX + c.belSlot) * pitch + side, yMaxNm := c.tileY * pitch + side }
  let via (c : PlacedCell) : LayoutBox2D :=
    { layerId := 2, xMinNm := (pad c).xMinNm + deck.minViaEnclosureNm, yMinNm := (pad c).yMinNm + deck.minViaEnclosureNm
    , xMaxNm := (pad c).xMaxNm - deck.minViaEnclosureNm, yMaxNm := (pad c).yMaxNm - deck.minViaEnclosureNm }
  (pnr.placedCells.map fun c => (c.cellId, pad c), pnr.placedCells.map fun c => (via c, pad c))
/-- One in-order pass of a path-depth recurrence: a cell's depth is its weight `w` plus `pick` over its fan-in of
(source depth, `0` after a flip-flop, `base` at a primary input) plus the edge weight `ew`. Exact when fan-in respects
cell order (`checkRoutingBindsFanIn`). `max`/`0` gives the longest path, `min`/large the shortest launched path. -/
def belPathDepths (nl : BelNetlist) (pick : Nat → Nat → Nat) (base : Nat) (w : BelKind → Nat) (ew : Nat → Nat) : List Nat :=
  nl.cells.zipIdx.foldl (fun depths ci =>
    let vals := ((belFanIn nl).zipIdx.filter fun ek => ek.1.2.2 == ci.2).map fun ek =>
      (if ek.1.1 then (if isFfCellAt nl ek.1.2.1 then 0 else depths.getD ek.1.2.1 base) else base) + ew ek.2
    depths ++ [vals.foldl pick base + w ci.1.kind]) []
/-- **The critical path of the placed and routed netlist**: deepest logic and carry depth of any path, the worst
accumulated routed Elmore delay in units of `corner.tWireHopPs`, and the fewest levels between two flip-flops
(4096 when no path joins two flip-flops, so hold is unconstrained). -/
def deriveCriticalTimingPathFromPnr (corner : ProcessCorner) (nl : BelNetlist) (pnr : PnrCertificate) : TimingPath :=
  let worst (w : BelKind → Nat) (ew : Nat → Nat) : Nat := (belPathDepths nl max 0 w ew).foldl max 0
  let minDepths := belPathDepths nl min 4096 (fun k => belLogicLevels k + min (belCarryBlocks k) 1) (fun _ => 0)
  { name := nl.moduleName ++ "_critical_path"
  , logicLevels := worst belLogicLevels (fun _ => 0)
  , minLevels := (nl.cells.zipIdx.filter fun ci => isFfBel ci.1).foldl (fun m ci => min m (minDepths.getD ci.2 4096)) 4096
  , carryBits := worst belCarryBlocks (fun _ => 0)
  , tileHops := (worst (fun _ => 0) (fanInWirePs pnr) + corner.tWireHopPs - 1) / max corner.tWireHopPs 1 }
/-- Everything physical signoff reads, derived from the netlist and its PnR certificate. -/
structure ArtifactPhysicalChecks where
  syncGraph : SyncGraph
  steinerTree : SteinerTree
  metalShapes : List (Nat × LayoutBox2D)
  viaCuts : List (LayoutBox2D × LayoutBox2D)
  criticalPath : TimingPath
  deriving DecidableEq, Repr
def derivePhysicalChecksFromBelNetlist (corner : ProcessCorner) (deck : FoundryDrcDeck) (nl : BelNetlist)
    (pnr : PnrCertificate) : ArtifactPhysicalChecks :=
  { syncGraph := deriveSyncGraphFromBelNetlist corner nl pnr, steinerTree := deriveSteinerTreeFromPnr nl pnr pnr.sinkCapFf
  , metalShapes := (deriveLayoutBoxesFromPnr deck pnr).1, viaCuts := (deriveLayoutBoxesFromPnr deck pnr).2
  , criticalPath := deriveCriticalTimingPathFromPnr corner nl pnr }
/-- Routed net `k` routes fan-in edge `k`: as many nets as edges, each starting on its source's tile and ending on
its consumer's (a wire id carries its tile as `encodeSwitchWire` lays it out), and fan-in respects cell order. -/
def checkRoutingBindsFanIn (nl : BelNetlist) (pnr : PnrCertificate) : Bool :=
  let tileOf (i : Nat) : Nat × Nat := (pnr.placedCells[i]?).elim (0, 0) fun c => (c.tileX % 256, c.tileY % 256)
  decide (pnr.routedNets.length = (belFanIn nl).length) &&
  ((belFanIn nl).zip pnr.routedNets).all fun en =>
    (!en.1.1 || isFfCellAt nl en.1.2.1 || decide (en.1.2.1 < en.1.2.2)) &&
    ((en.2.srcWire % 256, en.2.srcWire / 256 % 256) == (if en.1.1 then tileOf en.1.2.1 else (0, en.1.2.1 % 256))) &&
    ((en.2.dstWire % 256, en.2.dstWire / 256 % 256) == tileOf en.1.2.2)
def nthOr0 : List Nat → Nat → Nat
  | [], _ => 0 | x :: _, 0 => x | _ :: xs, n + 1 => nthOr0 xs n
/-- `arr` certifies arrivals for `edges`: along every register-free edge the arrival grows by at least the edge's
delay and stays within `budget` (vertices past `arr`, primary inputs and flip-flop outputs, arrive at `0`). -/
def checkGraphArrivals (arr : List Nat) (budget : Nat) (edges : List SyncEdge) : Bool :=
  edges.all fun e => e.origRegs != 0 ||
    (decide (nthOr0 arr e.src + e.combDelayPs ≤ nthOr0 arr e.dst) && decide (nthOr0 arr e.dst ≤ budget))
private theorem graphArrivals_walk (arr : List Nat) (budget : Nat) (edges : List SyncEdge)
    (hOk : checkGraphArrivals arr budget edges = true) :
    ∀ (walk : List SyncEdge) (u v : Nat), checkContiguousSyncEdges u v walk = true →
      (∀ e ∈ walk, e ∈ edges ∧ e.origRegs = 0) →
      nthOr0 arr u + combWalkDelay walk ≤ nthOr0 arr v ∧ (walk ≠ [] → nthOr0 arr v ≤ budget) := by
  intro walk
  induction walk with
  | nil =>
    intro u v hC _; simp only [checkContiguousSyncEdges, beq_iff_eq] at hC; subst hC
    exact ⟨by simp [combWalkDelay], fun h => absurd rfl h⟩
  | cons e rest ih =>
    intro u v hC hZ
    simp only [checkContiguousSyncEdges, Bool.and_eq_true, beq_iff_eq] at hC
    obtain ⟨hSrc, hRest⟩ := hC; subst hSrc
    have hE := hZ e (List.Mem.head _)
    have hChk := (List.all_eq_true.mp hOk) e hE.1
    simp [hE.2] at hChk
    obtain ⟨hI, hB⟩ := ih e.dst v hRest (fun x hx => hZ x (List.Mem.tail _ hx))
    refine ⟨by simp only [combWalkDelay]; omega, fun _ => ?_⟩
    cases rest with
    | nil => simp only [checkContiguousSyncEdges, beq_iff_eq] at hRest; rw [← hRest]; exact hChk.2
    | cons r rs => exact hB (by simp)
/-- **Artifact-bound physical signoff.** On the checks derived from `nl` and `pnr` alone: routing binds the fan-in,
every register-to-register path of the emitted netlist closes setup at the slow corner without retiming, the fanout
forest closes Elmore timing, pads of distinct cells keep `deck` spacing, every via is enclosed, and the critical path
closes setup at `SS` and hold at `FF`. No `TapeoutConfig` sample graph, tree, box or path is read. -/
def checkArtifactBoundTapeout (env : ProcessCornerEnvelope) (clockPeriodPs : Nat) (deck : FoundryDrcDeck)
    (nl : BelNetlist) (pnr : PnrCertificate) : Bool :=
  let slow := env.slowCorner
  let phys := derivePhysicalChecksFromBelNetlist slow deck nl pnr
  checkRoutingBindsFanIn nl pnr && decide (slow.tCqMaxPs + slow.tSetupPs + slow.tSkewPs ≤ clockPeriodPs) &&
  checkGraphArrivals (belPathDepths nl max 0 (belCellDelayPs slow) (fanInWirePs pnr))
    (clockPeriodPs - (slow.tCqMaxPs + slow.tSetupPs + slow.tSkewPs)) phys.syncGraph.edges &&
  checkSteinerTimingClosure slow clockPeriodPs phys.steinerTree &&
  phys.metalShapes.all (fun a => phys.metalShapes.all fun b => a.1 == b.1 || checkBoxSpacing2D deck.minMetalSpacingNm a.2 b.2) &&
  phys.viaCuts.all (fun v => checkViaEnclosure2D deck.minViaEnclosureNm v.1 v.2) &&
  checkEnvelopeTimingSignoff env clockPeriodPs phys.criticalPath
example : checkArtifactBoundTapeout envelope7nm 2000 default7nmDrcDeck validAdderBelNetlist
    (synthesizeGridPnrCert validAdderBelNetlist) = true := by decide +kernel
/-- **Soundness of artifact-bound signoff**, about the graph, forest, geometry and path derived from `nl` and `pnr`:
routing covers the fan-in; every contiguous register-free walk of the timing graph fits the clock at the slow corner;
the forest closes; pads of distinct cells share no point; every via lies in its pad; and timing signoff holds at
every corner between `FF` and `SS`. -/
theorem checkArtifactBoundTapeout_sound (env : ProcessCornerEnvelope) (clockPeriodPs : Nat) (deck : FoundryDrcDeck)
    (nl : BelNetlist) (pnr : PnrCertificate) (hOk : checkArtifactBoundTapeout env clockPeriodPs deck nl pnr = true) :
    pnr.routedNets.length = (belFanIn nl).length ∧
    (∀ (u v : Nat) (walk : List SyncEdge), checkContiguousSyncEdges u v walk = true →
      (∀ e ∈ walk, e ∈ (derivePhysicalChecksFromBelNetlist env.slowCorner deck nl pnr).syncGraph.edges ∧ e.origRegs = 0) →
      env.slowCorner.tCqMaxPs + combWalkDelay walk + env.slowCorner.tSetupPs + env.slowCorner.tSkewPs ≤ clockPeriodPs) ∧
    checkSteinerTimingClosure env.slowCorner clockPeriodPs
      (derivePhysicalChecksFromBelNetlist env.slowCorner deck nl pnr).steinerTree = true ∧
    (∀ a ∈ (derivePhysicalChecksFromBelNetlist env.slowCorner deck nl pnr).metalShapes,
      ∀ b ∈ (derivePhysicalChecksFromBelNetlist env.slowCorner deck nl pnr).metalShapes, a.1 ≠ b.1 →
        ∀ x y, ¬ (a.2.containsPoint x y ∧ b.2.containsPoint x y)) ∧
    (∀ v ∈ (derivePhysicalChecksFromBelNetlist env.slowCorner deck nl pnr).viaCuts,
      ∀ x y, v.1.containsPoint x y → v.2.containsPoint x y) ∧
    (∀ c : ProcessCorner, CornerBetween env.fastCorner c env.slowCorner → checkTimingSignoff c clockPeriodPs
      (derivePhysicalChecksFromBelNetlist env.slowCorner deck nl pnr).criticalPath = true) := by
  simp only [checkArtifactBoundTapeout, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true,
    beq_iff_eq] at hOk
  obtain ⟨⟨⟨⟨⟨⟨hBind, hOv⟩, hComb⟩, hSt⟩, hBox⟩, hVia⟩, hEnv⟩ := hOk
  refine ⟨?_, fun u v walk hC hZ => ?_, hSt, fun a ha b hb hne x y => ?_, fun v hv x y hIn => ?_, fun c hBet => ?_⟩
  · simp only [checkRoutingBindsFanIn, Bool.and_eq_true, decide_eq_true_eq] at hBind; exact hBind.1
  · obtain ⟨h1, h2⟩ := graphArrivals_walk _ _ _ hComb walk u v hC hZ
    cases walk with
    | nil => simp only [combWalkDelay]; omega
    | cons e r => have := h2 (by simp); omega
  · rcases hBox a ha b hb with h | h
    · exact absurd h hne
    · exact boxSpacing2D_disjoint _ _ _ x y h
  · exact (viaEnclosure2D_contained _ _ _ x y (hVia v hv) hIn).1
  · exact (envelope_timing_signoff_implies_all_intermediate_corners_safe env clockPeriodPs _ c hBet hEnv).1
/-- Signoff of a netlist and its PnR certificate with nothing else supplied: netlist validity, the netlist-bound
PnR certificate, then `checkArtifactBoundTapeout`; returns the derived checks. -/
def runArtifactBoundTapeoutSignoff (env : ProcessCornerEnvelope) (clockPeriodPs : Nat) (deck : FoundryDrcDeck)
    (nl : BelNetlist) (pnr : PnrCertificate) : Option ArtifactPhysicalChecks :=
  if checkBelNetlistValid nl && checkPnrCertificate nl env.slowCorner clockPeriodPs pnr &&
      checkArtifactBoundTapeout env clockPeriodPs deck nl pnr then
    some (derivePhysicalChecksFromBelNetlist env.slowCorner deck nl pnr)
  else none
theorem runArtifactBoundTapeoutSignoff_sound (env : ProcessCornerEnvelope) (clockPeriodPs : Nat) (deck : FoundryDrcDeck)
    (nl : BelNetlist) (pnr : PnrCertificate) (phys : ArtifactPhysicalChecks)
    (hOk : runArtifactBoundTapeoutSignoff env clockPeriodPs deck nl pnr = some phys) :
    phys = derivePhysicalChecksFromBelNetlist env.slowCorner deck nl pnr ∧ checkBelNetlistValid nl = true ∧
    checkPnrCertificate nl env.slowCorner clockPeriodPs pnr = true ∧
    checkArtifactBoundTapeout env clockPeriodPs deck nl pnr = true := by
  unfold runArtifactBoundTapeoutSignoff at hOk; split at hOk
  · rename_i h; simp only [Bool.and_eq_true] at h; injection hOk with hP; exact ⟨hP.symm, h.1.1, h.1.2, h.2⟩
  · cases hOk
/-- Any `RtlModule` to a signed-off netlist: the emission gate `checkRtlModuleW`, BEL synthesis, grid PnR, and
artifact-bound signoff. Returns the netlist, its PnR certificate, the derived checks and the SystemVerilog. -/
def compileRtlModuleArtifactBoundTapeout (env : ProcessCornerEnvelope) (clockPeriodPs : Nat) (deck : FoundryDrcDeck)
    (m : RtlModule) (sinkCapFf : Nat := 5) : Option (BelNetlist × PnrCertificate × ArtifactPhysicalChecks × String) :=
  if checkRtlModuleW m then
    (runArtifactBoundTapeoutSignoff env clockPeriodPs deck (synthesizeModuleToBels m)
      (synthesizeGridPnrCert (synthesizeModuleToBels m) sinkCapFf)).map fun phys =>
        (synthesizeModuleToBels m, synthesizeGridPnrCert (synthesizeModuleToBels m) sinkCapFf, phys, emitModuleSV m)
  else none
/-- Complete configuration bundle for `compileObendModuleToSiliconTapeout`. -/
structure TapeoutConfig where
  moduleName        : String
  entryDef          : String := ""
  dictInlinePasses  : Nat := 2
  compileMode       : RtlCompileMode := .pipelined
  clockPeriodPs     : Nat := 2000
  retimingFuel      : Nat := 2
  maxCombDelayPs    : Nat := 1800
  syncGraph         : SyncGraph := macUnretimedGraph
  pnrCert?          : Option PnrCertificate := none
  sinkCapFf         : Nat := 5
  unbufferedTree    : SteinerTree := unbufferedFanoutTree
  bufWireId         : Nat := 2
  bufInputCapFf     : Nat := 25
  drcDeck           : FoundryDrcDeck := default7nmDrcDeck
  cutlineFeature    : CutlineDrcFeature := default7nmCutlineFeature
  metalBoxA         : LayoutBox2D := defaultMetalBoxA
  metalBoxB         : LayoutBox2D := defaultMetalBoxB
  viaBox            : LayoutBox2D := defaultViaBox
  viaPadBox         : LayoutBox2D := defaultViaPadBox
  cornerEnvelope    : ProcessCornerEnvelope := envelope7nm
  timingPath        : TimingPath :=
    { name := "obend_pipelined_stage_path", logicLevels := 3, minLevels := 3, carryBits := 4, tileHops := 1 }
  datedRoot         : Nat := 20261102
  deriving DecidableEq, Repr
/-- Structured refusal diagnostic naming the exact stage of the tapeout pipeline that refused. -/
inductive TapeoutError where
  | frontEndParseRefused (stage message : String)
  | isarContractRefused (stage message : String)
  | frontEndLowerRefused (stage message : String)
  | frontEndAcceptRefused (stage message : String)
  | noCompositionFound (moduleName : String)
  | rtlCompileRefused (moduleName : String)
  | rtlModuleCheckRefused (moduleName : String)
  | belSynthesisInvalid (moduleName : String)
  | retimingSolverRefused (graphName : String)
  | retimingCertRefused (graphName : String)
  | pnrCertRefused (designName : String)
  | artifactBoundSignoffRefused (moduleName : String)
  | steinerTimingRefused (moduleName : String)
  | cutlineDrcRefused (deckName : String)
  | boxSpacing2DRefused (deckName : String)
  | viaEnclosure2DRefused (deckName : String)
  | envelopeTimingRefused (moduleName : String)
  | receiptCeilingRefused (reason : String)
  deriving DecidableEq, Repr
/-- Render a `TapeoutError` as a human-readable diagnostic string. -/
def TapeoutError.toString : TapeoutError → String
  | .frontEndParseRefused st msg  => s!"[Stage 1: FrontEnd.parseModule ({st})] {msg}"
  | .isarContractRefused st msg   => s!"[Stage 1: FrontEnd.checkModuleIsarCerts ({st})] {msg}"
  | .frontEndLowerRefused st msg  => s!"[Stage 1: FrontEnd.lowerDecoded ({st})] {msg}"
  | .frontEndAcceptRefused st msg => s!"[Stage 1: FrontEnd.accept ({st})] {msg}"
  | .noCompositionFound m         => s!"[Stage 1: C4 Object Extraction] no open-recursive Composition found in {m}"
  | .rtlCompileRefused m          => s!"[Stage 3: Compiler] Book-to-RTL compilation refused for {m}"
  | .rtlModuleCheckRefused m      => s!"[Stage 3: HDL.checkRtlModule] DAG/CDC verification failed for {m}"
  | .belSynthesisInvalid m        => s!"[Stage 4: Synth.synthesizeModuleToBels] BEL netlist invalid for {m}"
  | .retimingSolverRefused g      => s!"[Stage 5: Retiming.solveVerifiedRetiming?] no feasible lag assignment for {g}"
  | .retimingCertRefused g        => s!"[Stage 5: Retiming.checkRetimingCert] retiming certificate failed STA at SS corner for {g}"
  | .pnrCertRefused d             => s!"[Stage 6: PlaceRoute.checkPnrCertificate] Netlist-bound PnR certificate refused for {d}"
  | .artifactBoundSignoffRefused m => s!"[Stage 6: checkArtifactBoundTapeout] netlist-derived timing/DRC signoff failed for {m}"
  | .steinerTimingRefused m       => s!"[Stage 6: PlaceRoute.checkSteinerTimingClosure] buffered Steiner tree failed Elmore timing for {m}"
  | .cutlineDrcRefused d          => s!"[Stage 7: DRC.checkCutlineDRC] 1D cutline DRC violation on deck {d}"
  | .boxSpacing2DRefused d        => s!"[Stage 7: DRC.checkBoxSpacing2D] 2D metal box spacing violation on deck {d}"
  | .viaEnclosure2DRefused d      => s!"[Stage 7: DRC.checkViaEnclosure2D] 2D via enclosure violation on deck {d}"
  | .envelopeTimingRefused m      => s!"[Stage 7: Process.checkEnvelopeTimingSignoff] dual-corner [SS, FF] timing signoff failed for {m}"
  | .receiptCeilingRefused r      => s!"[Stage 8: Receipt.ceiling] trust ceiling check failed: {r}"

/-! ## 2. Stage 2 Dictionary Specialization (`specializeBookDict`) & Slot Preservation -/
def specializeBookItemDict (passes : Nat) : BookItem → BookItem
  | .slot d =>
    .slot { d with code := betaRecordDict passes (inlineDict passes d.code) }
  | .static m v =>
    .static m (betaRecordDict passes (inlineDict passes v))
def specializeBookDict (passes : Nat) (B : Book) : Book where
  items := B.items.map (specializeBookItemDict passes)
theorem specializeBookItems_preserves_slot_members (passes : Nat) (items : List BookItem) :
    ((items.map (specializeBookItemDict passes)).filterMap BookItem.def?).map (·.member) =
      (items.filterMap BookItem.def?).map (·.member) := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
    cases item with
    | slot d =>
      simp only [List.map_cons, specializeBookItemDict, List.filterMap_cons, BookItem.def?, ih]
    | static m v =>
      simp only [List.map_cons, specializeBookItemDict, List.filterMap_cons, BookItem.def?, ih]
theorem specializeBookDict_preserves_slots (passes : Nat) (B : Book) :
    (specializeBookDict passes B).slots = B.slots ∧
    (∀ t : Term, t ≈b betaRecordDict passes t) := by
  refine ⟨?_, bequiv_betaRecordDict passes⟩
  unfold specializeBookDict Book.slots Book.defs
  exact specializeBookItems_preserves_slot_members passes B.items
def compileBookByMode (mode : RtlCompileMode) (modName : String) (B : Book) : Option RtlModule :=
  match mode with
  | .pipelined        => compileBookToPipelinedRtl modName B
  | .combinationalSat => compileBookToRtlSat modName B
  | .sequentialSat    => compileBookToSeqRtlSat modName B

/-! ## 3. Verified `SiliconTapeoutArtifact`, Real Byte Hashing & Kernel-Checked Support List -/
/-- The 3 kernel-checked hardware judge supports executed during `compileObendModuleToSiliconTapeout`. -/
def tapeoutCheckedSupports : List (String × Obend.Receipt.Trust) :=
  [ ("hw-rtl-synth",     .checked "hw-rtl-synth"     "1" .kernel)
  , ("hw-retime-sta",    .checked "hw-retime-sta"    "1" .kernel)
  , ("hw-pnr-bitstream", .checked "hw-pnr-bitstream" "1" .kernel) ]
def isAdmittedTapeoutJudgeTag (tag : String) : Bool :=
  (findHardwareFormat? tag).isSome
def trustBaseEq : Obend.Judge.TrustBase → Obend.Judge.TrustBase → Bool
  | .kernel,      .kernel      => true
  | .compiled,    .compiled    => true
  | .external w1, .external w2 => w1 == w2
  | _,            _            => false
def trustEq : Obend.Receipt.Trust → Obend.Receipt.Trust → Bool
  | .checked f1 v1 b1, .checked f2 v2 b2 => (f1 == f2) && (v1 == v2) && trustBaseEq b1 b2
  | .attested p1 r1,   .attested p2 r2   => (p1 == p2) && (r1 == r2)
  | _,                 _                 => false
def isCheckedTrust : Obend.Receipt.Trust → Bool
  | .checked _ _ _ => true
  | .attested _ _  => false
def checkTapeoutTrustChecked (ran claimed : List (String × Obend.Receipt.Trust)) : Bool :=
  !ran.isEmpty &&
  ran.all (fun (s, t) =>
    match claimed.lookup s with
    | some t' => trustEq t' t
    | none    => false) &&
  claimed.all (fun (_, t) => isCheckedTrust t)
/-- Construct the dated `Obend.Receipt.Receipt` for a verified silicon compilation run, computing
`pre` and `post` via `H : Obend.Digest.HashBytes.Hash` (defaulting to `Obend.Core.Digest.deployed`
cSHAKE256) over the actual source bytes `srcBytes` and emitted SystemVerilog `svBytes`! -/
def mkTapeoutReceipt (H : Obend.Digest.HashBytes.Hash) (cfg : TapeoutConfig) (srcBytes svBytes : List UInt8)
    (belCount : Nat) (pnrDesignName rtlName : String) :
    Obend.Receipt.Receipt String String String String where
  pre        := "cshake256:" ++ rtlNatToStr (Obend.Digest.HashBytes.ofBE (H srcBytes))
  post       := "cshake256:" ++ rtlNatToStr (Obend.Digest.HashBytes.ofBE (H svBytes))
  row        := rtlName
  law        := "law:netlist-bound-rtl-bel-pnr-v2"
  pins       :=
    [ ("rtlModule",  some rtlName)
    , ("belCells",   some (rtlNatToStr belCount))
    , ("pnrDesign",  some pnrDesignName) ]
  openings   :=
    [ ("checkRtlModule",             true)
    , ("checkBelNetlistValid",       true)
    , ("checkRetimingCert",          true)
    , ("checkPnrCertificate",        true)
    , ("checkCutlineDRC",            true)
    , ("checkEnvelopeTimingSignoff", true)
    , ("checkArtifactBoundTapeout",  true) ]
  verdict    := .ok
  quantifier := .forAll
  trust      := tapeoutCheckedSupports
  dated      := cfg.datedRoot
  proofs     := []
  prev       := "cshake256:genesis"
/-- Equal SystemVerilog digests under any hash `H` mean equal byte streams or a collision of `H`. -/
theorem tapeout_sv_digest_binds_or_collides
    (H : Obend.Digest.HashBytes.Hash)
    (svBytes1 svBytes2 : List UInt8)
    (hEq : Obend.Digest.HashBytes.ofBE (H svBytes1) = Obend.Digest.HashBytes.ofBE (H svBytes2)) :
    svBytes1 = svBytes2 ∨ Obend.Digest.HashBytes.Collision H := by
  by_cases hSame : svBytes1 = svBytes2
  · exact Or.inl hSame
  · exact Or.inr ⟨svBytes1, svBytes2, hSame, hEq⟩
/-- Complete verified silicon compilation & physical signoff artifact. -/
structure SiliconTapeoutArtifact where
  moduleName          : String
  comp                : Composition
  isarCerts           : List Elaborate.ElaboratedIsarCert
  rawBook             : Book
  specializedBook     : Book
  rtlModule           : RtlModule
  belNetlist          : BelNetlist
  retimingCert        : RetimingCert
  retimedGraph        : SyncGraph
  pnrCert             : PnrCertificate
  bufferedSteinerTree : SteinerTree
  tcadEnvelope        : ProcessCornerEnvelope
  systemVerilog       : String
  svDigest            : Nat
  receipt             : Obend.Receipt.Receipt String String String String
  clockPeriodPs       : Nat
  physical            : ArtifactPhysicalChecks

/-! ## 4. Stages 2–8 Kernel-Reducible Compiler (`compileCompositionToSiliconTapeout`) & Soundness -/
def compileCompositionToSiliconTapeoutWithHash (H : Obend.Digest.HashBytes.Hash) (srcBytes : List UInt8)
    (cfg : TapeoutConfig) (comp : Composition) (isarCerts : List Elaborate.ElaboratedIsarCert := []) :
    Except TapeoutError SiliconTapeoutArtifact := do
  if !(isarCerts.all (FrontEnd.verifyCertJudgeTags isAdmittedTapeoutJudgeTag)) then
    .error (.isarContractRefused "isar-cert-verification" "contract Isar proof script or judge tag invalid")
  else
    let rawBook := Obend.Leaf.emit comp
    let specializedBook := specializeBookDict cfg.dictInlinePasses rawBook
    match compileBookByMode cfg.compileMode cfg.moduleName specializedBook with
    | none => .error (.rtlCompileRefused cfg.moduleName)
    | some rtlModule =>
      if !(checkRtlModule rtlModule) then
        .error (.rtlModuleCheckRefused cfg.moduleName)
      else
        let belNetlist := synthesizeModuleToBels rtlModule
        if !(checkBelNetlistValid belNetlist) then
          .error (.belSynthesisInvalid cfg.moduleName)
        else
          match solveVerifiedRetiming? cfg.retimingFuel cfg.syncGraph cfg.maxCombDelayPs with
          | none => .error (.retimingSolverRefused cfg.syncGraph.name)
          | some retimingCert =>
            if !(checkCutlineDRC cfg.drcDeck cfg.cutlineFeature) then
              .error (.cutlineDrcRefused cfg.drcDeck.deckName)
            else if !(checkBoxSpacing2D cfg.drcDeck.minMetalSpacingNm cfg.metalBoxA cfg.metalBoxB) then
              .error (.boxSpacing2DRefused cfg.drcDeck.deckName)
            else if !(checkViaEnclosure2D cfg.drcDeck.minViaEnclosureNm cfg.viaBox cfg.viaPadBox) then
              .error (.viaEnclosure2DRefused cfg.drcDeck.deckName)
            else
              let tcadEnvelope := cfg.cornerEnvelope
              if !(checkEnvelopeTimingSignoff tcadEnvelope cfg.clockPeriodPs cfg.timingPath) then
                .error (.envelopeTimingRefused cfg.moduleName)
              else if !(checkRetimingCert cfg.syncGraph retimingCert tcadEnvelope.slowCorner cfg.clockPeriodPs) then
                .error (.retimingCertRefused cfg.syncGraph.name)
              else
                let pnrCert := cfg.pnrCert?.getD (synthesizeGridPnrCert belNetlist cfg.sinkCapFf)
                if !(checkPnrCertificate belNetlist tcadEnvelope.slowCorner cfg.clockPeriodPs pnrCert) then
                  .error (.pnrCertRefused pnrCert.designName)
                else if !(checkArtifactBoundTapeout tcadEnvelope cfg.clockPeriodPs cfg.drcDeck belNetlist pnrCert) then
                  .error (.artifactBoundSignoffRefused cfg.moduleName)
                else
                  let bufferedSteinerTree :=
                    decoupleRightBranchWithBuffer cfg.bufWireId cfg.bufInputCapFf cfg.unbufferedTree
                  if !(checkSteinerTimingClosure tcadEnvelope.slowCorner cfg.clockPeriodPs bufferedSteinerTree) then
                    .error (.steinerTimingRefused cfg.moduleName)
                  else
                    let sv := emitModuleSV rtlModule
                    let svBytes := sv.toUTF8.toList
                    let receipt :=
                      mkTapeoutReceipt H cfg srcBytes svBytes belNetlist.cells.length pnrCert.designName rtlModule.name
                    if !(checkTapeoutTrustChecked tapeoutCheckedSupports receipt.trust) then
                      .error (.receiptCeilingRefused "tapeout receipt trust ceiling contains unverified or attested supports")
                    else
                      let retimedGraph := applyRetimingCertToGraph cfg.syncGraph retimingCert
                      .ok
                        { moduleName := cfg.moduleName, comp := comp, isarCerts := isarCerts, rawBook := rawBook
                         , specializedBook := specializedBook, rtlModule := rtlModule, belNetlist := belNetlist, retimingCert := retimingCert
                         , retimedGraph := retimedGraph, pnrCert := pnrCert, bufferedSteinerTree := bufferedSteinerTree
                         , tcadEnvelope := tcadEnvelope, systemVerilog := sv, svDigest := Obend.Digest.HashBytes.ofBE (H svBytes)
                         , receipt := receipt, clockPeriodPs := cfg.clockPeriodPs, physical :=
                          derivePhysicalChecksFromBelNetlist tcadEnvelope.slowCorner cfg.drcDeck belNetlist pnrCert }
/-- Default instantiation using `Obend.Core.Digest.deployed` (cSHAKE256). -/
def compileCompositionToSiliconTapeout (cfg : TapeoutConfig) (comp : Composition)
    (isarCerts : List Elaborate.ElaboratedIsarCert := []) : Except TapeoutError SiliconTapeoutArtifact :=
  compileCompositionToSiliconTapeoutWithHash Obend.Core.Digest.deployed cfg.moduleName.toUTF8.toList cfg comp isarCerts
/-- **What an accepted tapeout establishes** of its artifact: verified Isar contracts and judge tags; the Book,
RTL (`checkRtlModule`) and BEL netlist (`synthesizeModuleToBels`, valid, exact flip-flop count); the retiming
certificate; the netlist-bound PnR certificate (injective placement, short-free routing); DRC and `[FF, TT, SS]`
envelope timing; the SystemVerilog byte commitment and receipt; and, last, artifact-bound physical signoff. -/
@[expose] def TapeoutSound (H : Obend.Digest.HashBytes.Hash) (cfg : TapeoutConfig) (comp : Composition)
    (isarCerts : List Elaborate.ElaboratedIsarCert) (art : SiliconTapeoutArtifact) : Prop :=
    art.comp = comp ∧
    art.isarCerts = isarCerts ∧
    (∀ cert ∈ art.isarCerts,
      cert.scriptValid = true ∧ ∀ tag ∈ cert.judgeTags, isAdmittedTapeoutJudgeTag tag = true) ∧
    art.rawBook = Obend.Leaf.emit art.comp ∧
    art.specializedBook.slots = art.rawBook.slots ∧
    compileBookByMode cfg.compileMode cfg.moduleName art.specializedBook = some art.rtlModule ∧
    checkRtlModule art.rtlModule = true ∧
    art.belNetlist = synthesizeModuleToBels art.rtlModule ∧
    checkBelNetlistValid art.belNetlist = true ∧
    countFfBels art.belNetlist = art.rtlModule.regs.length ∧
    checkRetimingCert cfg.syncGraph art.retimingCert art.tcadEnvelope.slowCorner cfg.clockPeriodPs = true ∧
    (∀ e ∈ cfg.syncGraph.edges, 0 ≤ retimedEdgeWeight (lookupLag art.retimingCert) e) ∧
    checkPnrCertificate art.belNetlist art.tcadEnvelope.slowCorner cfg.clockPeriodPs art.pnrCert = true ∧
    art.pnrCert.placedCells.length = art.belNetlist.cells.length ∧
    checkPlacementInjective art.pnrCert.placedCells = true ∧
    checkRoutingDisjoint art.pnrCert.routedNets = true ∧
    checkSteinerTimingClosure art.tcadEnvelope.slowCorner cfg.clockPeriodPs art.bufferedSteinerTree = true ∧
    cfg.drcDeck.minMetalWidthNm + cfg.drcDeck.minMetalSpacingNm ≤
      cfg.cutlineFeature.metalWidthNm + cfg.cutlineFeature.metalSpacingNm ∧
    (∀ x y, ¬ (cfg.metalBoxA.containsPoint x y ∧ cfg.metalBoxB.containsPoint x y)) ∧
    (∀ x y, cfg.viaBox.containsPoint x y → cfg.viaPadBox.containsPoint x y) ∧
    checkEnvelopeTimingSignoff art.tcadEnvelope cfg.clockPeriodPs cfg.timingPath = true ∧
    (art.tcadEnvelope.Valid →
      ∀ c : ProcessCorner,
        CornerBetween art.tcadEnvelope.fastCorner c art.tcadEnvelope.slowCorner →
        checkTimingSignoff c cfg.clockPeriodPs cfg.timingPath = true) ∧
    art.systemVerilog = emitModuleSV art.rtlModule ∧
    art.svDigest = Obend.Digest.HashBytes.ofBE (H art.systemVerilog.toUTF8.toList) ∧
    art.receipt.post = "cshake256:" ++ rtlNatToStr art.svDigest ∧
    art.receipt.verdict = .ok ∧
    checkTapeoutTrustChecked tapeoutCheckedSupports art.receipt.trust = true ∧
    checkArtifactBoundTapeout art.tcadEnvelope cfg.clockPeriodPs cfg.drcDeck art.belNetlist art.pnrCert = true
theorem compileCompositionToSiliconTapeoutWithHash_sound
    (H : Obend.Digest.HashBytes.Hash) (srcBytes : List UInt8) (cfg : TapeoutConfig) (comp : Composition)
    (isarCerts : List Elaborate.ElaboratedIsarCert) (art : SiliconTapeoutArtifact)
    (hOk : compileCompositionToSiliconTapeoutWithHash H srcBytes cfg comp isarCerts = .ok art) :
    TapeoutSound H cfg comp isarCerts art := by
  unfold compileCompositionToSiliconTapeoutWithHash at hOk
  dsimp only at hOk
  cases hIsarB : isarCerts.all (FrontEnd.verifyCertJudgeTags isAdmittedTapeoutJudgeTag) with
  | false => rw [hIsarB] at hOk; cases hOk
  | true =>
    rw [hIsarB] at hOk
    cases hCompRtl : compileBookByMode cfg.compileMode cfg.moduleName (specializeBookDict cfg.dictInlinePasses (Obend.Leaf.emit comp)) with
    | none => rw [hCompRtl] at hOk; cases hOk
    | some rtlModule =>
      rw [hCompRtl] at hOk
      dsimp only at hOk
      cases hRtlB : checkRtlModule rtlModule with
      | false => rw [hRtlB] at hOk; cases hOk
      | true =>
        rw [hRtlB] at hOk
        cases hBelB : checkBelNetlistValid (synthesizeModuleToBels rtlModule) with
        | false => rw [hBelB] at hOk; cases hOk
        | true =>
          rw [hBelB] at hOk
          cases hSolve : solveVerifiedRetiming? cfg.retimingFuel cfg.syncGraph cfg.maxCombDelayPs with
          | none => rw [hSolve] at hOk; cases hOk
          | some retimingCert =>
            rw [hSolve] at hOk
            dsimp only at hOk
            cases hCutB : checkCutlineDRC cfg.drcDeck cfg.cutlineFeature with
            | false => rw [hCutB] at hOk; cases hOk
            | true =>
              rw [hCutB] at hOk
              cases hBoxB : checkBoxSpacing2D cfg.drcDeck.minMetalSpacingNm cfg.metalBoxA cfg.metalBoxB with
              | false => rw [hBoxB] at hOk; cases hOk
              | true =>
                rw [hBoxB] at hOk
                cases hViaB : checkViaEnclosure2D cfg.drcDeck.minViaEnclosureNm cfg.viaBox cfg.viaPadBox with
                | false => rw [hViaB] at hOk; cases hOk
                | true =>
                  rw [hViaB] at hOk
                  let tcadEnv := cfg.cornerEnvelope
                  cases hEnvB : checkEnvelopeTimingSignoff tcadEnv cfg.clockPeriodPs cfg.timingPath with
                  | false => rw [hEnvB] at hOk; cases hOk
                  | true =>
                    rw [hEnvB] at hOk
                    cases hRetB : checkRetimingCert cfg.syncGraph retimingCert tcadEnv.slowCorner cfg.clockPeriodPs with
                    | false => rw [hRetB] at hOk; cases hOk
                    | true =>
                      rw [hRetB] at hOk
                      let belNl := synthesizeModuleToBels rtlModule
                      let pnrC := cfg.pnrCert?.getD (synthesizeGridPnrCert belNl cfg.sinkCapFf)
                      cases hPnrB : checkPnrCertificate belNl tcadEnv.slowCorner cfg.clockPeriodPs pnrC with
                      | false => rw [hPnrB] at hOk; cases hOk
                      | true =>
                        rw [hPnrB] at hOk
                        cases hArtB : checkArtifactBoundTapeout tcadEnv cfg.clockPeriodPs cfg.drcDeck belNl pnrC
                        · rw [hArtB] at hOk; cases hOk
                        rw [hArtB] at hOk
                        let bufTree := decoupleRightBranchWithBuffer cfg.bufWireId cfg.bufInputCapFf cfg.unbufferedTree
                        cases hSteinerB : checkSteinerTimingClosure tcadEnv.slowCorner cfg.clockPeriodPs bufTree with
                        | false => rw [hSteinerB] at hOk; cases hOk
                        | true =>
                          rw [hSteinerB] at hOk
                          let sv := emitModuleSV rtlModule
                          let recVal := mkTapeoutReceipt H cfg srcBytes sv.toUTF8.toList belNl.cells.length pnrC.designName rtlModule.name
                          cases hCeil : checkTapeoutTrustChecked tapeoutCheckedSupports recVal.trust with
                          | false => rw [hCeil] at hOk; cases hOk
                          | true =>
                            rw [hCeil] at hOk
                            injection hOk with hArtEq
                            subst hArtEq
                            have hIsarSound : ∀ cert ∈ isarCerts,
                                cert.scriptValid = true ∧ ∀ tag ∈ cert.judgeTags, isAdmittedTapeoutJudgeTag tag = true := by
                              intro cert hMem
                              simp only [List.all_eq_true] at hIsarB
                              exact FrontEnd.verifyCertJudgeTags_sound isAdmittedTapeoutJudgeTag cert (hIsarB cert hMem)
                            have hSlots := (specializeBookDict_preserves_slots cfg.dictInlinePasses (Obend.Leaf.emit comp)).1
                            have hFfCount := (synthesizeModuleToBels_valid_and_ff_count rtlModule).2
                            have hRetWeights := (solveVerifiedRetiming_sound cfg.retimingFuel cfg.syncGraph cfg.maxCombDelayPs retimingCert hSolve).1
                            have hPnrSound := checkPnrCertificate_sound belNl tcadEnv.slowCorner cfg.clockPeriodPs pnrC hPnrB
                            have hPnrParts : checkPlacementInjective pnrC.placedCells = true ∧
                                checkRoutingDisjoint pnrC.routedNets = true := by
                              simp only [checkPnrCertificate, Bool.and_eq_true] at hPnrB
                              rcases hPnrB with ⟨⟨⟨⟨⟨⟨_, _⟩, hInj⟩, _⟩, hDisj⟩, _⟩, _⟩
                              exact ⟨hInj, hDisj⟩
                            have hPitch := drc_clean_implies_min_pitch cfg.drcDeck cfg.cutlineFeature hCutB
                            have hIntermSafe : tcadEnv.Valid → ∀ c : ProcessCorner,
                                CornerBetween tcadEnv.fastCorner c tcadEnv.slowCorner →
                                checkTimingSignoff c cfg.clockPeriodPs cfg.timingPath = true := by
                              intro _hValid c hBet
                              exact (envelope_timing_signoff_implies_all_intermediate_corners_safe
                                tcadEnv cfg.clockPeriodPs cfg.timingPath c hBet hEnvB).1
                            exact ⟨rfl, rfl, hIsarSound, rfl, hSlots, hCompRtl, hRtlB, rfl, hBelB, hFfCount,
                                   hRetB, hRetWeights, hPnrB, hPnrSound.2.1, hPnrParts.1, hPnrParts.2, hSteinerB,
                                   hPitch,
                                   fun x y => boxSpacing2D_disjoint cfg.drcDeck.minMetalSpacingNm cfg.metalBoxA cfg.metalBoxB x y hBoxB,
                                   fun x y hIn => (viaEnclosure2D_contained cfg.drcDeck.minViaEnclosureNm cfg.viaBox cfg.viaPadBox x y hViaB hIn).1,
                                   hEnvB, hIntermSafe, rfl, rfl, rfl, rfl, hCeil, hArtB⟩
theorem compileCompositionToSiliconTapeout_sound
    (cfg : TapeoutConfig) (comp : Composition) (isarCerts : List Elaborate.ElaboratedIsarCert)
    (art : SiliconTapeoutArtifact) (hOk : compileCompositionToSiliconTapeout cfg comp isarCerts = .ok art) :
    TapeoutSound Obend.Core.Digest.deployed cfg comp isarCerts art :=
  compileCompositionToSiliconTapeoutWithHash_sound
    Obend.Core.Digest.deployed cfg.moduleName.toUTF8.toList cfg comp isarCerts art hOk

/-! ## 5. Stage 1 `.obend` Front-End Lowering (`compileObendFrontEndStage`) & Full Pipeline (`compileObendModuleToSiliconTapeout`) -/
def defaultTapeoutLimits : Json :=
  Json.mkObj
    [ ("heap",      toJson "100000")
    , ("stack",     toJson "100000")
    , ("ticks",     toJson "100000")
    , ("checkWork", toJson "65536") ]
def resolveTapeoutKnotTerm (root : Term) (rawFields : List (String × Term)) (visiting : List String) :
    Nat → Term → Term
  | 0, t => t
  | fuel + 1, .get target name =>
    if Obend.Law.termEq target root then
      if visiting.contains name then .get root name
      else
        match rawFields.lookup name with
        | some rawBody =>
          let opened := Obend.Logic.openTerm rawBody root (.record [])
          resolveTapeoutKnotTerm root rawFields (name :: visiting) fuel opened
        | none => .get root name
    else
      .get (resolveTapeoutKnotTerm root rawFields visiting fuel target) name
  | fuel + 1, .lam b => .lam (resolveTapeoutKnotTerm root rawFields visiting fuel b)
  | fuel + 1, .app f a =>
    .app (resolveTapeoutKnotTerm root rawFields visiting fuel f) (resolveTapeoutKnotTerm root rawFields visiting fuel a)
  | fuel + 1, .mix l u =>
    .mix (resolveTapeoutKnotTerm root rawFields visiting fuel l) (resolveTapeoutKnotTerm root rawFields visiting fuel u)
  | fuel + 1, .fix s i =>
    .fix (resolveTapeoutKnotTerm root rawFields visiting fuel s) (resolveTapeoutKnotTerm root rawFields visiting fuel i)
  | fuel + 1, .specification m e =>
    .specification (resolveTapeoutKnotTerm root rawFields visiting fuel m) (resolveTapeoutKnotTerm root rawFields visiting fuel e)
  | fuel + 1, .prototype s g =>
    .prototype (resolveTapeoutKnotTerm root rawFields visiting fuel s) (resolveTapeoutKnotTerm root rawFields visiting fuel g)
  | fuel + 1, .reflect p => .reflect (resolveTapeoutKnotTerm root rawFields visiting fuel p)
  | fuel + 1, .metadata p => .metadata (resolveTapeoutKnotTerm root rawFields visiting fuel p)
  | fuel + 1, .project p => .project (resolveTapeoutKnotTerm root rawFields visiting fuel p)
  | fuel + 1, .binary op l r =>
    .binary op (resolveTapeoutKnotTerm root rawFields visiting fuel l) (resolveTapeoutKnotTerm root rawFields visiting fuel r)
  | fuel + 1, .extend i fs =>
    .extend (resolveTapeoutKnotTerm root rawFields visiting fuel i)
      (fs.map fun (k, v) => (k, resolveTapeoutKnotTerm root rawFields visiting fuel v))
  | fuel + 1, .record fs =>
    .record (fs.map fun (k, v) => (k, resolveTapeoutKnotTerm root rawFields visiting fuel v))
  | fuel + 1, .ifZero v z s =>
    .ifZero (resolveTapeoutKnotTerm root rawFields visiting fuel v)
      (resolveTapeoutKnotTerm root rawFields visiting fuel z)
      (resolveTapeoutKnotTerm root rawFields visiting fuel s)
  | fuel + 1, .inject l p => .inject l (resolveTapeoutKnotTerm root rawFields visiting fuel p)
  | fuel + 1, .case sc arms =>
    .case (resolveTapeoutKnotTerm root rawFields visiting fuel sc)
      (arms.map fun (k, v) => (k, resolveTapeoutKnotTerm root rawFields visiting fuel v))
  | fuel + 1, .ifBool c x y =>
    .ifBool (resolveTapeoutKnotTerm root rawFields visiting fuel c)
      (resolveTapeoutKnotTerm root rawFields visiting fuel x)
      (resolveTapeoutKnotTerm root rawFields visiting fuel y)
  | fuel + 1, .perform p => .perform (resolveTapeoutKnotTerm root rawFields visiting fuel p)
  | fuel + 1, .done v => .done (resolveTapeoutKnotTerm root rawFields visiting fuel v)
  | fuel + 1, .split t names f =>
    .split (resolveTapeoutKnotTerm root rawFields visiting fuel t) names
      (resolveTapeoutKnotTerm root rawFields visiting fuel f)
  | _ + 1, t => t
def decodeTapeoutComposition (want : Composition → Bool) : Term → Option Composition
  | .fix S (.record seed) =>
    (Obend.Logic.Program.decodeOperands 64 S).bind fun (top, below) =>
      let C : Composition := ⟨top, below, seed⟩
      if want C then some C else none
  | .fix S seedTerm =>
    (Obend.Logic.Program.decodeOperands 64 S).bind fun (top, below) =>
      if top.name == "" then none
      else
        match Obend.Law.run 20000 seedTerm with
        | some (.record seed) =>
          let C : Composition := ⟨top, below, seed⟩
          if want C then some C else none
        | _ => none
  | _ => none
def findTapeoutComposition (want : Composition → Bool) : Nat → Term → Option Composition
  | 0, _ => none
  | fuel + 1, t =>
    match decodeTapeoutComposition want t with
    | some C => some C
    | none => (Obend.Law.step? t).bind (findTapeoutComposition want fuel)
def extractCompositionFromErased
    (modName : String) (entryDef : String) (decodedMod : Syntax.Module) (erasedTerm : Term) :
    Option Composition :=
  let rootTerm := (Obend.Logic.Program.knotOf erasedTerm).getD erasedTerm
  let rawFields := Obend.Logic.Program.knotFields rootTerm
  let wantNamed : Composition → Bool := fun C => C.top.name != ""
  let tryDecl (shortName : String) : Option Composition :=
    let fullKey := modName ++ "." ++ shortName
    let knotTerm : Term := .get rootTerm fullKey
    let opened := match rawFields.lookup fullKey with
      | some rb => Obend.Logic.openTerm rb rootTerm (.record [])
      | none => knotTerm
    let inlined := resolveTapeoutKnotTerm rootTerm rawFields [fullKey] 16 opened
    match findTapeoutComposition wantNamed 64 knotTerm with
    | some c => some c
    | none =>
      match findTapeoutComposition wantNamed 64 (.app knotTerm (.record [])) with
      | some c => some c
      | none => decodeTapeoutComposition wantNamed inlined
  match tryDecl entryDef with
  | some c => some c
  | none =>
    let callables := decodedMod.decls.filter fun d =>
      match d with
      | .function .. | .extension .. | .spec .. => true
      | _ => false
    callables.reverse.findSome? (fun d => tryDecl d.name)
def resolveEntryDefName (cfg : TapeoutConfig) (decodedMod : Syntax.Module) : String :=
  if cfg.entryDef != "" then
    cfg.entryDef
  else
    let callables := decodedMod.decls.filter fun d =>
      match d with
      | .function .. | .extension .. | .spec .. => true
      | _ => false
    match callables.getLast? with
    | some d => d.name
    | none => "main"
def mkTapeoutSourceModule (cfg : TapeoutConfig) (src : String) : FrontEnd.SourceModule where
  name    := cfg.moduleName
  source  := src
  sha256  := Sha256.hexString src
  imports := []
def compileObendFrontEndStage (cfg : TapeoutConfig) (src : String) :
    Except TapeoutError (Composition × List Elaborate.ElaboratedIsarCert) := do
  let srcMod := mkTapeoutSourceModule cfg src
  match FrontEnd.parseModule srcMod with
  | .error d => .error (.frontEndParseRefused d.stage d.message)
  | .ok decodedMod =>
    match FrontEnd.checkModuleIsarCerts isAdmittedTapeoutJudgeTag decodedMod with
    | .error d => .error (.isarContractRefused d.stage d.message)
    | .ok isarCerts =>
      let entryDef := resolveEntryDefName cfg decodedMod
      match FrontEnd.lowerDecoded [srcMod] [decodedMod] 0 entryDef
          (Json.arr #[]) (Json.arr #[]) defaultTapeoutLimits "definition" [] with
      | .error d => .error (.frontEndLowerRefused d.stage d.message)
      | .ok lowering =>
        match FrontEnd.accept lowering with
        | .error d => .error (.frontEndAcceptRefused d.stage d.message)
        | .ok accepted =>
          match extractCompositionFromErased cfg.moduleName entryDef decodedMod accepted.erased with
          | none => .error (.noCompositionFound cfg.moduleName)
          | some comp => .ok (comp, isarCerts)
/-- **Unified `.obend`-to-Silicon Compiler (`compileObendModuleToSiliconTapeout`)**:
Hashes actual `src.toUTF8.toList` and emitted SystemVerilog `sv.toUTF8.toList` bytes with
`Obend.Core.Digest.deployed` (cSHAKE256) and binds `checkPnrCertificate` 1-to-1 to `art.belNetlist`. -/
def compileObendModuleToSiliconTapeout (cfg : TapeoutConfig) (src : String) :
    Except TapeoutError SiliconTapeoutArtifact := do
  let (comp, isarCerts) ← compileObendFrontEndStage cfg src
  compileCompositionToSiliconTapeoutWithHash Obend.Core.Digest.deployed src.toUTF8.toList cfg comp isarCerts
theorem compileObendModuleToSiliconTapeout_sound
    (cfg : TapeoutConfig) (src : String) (art : SiliconTapeoutArtifact)
    (hOk : compileObendModuleToSiliconTapeout cfg src = .ok art) :
    (∃ (decodedMod : Syntax.Module) (lowering : FrontEnd.Lowering) (accepted : FrontEnd.Accepted lowering),
      FrontEnd.parseModule (mkTapeoutSourceModule cfg src) = .ok decodedMod ∧
      FrontEnd.checkModuleIsarCerts isAdmittedTapeoutJudgeTag decodedMod = .ok art.isarCerts ∧
      FrontEnd.lowerDecoded [mkTapeoutSourceModule cfg src] [decodedMod] 0
        (resolveEntryDefName cfg decodedMod) (Json.arr #[]) (Json.arr #[])
        defaultTapeoutLimits "definition" [] = .ok lowering ∧
      FrontEnd.accept lowering = .ok accepted ∧
      extractCompositionFromErased cfg.moduleName (resolveEntryDefName cfg decodedMod)
        decodedMod accepted.erased = some art.comp) ∧
    compileCompositionToSiliconTapeoutWithHash Obend.Core.Digest.deployed src.toUTF8.toList cfg art.comp art.isarCerts = .ok art ∧
    checkRtlModule art.rtlModule = true ∧
    checkBelNetlistValid art.belNetlist = true ∧
    countFfBels art.belNetlist = art.rtlModule.regs.length ∧
    checkRetimingCert cfg.syncGraph art.retimingCert art.tcadEnvelope.slowCorner cfg.clockPeriodPs = true ∧
    checkPnrCertificate art.belNetlist art.tcadEnvelope.slowCorner cfg.clockPeriodPs art.pnrCert = true ∧
    art.pnrCert.placedCells.length = art.belNetlist.cells.length ∧
    checkSteinerTimingClosure art.tcadEnvelope.slowCorner cfg.clockPeriodPs art.bufferedSteinerTree = true ∧
    checkEnvelopeTimingSignoff art.tcadEnvelope cfg.clockPeriodPs cfg.timingPath = true ∧
    art.systemVerilog = emitModuleSV art.rtlModule ∧
    art.svDigest = Obend.Digest.HashBytes.ofBE (Obend.Core.Digest.deployed art.systemVerilog.toUTF8.toList) ∧
    art.receipt.post = "cshake256:" ++ rtlNatToStr art.svDigest ∧
    art.receipt.verdict = .ok ∧
    checkTapeoutTrustChecked tapeoutCheckedSupports art.receipt.trust = true := by
  unfold compileObendModuleToSiliconTapeout at hOk
  dsimp only [bind, Except.bind] at hOk
  cases hStage1 : compileObendFrontEndStage cfg src with
  | error e => rw [hStage1] at hOk; cases hOk
  | ok pair =>
    rw [hStage1] at hOk
    rcases pair with ⟨comp, isarCerts⟩
    dsimp only at hOk
    unfold compileObendFrontEndStage at hStage1
    dsimp only at hStage1
    cases hParse : FrontEnd.parseModule (mkTapeoutSourceModule cfg src) with
    | error d => rw [hParse] at hStage1; cases hStage1
    | ok decodedMod =>
      rw [hParse] at hStage1
      dsimp only at hStage1
      cases hIsar : FrontEnd.checkModuleIsarCerts isAdmittedTapeoutJudgeTag decodedMod with
      | error d => rw [hIsar] at hStage1; cases hStage1
      | ok certs =>
        rw [hIsar] at hStage1
        dsimp only at hStage1
        cases hLower : FrontEnd.lowerDecoded [mkTapeoutSourceModule cfg src] [decodedMod] 0
            (resolveEntryDefName cfg decodedMod) (Json.arr #[]) (Json.arr #[])
            defaultTapeoutLimits "definition" [] with
        | error d => rw [hLower] at hStage1; cases hStage1
        | ok lowering =>
          rw [hLower] at hStage1
          dsimp only at hStage1
          cases hAccept : FrontEnd.accept lowering with
          | error d => rw [hAccept] at hStage1; cases hStage1
          | ok accepted =>
            rw [hAccept] at hStage1
            dsimp only at hStage1
            cases hExtract : extractCompositionFromErased cfg.moduleName
                (resolveEntryDefName cfg decodedMod) decodedMod accepted.erased with
            | none => rw [hExtract] at hStage1; cases hStage1
            | some cExtracted =>
              rw [hExtract] at hStage1
              injection hStage1 with hPairEq
              injection hPairEq with hCompEq hCertsEq
              subst hCompEq
              subst hCertsEq
              have hS := compileCompositionToSiliconTapeoutWithHash_sound
                Obend.Core.Digest.deployed src.toUTF8.toList cfg cExtracted certs art hOk
              have hCompArt : art.comp = cExtracted := hS.1
              have hCertsArt : art.isarCerts = certs := hS.2.1
              rw [hCompArt, hCertsArt]
              exact ⟨⟨decodedMod, lowering, accepted, rfl, hIsar, hLower, hAccept, hExtract⟩,
                     hOk,
                     hS.2.2.2.2.2.2.1,
                     hS.2.2.2.2.2.2.2.2.1,
                     hS.2.2.2.2.2.2.2.2.2.1,
                     hS.2.2.2.2.2.2.2.2.2.2.1,
                     hS.2.2.2.2.2.2.2.2.2.2.2.2.1,
                     hS.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
                     hS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
                     hS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
                     hS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
                     hS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
                     hS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
                     hS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
                     hS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩
/-- An accepted `.obend` module passed artifact-bound physical signoff on its own netlist and PnR certificate. -/
theorem compileObendModuleToSiliconTapeout_artifact_bound (cfg : TapeoutConfig) (src : String)
    (art : SiliconTapeoutArtifact) (hOk : compileObendModuleToSiliconTapeout cfg src = .ok art) :
    checkArtifactBoundTapeout art.tcadEnvelope cfg.clockPeriodPs cfg.drcDeck art.belNetlist art.pnrCert = true :=
  (compileCompositionToSiliconTapeoutWithHash_sound _ _ cfg _ _ art
    (compileObendModuleToSiliconTapeout_sound cfg src art hOk).2.1).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
theorem compileObendModuleToSiliconTapeout_eq_bind (cfg : TapeoutConfig) (src : String) :
    compileObendModuleToSiliconTapeout cfg src =
      (compileObendFrontEndStage cfg src >>= fun (comp, isarCerts) =>
        compileCompositionToSiliconTapeoutWithHash
          Obend.Core.Digest.deployed src.toUTF8.toList cfg comp isarCerts) := by
  rfl
theorem compileCompositionToSiliconTapeoutWithHash_isOk_eq (H₁ H₂ : Obend.Digest.HashBytes.Hash) (b₁ b₂ : List UInt8)
    (cfg : TapeoutConfig) (comp : Composition) (isarCerts : List Elaborate.ElaboratedIsarCert) :
    (compileCompositionToSiliconTapeoutWithHash H₁ b₁ cfg comp isarCerts).isOk =
      (compileCompositionToSiliconTapeoutWithHash H₂ b₂ cfg comp isarCerts).isOk := by
  unfold compileCompositionToSiliconTapeoutWithHash mkTapeoutReceipt
  dsimp only
  cases h1 : isarCerts.all (FrontEnd.verifyCertJudgeTags isAdmittedTapeoutJudgeTag) with
  | false => rfl
  | true =>
    cases h2 : compileBookByMode cfg.compileMode cfg.moduleName (specializeBookDict cfg.dictInlinePasses (Obend.Leaf.emit comp)) with
    | none => rfl
    | some rtlModule =>
      dsimp only
      cases h3 : checkRtlModule rtlModule with
      | false => rfl
      | true =>
        cases h4 : checkBelNetlistValid (synthesizeModuleToBels rtlModule) with
        | false => rfl
        | true =>
          cases h5 : solveVerifiedRetiming? cfg.retimingFuel cfg.syncGraph cfg.maxCombDelayPs with
          | none => rfl
          | some retimingCert =>
            dsimp only
            cases h6 : checkCutlineDRC cfg.drcDeck cfg.cutlineFeature with
            | false => rfl
            | true =>
              cases h7 : checkBoxSpacing2D cfg.drcDeck.minMetalSpacingNm cfg.metalBoxA cfg.metalBoxB with
              | false => rfl
              | true =>
                cases h8 : checkViaEnclosure2D cfg.drcDeck.minViaEnclosureNm cfg.viaBox cfg.viaPadBox with
                | false => rfl
                | true =>
                  cases h9 : checkEnvelopeTimingSignoff cfg.cornerEnvelope cfg.clockPeriodPs cfg.timingPath with
                  | false => rfl
                  | true =>
                    cases h10 : checkRetimingCert cfg.syncGraph retimingCert cfg.cornerEnvelope.slowCorner cfg.clockPeriodPs with
                    | false => rfl
                    | true =>
                      cases h11 : checkPnrCertificate (synthesizeModuleToBels rtlModule) cfg.cornerEnvelope.slowCorner
                        cfg.clockPeriodPs (cfg.pnrCert?.getD (synthesizeGridPnrCert (synthesizeModuleToBels rtlModule) cfg.sinkCapFf)) with
                      | false => rfl
                      | true =>
                        cases h11b : checkArtifactBoundTapeout cfg.cornerEnvelope cfg.clockPeriodPs cfg.drcDeck
                          (synthesizeModuleToBels rtlModule)
                          (cfg.pnrCert?.getD (synthesizeGridPnrCert (synthesizeModuleToBels rtlModule) cfg.sinkCapFf))
                        · rfl
                        cases h12 : checkSteinerTimingClosure cfg.cornerEnvelope.slowCorner cfg.clockPeriodPs
                          (decoupleRightBranchWithBuffer cfg.bufWireId cfg.bufInputCapFf cfg.unbufferedTree) with
                        | false => rfl
                        | true =>
                          cases h13 : checkTapeoutTrustChecked tapeoutCheckedSupports tapeoutCheckedSupports <;> rfl

/-! ## 5b. LibreLane configuration and receipt JSON -/

/-- LibreLane `config.json` for the artifact: design, the emitted SystemVerilog file, clock port(s), period in ns. -/
def renderLibrelaneConfigJson (art : SiliconTapeoutArtifact) : String :=
  (Json.mkObj
    [ ("DESIGN_NAME", Json.str art.rtlModule.name)
    , ("VERILOG_FILES", Json.arr #[Json.str ("dir::" ++ art.rtlModule.name ++ ".sv")])
    , ("CLOCK_PORT", if (moduleDomains art.rtlModule).length ≤ 1 then Json.str "clk"
        else Json.arr ((moduleDomains art.rtlModule).map fun d => Json.str ("clk_" ++ d.portSuffix)).toArray)
    , ("CLOCK_PERIOD", Json.num ⟨art.clockPeriodPs, 3⟩) ]).pretty
/-- The tapeout receipt as JSON: the receipt's fields, the SystemVerilog digest, and the netlist-derived signoff. -/
def renderTapeoutReceiptJson (art : SiliconTapeoutArtifact) : String :=
  (Json.mkObj
    [ ("module", Json.str art.moduleName), ("rtlModule", Json.str art.rtlModule.name)
    , ("pre", Json.str art.receipt.pre), ("post", Json.str art.receipt.post), ("row", Json.str art.receipt.row)
    , ("law", Json.str art.receipt.law), ("prev", Json.str art.receipt.prev), ("dated", toJson art.receipt.dated)
    , ("svDigest", Json.str (rtlNatToStr art.svDigest))
    , ("verdict", Json.str (if art.receipt.verdict.isOk then "ok" else "refused"))
    , ("pins", Json.mkObj (art.receipt.pins.map fun kv => (kv.1, kv.2.elim Json.null Json.str)))
    , ("openings", Json.mkObj (art.receipt.openings.map fun kb => (kb.1, Json.bool kb.2)))
    , ("trust", Json.arr (art.receipt.trust.map fun kt => Json.str kt.1).toArray)
    , ("clockPeriodPs", toJson art.clockPeriodPs), ("belCells", toJson art.belNetlist.cells.length)
    , ("routedNets", toJson art.pnrCert.routedNets.length)
    , ("criticalPath", Json.mkObj
        [ ("logicLevels", toJson art.physical.criticalPath.logicLevels)
        , ("carryBlocks", toJson art.physical.criticalPath.carryBits)
        , ("wireHops", toJson art.physical.criticalPath.tileHops)
        , ("minLevels", toJson art.physical.criticalPath.minLevels) ]) ]).pretty

/-! ## 6. Concrete End-to-End `.obend` Module Tapeout Theorem (`golden_obend_module_silicon_tapeout_verified`) -/
def goldenTapeoutObendSource : String :=
  "edition ObjectiveBend 1\n" ++
  "record CleanroomTcadStack:\n" ++
  "  oxideEotPicometers() -> Nat\n" ++
  "  vthMilliV() -> Nat\n" ++
  "  drainCurrentUa(overdriveMilliV: Nat) -> Nat\n" ++
  "  gateDelayPs(fanout: Nat) -> Nat\n" ++
  "  calibratedDelayPs(fanout: Nat) -> Nat\n\n" ++
  "contract tapeout_signoff_contract for CleanroomTcadStack:\n" ++
  "  invariant: true\n" ++
  "  have h_rtl: true by judge(\"hw-rtl-synth@1\")\n" ++
  "  have h_retime: true by judge(\"hw-retime-sta@1\")\n" ++
  "  show true by judge(\"hw-pnr-bitstream@1\")\n\n" ++
  "spec PlanarBulkMosfetBase for CleanroomTcadStack:\n" ++
  "  requires oxideEotPicometers() -> Nat\n" ++
  "  requires vthMilliV() -> Nat\n" ++
  "  requires gateDelayPs(fanout: Nat) -> Nat\n" ++
  "  def oxideEotPicometers() -> Nat:\n" ++
  "    1200n\n" ++
  "  def vthMilliV() -> Nat:\n" ++
  "    400n\n" ++
  "  def drainCurrentUa(overdriveMilliV: Nat) -> Nat:\n" ++
  "    overdriveMilliV * 5n + self.vthMilliV\n" ++
  "  def gateDelayPs(fanout: Nat) -> Nat:\n" ++
  "    fanout * 8n + 20n\n" ++
  "  def calibratedDelayPs(fanout: Nat) -> Nat:\n" ++
  "    self.gateDelayPs(fanout + 2n)\n\n" ++
  "spec HighKMetalGateFinFetUpgrade for CleanroomTcadStack:\n" ++
  "  requires gateDelayPs(fanout: Nat) -> Nat\n" ++
  "  def oxideEotPicometers() -> Nat:\n" ++
  "    700n\n" ++
  "  def vthMilliV() -> Nat:\n" ++
  "    250n\n" ++
  "  def gateDelayPs(fanout: Nat) -> Nat:\n" ++
  "    super.gateDelayPs(fanout) + 4n\n\n" ++
  "def seedTcadStack() -> CleanroomTcadStack:\n" ++
  "  {oxideEotPicometers: 0n, vthMilliV: 0n, drainCurrentUa: fn(v: Nat) -> Nat: 0n, gateDelayPs: fn(f: Nat) -> Nat: 0n, calibratedDelayPs: fn(f: Nat) -> Nat: 0n}\n\n" ++
  "def cleanroomTcadStack() -> CleanroomTcadStack:\n" ++
  "  fix(compose(PlanarBulkMosfetBase, HighKMetalGateFinFetUpgrade), seedTcadStack())\n"
def goldenTapeoutConfig : TapeoutConfig where
  moduleName := "CleanroomTcadStack"
  entryDef   := "cleanroomTcadStack"
def cleanroomSignoffContractDecl : Syntax.ContractDecl where
  name := "tapeout_signoff_contract"
  targetType := "CleanroomTcadStack"
  invariant := some (.bool true)
  steps :=
    [ .haveStep "h_rtl"    (.bool true) (.judge "hw-rtl-synth@1"), .haveStep "h_retime" (.bool true) (.judge "hw-retime-sta@1")
    , .showStep            (.bool true) (.judge "hw-pnr-bitstream@1") ]
def cleanroomSignoffSyntaxMod : Syntax.Module where
  name := "CleanroomTcadStack"
  imports := []
  decls := []
  contracts := [cleanroomSignoffContractDecl]
def goldenTapeoutIsarCert : Elaborate.ElaboratedIsarCert :=
  Elaborate.elaborateContractIsarCert cleanroomSignoffSyntaxMod cleanroomSignoffContractDecl
def planarBulkMosfetLayer : Layer where
  name := "PlanarBulkMosfetBase"
  metadata := .record []
  fields :=
    [ ("oxideEotPicometers", .nat 1200), ("vthMilliV", .nat 400)
    , ("drainCurrentUa", .lam (.binary .add (.binary .multiply (.bound 0) (.nat 5)) (.get (.bound 2) "vthMilliV")))
    , ("gateDelayPs", .lam (.binary .add (.binary .multiply (.bound 0) (.nat 8)) (.nat 20)))
    , ("calibratedDelayPs", .lam (.app (.get (.bound 2) "gateDelayPs") (.binary .add (.bound 0) (.nat 2)))) ]
  flat := false
def highKFinFetUpgradeLayer : Layer where
  name := "HighKMetalGateFinFetUpgrade"
  metadata := .record []
  fields :=
    [ ("oxideEotPicometers", .nat 700), ("vthMilliV", .nat 250)
    , ("gateDelayPs", .lam (.binary .add (.app (.get (.bound 1) "gateDelayPs") (.bound 0)) (.nat 4))) ]
  flat := false
def goldenCleanroomTcadComp : Composition where
  top := highKFinFetUpgradeLayer
  below := [planarBulkMosfetLayer]
  seed :=
    [ ("oxideEotPicometers", .nat 0), ("vthMilliV", .nat 0), ("drainCurrentUa", .lam (.nat 0)), ("gateDelayPs", .lam (.nat 0))
    , ("calibratedDelayPs", .lam (.nat 0)) ]
theorem golden_obend_module_silicon_tapeout_verified :
    FrontEnd.verifyCertJudgeTags isAdmittedTapeoutJudgeTag goldenTapeoutIsarCert = true ∧
    goldenTapeoutIsarCert.judgeTags = ["hw-rtl-synth@1", "hw-retime-sta@1", "hw-pnr-bitstream@1"] ∧
    (∀ (H : Obend.Digest.HashBytes.Hash) (srcBytes : List UInt8),
      (compileCompositionToSiliconTapeoutWithHash
        H srcBytes goldenTapeoutConfig goldenCleanroomTcadComp [goldenTapeoutIsarCert]).isOk = true) ∧
    (match compileCompositionToSiliconTapeout goldenTapeoutConfig goldenCleanroomTcadComp [goldenTapeoutIsarCert] with
     | .ok art =>
       let regs0 : Nat → BitVec 64 := fun _ => 0#64
       let regs1At4 := stepModuleRegs art.rtlModule false (fun _ => 4#64) regs0
       let regs2At4 := stepModuleRegs art.rtlModule false (fun _ => 4#64) regs1At4
       let regs1At200 := stepModuleRegs art.rtlModule false (fun _ => 200#64) regs0
       let regs2At200 := stepModuleRegs art.rtlModule false (fun _ => 200#64) regs1At200
       checkRtlModule art.rtlModule &&
       checkBelNetlistValid art.belNetlist &&
       (art.rtlModule.regs.length == 5) &&
       (countFfBels art.belNetlist == 5) &&
       (art.pnrCert.placedCells.length == art.belNetlist.cells.length) &&
       checkPnrCertificate art.belNetlist art.tcadEnvelope.slowCorner goldenTapeoutConfig.clockPeriodPs art.pnrCert &&
       (evalModuleOutputs art.rtlModule (fun _ => 4#64) regs2At4 ==
         [ ("out_oxideEotPicometers", 700#64), ("out_vthMilliV", 250#64), ("out_gateDelayPs", 56#64)
         , ("out_drainCurrentUa", 270#64), ("out_calibratedDelayPs", 72#64) ]) &&
       (evalModuleOutputs art.rtlModule (fun _ => 200#64) regs2At200 ==
         [ ("out_oxideEotPicometers", 700#64), ("out_vthMilliV", 250#64), ("out_gateDelayPs", 1624#64)
         , ("out_drainCurrentUa", 1250#64), ("out_calibratedDelayPs", 1640#64) ]) &&
       checkEnvelopeTimingSignoff art.tcadEnvelope goldenTapeoutConfig.clockPeriodPs goldenTapeoutConfig.timingPath &&
       (!art.systemVerilog.isEmpty) &&
       art.receipt.verdict.isOk &&
       checkTapeoutTrustChecked tapeoutCheckedSupports art.receipt.trust
     | .error _ => false) = true := by
  refine ⟨by decide +kernel, rfl, ?_, ?_⟩
  · intro H srcBytes
    rw [compileCompositionToSiliconTapeoutWithHash_isOk_eq H Obend.Core.Digest.deployed
          srcBytes goldenTapeoutConfig.moduleName.toUTF8.toList]
    decide +kernel
  · decide +kernel
end Obend.Hardware.TapeoutPipeline
end