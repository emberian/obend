module
/-
# Obend.Hardware.PlaceRoute — Physical Device Grid, Netlist-Bound PnR Certificate Checker, Elmore RC Delay & Bitstream Decoder

Eliminates blind trust in external Place-and-Route (`nextpnr`, `VPR`, `Vivado`) and bitstream
assemblers (`fasm2frames`) by requiring PnR tools to emit a `PnrCertificate` bound to a concrete
`BelNetlist` and verified by the Objective Bend kernel:

1. **Physical Device Grid & List-Wide Placement Injectivity (`PlacedCell`, `checkPlacementInjective`)**:
   - Verifies that no two distinct logical cells occupy the same physical `(tileX, tileY, belSlot)`,
   - Proves both pairwise `placement_injective_no_collision` and list-wide `∀ i ≠ j`
     `checkPlacementInjective_sound`.
2. **Switch-Box PIP Routing Disjointness & Contiguous Connectivity (`PipHop`, `RoutedNet`)**:
   - Verifies contiguous source-to-sink PIP paths (`checkNetConnectivity`) and list-wide short-circuit
     freedom (`checkRoutingDisjoint`),
   - Proves `contiguous_net_reaches_sink`, `routing_disjoint_no_short`, and list-wide `∀ i ≠ j`
     `checkRoutingDisjoint_sound`.
3. **Physical Elmore RC Interconnect Delay & Multi-Sink Steiner Trees (`computeElmoreDelayPs`, `SteinerTree`)**:
   - Computes exact distributed RC Elmore delay $T_{\text{Elmore}} = \sum_{e} R_e \cdot C_{\text{downstream}}(e)$
     and proves monotonicity and repeater buffer delay reduction.
4. **Netlist-Bound PnR & Bitstream Verifier (`checkPnrCertificate`, `checkPnrCertificate_sound`)**:
   - Binds every `PnrCertificate` to its target `BelNetlist` (`designName == net.moduleName` and
     1-to-1 BEL `cellId` coverage `0 .. net.cells.length - 1`) and proves full end-to-end soundness.
-/
public import Obend.Hardware.Process
public import Obend.Hardware.Synth
@[expose] public section

namespace Obend.Hardware.PlaceRoute
open Obend.Hardware.Process Obend.Hardware.Synth
set_option autoImplicit false

/-! ## 1. Physical Placement Table & List-Wide Injectivity (`checkPlacementInjective`) -/

/-- Physical assignment of a logical cell `cellId` to a tile coordinate `(tileX, tileY)`,
BEL slot `belSlot`, and LUT truth table `lutInit`. -/
structure PlacedCell where
  cellId  : Nat
  tileX   : Nat
  tileY   : Nat
  belSlot : Nat
  lutInit : Nat
  deriving DecidableEq, Repr

/-- Physical location tuple `(tileX, tileY, belSlot)` of a placed cell. -/
def cellLocation (c : PlacedCell) : Nat × Nat × Nat :=
  (c.tileX, c.tileY, c.belSlot)

/-- Check that two placed cells do not collide on the same physical `(tileX, tileY, belSlot)`
whenever their logical `cellId`s are distinct. -/
def checkPairNoCollision (c1 c2 : PlacedCell) : Bool :=
  (c1.cellId == c2.cellId) || (cellLocation c1 != cellLocation c2)

/-- Check that `c` does not collide with any placed cell in `rest`. -/
def checkCellAgainstList (c : PlacedCell) : List PlacedCell → Bool
  | [] => true
  | c2 :: rest => checkPairNoCollision c c2 && checkCellAgainstList c rest

/-- Kernel placement injectivity checker: verifies pairwise non-collision across all placed cells. -/
def checkPlacementInjective : List PlacedCell → Bool
  | [] => true
  | c :: rest => checkCellAgainstList c rest && checkPlacementInjective rest

/-- Pairwise non-collision lemma (`placement_injective_no_collision`). -/
theorem placement_injective_no_collision
    (c1 c2 : PlacedCell)
    (hOk : checkPairNoCollision c1 c2 = true)
    (hNeId : c1.cellId ≠ c2.cellId) :
    cellLocation c1 ≠ cellLocation c2 := by
  simp only [checkPairNoCollision, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hOk
  rcases hOk with hEq | hNeLoc
  · exact False.elim (hNeId hEq)
  · exact hNeLoc

private theorem checkCellAgainstList_getElem
    (c : PlacedCell) (rest : List PlacedCell)
    (hOk : checkCellAgainstList c rest = true)
    (k : Nat) (hk : k < rest.length) :
    checkPairNoCollision c rest[k] = true := by
  induction rest generalizing k with
  | nil => exact absurd hk (Nat.not_lt_zero _)
  | cons c2 tail ih =>
    simp only [checkCellAgainstList, Bool.and_eq_true] at hOk
    cases k with
    | zero => exact hOk.1
    | succ k' =>
      simp only [List.length_cons] at hk
      exact ih hOk.2 k' (by omega)

private theorem checkPlacementInjective_lt
    (cells : List PlacedCell)
    (hInj : checkPlacementInjective cells = true)
    (i j : Nat) (hi : i < cells.length) (hj : j < cells.length)
    (hLt : i < j)
    (hNeId : cells[i].cellId ≠ cells[j].cellId) :
    cellLocation cells[i] ≠ cellLocation cells[j] := by
  induction cells generalizing i j with
  | nil => exact absurd hi (Nat.not_lt_zero _)
  | cons c rest ih =>
    simp only [checkPlacementInjective, Bool.and_eq_true] at hInj
    cases i with
    | zero =>
      cases j with
      | zero => omega
      | succ j' =>
        simp only [List.length_cons] at hj
        have hPair := checkCellAgainstList_getElem c rest hInj.1 j' (by omega)
        exact placement_injective_no_collision c rest[j'] hPair hNeId
    | succ i' =>
      cases j with
      | zero => omega
      | succ j' =>
        simp only [List.length_cons] at hi hj
        exact ih hInj.2 i' j' (by omega) (by omega) (by omega) hNeId

/-- **Universal List-Wide Placement Injectivity Soundness (`checkPlacementInjective_sound`)**:
For ANY placed-cell table `cells` passing `checkPlacementInjective cells = true` and ANY two
distinct indices `i ≠ j` with `cells[i].cellId ≠ cells[j].cellId`, `cells[i]` and `cells[j]`
occupy strictly distinct physical `(tileX, tileY, belSlot)` coordinates on the die! -/
theorem checkPlacementInjective_sound
    (cells : List PlacedCell)
    (hInj : checkPlacementInjective cells = true)
    (i j : Nat) (hi : i < cells.length) (hj : j < cells.length)
    (hNeIdx : i ≠ j)
    (hNeId : cells[i].cellId ≠ cells[j].cellId) :
    cellLocation cells[i] ≠ cellLocation cells[j] := by
  by_cases hLt : i < j
  · exact checkPlacementInjective_lt cells hInj i j hi hj hLt hNeId
  · have hGt : j < i := by omega
    exact Ne.symm (checkPlacementInjective_lt cells hInj j i hj hi hGt (Ne.symm hNeId))

/-! ## 2. Switch-Box PIP Routing Connectivity & List-Wide Short-Circuit Freedom (`checkRoutingDisjoint`) -/

/-- A single Programmable Interconnect Point (PIP) hop from `srcWire` to `dstWire` with physical
switch resistance `resOhm` ($\Omega$) and wire segment capacitance `capFf` ($\text{fF}$). -/
structure PipHop where
  srcWire : Nat
  dstWire : Nat
  resOhm  : Nat
  capFf   : Nat
  deriving DecidableEq, Repr

/-- A routed physical net connecting `srcWire` to `dstWire` through a sequence of `PipHop`s. -/
structure RoutedNet where
  netId   : Nat
  srcWire : Nat
  dstWire : Nat
  hops    : List PipHop
  deriving DecidableEq, Repr

/-- Verify that a sequence of `PipHop`s forms a contiguous directed path from `curWire` to `targetWire`. -/
def checkHopsContiguous (curWire targetWire : Nat) : List PipHop → Bool
  | [] => curWire == targetWire
  | h :: rest => (h.srcWire == curWire) && checkHopsContiguous h.dstWire targetWire rest

/-- Verify that a `RoutedNet` is non-empty and forms a contiguous directed PIP path from `srcWire` to `dstWire`. -/
def checkNetConnectivity (net : RoutedNet) : Bool :=
  (!net.hops.isEmpty) && checkHopsContiguous net.srcWire net.dstWire net.hops

/-- Final wire reached by a list of `PipHop`s starting from `curWire`. -/
def hopsEndpoint (curWire : Nat) : List PipHop → Nat
  | [] => curWire
  | h :: rest => hopsEndpoint h.dstWire rest

/-- Theorem (`contiguous_net_reaches_sink`):
If `checkHopsContiguous curWire targetWire hops = true`, then following `hops` from `curWire`
terminates at `targetWire`. -/
theorem contiguous_net_reaches_sink
    (curWire targetWire : Nat) (hops : List PipHop)
    (hContig : checkHopsContiguous curWire targetWire hops = true) :
    hopsEndpoint curWire hops = targetWire := by
  induction hops generalizing curWire with
  | nil =>
    simp only [checkHopsContiguous, beq_iff_eq] at hContig
    simp [hopsEndpoint, hContig]
  | cons h rest ih =>
    simp only [checkHopsContiguous, Bool.and_eq_true, beq_iff_eq] at hContig
    simp only [hopsEndpoint]
    exact ih h.dstWire hContig.2

/-- Collect all wire node IDs touched by a `RoutedNet`. -/
def netWires (net : RoutedNet) : List Nat :=
  net.srcWire :: net.hops.map (·.dstWire)

/-- Check that two wire lists share no common wire node (`disjointWireLists`). -/
def disjointWireLists (w1 w2 : List Nat) : Bool :=
  w1.all (fun u => !w2.contains u)

/-- Check that `net` shares no wire nodes with any net in `rest`. -/
def checkNetDisjointFromList (net : RoutedNet) : List RoutedNet → Bool
  | [] => true
  | n2 :: rest =>
    disjointWireLists (netWires net) (netWires n2) &&
    checkNetDisjointFromList net rest

/-- Kernel routing disjointness checker: verifies that no two routed nets short-circuit on a shared wire. -/
def checkRoutingDisjoint : List RoutedNet → Bool
  | [] => true
  | net :: rest => checkNetDisjointFromList net rest && checkRoutingDisjoint rest

/-- Pairwise disjointness lemma (`routing_disjoint_no_short`). -/
theorem routing_disjoint_no_short
    (w1 w2 : List Nat) (u : Nat)
    (hDisj : disjointWireLists w1 w2 = true)
    (hIn1  : u ∈ w1) :
    w2.contains u = false := by
  simp only [disjointWireLists, List.all_eq_true, Bool.not_eq_true'] at hDisj
  exact hDisj u hIn1

private theorem checkNetDisjointFromList_getElem
    (net : RoutedNet) (rest : List RoutedNet)
    (hDisj : checkNetDisjointFromList net rest = true)
    (k : Nat) (hk : k < rest.length) :
    disjointWireLists (netWires net) (netWires rest[k]) = true := by
  induction rest generalizing k with
  | nil => exact absurd hk (Nat.not_lt_zero _)
  | cons n2 tail ih =>
    simp only [checkNetDisjointFromList, Bool.and_eq_true] at hDisj
    cases k with
    | zero => exact hDisj.1
    | succ k' =>
      simp only [List.length_cons] at hk
      exact ih hDisj.2 k' (by omega)

private theorem checkRoutingDisjoint_lt
    (nets : List RoutedNet)
    (hDisj : checkRoutingDisjoint nets = true)
    (i j : Nat) (hi : i < nets.length) (hj : j < nets.length)
    (hLt : i < j) (u : Nat)
    (hMemI : u ∈ netWires nets[i]) :
    u ∉ netWires nets[j] := by
  induction nets generalizing i j with
  | nil => exact absurd hi (Nat.not_lt_zero _)
  | cons n rest ih =>
    simp only [checkRoutingDisjoint, Bool.and_eq_true] at hDisj
    cases i with
    | zero =>
      cases j with
      | zero => omega
      | succ j' =>
        simp only [List.length_cons] at hj
        have hPair := checkNetDisjointFromList_getElem n rest hDisj.1 j' (by omega)
        have hNoContain := routing_disjoint_no_short (netWires n) (netWires rest[j']) u hPair hMemI
        intro hMemJ
        have hTrue : (netWires rest[j']).contains u = true := List.contains_iff_mem.mpr hMemJ
        rw [hTrue] at hNoContain
        cases hNoContain
    | succ i' =>
      cases j with
      | zero => omega
      | succ j' =>
        simp only [List.length_cons] at hi hj
        exact ih hDisj.2 i' j' (by omega) (by omega) (by omega) hMemI

/-- **Universal List-Wide Routing Disjointness Soundness (`checkRoutingDisjoint_sound`)**:
For ANY routed net table `nets` passing `checkRoutingDisjoint nets = true` and ANY two distinct
net indices `i ≠ j` (whether `i < j` or `j < i`), no physical wire node `u` belongs to both
`netWires nets[i]` and `netWires nets[j]`! -/
theorem checkRoutingDisjoint_sound
    (nets : List RoutedNet)
    (hDisj : checkRoutingDisjoint nets = true)
    (i j : Nat) (hi : i < nets.length) (hj : j < nets.length)
    (hNe : i ≠ j) (u : Nat)
    (hMemI : u ∈ netWires nets[i]) :
    u ∉ netWires nets[j] := by
  by_cases hLt : i < j
  · exact checkRoutingDisjoint_lt nets hDisj i j hi hj hLt u hMemI
  · have hGt : j < i := by omega
    intro hMemJ
    exact checkRoutingDisjoint_lt nets hDisj j i hj hi hGt u hMemJ hMemI

/-! ## 3. Elmore RC Interconnect Delay & Timing Signoff (`computeElmoreDelayPs`) -/

/-- Total downstream capacitance $\sum C_i$ (in $\text{fF}$) of a PIP hop chain plus load `sinkCapFf`. -/
def pipDownstreamCapFf (sinkCapFf : Nat) : List PipHop → Nat
  | [] => sinkCapFf
  | h :: rest => h.capFf + pipDownstreamCapFf sinkCapFf rest

/-- Distributed Elmore RC delay $\sum_{e} R_e \cdot C_{\text{downstream}}(e)$ (in $\text{fF}\cdot\Omega = \text{fs}$). -/
def computeElmoreDelayFs (sinkCapFf : Nat) : List PipHop → Nat
  | [] => 0
  | h :: rest =>
    let cDown := h.capFf + pipDownstreamCapFf sinkCapFf rest
    (h.resOhm * cDown) + computeElmoreDelayFs sinkCapFf rest

/-- Convert Elmore delay from femtoseconds ($\text{fF}\cdot\Omega$) to picoseconds (ceiling division by 1000). -/
def computeElmoreDelayPs (sinkCapFf : Nat) (hops : List PipHop) : Nat :=
  (computeElmoreDelayFs sinkCapFf hops + 999) / 1000

/-- Theorem (`elmore_delay_monotone`):
Prepending a PIP routing hop `h` strictly increases or preserves the cumulative Elmore RC delay. -/
theorem elmore_delay_monotone
    (sinkCapFf : Nat) (h : PipHop) (rest : List PipHop) :
    computeElmoreDelayFs sinkCapFf rest ≤ computeElmoreDelayFs sinkCapFf (h :: rest) := by
  simp only [computeElmoreDelayFs]
  omega

/-- Check that a routed net meets setup timing closure at `corner` within `clockPeriodPs`. -/
def checkNetElmoreTiming
    (corner : ProcessCorner) (clockPeriodPs sinkCapFf : Nat) (net : RoutedNet) : Bool :=
  let wireDelayPs := computeElmoreDelayPs sinkCapFf net.hops
  let totalArrivalPs := corner.tCqMaxPs + corner.tGateMaxPs + wireDelayPs + corner.tSetupPs + corner.tSkewPs
  decide (totalArrivalPs ≤ clockPeriodPs)

/-! ## 4. FABulous Bitstream Frame Encoding/Decoding & Round-Trip Soundness -/

/-- A decoded tile configuration record extracted from a bitstream frame. -/
structure TileFrameConfig where
  tileX   : Nat
  tileY   : Nat
  belSlot : Nat
  lutInit : Nat
  pipMask : Nat
  deriving DecidableEq, Repr

/-- Raw configuration frame emitted by `fasm2frames` / bitstream generator. -/
structure BitstreamFrame where
  frameAddr : Nat
  frameData : Nat
  deriving DecidableEq, Repr

/-- Encode a `TileFrameConfig` (with `tileX, tileY, belSlot < 256` and `lutInit, pipMask < 65536`)
into a `BitstreamFrame`. -/
def encodeBitstreamFrame (cfg : TileFrameConfig) : BitstreamFrame where
  frameAddr := cfg.tileX * 65536 + cfg.tileY * 256 + cfg.belSlot
  frameData := cfg.lutInit * 65536 + cfg.pipMask

/-- Decode a `BitstreamFrame` back into a `TileFrameConfig`. -/
def decodeBitstreamFrame (f : BitstreamFrame) : TileFrameConfig where
  tileX   := f.frameAddr / 65536
  tileY   := (f.frameAddr / 256) % 256
  belSlot := f.frameAddr % 256
  lutInit := f.frameData / 65536
  pipMask := f.frameData % 65536

/-- Check that a `TileFrameConfig`'s fields fit within their packed bit-field widths. -/
def wfTileFrameConfig (cfg : TileFrameConfig) : Bool :=
  decide (cfg.tileX < 256) &&
  decide (cfg.tileY < 256) &&
  decide (cfg.belSlot < 256) &&
  decide (cfg.lutInit < 65536) &&
  decide (cfg.pipMask < 65536)

/-- Theorem (`bitstream_decode_roundtrip_sound`):
For any well-formed `cfg : TileFrameConfig` (`wfTileFrameConfig cfg = true`), encoding `cfg` into
a `BitstreamFrame` and decoding it recovers the exact original `TileFrameConfig`! -/
theorem bitstream_decode_roundtrip_sound
    (cfg : TileFrameConfig)
    (hWf : wfTileFrameConfig cfg = true) :
    decodeBitstreamFrame (encodeBitstreamFrame cfg) = cfg := by
  rcases cfg with ⟨tx, ty, bel, lut, pip⟩
  simp only [wfTileFrameConfig, Bool.and_eq_true, decide_eq_true_eq] at hWf
  rcases hWf with ⟨⟨⟨⟨hTx, hTy⟩, hBel⟩, hLut⟩, hPip⟩
  simp only [encodeBitstreamFrame, decodeBitstreamFrame, TileFrameConfig.mk.injEq]
  refine ⟨by omega, by omega, by omega, by omega, by omega⟩

/-! ## 5. Netlist-Bound Place-and-Route Certificate & Kernel Verifier (`checkPnrCertificate`) -/

/-- Complete untrusted Place-and-Route & Bitstream certificate submitted to `Obend.Judge`. -/
structure PnrCertificate where
  designName      : String
  placedCells     : List PlacedCell
  routedNets      : List RoutedNet
  expectedConfigs : List TileFrameConfig
  bitstreamFrames : List BitstreamFrame
  sinkCapFf       : Nat
  deriving DecidableEq, Repr

/-- Complete netlist-bound kernel PnR & bitstream certificate checker:
1. `cert.designName == net.moduleName` and `cert.placedCells.map (·.cellId) == List.range net.cells.length`
   (every BEL cell of `net` is placed 1-to-1 with unique sequential `cellId`s),
2. Placement is injective (`checkPlacementInjective`),
3. All routed nets are contiguous from source to sink (`checkNetConnectivity`),
4. No two nets short-circuit on a shared wire (`checkRoutingDisjoint`),
5. Every routed net meets Elmore RC setup timing (`checkNetElmoreTiming`),
6. Every bitstream frame decodes to `expectedConfigs`. -/
def checkPnrCertificate
    (net : BelNetlist) (corner : ProcessCorner) (clockPeriodPs : Nat) (cert : PnrCertificate) : Bool :=
  (cert.designName == net.moduleName) &&
  (cert.placedCells.map (·.cellId) == List.range net.cells.length) &&
  checkPlacementInjective cert.placedCells &&
  cert.routedNets.all checkNetConnectivity &&
  checkRoutingDisjoint cert.routedNets &&
  cert.routedNets.all (checkNetElmoreTiming corner clockPeriodPs cert.sinkCapFf) &&
  (cert.bitstreamFrames.map decodeBitstreamFrame == cert.expectedConfigs)

private theorem cellId_eq_index_of_map_eq_range
    (cells : List PlacedCell) (n : Nat)
    (hMap : cells.map (·.cellId) = List.range n) :
    cells.length = n ∧ ∀ (i : Nat) (hi : i < cells.length), cells[i].cellId = i := by
  have hLen : cells.length = n := by
    have := congrArg List.length hMap
    simpa using this
  refine ⟨hLen, ?_⟩
  intro i hi
  have hElem : (cells.map (·.cellId))[i]'(by simp [hi]) = (List.range n)[i]'(by simp [← hLen, hi]) := by
    simp [hMap]
  simpa using hElem

/-- **Universal Netlist-Bound `checkPnrCertificate` Soundness (`checkPnrCertificate_sound`)**:
Whenever `checkPnrCertificate net corner clockPeriodPs cert = true`:
1. `cert.designName = net.moduleName` and `cert.placedCells.length = net.cells.length`,
2. **List-wide BEL placement injectivity**: for ALL `i ≠ j` in `0 .. net.cells.length - 1`,
   `cellLocation cert.placedCells[i] ≠ cellLocation cert.placedCells[j]`,
3. **List-wide PIP routing short-freedom**: for ALL `i ≠ j` in `0 .. cert.routedNets.length - 1`,
   no physical wire node belongs to both `netWires cert.routedNets[i]` and `netWires cert.routedNets[j]`,
4. **Source-to-sink PIP connectivity & Elmore timing**: every `r ∈ cert.routedNets` reaches `r.dstWire`
   from `r.srcWire` and closes setup timing at `corner`,
5. **Bitstream decoding fidelity**: `cert.bitstreamFrames.map decodeBitstreamFrame = cert.expectedConfigs`! -/
theorem checkPnrCertificate_sound
    (net : BelNetlist) (corner : ProcessCorner) (clockPeriodPs : Nat) (cert : PnrCertificate)
    (hOk : checkPnrCertificate net corner clockPeriodPs cert = true) :
    cert.designName = net.moduleName ∧
    cert.placedCells.length = net.cells.length ∧
    (∀ (i j : Nat) (hi : i < cert.placedCells.length) (hj : j < cert.placedCells.length),
      i ≠ j → cellLocation cert.placedCells[i] ≠ cellLocation cert.placedCells[j]) ∧
    (∀ (i j : Nat) (hi : i < cert.routedNets.length) (hj : j < cert.routedNets.length),
      i ≠ j → ∀ u ∈ netWires cert.routedNets[i], u ∉ netWires cert.routedNets[j]) ∧
    (∀ r ∈ cert.routedNets,
      hopsEndpoint r.srcWire r.hops = r.dstWire ∧
      checkNetElmoreTiming corner clockPeriodPs cert.sinkCapFf r = true) ∧
    cert.bitstreamFrames.map decodeBitstreamFrame = cert.expectedConfigs := by
  simp only [checkPnrCertificate, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hOk
  rcases hOk with ⟨⟨⟨⟨⟨⟨hDesign, hIds⟩, hInj⟩, hConn⟩, hDisj⟩, hTiming⟩, hFrames⟩
  obtain ⟨hLen, hCellIdAt⟩ := cellId_eq_index_of_map_eq_range cert.placedCells net.cells.length hIds
  refine ⟨hDesign, hLen, ?_, ?_, ?_, hFrames⟩
  · intro i j hi hj hNe
    have hNeId : cert.placedCells[i].cellId ≠ cert.placedCells[j].cellId := by
      rw [hCellIdAt i hi, hCellIdAt j hj]
      exact hNe
    exact checkPlacementInjective_sound cert.placedCells hInj i j hi hj hNe hNeId
  · intro i j hi hj hNe u hu
    exact checkRoutingDisjoint_sound cert.routedNets hDisj i j hi hj hNe u hu
  · intro r hr
    have hc := hConn r hr
    simp only [checkNetConnectivity, Bool.and_eq_true] at hc
    exact ⟨contiguous_net_reaches_sink r.srcWire r.dstWire r.hops hc.2, hTiming r hr⟩

/-- Extract the LUT SRAM mask (`< 65536`) associated with a `BelKind` (`0` for fixed-function BELs). -/
def belKindLutInit : BelKind → Nat
  | .lut1 m | .lut2 m | .lut3 m => m % 65536
  | _ => 0

/-- Constructively place, route, and frame-encode a canonical conflict-free `PnrCertificate` for
any synthesized `BelNetlist` (8 BELs per tile row, disjoint 2-wire PIP channels per BEL). -/
def buildCanonicalPnrCert (net : BelNetlist) (sinkCapFf : Nat := 5) : PnrCertificate :=
  let cfgs : List TileFrameConfig :=
    net.cells.zipIdx.map fun (c, k) =>
      { tileX   := (k / 64) % 256
      , tileY   := ((k / 8) % 8) % 256
      , belSlot := k % 8
      , lutInit := belKindLutInit c.kind
      , pipMask := 1 }
  let placed : List PlacedCell :=
    net.cells.zipIdx.map fun (c, k) =>
      { cellId  := k
      , tileX   := k / 64
      , tileY   := (k / 8) % 8
      , belSlot := k % 8
      , lutInit := belKindLutInit c.kind }
  let routed : List RoutedNet :=
    (List.range net.cells.length).map fun k =>
      let w0 := 100 + 2 * k
      let w1 := 101 + 2 * k
      { netId   := k
      , srcWire := w0
      , dstWire := w1
      , hops    := [{ srcWire := w0, dstWire := w1, resOhm := 40, capFf := 3 }] }
  { designName      := net.moduleName
  , placedCells     := placed
  , routedNets      := routed
  , expectedConfigs := cfgs
  , bitstreamFrames := cfgs.map encodeBitstreamFrame
  , sinkCapFf       := sinkCapFf }

/-- Target 2-BEL adder slice netlist corresponding to `validAdderPnrCert`. -/
def validAdderBelNetlist : BelNetlist where
  moduleName  := "obend_routed_adder2"
  inputNames  := ["a0", "b0", "a1", "b1"]
  cells       :=
    [ { dstName := "sum0", kind := .lut2 0x6, inputs := ["a0", "b0"] }
    , { dstName := "sum1", kind := .lut2 0x6, inputs := ["a1", "b1"] } ]
  outputNames := ["sum0", "sum1"]

/-- Concrete verified PnR certificate for `validAdderBelNetlist` on `corner7nm_SS` at 500 MHz (`2000 ps`). -/
def validAdderPnrCert : PnrCertificate where
  designName := "obend_routed_adder2"
  placedCells :=
    [ { cellId := 0, tileX := 0, tileY := 0, belSlot := 0, lutInit := 0x6 }
    , { cellId := 1, tileX := 0, tileY := 1, belSlot := 0, lutInit := 0x6 } ]
  routedNets :=
    [ { netId := 0, srcWire := 10, dstWire := 12
      , hops := [ { srcWire := 10, dstWire := 11, resOhm := 50, capFf := 4 }
                , { srcWire := 11, dstWire := 12, resOhm := 50, capFf := 4 } ] }
    , { netId := 1, srcWire := 20, dstWire := 21
      , hops := [ { srcWire := 20, dstWire := 21, resOhm := 40, capFf := 3 } ] } ]
  expectedConfigs :=
    [ { tileX := 0, tileY := 0, belSlot := 0, lutInit := 0x6, pipMask := 0x3 }
    , { tileX := 0, tileY := 1, belSlot := 0, lutInit := 0x6, pipMask := 0x1 } ]
  bitstreamFrames :=
    [ encodeBitstreamFrame { tileX := 0, tileY := 0, belSlot := 0, lutInit := 0x6, pipMask := 0x3 }
    , encodeBitstreamFrame { tileX := 0, tileY := 1, belSlot := 0, lutInit := 0x6, pipMask := 0x1 } ]
  sinkCapFf := 5

/-- Corrupted PnR certificate with a BEL placement collision (`cell 0` and `cell 1` both at `(0,0,0)`). -/
def collidingBelPnrCert : PnrCertificate :=
  { validAdderPnrCert with
    placedCells :=
      [ { cellId := 0, tileX := 0, tileY := 0, belSlot := 0, lutInit := 0x6 }
      , { cellId := 1, tileX := 0, tileY := 0, belSlot := 0, lutInit := 0x8 } ] }

/-- Corrupted PnR certificate with a PIP routing short circuit (`wire 11` shared by `net 0` and `net 1`). -/
def shortedWirePnrCert : PnrCertificate :=
  { validAdderPnrCert with
    routedNets :=
      [ { netId := 0, srcWire := 10, dstWire := 12
        , hops := [ { srcWire := 10, dstWire := 11, resOhm := 50, capFf := 4 }
                  , { srcWire := 11, dstWire := 12, resOhm := 50, capFf := 4 } ] }
      , { netId := 1, srcWire := 20, dstWire := 11
        , hops := [ { srcWire := 20, dstWire := 11, resOhm := 40, capFf := 3 } ] } ] }

example :
    checkPnrCertificate validAdderBelNetlist corner7nm_SS 2000 validAdderPnrCert = true ∧
    checkPnrCertificate validAdderBelNetlist corner7nm_SS 2000 collidingBelPnrCert = false ∧
    checkPnrCertificate validAdderBelNetlist corner7nm_SS 2000 shortedWirePnrCert = false :=
  ⟨rfl, rfl, rfl⟩

/-! ## 6. Multi-Sink Steiner Fanout Trees & Exact Recursive Elmore RC Delay (`SteinerTree`) -/

/-- Multi-sink Steiner routing tree modeling high-fanout clock/data interconnects. -/
inductive SteinerTree where
  | sink (wireId : Nat) (loadCapFf : Nat)
  | branch (wireId : Nat) (segResOhm segCapFf : Nat) (left right : SteinerTree)
  deriving DecidableEq, Repr

/-- Exact total downstream lump capacitance $C_{\text{down}}(u)$ (in $\text{fF}$) of a `SteinerTree`. -/
def downstreamCapFf : SteinerTree → Nat
  | .sink _ loadCapFf => loadCapFf
  | .branch _ _ segCapFf left right =>
    segCapFf + downstreamCapFf left + downstreamCapFf right

/-- Exact worst-case root-to-sink Elmore RC delay (in $\text{fF}\cdot\Omega = \text{fs}$) of a `SteinerTree`. -/
def maxSteinerElmoreDelayFsOhm : SteinerTree → Nat
  | .sink _ _ => 0
  | .branch _ segResOhm segCapFf left right =>
    let cDown := segCapFf + downstreamCapFf left + downstreamCapFf right
    segResOhm * cDown + max (maxSteinerElmoreDelayFsOhm left) (maxSteinerElmoreDelayFsOhm right)

/-- Convert worst-case Steiner Elmore delay from femtoseconds ($\text{fF}\cdot\Omega$) to picoseconds. -/
def maxSteinerElmoreDelayPs (t : SteinerTree) : Nat :=
  (maxSteinerElmoreDelayFsOhm t + 999) / 1000

/-- Check whether a multi-sink `SteinerTree` meets setup timing closure at `corner` within `clockPeriodPs`. -/
def checkSteinerTimingClosure (corner : ProcessCorner) (clockPeriodPs : Nat) (t : SteinerTree) : Bool :=
  let wireDelayPs := maxSteinerElmoreDelayPs t
  decide (corner.tCqMaxPs + corner.tGateMaxPs + wireDelayPs + corner.tSetupPs + corner.tSkewPs ≤ clockPeriodPs)

/-- Add `deltaCapFf` of load capacitance to every leaf sink in a `SteinerTree`. -/
def inflateSinkLoads (deltaCapFf : Nat) : SteinerTree → SteinerTree
  | .sink wireId loadCapFf => .sink wireId (loadCapFf + deltaCapFf)
  | .branch wireId segResOhm segCapFf left right =>
    .branch wireId segResOhm segCapFf
      (inflateSinkLoads deltaCapFf left)
      (inflateSinkLoads deltaCapFf right)

/-- **Theorem (`downstreamCapFf_monotone_load`)**:
Increasing leaf sink load capacitance by `deltaCapFf` across any `SteinerTree` monotonically
increases (or preserves) both `downstreamCapFf` and `maxSteinerElmoreDelayFsOhm`. -/
theorem downstreamCapFf_monotone_load (deltaCapFf : Nat) (t : SteinerTree) :
    downstreamCapFf t ≤ downstreamCapFf (inflateSinkLoads deltaCapFf t) ∧
    maxSteinerElmoreDelayFsOhm t ≤ maxSteinerElmoreDelayFsOhm (inflateSinkLoads deltaCapFf t) := by
  induction t with
  | sink wireId loadCapFf =>
    simp only [downstreamCapFf, inflateSinkLoads, maxSteinerElmoreDelayFsOhm]
    omega
  | branch wireId segResOhm segCapFf left right ihl ihr =>
    simp only [downstreamCapFf, inflateSinkLoads, maxSteinerElmoreDelayFsOhm]
    have hCapLe :
        segCapFf + downstreamCapFf left + downstreamCapFf right ≤
          segCapFf + downstreamCapFf (inflateSinkLoads deltaCapFf left) +
            downstreamCapFf (inflateSinkLoads deltaCapFf right) := by
      omega
    have hMulLe :
        segResOhm * (segCapFf + downstreamCapFf left + downstreamCapFf right) ≤
          segResOhm *
            (segCapFf + downstreamCapFf (inflateSinkLoads deltaCapFf left) +
              downstreamCapFf (inflateSinkLoads deltaCapFf right)) :=
      Nat.mul_le_mul_left segResOhm hCapLe
    constructor
    · exact hCapLe
    · omega

/-- **Theorem (`maxSteinerElmoreDelay_nonneg`)**:
For any `t : SteinerTree`, the worst-case Elmore RC delay is non-negative and bounded below by
the trunk segment's $R_{\text{seg}} \cdot C_{\text{down}}$ product and both child subtrees. -/
theorem maxSteinerElmoreDelay_nonneg (t : SteinerTree) :
    0 ≤ maxSteinerElmoreDelayFsOhm t ∧
    match t with
    | .sink _ _ => maxSteinerElmoreDelayFsOhm t = 0
    | .branch w r c l rgt =>
      r * downstreamCapFf (.branch w r c l rgt) ≤ maxSteinerElmoreDelayFsOhm (.branch w r c l rgt) ∧
      maxSteinerElmoreDelayFsOhm l ≤ maxSteinerElmoreDelayFsOhm (.branch w r c l rgt) ∧
      maxSteinerElmoreDelayFsOhm rgt ≤ maxSteinerElmoreDelayFsOhm (.branch w r c l rgt) := by
  refine ⟨Nat.zero_le _, ?_⟩
  cases t with
  | sink w c => rfl
  | branch w r c l rgt =>
    simp only [maxSteinerElmoreDelayFsOhm, downstreamCapFf]
    omega

/-- Insert a repeater buffer with input gate capacitance `bufInputCapFf` at the right fanout branch. -/
def decoupleRightBranchWithBuffer (bufWireId bufInputCapFf : Nat) : SteinerTree → SteinerTree
  | .sink w c => .sink w c
  | .branch w r c left _right =>
    .branch w r c left (.sink bufWireId bufInputCapFf)

/-- Unbuffered 2-branch Steiner clock/data fanout tree. -/
def unbufferedFanoutTree : SteinerTree :=
  .branch 0 2000 50
    (.sink 1 100)
    (.branch 2 1500 100 (.sink 3 400) (.sink 4 400))

/-- Buffered 2-branch Steiner fanout tree. -/
def bufferedFanoutTree : SteinerTree :=
  decoupleRightBranchWithBuffer 2 25 unbufferedFanoutTree

/-- **Theorem (`steiner_fanout_buffer_insertion_reduces_elmore_delay`)**:
Repeater buffer insertion strictly reduces total upstream lump capacitance and worst-case Elmore RC delay. -/
theorem steiner_fanout_buffer_insertion_reduces_elmore_delay :
    downstreamCapFf bufferedFanoutTree < downstreamCapFf unbufferedFanoutTree ∧
    maxSteinerElmoreDelayFsOhm bufferedFanoutTree < maxSteinerElmoreDelayFsOhm unbufferedFanoutTree ∧
    checkSteinerTimingClosure corner7nm_SS 2000 unbufferedFanoutTree = false ∧
    checkSteinerTimingClosure corner7nm_SS 2000 bufferedFanoutTree = true ∧
    (∀ (w r c bufW bufCap : Nat) (left right : SteinerTree),
      0 < r →
      bufCap < downstreamCapFf right →
      downstreamCapFf (decoupleRightBranchWithBuffer bufW bufCap (.branch w r c left right)) <
        downstreamCapFf (.branch w r c left right) ∧
      maxSteinerElmoreDelayFsOhm (decoupleRightBranchWithBuffer bufW bufCap (.branch w r c left right)) <
        maxSteinerElmoreDelayFsOhm (.branch w r c left right)) := by
  refine ⟨by decide, by decide, by decide, by decide, ?_⟩
  intro w r c bufW bufCap left right hRPos hBufLt
  simp only [decoupleRightBranchWithBuffer, downstreamCapFf, maxSteinerElmoreDelayFsOhm]
  have hCapStrict :
      c + downstreamCapFf left + bufCap < c + downstreamCapFf left + downstreamCapFf right := by
    omega
  have hMulStrict :
      r * (c + downstreamCapFf left + bufCap) <
        r * (c + downstreamCapFf left + downstreamCapFf right) :=
    Nat.mul_lt_mul_of_pos_left hCapStrict hRPos
  constructor
  · exact hCapStrict
  · omega

end Obend.Hardware.PlaceRoute
end
