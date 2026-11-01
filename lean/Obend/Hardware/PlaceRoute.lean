module
/-
# Obend.Hardware.PlaceRoute — Physical Device Grid, Untrusted PnR Certificate Checker, Elmore RC Delay & Bitstream Decoder

Eliminates blind trust in vendor/open-source Place-and-Route (`nextpnr`, `VPR`, `Vivado`) and
bitstream assemblers (`fasm2frames`) by requiring external PnR tools to emit a verifiable
`PnrCertificate` checked in linear/quadratic time by the Objective Bend kernel:

1. **Physical Device Grid & Placement Injectivity (`PlacedCell`, `checkPlacementInjective`)**:
   - Verifies that no two distinct logical cells occupy the same physical `(tileX, tileY, belSlot)`,
   - Proves `placement_injective_no_collision`.
2. **Switch-Box PIP Routing Disjointness & Contiguous Connectivity (`PipHop`, `RoutedNet`)**:
   - Verifies that every net's PIP hops form a contiguous directed path from `srcWire` to `dstWire`
     (`checkNetContiguous`) and that no wire node is driven by two distinct nets (`checkRoutingDisjoint`),
   - Proves `routing_disjoint_no_short` and `contiguous_net_reaches_sink`.
3. **Physical Elmore RC Interconnect Delay (`computeElmoreDelayFsOhm`, `checkElmoreTiming`)**:
   - Computes exact distributed RC Elmore delay $T_{\text{Elmore}} = \sum_{e} R_e \cdot C_{\text{downstream}}(e)$
     along each routed PIP tree and checks setup timing closure at the target `ProcessCorner`,
   - Proves `elmore_delay_monotone`.
4. **FABulous Configuration Bitstream Frame Encoder/Decoder (`BitstreamFrame`, `decodeBitstreamFrame`)**:
   - Decodes raw 32-bit configuration frames into `(tileX, tileY, belSlot, lutInit, pipMask)`,
   - Proves `bitstream_decode_roundtrip_sound` (`decodeBitstreamFrames (encodeBitstreamFrames cfg) = cfg`).
-/
public import Obend.Hardware.Process
@[expose] public section

namespace Obend.Hardware.PlaceRoute
open Obend.Hardware.Process
set_option autoImplicit false

/-! ## 1. Physical Placement Table & Injectivity Checker (`checkPlacementInjective`) -/

/-- Physical assignment of a logical cell `cellId` to a tile coordinate `(tileX, tileY)`,
BEL slot `belSlot`, and 4-LUT truth table `lutInit`. -/
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

/-- Theorem (`placement_injective_no_collision`):
If `checkPairNoCollision c1 c2 = true` and `c1.cellId ≠ c2.cellId`, then `c1` and `c2` occupy
strictly distinct physical `(tileX, tileY, belSlot)` locations on the die! -/
theorem placement_injective_no_collision
    (c1 c2 : PlacedCell)
    (hOk : checkPairNoCollision c1 c2 = true)
    (hNeId : c1.cellId ≠ c2.cellId) :
    cellLocation c1 ≠ cellLocation c2 := by
  simp only [checkPairNoCollision, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hOk
  rcases hOk with hEq | hNeLoc
  · exact False.elim (hNeId hEq)
  · exact hNeLoc

/-! ## 2. Switch-Box PIP Routing Connectivity & Short-Circuit Freedom (`checkRoutingDisjoint`) -/

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

/-- Check that two wire lists share no common wire node (`disjointWires`). -/
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

/-- Theorem (`routing_disjoint_no_short`):
If `disjointWireLists w1 w2 = true`, then no wire `u ∈ w1` is contained in `w2` (`w2.contains u = false`). -/
theorem routing_disjoint_no_short
    (w1 w2 : List Nat) (u : Nat)
    (hDisj : disjointWireLists w1 w2 = true)
    (hIn1  : u ∈ w1) :
    w2.contains u = false := by
  simp only [disjointWireLists, List.all_eq_true, Bool.not_eq_true'] at hDisj
  exact hDisj u hIn1

/-! ## 3. Elmore RC Interconnect Delay & Timing Signoff (`computeElmoreDelayPs`) -/

/-- Total downstream capacitance $\sum C_i$ (in $\text{fF}$) of a PIP hop chain plus load `sinkCapFf`. -/
def downstreamCapFf (sinkCapFf : Nat) : List PipHop → Nat
  | [] => sinkCapFf
  | h :: rest => h.capFf + downstreamCapFf sinkCapFf rest

/-- Distributed Elmore RC delay $\sum_{e} R_e \cdot C_{\text{downstream}}(e)$ (in $\text{fF}\cdot\Omega = \text{fs}$). -/
def computeElmoreDelayFs (sinkCapFf : Nat) : List PipHop → Nat
  | [] => 0
  | h :: rest =>
    let cDown := h.capFf + downstreamCapFf sinkCapFf rest
    (h.resOhm * cDown) + computeElmoreDelayFs sinkCapFf rest

/-- Convert Elmore delay from femtoseconds ($\text{fF}\cdot\Omega$) to picoseconds (ceiling division by 1000). -/
def computeElmoreDelayPs (sinkCapFf : Nat) (hops : List PipHop) : Nat :=
  (computeElmoreDelayFs sinkCapFf hops + 999) / 1000

/-- Theorem (`elmore_delay_monotone`):
Prepending a PIP routing hop `h` strictly increases or preserves the cumulative Elmore RC delay
(`computeElmoreDelayFs sinkCapFf (h :: rest) ≥ computeElmoreDelayFs sinkCapFf rest`). -/
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

/-! ## 5. Complete Untrusted Place-and-Route Certificate & Kernel Verifier (`checkPnrCertificate`) -/

/-- Complete untrusted Place-and-Route & Bitstream certificate submitted to `Obend.Judge`. -/
structure PnrCertificate where
  designName      : String
  placedCells     : List PlacedCell
  routedNets      : List RoutedNet
  expectedConfigs : List TileFrameConfig
  bitstreamFrames : List BitstreamFrame
  sinkCapFf       : Nat
  deriving DecidableEq, Repr

/-- Complete kernel PnR & bitstream certificate checker:
1. Placement is injective (`checkPlacementInjective`),
2. All routed nets are contiguous from source to sink (`checkNetConnectivity`),
3. No two nets short-circuit on a shared wire (`checkRoutingDisjoint`),
4. Every routed net meets Elmore RC setup timing (`checkNetElmoreTiming`),
5. Every bitstream frame decodes to `expectedConfigs` (`bitstreamFrames.map decodeBitstreamFrame == expectedConfigs`). -/
def checkPnrCertificate
    (corner : ProcessCorner) (clockPeriodPs : Nat) (cert : PnrCertificate) : Bool :=
  checkPlacementInjective cert.placedCells &&
  cert.routedNets.all checkNetConnectivity &&
  checkRoutingDisjoint cert.routedNets &&
  cert.routedNets.all (checkNetElmoreTiming corner clockPeriodPs cert.sinkCapFf) &&
  (cert.bitstreamFrames.map decodeBitstreamFrame == cert.expectedConfigs)

/-- Concrete verified PnR certificate for a 2-BEL routed adder slice on `corner7nm_SS` at 500 MHz (`2000 ps`). -/
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

/-- Theorem: `checkPnrCertificate` accepts `validAdderPnrCert` and refuses both BEL placement
collisions (`collidingBelPnrCert`) and PIP routing shorts (`shortedWirePnrCert`)! -/
theorem pnr_certificate_verification_poles :
    checkPnrCertificate corner7nm_SS 2000 validAdderPnrCert = true ∧
    checkPnrCertificate corner7nm_SS 2000 collidingBelPnrCert = false ∧
    checkPnrCertificate corner7nm_SS 2000 shortedWirePnrCert = false :=
  ⟨rfl, rfl, rfl⟩

end Obend.Hardware.PlaceRoute
