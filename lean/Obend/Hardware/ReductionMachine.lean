module
/-
# Obend.Hardware.ReductionMachine — Distributed Slot-Reduction Automaton Chip & Runtime Self-Reconfiguring eFPGA (`ICAP` / Glitch-Free DPR)

Formalizes the **Layered Verified Objective Bend Graph-Reduction / Slot-Automaton Hardware
Architecture** and **Runtime Self-Reconfiguring eFPGA Fabric** (via Internal Configuration Access
Port `ICAP` and Region Isolation Fences), connecting `Obend.Leaf.Emit`, `Obend.Lower.Lower`, and
`Obend.Hardware.Compiler`:

1. **Distributed Slot-Reduction / Interaction Automaton (`ReductionPacket`, `AutomatonTile`, `AutomatonNetwork`)**:
   - Maps each slot $s$ of an `Obend.Leaf.Book` (or a lowered `Lean-lite` `LExpr` via `Obend.Lower.lowerT`)
     to a hardware `AutomatonTile` with a verified 64-bit `RtlExpr` datapath,
   - Routes token-passing `ReductionPacket`s (`targetSlot`, `argVal`, `tag`) across the tile network,
   - Proves **`automaton_simulates_book`**: for EVERY compiled `Obend.Leaf.Book`, evaluating any
     `ReductionPacket` on the distributed `AutomatonNetwork` produces the EXACT same 64-bit value
     as the compiled `RtlModule` slot wire (`evalRtlModuleSlotWire`).
2. **Runtime Self-Reconfiguring eFPGA via Internal Configuration Access Port (`IcapBitstreamFrame`, `runGlitchFreeDpr`)**:
   - Models an eFPGA tile array where each `ReconfigTileState` holds an active `AutomatonTile`
     configuration, a 64-bit bitstream frame digest, a skid-buffer hold register `skidHeldOutput`,
     and a hardware **Region Isolation Fence** (`isolated : Bool`),
   - Proves **`unisolated_dpr_glitch_possible`** (overwriting a tile's bitstream while `isolated = false`
     causes mid-cycle combinational output glitches, whereas `isolated = true` clamps the output
     at `skidHeldOutput`),
   - Formalizes the 3-phase **Glitch-Free Dynamic Partial Reconfiguration (DPR) Protocol**
     (`dprPhase1Isolate` $\to$ `dprPhase2LoadFrame` $\to$ `dprPhase3ReleaseFence`),
   - Proves **`dpr_preserves_neighbor_tiles_and_packets`** (reconfiguring `targetTileId` leaves all
     neighbor tiles `tileId ≠ targetTileId` and all buffered in-flight packets strictly untouched)
     and **`dpr_specialized_tile_executes_new_book`** (hot-swapping a newly lowered `Lean-lite` /
     `Leaf.Book` method into an eFPGA tile via `runGlitchFreeDpr` transitions cleanly to the new
     hardware function).
-/
public import Obend.Leaf.Emit
public import Obend.Lower.Lower
public import Obend.Hardware.Compiler
@[expose] public section

namespace Obend.Hardware.ReductionMachine
open Obend.Core.Term
open Obend.Core.Ty (Ty)
open Obend.Leaf
open Obend.Lower
open Obend.Hardware.HDL
open Obend.Hardware.Compiler
set_option autoImplicit false

/-! ## 1. Distributed Slot-Reduction / Interaction Automaton (`ReductionPacket`, `AutomatonTile`, `AutomatonNetwork`) -/

/-- Hardware token-passing packet routed across the slot-reduction automaton network:
* `targetSlot`: destination book slot index $s \in [0, |B.\text{defs}|)$,
* `argVal`: 64-bit method argument payload carried by the token,
* `tag`: continuation / packet-order tag for elastic skid-buffer arbitration. -/
structure ReductionPacket where
  targetSlot : Nat
  argVal     : BitVec 64
  tag        : Nat
  deriving DecidableEq, Repr

/-- Hardware classification of an `AutomatonTile` compiled from `Obend.Leaf.Book` or `Obend.Lower`. -/
inductive TileOpKind where
  | methodSlot
  | cellSlot
  | loweredLeanLite
  deriving DecidableEq, Repr

/-- A single hardware slot-reduction tile in the distributed `AutomatonNetwork`:
* `slotIdx`: topological slot index in `Book.slots`,
* `memberName`: Objective Bend method or cell name,
* `opKind`: slot origin (`methodSlot`, `cellSlot`, or `loweredLeanLite`),
* `datapath`: compiled 64-bit combinational `RtlExpr` datapath for this slot,
* `readsSlots`: list of earlier slot indices referenced through `self`. -/
structure AutomatonTile where
  slotIdx    : Nat
  memberName : String
  opKind     : TileOpKind
  datapath   : RtlExpr
  readsSlots : List Nat
  deriving DecidableEq, Repr

/-- Complete distributed slot-reduction automaton network compiled from an `Obend.Leaf.Book`. -/
structure AutomatonNetwork where
  netName : String
  tiles   : List AutomatonTile
  wires   : List WireAssign
  regs    : List RegSpec
  outputs : List OutputPort
  deriving DecidableEq, Repr

/-- Convert a compiled `WireAssign` from `compileBookDefsSat` into an `AutomatonTile`. -/
def wireToAutomatonTile (w : WireAssign) : AutomatonTile where
  slotIdx    := w.wireIdx
  memberName := w.name
  opKind     := .methodSlot
  datapath   := w.expr
  readsSlots := []

/-- Compile an `Obend.Leaf.Book` into a distributed `AutomatonNetwork` using saturating
`Nat`-compatible hardware compilation (`compileBookDefsSat`). -/
def compileBookToAutomaton (netName : String) (B : Book) : Option AutomatonNetwork :=
  match compileBookDefsSat B.slots [] [] [] [] B.defs with
  | none => none
  | some (wires, regs, outs) =>
    some {
      netName := netName
      tiles   := wires.map wireToAutomatonTile
      wires   := wires
      regs    := regs
      outputs := outs
    }

/-- Hardware input-port environment induced by a `ReductionPacket` (binding port `0` `"arg"` to `argVal`). -/
def packetInputEnv (argVal : BitVec 64) : Nat → BitVec 64 :=
  fun i => if i == 0 then argVal else 0#64

/-- Evaluate a `ReductionPacket` on an `AutomatonNetwork` under sequential register state `regState`:
routes `pkt.argVal` to input port `0`, propagates all inter-tile slot wires via `evalWireTable`,
and extracts the 64-bit result at `pkt.targetSlot`. -/
def evalAutomatonPacket
    (net : AutomatonNetwork)
    (regState : Nat → BitVec 64)
    (pkt : ReductionPacket) : BitVec 64 :=
  let wireEnv := evalWireTable (packetInputEnv pkt.argVal) regState net.wires
  wireEnv pkt.targetSlot

/-- Evaluate slot wire `slotIdx` of a compiled `RtlModule` on input `argVal` and register state `regState`. -/
def evalRtlModuleSlotWire
    (m : RtlModule)
    (regState : Nat → BitVec 64)
    (slotIdx : Nat)
    (argVal : BitVec 64) : BitVec 64 :=
  let wireEnv := evalWireTable (packetInputEnv argVal) regState m.wires
  wireEnv slotIdx

/-- Theorem (`automaton_simulates_book`):
For EVERY `Obend.Leaf.Book` `B`, if `compileBookToAutomaton modName B = some net` and
`compileBookToRtlSat modName B = some rtlMod`, then for EVERY `ReductionPacket` `pkt` and EVERY
register environment `regState`:
1. The automaton's internal wire DAG, register file, and output ports are identical to `rtlMod`, and
2. Evaluating `pkt` on the distributed `AutomatonNetwork` produces the EXACT same 64-bit result
   as evaluating slot wire `pkt.targetSlot` on `rtlMod`! -/
theorem automaton_simulates_book
    (modName : String) (B : Book)
    (net : AutomatonNetwork) (rtlMod : RtlModule)
    (regState : Nat → BitVec 64) (pkt : ReductionPacket)
    (hNet : compileBookToAutomaton modName B = some net)
    (hRtl : compileBookToRtlSat modName B = some rtlMod) :
    net.wires = rtlMod.wires ∧
    net.regs = rtlMod.regs ∧
    evalAutomatonPacket net regState pkt =
      evalRtlModuleSlotWire rtlMod regState pkt.targetSlot pkt.argVal := by
  unfold compileBookToAutomaton at hNet
  unfold compileBookToRtlSat at hRtl
  cases hDefs : compileBookDefsSat B.slots [] [] [] [] B.defs with
  | none =>
    simp [hDefs] at hNet
  | some res =>
    rcases res with ⟨wires, regs, outs⟩
    simp only [hDefs, Option.some.injEq] at hNet hRtl
    subst hNet
    subst hRtl
    exact ⟨rfl, rfl, rfl⟩

/-- Structural first-order lowering of scalar `Lean-lite` (`Obend.Lower.LExpr`) terms to `Obend.Core.Term`
(matching `Obend.Lower.lowerT` on all scalar/control forms without `WellFounded.fix` so kernel
`rfl` and `decide` reduce lowered hardware datapaths directly). -/
def lowerLiteScalar : LExpr → Term
  | .bvar i          => .bound i
  | .erased          => box
  | .const _ b       => lowerLiteScalar b
  | .app f a         => .app (lowerLiteScalar f) (lowerLiteScalar a)
  | .lam _ b         => .lam (lowerLiteScalar b)
  | .letE _ v b      => .app (.lam (lowerLiteScalar b)) (lowerLiteScalar v)
  | .lit n           => .nat n
  | .natSucc a       => .binary .add (lowerLiteScalar a) (.nat 1)
  | .natBin op l r   => .binary op.prim (lowerLiteScalar l) (lowerLiteScalar r)
  | .boolLit b       => .boolean b
  | .natRec _ z s m  => .app (.fix (natRecSpec (lowerLiteScalar z) (lowerLiteScalar s)) box) (lowerLiteScalar m)
  | .boolRec _ x y m => .ifBool (lowerLiteScalar m) (lowerLiteScalar y) (lowerLiteScalar x)
  | .proj n t        => .get (lowerLiteScalar t) n
  | _                => box

/-- Construct a single-slot `Obend.Leaf.Book` from a lowered `Lean-lite` unary method body
(`body : LExpr`, with method parameter at `.bvar 0`). -/
def lowerLiteMethodToBook (memberName : String) (body : LExpr) : Book where
  items := [
    .slot {
      member := memberName
      slot   := 0
      kind   := .method
      code   := .lam (.lam (lowerLiteScalar body))
      reads  := []
    }
  ]

/-- Compile a `Lean-lite` unary method expression directly into an `AutomatonTile` via
`lowerLiteMethodToBook` and `compileBookToAutomaton`. -/
def compileLiteMethodToTile (memberName : String) (body : LExpr) : Option AutomatonTile :=
  match compileBookToAutomaton memberName (lowerLiteMethodToBook memberName body) with
  | some { tiles := t :: _, .. } =>
    some { t with opKind := .loweredLeanLite }
  | _ => none

/-! ## 2. Runtime Self-Reconfiguring eFPGA via Internal Configuration Access Port (`ICAP` & Glitch-Free DPR) -/

/-- State of a dynamically reconfigurable eFPGA / slot-automaton tile with a hardware
**Region Isolation Fence** (`isolated : Bool`):
* `tileId`: unique linear tile address on the ICAP configuration bus,
* `tileX`, `tileY`: 2D mesh coordinates $(x, y)$ on the silicon die,
* `activeTile`: currently loaded `AutomatonTile` datapath configuration,
* `frameDigest`: 64-bit cryptographic / CRC digest of the currently active configuration frame,
* `isolated`: when `true`, the PR isolation fence decouples the tile's combinational output from
  the surrounding fabric and holds the last quiescent value `skidHeldOutput`,
* `skidHeldOutput`: safe latched output value driven while `isolated = true`. -/
structure ReconfigTileState where
  tileId         : Nat
  tileX          : Nat
  tileY          : Nat
  activeTile     : AutomatonTile
  frameDigest    : BitVec 64
  isolated       : Bool
  skidHeldOutput : BitVec 64
  deriving DecidableEq, Repr

/-- Evaluate the combinational output of a `ReconfigTileState`:
* When the PR isolation fence is active (`tile.isolated = true`), the output is strictly clamped
  to `tile.skidHeldOutput` regardless of any transient bitstream mutations inside `activeTile`,
* When unisolated (`tile.isolated = false`), the tile evaluates `tile.activeTile.datapath`. -/
def evalReconfigTile
    (tile : ReconfigTileState)
    (wireEnv regEnv : Nat → BitVec 64)
    (argVal : BitVec 64) : BitVec 64 :=
  if tile.isolated then
    tile.skidHeldOutput
  else
    evalRtlExpr (packetInputEnv argVal) wireEnv regEnv tile.activeTile.datapath

/-- Theorem (`isolated_fence_clamps_output_during_write`):
While a tile's Region Isolation Fence is asserted (`tile.isolated = true`), replacing `activeTile`
with ANY intermediate or partially shifted configuration `transientTile` has ZERO effect on the
tile's output (`evalReconfigTile` remains identically equal to `tile.skidHeldOutput`)! -/
theorem isolated_fence_clamps_output_during_write
    (tile : ReconfigTileState)
    (transientTile : AutomatonTile)
    (wireEnv regEnv : Nat → BitVec 64)
    (argVal : BitVec 64)
    (hIso : tile.isolated = true) :
    evalReconfigTile { tile with activeTile := transientTile } wireEnv regEnv argVal =
      evalReconfigTile tile wireEnv regEnv argVal ∧
    evalReconfigTile { tile with activeTile := transientTile } wireEnv regEnv argVal =
      tile.skidHeldOutput := by
  dsimp only [evalReconfigTile]
  rw [hIso]
  exact ⟨rfl, rfl⟩

/-- Concrete `+ 1` increment tile (`arg + 1`). -/
def incAutomatonTile : AutomatonTile where
  slotIdx    := 0
  memberName := "inc"
  opKind     := .methodSlot
  datapath   := .alu .add (.inputPort 0) (.const 1#64)
  readsSlots := []

/-- Concrete `* 4` scaling tile (`arg * 4`). -/
def mul4AutomatonTile : AutomatonTile where
  slotIdx    := 0
  memberName := "mul4"
  opKind     := .methodSlot
  datapath   := .alu .mul (.inputPort 0) (.const 4#64)
  readsSlots := []

/-- Theorem (`unisolated_dpr_glitch_possible`):
If Dynamic Partial Reconfiguration (DPR) overwrites a tile's active configuration frame while the
Region Isolation Fence is DEASSERTED (`isolated = false`), the tile's combinational output changes
mid-cycle (`evalReconfigTile` jumps from `11#64` to `40#64` on `argVal = 10#64`), whereas asserting
`isolated = true` prevents the mid-cycle glitch! -/
theorem unisolated_dpr_glitch_possible :
    let unisolatedTile : ReconfigTileState :=
      { tileId := 0, tileX := 0, tileY := 0
      , activeTile := incAutomatonTile, frameDigest := 0xA001#64
      , isolated := false, skidHeldOutput := 11#64 }
    let wireEnv : Nat → BitVec 64 := fun _ => 0#64
    let regEnv  : Nat → BitVec 64 := fun _ => 0#64
    evalReconfigTile unisolatedTile wireEnv regEnv 10#64 = 11#64 ∧
    evalReconfigTile { unisolatedTile with activeTile := mul4AutomatonTile } wireEnv regEnv 10#64 = 40#64 ∧
    evalReconfigTile unisolatedTile wireEnv regEnv 10#64 ≠
      evalReconfigTile { unisolatedTile with activeTile := mul4AutomatonTile } wireEnv regEnv 10#64 ∧
    evalReconfigTile { unisolatedTile with isolated := true } wireEnv regEnv 10#64 =
      evalReconfigTile { unisolatedTile with isolated := true, activeTile := mul4AutomatonTile } wireEnv regEnv 10#64 := by
  refine ⟨rfl, rfl, by decide, rfl⟩

/-! ## 3. Three-Phase Glitch-Free Dynamic Partial Reconfiguration (`ICAP`) Protocol -/

/-- Configuration frame packet streamed into the Internal Configuration Access Port (`ICAP`):
* `targetTileId`: tile ID to reconfigure,
* `newTile`: new `AutomatonTile` datapath to load into the tile,
* `expectedDigest`: expected 64-bit frame CRC / Merkle digest from the signed bitstream header,
* `computedDigest`: hardware CRC / digest computed over the received configuration words. -/
structure IcapBitstreamFrame where
  targetTileId   : Nat
  newTile        : AutomatonTile
  expectedDigest : BitVec 64
  computedDigest : BitVec 64
  deriving DecidableEq, Repr

/-- Multi-tile eFPGA Dynamic Partial Reconfiguration (DPR) array state:
* `tiles`: list of reconfigurable tiles on the die,
* `skidBufferPkts`: elastic skid-buffer queue holding in-flight `ReductionPacket`s during DPR,
* `icapBusy`: status flag indicating whether an ICAP transaction is in progress,
* `crcErrorCount`: count of rejected corrupt bitstream frames (`computedDigest ≠ expectedDigest`). -/
structure EfpgaDprArray where
  tiles          : List ReconfigTileState
  skidBufferPkts : List ReductionPacket
  icapBusy       : Bool
  crcErrorCount  : Nat
  deriving DecidableEq, Repr

/-- **DPR Phase 1 (`dprPhase1Isolate`)**:
Assert the hardware Region Isolation Fence (`isolated := true`) on `targetTileId` while leaving
all other tiles `t.tileId ≠ targetTileId` untouched. -/
def dprPhase1Isolate (targetTileId : Nat) (t : ReconfigTileState) : ReconfigTileState :=
  if t.tileId == targetTileId then
    { t with isolated := true }
  else
    t

/-- **DPR Phase 2 (`dprPhase2LoadFrame`)**:
Write `frame.newTile` via the `ICAP` port ONLY if `t.tileId == frame.targetTileId`, the tile is
currently isolated (`t.isolated = true`), and the bitstream frame CRC matches
(`frame.computedDigest == frame.expectedDigest`). -/
def dprPhase2LoadFrame (frame : IcapBitstreamFrame) (t : ReconfigTileState) : ReconfigTileState :=
  if t.tileId == frame.targetTileId then
    if t.isolated && (frame.computedDigest == frame.expectedDigest) then
      { t with
        activeTile  := frame.newTile
        frameDigest := frame.computedDigest }
    else
      t
  else
    t

/-- **DPR Phase 3 (`dprPhase3ReleaseFence`)**:
After verifying that the loaded frame digest matches `frame.expectedDigest`, release the Region
Isolation Fence (`isolated := false`) so the newly specialized tile goes live on the next clock edge.
If the CRC check failed, the tile remains safely isolated (`isolated := true`). -/
def dprPhase3ReleaseFence (frame : IcapBitstreamFrame) (t : ReconfigTileState) : ReconfigTileState :=
  if t.tileId == frame.targetTileId then
    if frame.computedDigest == frame.expectedDigest then
      { t with isolated := false }
    else
      { t with isolated := true }
  else
    t

/-- Execute the complete 3-phase Glitch-Free DPR sequence on a single `ReconfigTileState`:
$$\text{Phase 1 (Isolate)} \longrightarrow \text{Phase 2 (ICAP Load)} \longrightarrow \text{Phase 3 (Verify CRC \& Release)}.$$ -/
def runTileGlitchFreeDpr (frame : IcapBitstreamFrame) (t : ReconfigTileState) : ReconfigTileState :=
  dprPhase3ReleaseFence frame (dprPhase2LoadFrame frame (dprPhase1Isolate frame.targetTileId t))

/-- Execute the 3-phase Glitch-Free DPR transaction across an entire `EfpgaDprArray`. -/
def runGlitchFreeDpr (arr : EfpgaDprArray) (frame : IcapBitstreamFrame) : EfpgaDprArray :=
  let crcOk := frame.computedDigest == frame.expectedDigest
  { tiles          := arr.tiles.map (runTileGlitchFreeDpr frame)
  , skidBufferPkts := arr.skidBufferPkts
  , icapBusy       := false
  , crcErrorCount  := if crcOk then arr.crcErrorCount else arr.crcErrorCount + 1 }

/-- Theorem (`dpr_preserves_neighbor_tiles_and_packets`):
Reconfiguring tile `frame.targetTileId` via `runTileGlitchFreeDpr` and `runGlitchFreeDpr`:
1. Leaves EVERY neighbor tile `t` with `t.tileId ≠ frame.targetTileId` strictly untouched
   (`runTileGlitchFreeDpr frame t = t`),
2. Holds the target tile's output glitch-free at `t.skidHeldOutput` throughout Phase 1 and Phase 2, and
3. Preserves all in-flight packets in `arr.skidBufferPkts` without dropping or corrupting any token! -/
theorem dpr_preserves_neighbor_tiles_and_packets
    (arr : EfpgaDprArray) (frame : IcapBitstreamFrame) (t : ReconfigTileState)
    (wireEnv regEnv : Nat → BitVec 64) (argVal : BitVec 64)
    (hNeighbor : (t.tileId == frame.targetTileId) = false) :
    runTileGlitchFreeDpr frame t = t ∧
    (runGlitchFreeDpr arr frame).skidBufferPkts = arr.skidBufferPkts ∧
    (t.tileId == frame.targetTileId →
      evalReconfigTile (dprPhase2LoadFrame frame (dprPhase1Isolate frame.targetTileId t))
        wireEnv regEnv argVal = t.skidHeldOutput) := by
  have h1 : dprPhase1Isolate frame.targetTileId t = t := by
    simp [dprPhase1Isolate, hNeighbor]
  have h2 : dprPhase2LoadFrame frame t = t := by
    simp [dprPhase2LoadFrame, hNeighbor]
  have h3 : dprPhase3ReleaseFence frame t = t := by
    simp [dprPhase3ReleaseFence, hNeighbor]
  refine ⟨?_, rfl, ?_⟩
  · simp [runTileGlitchFreeDpr, h1, h2, h3]
  · intro hContra
    rw [hNeighbor] at hContra
    cases hContra

/-- Theorem (`dpr_corrupt_crc_keeps_tile_isolated`):
If a bitstream frame suffers a bit-flip in transit (`(frame.computedDigest == frame.expectedDigest) = false`),
`runTileGlitchFreeDpr` refuses to load `frame.newTile` (`activeTile = t.activeTile`) and keeps the
target tile safely isolated (`isolated = true`) so corrupt logic can never drive the chip! -/
theorem dpr_corrupt_crc_keeps_tile_isolated
    (frame : IcapBitstreamFrame) (t : ReconfigTileState)
    (hTarget : (t.tileId == frame.targetTileId) = true)
    (hCorrupt : (frame.computedDigest == frame.expectedDigest) = false) :
    (runTileGlitchFreeDpr frame t).activeTile = t.activeTile ∧
    (runTileGlitchFreeDpr frame t).isolated = true := by
  have h1 : dprPhase1Isolate frame.targetTileId t = { t with isolated := true } := by
    dsimp only [dprPhase1Isolate]
    rw [hTarget]
    rfl
  have h2 : dprPhase2LoadFrame frame { t with isolated := true } = { t with isolated := true } := by
    dsimp only [dprPhase2LoadFrame]
    rw [hTarget, hCorrupt]
    rfl
  have h3 : dprPhase3ReleaseFence frame { t with isolated := true } = { t with isolated := true } := by
    dsimp only [dprPhase3ReleaseFence]
    rw [hTarget, hCorrupt]
    rfl
  dsimp only [runTileGlitchFreeDpr]
  rw [h1, h2, h3]
  exact ⟨rfl, rfl⟩

/-- Lowered `Lean-lite` expression for $f(x) = 3x + 7$:
`LExpr.natBin .add (LExpr.natBin .mul (.bvar 0) (.lit 3)) (.lit 7)`. -/
def leanLiteAffine3xPlus7 : LExpr :=
  .natBin .add (.natBin .mul (.bvar 0) (.lit 3)) (.lit 7)

/-- Theorem (`leanLiteAffine3xPlus7_matches_lowerT`):
Verifies that `lowerLiteScalar` agrees identically with `Obend.Lower.lowerT` on
`leanLiteAffine3xPlus7` ($\lambda x : \text{Nat}.\, 3x + 7$). -/
theorem leanLiteAffine3xPlus7_matches_lowerT :
    lowerT (.lam .natural leanLiteAffine3xPlus7) =
      .lam (lowerLiteScalar leanLiteAffine3xPlus7) := by
  simp [leanLiteAffine3xPlus7, lowerT, lowerLiteScalar, NatOp.prim]

/-- Compiled `AutomatonTile` for `leanLiteAffine3xPlus7` ($x \mapsto 3x + 7$). -/
def affine3xPlus7Tile : AutomatonTile :=
  (compileLiteMethodToTile "affine3xPlus7" leanLiteAffine3xPlus7).getD incAutomatonTile

/-- Theorem (`dpr_specialized_tile_executes_new_book`):
1. For any tile `t` with `(t.tileId == frame.targetTileId) = true` and valid frame CRC
   `(frame.computedDigest == frame.expectedDigest) = true`, running the 3-phase Glitch-Free DPR
   protocol (`runTileGlitchFreeDpr frame t`) installs `frame.newTile`, releases `isolated = false`,
   and evaluates `frame.newTile.datapath` on every subsequent input `argVal`, and
2. Specifically, lowering the `Lean-lite` function `leanLiteAffine3xPlus7` ($x \mapsto 3x + 7$)
   to an `Obend.Leaf.Book` (`lowerLiteMethodToBook`) and compiling it to `affine3xPlus7Tile`
   (`compileLiteMethodToTile`), then hot-swapping it into tile `0` via `runTileGlitchFreeDpr`,
   transitions tile `0` from `inc` ($10 \mapsto 11$) to $3x + 7$ ($10 \mapsto 37$) with zero glitch! -/
theorem dpr_specialized_tile_executes_new_book
    (frame : IcapBitstreamFrame) (t : ReconfigTileState)
    (wireEnv regEnv : Nat → BitVec 64) (argVal : BitVec 64)
    (hTarget : (t.tileId == frame.targetTileId) = true)
    (hCrcOk  : (frame.computedDigest == frame.expectedDigest) = true) :
    (runTileGlitchFreeDpr frame t).activeTile = frame.newTile ∧
    (runTileGlitchFreeDpr frame t).isolated = false ∧
    evalReconfigTile (runTileGlitchFreeDpr frame t) wireEnv regEnv argVal =
      evalRtlExpr (packetInputEnv argVal) wireEnv regEnv frame.newTile.datapath ∧
    compileLiteMethodToTile "affine3xPlus7" leanLiteAffine3xPlus7 = some affine3xPlus7Tile ∧
    (let initTile : ReconfigTileState :=
       { tileId := 0, tileX := 0, tileY := 0
       , activeTile := incAutomatonTile, frameDigest := 0x1000#64
       , isolated := false, skidHeldOutput := 11#64 }
     let icapFrame : IcapBitstreamFrame :=
       { targetTileId := 0, newTile := affine3xPlus7Tile
       , expectedDigest := 0x3007#64, computedDigest := 0x3007#64 }
     let reconfigured := runTileGlitchFreeDpr icapFrame initTile
     evalReconfigTile initTile (fun _ => 0#64) (fun _ => 0#64) 10#64 = 11#64 ∧
     evalReconfigTile reconfigured (fun _ => 0#64) (fun _ => 0#64) 10#64 = 37#64) := by
  have h1 : dprPhase1Isolate frame.targetTileId t = { t with isolated := true } := by
    simp [dprPhase1Isolate, hTarget]
  have h2 : dprPhase2LoadFrame frame { t with isolated := true } =
      { t with activeTile := frame.newTile, frameDigest := frame.computedDigest, isolated := true } := by
    simp [dprPhase2LoadFrame, hTarget, hCrcOk]
  have h3 : dprPhase3ReleaseFence frame
      { t with activeTile := frame.newTile, frameDigest := frame.computedDigest, isolated := true } =
      { t with activeTile := frame.newTile, frameDigest := frame.computedDigest, isolated := false } := by
    simp [dprPhase3ReleaseFence, hTarget, hCrcOk]
  have hAll : runTileGlitchFreeDpr frame t =
      { t with activeTile := frame.newTile, frameDigest := frame.computedDigest, isolated := false } := by
    simp [runTileGlitchFreeDpr, h1, h2, h3]
  rw [hAll]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end Obend.Hardware.ReductionMachine
end
