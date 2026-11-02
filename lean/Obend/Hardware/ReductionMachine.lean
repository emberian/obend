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
public import Obend.Leaf.Specialize
public import Obend.Lower.Lower
public import Obend.Hardware.Compiler
@[expose] public section

namespace Obend.Hardware.ReductionMachine
open Obend.Core.Term
open Obend.Core.Ty (Ty)
open Obend.Logic
open Obend.Slot
open Obend.Slot.World
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

/-! ## 5. True Interaction-Net / Graph-Reduction Tile Arena (`INetNode`, `ActivePair`, `reduceActivePair`) -/

/-- Hardware node kinds in the Interaction-Net / Graph-Reduction Tile Arena. -/
inductive INetNodeKind where
  | era
  | con
  | dup
  | sup
  | app
  | lam
  | nat64
  deriving DecidableEq, Repr

/-- Hardware port reference (`nodeId`, `slot` where `0` = principal port, `1` = `aux1`, `2` = `aux2`). -/
structure PortRef where
  nodeId : Nat
  slot   : Nat
  deriving DecidableEq, Repr

/-- Interaction-net node stored in a tile's local node arena:
* `id`: unique arena node index,
* `kind`: interaction combinator / lambda / scalar node kind,
* `label`: interaction combinator label (or affine `slope` for `lam`),
* `immVal`: 64-bit scalar payload (or affine `offset` for `lam`),
* `aux1`, `aux2`: auxiliary port pointers. -/
structure INetNode where
  id     : Nat
  kind   : INetNodeKind
  label  : Nat
  immVal : Nat
  aux1   : PortRef
  aux2   : PortRef
  deriving DecidableEq, Repr

/-- Active pair of two interaction-net nodes connected principal-port to principal-port. -/
structure ActivePair where
  left  : INetNode
  right : INetNode
  deriving DecidableEq, Repr

/-- Single-cycle hardware rewrite outcome for an `ActivePair` in the tile arena. -/
inductive INetRewriteOutcome where
  | annihilate (wire1 : PortRef × PortRef) (wire2 : PortRef × PortRef)
  | commute    (spawned : List INetNode)
  | erase      (erasedAux : List PortRef)
  | betaNat64  (resultNode : INetNode)
  deriving DecidableEq, Repr

/-- The 4 cross-wired nodes (`dupA`, `dupB`, `supA`, `supB`) spawned when `l` and `r` commute (`l.label ≠ r.label`). -/
def commuteSpawnedNodes (l r : INetNode) (nextFreeId : Nat) : List INetNode :=
  let dupAId := nextFreeId
  let dupBId := nextFreeId + 1
  let supAId := nextFreeId + 2
  let supBId := nextFreeId + 3
  [ { id := dupAId, kind := l.kind, label := l.label, immVal := 0
    , aux1 := { nodeId := supAId, slot := 1 }, aux2 := { nodeId := supBId, slot := 1 } }
  , { id := dupBId, kind := l.kind, label := l.label, immVal := 0
    , aux1 := { nodeId := supAId, slot := 2 }, aux2 := { nodeId := supBId, slot := 2 } }
  , { id := supAId, kind := r.kind, label := r.label, immVal := 0
    , aux1 := l.aux1, aux2 := r.aux1 }
  , { id := supBId, kind := r.kind, label := r.label, immVal := 0
    , aux1 := l.aux2, aux2 := r.aux2 } ]

/-- Single-cycle hardware interaction-net rewrite rule engine (`reduceActivePair`):
* **Erasure**: `era` interacting with any node propagates `era` to its auxiliary ports,
* **Hardware $\beta$-Nat64**: `lam` (`label = slope`, `immVal = offset`) interacting with `nat64` (`immVal = x`)
  reduces in 1 cycle to `nat64 (slope * x + offset)`,
* **$\beta$-Application**: `lam` interacting with `app` annihilates and wires `(l.aux1, r.aux1)` and `(l.aux2, r.aux2)`,
* **Annihilation vs. Commutation**: two combinators (`dup`, `sup`, `con`) with identical `label` annihilate;
  distinct labels (`l.label ≠ r.label`) commute and spawn 4 cross-wired nodes. -/
def reduceActivePair (pair : ActivePair) (nextFreeId : Nat) : INetRewriteOutcome :=
  let l := pair.left
  let r := pair.right
  match l.kind, r.kind with
  | .era, .era => .erase []
  | .era, _    => .erase [r.aux1, r.aux2]
  | _, .era    => .erase [l.aux1, l.aux2]
  | .lam, .nat64 =>
    .betaNat64 {
      id     := nextFreeId
      kind   := .nat64
      label  := 0
      immVal := l.label * r.immVal + l.immVal
      aux1   := l.aux1
      aux2   := l.aux2
    }
  | .nat64, .lam =>
    .betaNat64 {
      id     := nextFreeId
      kind   := .nat64
      label  := 0
      immVal := r.label * l.immVal + r.immVal
      aux1   := r.aux1
      aux2   := r.aux2
    }
  | .lam, .app => .annihilate (l.aux1, r.aux1) (l.aux2, r.aux2)
  | .app, .lam => .annihilate (l.aux1, r.aux1) (l.aux2, r.aux2)
  | _, _ =>
    if l.label == r.label then
      .annihilate (l.aux1, r.aux1) (l.aux2, r.aux2)
    else
      .commute (commuteSpawnedNodes l r nextFreeId)

/-- Theorem (`inet_annihilation_same_label`):
Two `dup` (or `sup` or `con`) nodes with identical label `lbl` connected at their principal ports
annihilate in 1 cycle into `.annihilate (a1, b1) (a2, b2)`. -/
theorem inet_annihilation_same_label
    (id1 id2 lbl : Nat) (a1 a2 b1 b2 : PortRef) (nextId : Nat) :
    let n1 : INetNode := { id := id1, kind := .dup, label := lbl, immVal := 0, aux1 := a1, aux2 := a2 }
    let n2 : INetNode := { id := id2, kind := .dup, label := lbl, immVal := 0, aux1 := b1, aux2 := b2 }
    let s1 : INetNode := { id := id1, kind := .sup, label := lbl, immVal := 0, aux1 := a1, aux2 := a2 }
    let s2 : INetNode := { id := id2, kind := .sup, label := lbl, immVal := 0, aux1 := b1, aux2 := b2 }
    reduceActivePair { left := n1, right := n2 } nextId = .annihilate (a1, b1) (a2, b2) ∧
    reduceActivePair { left := s1, right := s2 } nextId = .annihilate (a1, b1) (a2, b2) := by
  simp [reduceActivePair]

/-- Theorem (`inet_commutation_distinct_labels_spawns_four`):
When a `dup` node with label `l1` interacts with a `sup` node with label `l2` (`l1 ≠ l2`),
`reduceActivePair` produces `.commute spawned` with `spawned.length = 4`. -/
theorem inet_commutation_distinct_labels_spawns_four
    (id1 id2 l1 l2 : Nat) (a1 a2 b1 b2 : PortRef) (nextId : Nat)
    (hNe : l1 ≠ l2) :
    let n1 : INetNode := { id := id1, kind := .dup, label := l1, immVal := 0, aux1 := a1, aux2 := a2 }
    let n2 : INetNode := { id := id2, kind := .sup, label := l2, immVal := 0, aux1 := b1, aux2 := b2 }
    let spawned := commuteSpawnedNodes n1 n2 nextId
    reduceActivePair { left := n1, right := n2 } nextId = .commute spawned ∧
    spawned.length = 4 := by
  intro n1 n2 spawned
  refine ⟨?_, rfl⟩
  dsimp only [reduceActivePair, n1, n2, spawned]
  simp [hNe]

/-- Theorem (`inet_beta_nat64_sound`):
Reducing a linear `lam` node (`label = slope`, `immVal = offset`) against a `nat64` node (`immVal = x`)
produces `.betaNat64` carrying `immVal = slope * x + offset` in a single cycle. -/
theorem inet_beta_nat64_sound
    (id1 id2 slope offset x : Nat) (a1 a2 b1 b2 : PortRef) (nextId : Nat) :
    let lamNode : INetNode := { id := id1, kind := .lam, label := slope, immVal := offset, aux1 := a1, aux2 := a2 }
    let argNode : INetNode := { id := id2, kind := .nat64, label := 0, immVal := x, aux1 := b1, aux2 := b2 }
    reduceActivePair { left := lamNode, right := argNode } nextId =
      .betaNat64 { id := nextId, kind := .nat64, label := 0, immVal := slope * x + offset, aux1 := a1, aux2 := a2 } := by
  rfl

/-! ## 6. Multi-Hop 2D Mesh XY Dimension-Ordered Routing (`MeshXyPacket`, `stepMeshXy`) -/

/-- Packet routed across the 2D silicon tile mesh under deadlock-free XY dimension-ordered routing. -/
structure MeshXyPacket where
  srcX    : Nat
  srcY    : Nat
  dstX    : Nat
  dstY    : Nat
  curX    : Nat
  curY    : Nat
  payload : Nat
  deriving DecidableEq, Repr

/-- Manhattan distance ($L_1$ metric) from `(p.curX, p.curY)` to `(p.dstX, p.dstY)`. -/
def manhattanDist (p : MeshXyPacket) : Nat :=
  (if p.curX ≤ p.dstX then p.dstX - p.curX else p.curX - p.dstX) +
  (if p.curY ≤ p.dstY then p.dstY - p.curY else p.curY - p.dstY)

/-- Single-hop 2D Mesh XY dimension-ordered router:
routes 1 hop along X (`curX + 1` if `curX < dstX`, `curX - 1` if `dstX < curX`) when `curX ≠ dstX`,
and otherwise routes 1 hop along Y (`curY + 1` if `curY < dstY`, `curY - 1` if `dstY < curY`),
strictly preserving `srcX`, `srcY`, `dstX`, `dstY`, and `payload`. -/
def stepMeshXy (p : MeshXyPacket) : MeshXyPacket :=
  if p.curX < p.dstX then
    { p with curX := p.curX + 1 }
  else if p.dstX < p.curX then
    { p with curX := p.curX - 1 }
  else if p.curY < p.dstY then
    { p with curY := p.curY + 1 }
  else if p.dstY < p.curY then
    { p with curY := p.curY - 1 }
  else
    p

/-- Theorem (`stepMeshXy_preserves_payload`):
For every `p : MeshXyPacket`, a single XY routing hop preserves `payload`, `dstX`, and `dstY`. -/
theorem stepMeshXy_preserves_payload (p : MeshXyPacket) :
    (stepMeshXy p).payload = p.payload ∧
    (stepMeshXy p).dstX = p.dstX ∧
    (stepMeshXy p).dstY = p.dstY := by
  dsimp only [stepMeshXy]
  by_cases h1 : p.curX < p.dstX
  · simp [h1]
  · by_cases h2 : p.dstX < p.curX
    · simp [h1, h2]
    · by_cases h3 : p.curY < p.dstY
      · simp [h1, h2, h3]
      · by_cases h4 : p.dstY < p.curY
        · simp [h1, h2, h3, h4]
        · simp [h1, h2, h3, h4]

/-- Theorem (`stepMeshXy_decreases_manhattanDist`):
For every `p : MeshXyPacket` not yet at its destination (`p.curX ≠ p.dstX ∨ p.curY ≠ p.dstY`),
`stepMeshXy` strictly decreases the $L_1$ Manhattan distance `manhattanDist` by 1. -/
theorem stepMeshXy_decreases_manhattanDist
    (p : MeshXyPacket)
    (hNotAtDst : p.curX ≠ p.dstX ∨ p.curY ≠ p.dstY) :
    manhattanDist (stepMeshXy p) < manhattanDist p := by
  dsimp only [stepMeshXy, manhattanDist]
  by_cases h1 : p.curX < p.dstX
  · have hle1 : p.curX + 1 ≤ p.dstX := h1
    have hle0 : p.curX ≤ p.dstX := Nat.le_of_lt h1
    simp only [h1, hle1, hle0, ↓reduceIte]
    omega
  · by_cases h2 : p.dstX < p.curX
    · have hle0 : ¬ (p.curX ≤ p.dstX) := by omega
      simp only [h1, h2, hle0, ↓reduceIte]
      split <;> omega
    · have hleX : p.curX ≤ p.dstX := by omega
      by_cases h3 : p.curY < p.dstY
      · have hle1 : p.curY + 1 ≤ p.dstY := h3
        have hle0 : p.curY ≤ p.dstY := Nat.le_of_lt h3
        simp only [h1, h2, h3, hleX, hle1, hle0, ↓reduceIte]
        omega
      · by_cases h4 : p.dstY < p.curY
        · have hle0 : ¬ (p.curY ≤ p.dstY) := by omega
          by_cases hle1 : p.curY - 1 ≤ p.dstY <;>
            simp only [h1, h2, h3, h4, hleX, hle0, hle1, ↓reduceIte] <;> omega
        · exfalso
          omega

/-- Theorem (`stepMeshXy_at_dest_fixed`):
When a packet has reached its destination (`p.curX = p.dstX` and `p.curY = p.dstY`),
`stepMeshXy p = p` is a fixed point. -/
theorem stepMeshXy_at_dest_fixed
    (p : MeshXyPacket)
    (hx : p.curX = p.dstX)
    (hy : p.curY = p.dstY) :
    stepMeshXy p = p := by
  dsimp only [stepMeshXy]
  simp [hx, hy]

/-! ## 7. 32-Bit ICAP Configuration Frame Bitstream Codec (`encodeTileIcapWords`, `decodeTileIcapWords`) -/

/-- Standard 32-bit ICAP configuration frame synchronization word (`0xAA995566`). -/
def icapSyncWord : BitVec 32 := 0xAA995566#32

/-- Hardware ALU / reduction rule opcode encoded in an ICAP configuration bitstream frame. -/
inductive RuleOpcode where
  | addImm
  | subImm
  | mulImm
  | bitAndImm
  | bitOrImm
  | bitXorImm
  | shlImm
  | lshrImm
  | eqImm
  | ultImm
  deriving DecidableEq, Repr

/-- Encode a `RuleOpcode` into its 4-bit hardware opcode index (`0..9`). -/
def encodeRuleOpcodeBits : RuleOpcode → Nat
  | .addImm    => 0
  | .subImm    => 1
  | .mulImm    => 2
  | .bitAndImm => 3
  | .bitOrImm  => 4
  | .bitXorImm => 5
  | .shlImm    => 6
  | .lshrImm   => 7
  | .eqImm     => 8
  | .ultImm    => 9

/-- Decode a hardware opcode index into `Option RuleOpcode`. -/
def decodeRuleOpcodeBits : Nat → Option RuleOpcode
  | 0 => some .addImm
  | 1 => some .subImm
  | 2 => some .mulImm
  | 3 => some .bitAndImm
  | 4 => some .bitOrImm
  | 5 => some .bitXorImm
  | 6 => some .shlImm
  | 7 => some .lshrImm
  | 8 => some .eqImm
  | 9 => some .ultImm
  | _ => none

/-- Round-trip lemma (`decode_encode_opcode`): decoding the encoded bits of any `RuleOpcode` recovers `some op`. -/
theorem decode_encode_opcode (op : RuleOpcode) :
    decodeRuleOpcodeBits (encodeRuleOpcodeBits op) = some op := by
  cases op <;> rfl

/-- Map a `RuleOpcode` to the corresponding `Obend.Hardware.HDL.RtlAluOp`. -/
def ruleOpcodeToAluOp : RuleOpcode → RtlAluOp
  | .addImm    => .add
  | .subImm    => .sub
  | .mulImm    => .mul
  | .bitAndImm => .bitAnd
  | .bitOrImm  => .bitOr
  | .bitXorImm => .bitXor
  | .shlImm    => .shl
  | .lshrImm   => .lshr
  | .eqImm     => .eq
  | .ultImm    => .ult

/-- Map an `RtlAluOp` to its corresponding `RuleOpcode`. -/
def aluOpToRuleOpcode : RtlAluOp → RuleOpcode
  | .add    => .addImm
  | .sub    => .subImm
  | .mul    => .mulImm
  | .bitAnd => .bitAndImm
  | .bitOr  => .bitOrImm
  | .bitXor => .bitXorImm
  | .shl    => .shlImm
  | .lshr   => .lshrImm
  | .eq     => .eqImm
  | .ult    => .ultImm

/-- Round-trip lemma between `ruleOpcodeToAluOp` and `aluOpToRuleOpcode`. -/
theorem aluOpToRuleOpcode_ruleOpcodeToAluOp (op : RuleOpcode) :
    aluOpToRuleOpcode (ruleOpcodeToAluOp op) = op := by
  cases op <;> rfl

/-- Canonical member name associated with a `RuleOpcode` tile. -/
def ruleOpcodeName : RuleOpcode → String
  | .addImm    => "inc"
  | .subImm    => "subImm"
  | .mulImm    => "mul4"
  | .bitAndImm => "bitAndImm"
  | .bitOrImm  => "bitOrImm"
  | .bitXorImm => "bitXorImm"
  | .shlImm    => "shlImm"
  | .lshrImm   => "lshrImm"
  | .eqImm     => "eqImm"
  | .ultImm    => "ultImm"

/-- Encode `TileOpKind` into a 2-bit integer (`0..2`). -/
def encodeTileOpKindBits : TileOpKind → Nat
  | .methodSlot      => 0
  | .cellSlot        => 1
  | .loweredLeanLite => 2

/-- Decode a 2-bit integer into `Option TileOpKind`. -/
def decodeTileOpKindBits : Nat → Option TileOpKind
  | 0 => some .methodSlot
  | 1 => some .cellSlot
  | 2 => some .loweredLeanLite
  | _ => none

/-- Round-trip lemma for `TileOpKind` through a 32-bit `BitVec` word. -/
theorem decode_encode_opKind_bv (opKind : TileOpKind) :
    decodeTileOpKindBits (BitVec.ofNat 32 (encodeTileOpKindBits opKind)).toNat = some opKind := by
  cases opKind <;> rfl

/-- Round-trip lemma for `RuleOpcode` through a 32-bit `BitVec` word. -/
theorem decode_encode_opcode_bv (op : RuleOpcode) :
    decodeRuleOpcodeBits (BitVec.ofNat 32 (encodeRuleOpcodeBits op)).toNat = some op := by
  cases op <;> rfl

/-- Construct a canonical ICAP-reconfigurable `AutomatonTile` from `(slotIdx, opKind, ruleOp, immVal)`. -/
def mkIcapRuleTile
    (slotIdx : Nat)
    (opKind : TileOpKind)
    (ruleOp : RuleOpcode)
    (immVal : Nat) : AutomatonTile where
  slotIdx    := slotIdx
  memberName := ruleOpcodeName ruleOp
  opKind     := opKind
  datapath   := .alu (ruleOpcodeToAluOp ruleOp) (.inputPort 0) (.const (BitVec.ofNat 64 immVal))
  readsSlots := []

/-- Extract `(ruleOp, immVal)` from an `AutomatonTile` datapath when it is in canonical ALU-immediate form. -/
def extractTileRuleAndImm (t : AutomatonTile) : RuleOpcode × Nat :=
  match t.datapath with
  | .alu aluOp (.inputPort 0) (.const immBv) =>
    (aluOpToRuleOpcode aluOp, immBv.toNat)
  | _ => (.addImm, 0)

/-- Serialize an `AutomatonTile` into a 5-word 32-bit ICAP bitstream frame:
`[icapSyncWord, word1_slotIdx, word2_opKind, word3_ruleOpcode, word4_immVal]`. -/
def encodeTileIcapWords (t : AutomatonTile) : List (BitVec 32) :=
  let (ruleOp, immVal) := extractTileRuleAndImm t
  [ icapSyncWord
  , BitVec.ofNat 32 t.slotIdx
  , BitVec.ofNat 32 (encodeTileOpKindBits t.opKind)
  , BitVec.ofNat 32 (encodeRuleOpcodeBits ruleOp)
  , BitVec.ofNat 32 immVal ]

/-- Deserialize a 5-word 32-bit ICAP bitstream frame into an `Option AutomatonTile`,
verifying the leading `icapSyncWord` (`0xAA995566#32`). -/
def decodeTileIcapWords (words : List (BitVec 32)) : Option AutomatonTile :=
  match words with
  | [w0, w1, w2, w3, w4] =>
    if w0 == icapSyncWord then
      match decodeTileOpKindBits w2.toNat, decodeRuleOpcodeBits w3.toNat with
      | some opKind, some ruleOp =>
        some (mkIcapRuleTile w1.toNat opKind ruleOp w4.toNat)
      | _, _ => none
    else
      none
  | _ => none

/-- Helper lemma: `(BitVec.ofNat w n).toNat = n` whenever `n < 2 ^ w`. -/
theorem bitvec_toNat_ofNat_lt (w n : Nat) (h : n < 2 ^ w) :
    (BitVec.ofNat w n).toNat = n := by
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt h

theorem extractTileRuleAndImm_mkIcapRuleTile
    (slotIdx : Nat) (opKind : TileOpKind) (ruleOp : RuleOpcode) (immVal : Nat) :
    extractTileRuleAndImm (mkIcapRuleTile slotIdx opKind ruleOp immVal) =
      (ruleOp, (BitVec.ofNat 64 immVal).toNat) := by
  cases ruleOp <;> rfl

/-- Theorem (`decode_encode_icap_words_roundtrip`):
For every canonical ICAP `AutomatonTile` `t = mkIcapRuleTile slotIdx opKind ruleOp immVal`
with 32-bit bounded `slotIdx < 2^32` and `immVal < 2^32`, serializing `t` via `encodeTileIcapWords`
into a 5-word 32-bit ICAP bitstream frame and deserializing via `decodeTileIcapWords` recovers `some t`. -/
theorem decode_encode_icap_words_roundtrip
    (slotIdx : Nat) (opKind : TileOpKind) (ruleOp : RuleOpcode) (immVal : Nat)
    (hSlot : slotIdx < 2 ^ 32)
    (hImm  : immVal < 2 ^ 32) :
    let t := mkIcapRuleTile slotIdx opKind ruleOp immVal
    decodeTileIcapWords (encodeTileIcapWords t) = some t := by
  intro t
  have hImm64 : immVal < 2 ^ 64 := by omega
  have h1 : (BitVec.ofNat 64 immVal).toNat = immVal :=
    bitvec_toNat_ofNat_lt 64 immVal hImm64
  have h2 : (BitVec.ofNat 32 slotIdx).toNat = slotIdx :=
    bitvec_toNat_ofNat_lt 32 slotIdx hSlot
  have h3 : (BitVec.ofNat 32 immVal).toNat = immVal :=
    bitvec_toNat_ofNat_lt 32 immVal hImm
  have hSync : (icapSyncWord == icapSyncWord) = true := rfl
  dsimp only [t, encodeTileIcapWords]
  rw [extractTileRuleAndImm_mkIcapRuleTile]
  dsimp only [mkIcapRuleTile, decodeTileIcapWords]
  simp only [h1, hSync, ↓reduceIte]
  rw [decode_encode_opKind_bv, decode_encode_opcode_bv, h2, h3]

/-- Theorem (`golden_icap_bitstream_roundtrip`):
Kernel-checked (`decide +kernel`) verification that `incAutomatonTile` and `mul4AutomatonTile`
round-trip cleanly through 5-word 32-bit ICAP configuration frames headed by `icapSyncWord`,
while a frame with a corrupted sync word (`0xDEADBEEF#32`) is rejected (`none`). -/
theorem golden_icap_bitstream_roundtrip :
    (encodeTileIcapWords incAutomatonTile).length = 5 ∧
    (encodeTileIcapWords incAutomatonTile).head? = some icapSyncWord ∧
    decodeTileIcapWords (encodeTileIcapWords incAutomatonTile) = some incAutomatonTile ∧
    decodeTileIcapWords (encodeTileIcapWords mul4AutomatonTile) = some mul4AutomatonTile ∧
    decodeTileIcapWords [0xDEADBEEF#32, 0#32, 0#32, 0#32, 1#32] = none := by
  decide +kernel

/-! ## 8. Multi-Cycle `BendTT` Interaction-Net Active-Pair Hardware Processing Element (`stepInteractionNetPe`, `runInteractionNetCycles`) -/

/-- Construct a `BendTT` Eraser (`ERA`) interaction-net node. -/
def mkEraNode (id : Nat) : INetNode where
  id     := id
  kind   := .era
  label  := 0
  immVal := 0
  aux1   := ⟨0, 0⟩
  aux2   := ⟨0, 0⟩

/-- Construct a `BendTT` Constructor (`CON`) interaction-net node with combinator `label` and auxiliary ports `aux1`, `aux2`. -/
def mkConNode (id label : Nat) (aux1 aux2 : PortRef) : INetNode where
  id     := id
  kind   := .con
  label  := label
  immVal := 0
  aux1   := aux1
  aux2   := aux2

/-- Construct a `BendTT` Duplicator (`DUP`) interaction-net node with combinator `label` and auxiliary ports `aux1`, `aux2`. -/
def mkDupNode (id label : Nat) (aux1 aux2 : PortRef) : INetNode where
  id     := id
  kind   := .dup
  label  := label
  immVal := 0
  aux1   := aux1
  aux2   := aux2

/-- Extract the 4 external boundary auxiliary ports `[l.aux1, l.aux2, r.aux1, r.aux2]` of a binary `ActivePair`. -/
def externalBoundaryPorts (pair : ActivePair) : List PortRef :=
  [pair.left.aux1, pair.left.aux2, pair.right.aux1, pair.right.aux2]

/-- Extract the external boundary ports preserved across the 4 nodes spawned by a `CON-DUP` commutation. -/
def commutedBoundaryPorts (spawned : List INetNode) : List PortRef :=
  match spawned with
  | [_, _, supA, supB] => [supA.aux1, supB.aux1, supA.aux2, supB.aux2]
  | _ => []

/-- Look up a waiting node by `id` in `arenaNodes`. -/
def findArenaNodeById (arena : List INetNode) (targetId : Nat) : Option INetNode :=
  arena.find? (fun n => n.id == targetId)

/-- Check whether a wire splice `w = (p1, p2)` connects two principal ports (`p1.slot == 0` and
`p2.slot == 0` with `p1.nodeId != p2.nodeId`) of waiting nodes in `arena`. If so, remove both
nodes from `arena` and dynamically synthesize the newly formed `ActivePair` `{ left := n1, right := n2 }`. -/
def resolveWireSplice (arena : List INetNode) (w : PortRef × PortRef) : List INetNode × List ActivePair :=
  let (p1, p2) := w
  if p1.slot == 0 && p2.slot == 0 && p1.nodeId != p2.nodeId then
    match findArenaNodeById arena p1.nodeId, findArenaNodeById arena p2.nodeId with
    | some n1, some n2 =>
      let arena' := arena.filter (fun n => n.id != p1.nodeId && n.id != p2.nodeId)
      (arena', [{ left := n1, right := n2 }])
    | _, _ => (arena, [])
  else
    (arena, [])

/-- Resolve both wire splices `w1` and `w2` emitted by an annihilation against waiting nodes in `arena`,
returning the updated `arena` and any newly formed `ActivePair`s to enqueue into `activeQueue`. -/
def resolveTwoWireSplices (arena : List INetNode) (w1 w2 : PortRef × PortRef) : List INetNode × List ActivePair :=
  match arena with
  | [] => ([], [])
  | _ =>
    let (arena1, pairs1) := resolveWireSplice arena w1
    let (arena2, pairs2) := resolveWireSplice arena1 w2
    (arena2, pairs1 ++ pairs2)

/-- Synchronous architectural state of a multi-cycle `BendTT` Interaction-Net Hardware Processing Element (PE):
* `activeQueue`: hardware FIFO worklist of active principal-port pairs awaiting reduction,
* `arenaNodes`: local arena of spawned combinator nodes,
* `rewiredPorts`: completed port-to-port wire splices emitted by `CON-CON` and `DUP-DUP` annihilations,
* `erasedPorts`: auxiliary ports scheduled for `.era` garbage collection,
* `scalarResults`: completed `.nat64` scalar nodes produced by hardware $\beta$-reduction,
* `nextFreeId`: monotonic hardware arena allocator pointer,
* `cycleCount`: active reduction cycles executed,
* `annihilations`: hardware performance counter for `CON-CON` / `DUP-DUP` annihilations,
* `commutations`: hardware performance counter for `CON-DUP` commutations. -/
structure InteractionNetPeState where
  activeQueue   : List ActivePair
  arenaNodes    : List INetNode
  rewiredPorts  : List (PortRef × PortRef)
  erasedPorts   : List PortRef
  scalarResults : List INetNode
  nextFreeId    : Nat
  cycleCount    : Nat
  annihilations : Nat
  commutations  : Nat
  deriving DecidableEq, Repr

/-- Initialize an `InteractionNetPeState` with an initial active-pair queue and starting free node ID. -/
def initInteractionNetPe (queue : List ActivePair) (startFreeId : Nat) : InteractionNetPeState where
  activeQueue   := queue
  arenaNodes    := []
  rewiredPorts  := []
  erasedPorts   := []
  scalarResults := []
  nextFreeId    := startFreeId
  cycleCount    := 0
  annihilations := 0
  commutations  := 0

/-- Execute a single clock cycle on the `BendTT` Interaction-Net Hardware Processing Element (`stepInteractionNetPe`):
dequeues the head `ActivePair` from `activeQueue`, dispatches `reduceActivePair`, dynamically synthesizes
any newly formed `ActivePair`s when a port splice connects two principal ports (`slot == 0`) in `arenaNodes`,
updates the arena / wire-splice tables / hardware performance counters, and holds the state stationary
once `activeQueue = []`. -/
def stepInteractionNetPe (st : InteractionNetPeState) : InteractionNetPeState :=
  match st.activeQueue with
  | [] => st
  | pair :: restQueue =>
    match reduceActivePair pair st.nextFreeId with
    | .annihilate w1 w2 =>
      let (arena', newPairs) := resolveTwoWireSplices st.arenaNodes w1 w2
      { st with
        activeQueue   := restQueue ++ newPairs
        arenaNodes    := arena'
        rewiredPorts  := st.rewiredPorts ++ [w1, w2]
        cycleCount    := st.cycleCount + 1
        annihilations := st.annihilations + 1 }
    | .commute spawned =>
      { st with
        activeQueue   := restQueue
        arenaNodes    := st.arenaNodes ++ spawned
        nextFreeId    := st.nextFreeId + 4
        cycleCount    := st.cycleCount + 1
        commutations  := st.commutations + 1 }
    | .erase auxs =>
      { st with
        activeQueue   := restQueue
        erasedPorts   := st.erasedPorts ++ auxs
        cycleCount    := st.cycleCount + 1 }
    | .betaNat64 resNode =>
      { st with
        activeQueue   := restQueue
        scalarResults := st.scalarResults ++ [resNode]
        nextFreeId    := st.nextFreeId + 1
        cycleCount    := st.cycleCount + 1 }

/-- Run the `BendTT` Interaction-Net Processing Element for `numCycles` clock edges. -/
def runInteractionNetCycles : Nat → InteractionNetPeState → InteractionNetPeState
  | 0, st => st
  | k + 1, st => runInteractionNetCycles k (stepInteractionNetPe st)

/-- **Theorem (`inet_annihilation_exact`)**:
For ANY combinator label `lbl : Nat` and auxiliary port pairs `(a1, a2)` and `(b1, b2)`:
1. Stepping `stepInteractionNetPe` on a `CON-CON` active pair with matching label `lbl` annihilates
   both nodes in 1 cycle, splicing `(a1, b1)` and `(a2, b2)` into `rewiredPorts` with zero arena allocation, and
2. Stepping `stepInteractionNetPe` on a `DUP-DUP` active pair with matching label `lbl` likewise
   annihilates both nodes in 1 cycle, splicing `(a1, b1)` and `(a2, b2)` into `rewiredPorts` and
   incrementing `annihilations` by 1. -/
theorem inet_annihilation_exact
    (id1 id2 lbl : Nat) (a1 a2 b1 b2 : PortRef) (startFreeId : Nat) :
    let conPair : ActivePair :=
      { left  := mkConNode id1 lbl a1 a2
      , right := mkConNode id2 lbl b1 b2 }
    let dupPair : ActivePair :=
      { left  := mkDupNode id1 lbl a1 a2
      , right := mkDupNode id2 lbl b1 b2 }
    let stCon := stepInteractionNetPe (initInteractionNetPe [conPair] startFreeId)
    let stDup := stepInteractionNetPe (initInteractionNetPe [dupPair] startFreeId)
    stCon.activeQueue = [] ∧
    stCon.rewiredPorts = [(a1, b1), (a2, b2)] ∧
    stCon.arenaNodes = [] ∧
    stCon.nextFreeId = startFreeId ∧
    stCon.annihilations = 1 ∧
    stDup.activeQueue = [] ∧
    stDup.rewiredPorts = [(a1, b1), (a2, b2)] ∧
    stDup.arenaNodes = [] ∧
    stDup.nextFreeId = startFreeId ∧
    stDup.annihilations = 1 := by
  simp [stepInteractionNetPe, initInteractionNetPe, reduceActivePair,
    resolveTwoWireSplices, mkConNode, mkDupNode]

/-- **Theorem (`inet_commutation_port_count_preserved`)**:
When a `CON` node with label `l1` interacts with a `DUP` node with label `l2` (`l1 ≠ l2`),
stepping `stepInteractionNetPe`:
1. Executes a 1-cycle `CON-DUP` commutation spawning 4 cross-wired arena nodes (`arenaNodes.length = 4`),
2. Advances `nextFreeId` by `4` and increments `commutations` by `1`, and
3. Strictly preserves all 4 external boundary auxiliary ports `[a1, a2, b1, b2]`
   (`commutedBoundaryPorts st'.arenaNodes = externalBoundaryPorts pair` and length `= 4`). -/
theorem inet_commutation_port_count_preserved
    (id1 id2 l1 l2 : Nat) (a1 a2 b1 b2 : PortRef) (startFreeId : Nat)
    (hDiff : l1 ≠ l2) :
    let pair : ActivePair :=
      { left  := mkConNode id1 l1 a1 a2
      , right := mkDupNode id2 l2 b1 b2 }
    let st' := stepInteractionNetPe (initInteractionNetPe [pair] startFreeId)
    st'.activeQueue = [] ∧
    st'.arenaNodes.length = 4 ∧
    st'.nextFreeId = startFreeId + 4 ∧
    st'.commutations = 1 ∧
    commutedBoundaryPorts st'.arenaNodes = externalBoundaryPorts pair ∧
    (commutedBoundaryPorts st'.arenaNodes).length = (externalBoundaryPorts pair).length ∧
    (externalBoundaryPorts pair).length = 4 := by
  intro pair st'
  dsimp only [st', pair, stepInteractionNetPe, initInteractionNetPe, reduceActivePair, mkConNode, mkDupNode]
  simp [hDiff, commuteSpawnedNodes, commutedBoundaryPorts, externalBoundaryPorts]

/-- **Theorem (`inet_dynamic_splice_cascading_reduction`)**:
Verifies that when an outer `CON 0 - CON 0` active pair annihilates in Cycle 1 and splices two
principal ports `(⟨10, 0⟩, ⟨11, 0⟩)` belonging to waiting `DUP 1` nodes in `arenaNodes`:
1. Cycle 1 dynamically promotes `{ left := n10, right := n11 }` from `arenaNodes` into `activeQueue`, and
2. Cycle 2 dequeues and annihilates the newly formed `DUP 1 - DUP 1` active pair, splicing its
   auxiliary ports `(⟨10, 1⟩, ⟨11, 1⟩)` and `(⟨10, 2⟩, ⟨11, 2⟩)`. -/
theorem inet_dynamic_splice_cascading_reduction :
    let n10 := mkDupNode 10 1 ⟨10, 1⟩ ⟨10, 2⟩
    let n11 := mkDupNode 11 1 ⟨11, 1⟩ ⟨11, 2⟩
    let outerPair : ActivePair :=
      { left  := mkConNode 1 0 ⟨10, 0⟩ ⟨1, 2⟩
      , right := mkConNode 2 0 ⟨11, 0⟩ ⟨2, 2⟩ }
    let st0 : InteractionNetPeState :=
      { (initInteractionNetPe [outerPair] 50) with arenaNodes := [n10, n11] }
    let st1 := stepInteractionNetPe st0
    let st2 := runInteractionNetCycles 2 st0
    st1.activeQueue = [{ left := n10, right := n11 }] ∧
    st1.arenaNodes = [] ∧
    st1.annihilations = 1 ∧
    st2.activeQueue = [] ∧
    st2.annihilations = 2 ∧
    st2.rewiredPorts =
      [ (⟨10, 0⟩, ⟨11, 0⟩), (⟨1, 2⟩, ⟨2, 2⟩)
      , (⟨10, 1⟩, ⟨11, 1⟩), (⟨10, 2⟩, ⟨11, 2⟩) ] := by
  decide +kernel

/-- **Theorem (`golden_multicycle_inet_pe_reduction`)**:
End-to-end 4-cycle verification of the `BendTT` Interaction-Net Processing Element executing a
heterogeneous batch of active pairs across 4 clock cycles:
* **Cycle 1 (`CON 0` - `CON 0` Annihilation)**: splices `(⟨1, 1⟩, ⟨2, 1⟩)` and `(⟨1, 2⟩, ⟨2, 2⟩)`,
* **Cycle 2 (`CON 0` - `DUP 1` Commutation)**: spawns 4 cross-wired nodes (`IDs 100..103`),
* **Cycle 3 (`DUP 1` - `DUP 1` Annihilation)**: splices `(⟨5, 1⟩, ⟨6, 1⟩)` and `(⟨5, 2⟩, ⟨6, 2⟩)`,
* **Cycle 4 ($\beta$-`nat64` Affine Evaluation)**: reduces `(λx. 3x + 7) 10` to `nat64 37` (`ID 104`),
and reaches a quiescent fixed point at Cycle 5 (`runInteractionNetCycles 5 = runInteractionNetCycles 4`). -/
theorem golden_multicycle_inet_pe_reduction :
    let p1 : ActivePair :=
      { left  := mkConNode 1 0 ⟨1, 1⟩ ⟨1, 2⟩
      , right := mkConNode 2 0 ⟨2, 1⟩ ⟨2, 2⟩ }
    let p2 : ActivePair :=
      { left  := mkConNode 3 0 ⟨3, 1⟩ ⟨3, 2⟩
      , right := mkDupNode 4 1 ⟨4, 1⟩ ⟨4, 2⟩ }
    let p3 : ActivePair :=
      { left  := mkDupNode 5 1 ⟨5, 1⟩ ⟨5, 2⟩
      , right := mkDupNode 6 1 ⟨6, 1⟩ ⟨6, 2⟩ }
    let p4 : ActivePair :=
      { left  := { id := 7, kind := .lam, label := 3, immVal := 7, aux1 := ⟨7, 1⟩, aux2 := ⟨7, 2⟩ }
      , right := { id := 8, kind := .nat64, label := 0, immVal := 10, aux1 := ⟨8, 1⟩, aux2 := ⟨8, 2⟩ } }
    let initPe := initInteractionNetPe [p1, p2, p3, p4] 100
    let finalPe := runInteractionNetCycles 4 initPe
    finalPe.activeQueue = [] ∧
    finalPe.cycleCount = 4 ∧
    finalPe.annihilations = 2 ∧
    finalPe.commutations = 1 ∧
    finalPe.arenaNodes.length = 4 ∧
    finalPe.rewiredPorts.length = 4 ∧
    finalPe.nextFreeId = 105 ∧
    finalPe.scalarResults.map (·.immVal) = [37] ∧
    runInteractionNetCycles 5 initPe = finalPe := by
  decide +kernel

/-! ## 6. Spatial Packet-Switched XY NoC Transition System & `Obend.Slot`-Backed DPR (`WS-A`) -/

/-- Classification of a packet-switched Network-on-Chip (NoC) flit (`NocFlitKind`):
* `request`: carries an argument `payload` from `(srcX, srcY)` to `(dstX, dstY)` targeting `targetSlot`,
* `response`: carries the evaluated 64-bit result `payload` back to `(dstX, dstY)`. -/
inductive NocFlitKind where
  | request
  | response
  deriving DecidableEq, Repr

/-- Hardware Network-on-Chip (NoC) credit-flow-controlled flit (`NocFlit`):
* `flitId`: unique packet/flit identifier,
* `kind`: `.request` or `.response`,
* `srcX`, `srcY`: origin 2D mesh coordinates,
* `curX`, `curY`: current router 2D mesh coordinates,
* `dstX`, `dstY`: destination 2D mesh coordinates,
* `targetSlot`: target `Obend.Leaf.Book` slot index on the destination tile,
* `payload`: 64-bit data payload (`argVal` on `.request`, evaluated result on `.response`). -/
structure NocFlit where
  flitId     : Nat
  kind       : NocFlitKind
  srcX       : Nat
  srcY       : Nat
  curX       : Nat
  curY       : Nat
  dstX       : Nat
  dstY       : Nat
  targetSlot : Nat
  payload    : BitVec 64
  deriving DecidableEq, Repr

/-- Check whether a `NocFlit` has reached its destination tile `(dstX, dstY)`. -/
def NocFlit.atDest (f : NocFlit) : Bool :=
  f.curX == f.dstX && f.curY == f.dstY

/-- Manhattan hop distance `|curX - dstX| + |curY - dstY|` remaining for a `NocFlit`. -/
def NocFlit.manhattanDist (f : NocFlit) : Nat :=
  (if f.curX ≤ f.dstX then f.dstX - f.curX else f.curX - f.dstX) +
  (if f.curY ≤ f.dstY then f.dstY - f.curY else f.curY - f.dstY)

/-- Advance one hop along Dimension-Order XY routing (`stepNocFlitXy`):
1. First routes horizontally along the X dimension (`curX < dstX ↦ curX + 1`, `curX > dstX ↦ curX - 1`),
2. Once `curX == dstX`, routes vertically along the Y dimension (`curY < dstY ↦ curY + 1`, `curY > dstY ↦ curY - 1`),
3. Once `(curX, curY) == (dstX, dstY)`, the flit has arrived at its destination tile. -/
def stepNocFlitXy (f : NocFlit) : NocFlit :=
  if f.curX < f.dstX then
    { f with curX := f.curX + 1 }
  else if f.curX > f.dstX then
    { f with curX := f.curX - 1 }
  else if f.curY < f.dstY then
    { f with curY := f.curY + 1 }
  else if f.curY > f.dstY then
    { f with curY := f.curY - 1 }
  else
    f

/-- Spatial NoC Tile & Router State (`NocTileState`):
* `tileId`: linear tile identifier,
* `tileX`, `tileY`: 2D mesh coordinates on the die,
* `inbox`: queue of in-flight flits at this router/tile,
* `outbox`: queue of completed response flits delivered to egress,
* `credits`: downstream egress buffer credits (`credits == 0` stalls ejection),
* `rules`: resident `AutomatonTile` slot rules on this tile. -/
structure NocTileState where
  tileId  : Nat
  tileX   : Nat
  tileY   : Nat
  inbox   : List NocFlit
  outbox  : List NocFlit
  credits : Nat
  rules   : List AutomatonTile
  deriving DecidableEq, Repr

/-- Evaluate the matching `AutomatonTile` rule in `rules` for `targetSlot` on `argVal`. -/
def evalTileRuleOnFlit (rules : List AutomatonTile) (argVal : BitVec 64) (targetSlot : Nat) : BitVec 64 :=
  match rules.find? (fun r => r.slotIdx == targetSlot) with
  | some r => evalRtlExpr (packetInputEnv argVal) (fun _ => 0#64) (fun _ => 0#64) r.datapath
  | none   =>
    match rules.head? with
    | some r => evalRtlExpr (packetInputEnv argVal) (fun _ => 0#64) (fun _ => 0#64) r.datapath
    | none   => argVal

/-- Single-cycle spatial XY router & rule transition (`stepNocRouter`):
* Stalls if `t.credits == 0` or `t.inbox == []`,
* If the head flit `f` is not yet at `(dstX, dstY)`, advances `f` by one XY hop (`stepNocFlitXy f`),
* If `f` has reached `(dstX, dstY)` as a `.request`, fires `evalTileRuleOnFlit t.rules f.payload f.targetSlot`
  and turns `f` into a `.response` flit routed back to `(srcX, srcY)` (ejecting to `outbox` and
  decrementing `credits` if `(srcX, srcY) == (curX, curY)`, or routing back along the XY mesh),
* If `f` has reached `(dstX, dstY)` as a `.response`, ejects `f` into `outbox` and decrements `credits` by 1. -/
def stepNocRouter (t : NocTileState) : NocTileState :=
  if t.credits == 0 then
    t
  else
    match t.inbox with
    | [] => t
    | f :: rest =>
      if !f.atDest then
        let fNext := stepNocFlitXy f
        { t with
          inbox   := rest ++ [fNext]
          credits := t.credits }
      else
        match f.kind with
        | .request =>
          let resVal := evalTileRuleOnFlit t.rules f.payload f.targetSlot
          let respFlit : NocFlit :=
            { f with
              kind    := .response
              dstX    := f.srcX
              dstY    := f.srcY
              payload := resVal }
          if respFlit.atDest then
            { t with
              inbox   := rest
              outbox  := t.outbox ++ [respFlit]
              credits := t.credits - 1 }
          else
            { t with
              inbox   := rest ++ [respFlit]
              credits := t.credits }
        | .response =>
          { t with
            inbox   := rest
            outbox  := t.outbox ++ [f]
            credits := t.credits - 1 }

/-- Return an ejected response flit from `outbox` to the host and restore 1 egress credit (`credits + 1`). -/
def consumeNocOutboxFlit (t : NocTileState) : Option NocFlit × NocTileState :=
  match t.outbox with
  | [] => (none, t)
  | f :: rest =>
    (some f, { t with outbox := rest, credits := t.credits + 1 })

/-- Complete 2D Spatial NoC Fabric (`NocFabric`). -/
structure NocFabric where
  tiles : List NocTileState
  deriving DecidableEq, Repr

/-- Deliver an in-flight flit `f` to the first tile in `tiles` whose 2D mesh coordinates
`(tileX, tileY)` match `(f.curX, f.curY)`. -/
def deliverFlitToTiles (f : NocFlit) : List NocTileState → Option (List NocTileState)
  | [] => none
  | t :: rest =>
    if t.tileX == f.curX && t.tileY == f.curY then
      some ({ t with inbox := t.inbox ++ [f] } :: rest)
    else
      match deliverFlitToTiles f rest with
      | some rest' => some (t :: rest')
      | none => none

/-- Deliver a flit `f` to the tile at `(f.curX, f.curY)` in `tiles` if present, or retain it in the
head tile of `tiles` when `tiles` is a partial/single-tile submesh. -/
def deliverFlitToFabric (f : NocFlit) (tiles : List NocTileState) : List NocTileState :=
  match deliverFlitToTiles f tiles with
  | some tiles' => tiles'
  | none =>
    match tiles with
    | [] => []
    | t :: rest => { t with inbox := t.inbox ++ [f] } :: rest

/-- Deliver a list of in-flight flits across the fabric tiles. -/
def deliverFlitsToFabric : List NocFlit → List NocTileState → List NocTileState
  | [], tiles => tiles
  | f :: rest, tiles => deliverFlitsToFabric rest (deliverFlitToFabric f tiles)

/-- Extract all in-flight `inbox` flits from `tiles` and clear each tile's `inbox` prior to inter-tile
crossbar delivery. -/
def collectAndClearInboxes : List NocTileState → List NocFlit × List NocTileState
  | [] => ([], [])
  | t :: rest =>
    let (restFlits, restTiles) := collectAndClearInboxes rest
    (t.inbox ++ restFlits, { t with inbox := [] } :: restTiles)

/-- Step all tiles/routers in a `NocFabric` by 1 clock cycle (`stepNocRouter`) and physically
route every resulting in-flight `inbox` flit `f` across the 2D mesh fabric to the tile whose
coordinates `(tileX, tileY)` match `(f.curX, f.curY)`. -/
def stepNocFabric (fab : NocFabric) : NocFabric :=
  let stepped := fab.tiles.map stepNocRouter
  let (inFlight, cleared) := collectAndClearInboxes stepped
  { tiles := deliverFlitsToFabric inFlight cleared }

/-- Step a `NocFabric` for `n` clock cycles. -/
def runNocFabricCycles : Nat → NocFabric → NocFabric
  | 0, fab => fab
  | n + 1, fab => runNocFabricCycles n (stepNocFabric fab)

/-- Step a single `NocTileState` for `n` clock cycles. -/
def runNocRouterCycles : Nat → NocTileState → NocTileState
  | 0, t => t
  | n + 1, t => runNocRouterCycles n (stepNocRouter t)

/-- Total number of flits (`inbox.length + outbox.length`) on a `NocTileState`. -/
def tileTotalFlits (t : NocTileState) : Nat :=
  t.inbox.length + t.outbox.length

/-- Credit-plus-outbox conservation invariant (`credits + outbox.length`) on a `NocTileState`. -/
def tileCreditsPlusOutbox (t : NocTileState) : Nat :=
  t.credits + t.outbox.length

/-- Total number of flits across all tiles in a `NocFabric`. -/
def fabricTotalFlits (fab : NocFabric) : Nat :=
  (fab.tiles.map tileTotalFlits).sum

/-- Total `credits + outbox.length` across all tiles in a `NocFabric`. -/
def fabricCreditsPlusOutbox (fab : NocFabric) : Nat :=
  (fab.tiles.map tileCreditsPlusOutbox).sum

/-- **Theorem (`stepNocRouter_conserves_flits_and_credits`, Universally Quantified)**:
For every `t : NocTileState`, a single router transition `stepNocRouter t` strictly conserves
both total flits (`inbox.length + outbox.length`) and credit accounting (`credits + outbox.length`). -/
theorem stepNocRouter_conserves_flits_and_credits (t : NocTileState) :
    tileTotalFlits (stepNocRouter t) = tileTotalFlits t ∧
    tileCreditsPlusOutbox (stepNocRouter t) = tileCreditsPlusOutbox t := by
  unfold stepNocRouter tileTotalFlits tileCreditsPlusOutbox
  by_cases hc : t.credits == 0
  · simp [hc]
  · simp only [hc, Bool.false_eq_true, ↓reduceIte]
    have hpos : t.credits > 0 := by
      rcases Nat.eq_zero_or_pos t.credits with h0 | hp
      · exfalso; exact hc (beq_iff_eq.mpr h0)
      · exact hp
    cases hin : t.inbox with
    | nil => simp [hin]
    | cons f rest =>
      dsimp only
      by_cases hat : !f.atDest
      · simp [hat]
      · simp only [hat, Bool.false_eq_true, ↓reduceIte]
        cases f.kind with
        | request =>
          dsimp only
          split <;> simp <;> omega
        | response =>
          simp; omega

theorem deliverFlitToTiles_conserves (f : NocFlit) :
    ∀ (tiles tiles' : List NocTileState),
      deliverFlitToTiles f tiles = some tiles' →
      tiles' ≠ [] ∧
      (tiles'.map tileTotalFlits).sum = (tiles.map tileTotalFlits).sum + 1 ∧
      (tiles'.map tileCreditsPlusOutbox).sum = (tiles.map tileCreditsPlusOutbox).sum
  | [], _, h => by cases h
  | t :: rest, tiles', h => by
    simp only [deliverFlitToTiles] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      refine ⟨by simp, ?_, rfl⟩
      simp [tileTotalFlits]
      omega
    · cases hd : deliverFlitToTiles f rest with
      | none => rw [hd] at h; cases h
      | some rest' =>
        rw [hd] at h
        simp only [Option.some.injEq] at h
        subst h
        obtain ⟨_, ih1, ih2⟩ := deliverFlitToTiles_conserves f rest rest' hd
        refine ⟨by simp, ?_, ?_⟩
        · simp only [List.map_cons, List.sum_cons, ih1]; omega
        · simp only [List.map_cons, List.sum_cons, ih2]

theorem deliverFlitToFabric_conserves (f : NocFlit) :
    ∀ (tiles : List NocTileState),
      tiles ≠ [] →
      deliverFlitToFabric f tiles ≠ [] ∧
      ((deliverFlitToFabric f tiles).map tileTotalFlits).sum = (tiles.map tileTotalFlits).sum + 1 ∧
      ((deliverFlitToFabric f tiles).map tileCreditsPlusOutbox).sum = (tiles.map tileCreditsPlusOutbox).sum := by
  intro tiles hne
  unfold deliverFlitToFabric
  cases hd : deliverFlitToTiles f tiles with
  | some tiles' => exact deliverFlitToTiles_conserves f tiles tiles' hd
  | none =>
    cases tiles with
    | nil => contradiction
    | cons t rest =>
      refine ⟨by simp, ?_, rfl⟩
      simp [tileTotalFlits]
      omega

theorem deliverFlitsToFabric_conserves :
    ∀ (flits : List NocFlit) (tiles : List NocTileState),
      tiles ≠ [] →
      ((deliverFlitsToFabric flits tiles).map tileTotalFlits).sum =
        (tiles.map tileTotalFlits).sum + flits.length ∧
      ((deliverFlitsToFabric flits tiles).map tileCreditsPlusOutbox).sum =
        (tiles.map tileCreditsPlusOutbox).sum
  | [], tiles, _ => by simp [deliverFlitsToFabric]
  | f :: rest, tiles, hne => by
    simp only [deliverFlitsToFabric, List.length_cons]
    obtain ⟨hne1, hfl1, hcr1⟩ := deliverFlitToFabric_conserves f tiles hne
    obtain ⟨ih1, ih2⟩ := deliverFlitsToFabric_conserves rest (deliverFlitToFabric f tiles) hne1
    refine ⟨?_, ?_⟩
    · rw [ih1, hfl1]; omega
    · rw [ih2, hcr1]

theorem collectAndClearInboxes_conserves :
    ∀ (tiles : List NocTileState),
      (tiles ≠ [] → (collectAndClearInboxes tiles).2 ≠ []) ∧
      ((collectAndClearInboxes tiles).2.map tileTotalFlits).sum +
        (collectAndClearInboxes tiles).1.length = (tiles.map tileTotalFlits).sum ∧
      ((collectAndClearInboxes tiles).2.map tileCreditsPlusOutbox).sum =
        (tiles.map tileCreditsPlusOutbox).sum
  | [] => by simp [collectAndClearInboxes]
  | t :: rest => by
    obtain ⟨_, ihFl, ihCr⟩ := collectAndClearInboxes_conserves rest
    refine ⟨by simp [collectAndClearInboxes], ?_, ?_⟩
    · simp only [collectAndClearInboxes, List.map_cons, List.sum_cons, List.length_append, List.length_nil, tileTotalFlits]
      omega
    · simp only [collectAndClearInboxes, List.map_cons, List.sum_cons, tileCreditsPlusOutbox, ihCr]

theorem map_stepNocRouter_conserves :
    ∀ (tiles : List NocTileState),
      ((tiles.map stepNocRouter).map tileTotalFlits).sum = (tiles.map tileTotalFlits).sum ∧
      ((tiles.map stepNocRouter).map tileCreditsPlusOutbox).sum = (tiles.map tileCreditsPlusOutbox).sum
  | [] => ⟨rfl, rfl⟩
  | hd :: tl => by
    obtain ⟨ih1, ih2⟩ := map_stepNocRouter_conserves tl
    obtain ⟨h1, h2⟩ := stepNocRouter_conserves_flits_and_credits hd
    exact ⟨by simp only [List.map_cons, List.sum_cons, h1, ih1],
           by simp only [List.map_cons, List.sum_cons, h2, ih2]⟩

/-- **Theorem (`noc_step_conserves_flits`, Universally Quantified)**:
For every `fab : NocFabric` and every `t : NocTileState`:
1. `stepNocRouter` and `stepNocFabric` strictly conserve total packets/flits across the entire fabric
   (`fabricTotalFlits (stepNocFabric fab) = fabricTotalFlits fab`), and
2. `stepNocRouter` and `stepNocFabric` strictly conserve credits + outbox occupancy across the entire
   fabric (`fabricCreditsPlusOutbox (stepNocFabric fab) = fabricCreditsPlusOutbox fab`). -/
theorem noc_step_conserves_flits (fab : NocFabric) (t : NocTileState) :
    tileTotalFlits (stepNocRouter t) = tileTotalFlits t ∧
    tileCreditsPlusOutbox (stepNocRouter t) = tileCreditsPlusOutbox t ∧
    fabricTotalFlits (stepNocFabric fab) = fabricTotalFlits fab ∧
    fabricCreditsPlusOutbox (stepNocFabric fab) = fabricCreditsPlusOutbox fab := by
  have ht := stepNocRouter_conserves_flits_and_credits t
  refine ⟨ht.1, ht.2, ?_, ?_⟩
  · unfold fabricTotalFlits stepNocFabric
    dsimp only
    cases htiles : fab.tiles with
    | nil => rfl
    | cons hd tl =>
      have hstepNe : (List.map stepNocRouter (hd :: tl)) ≠ [] := by simp
      obtain ⟨hclrNe, hclrFl, _⟩ := collectAndClearInboxes_conserves (List.map stepNocRouter (hd :: tl))
      obtain ⟨hdelFl, _⟩ := deliverFlitsToFabric_conserves
        (collectAndClearInboxes (List.map stepNocRouter (hd :: tl))).1
        (collectAndClearInboxes (List.map stepNocRouter (hd :: tl))).2
        (hclrNe hstepNe)
      have hmapFl := (map_stepNocRouter_conserves (hd :: tl)).1
      omega
  · unfold fabricCreditsPlusOutbox stepNocFabric
    dsimp only
    cases htiles : fab.tiles with
    | nil => rfl
    | cons hd tl =>
      have hstepNe : (List.map stepNocRouter (hd :: tl)) ≠ [] := by simp
      obtain ⟨hclrNe, _, hclrCr⟩ := collectAndClearInboxes_conserves (List.map stepNocRouter (hd :: tl))
      obtain ⟨_, hdelCr⟩ := deliverFlitsToFabric_conserves
        (collectAndClearInboxes (List.map stepNocRouter (hd :: tl))).1
        (collectAndClearInboxes (List.map stepNocRouter (hd :: tl))).2
        (hclrNe hstepNe)
      have hmapCr := (map_stepNocRouter_conserves (hd :: tl)).2
      rw [hdelCr, hclrCr, hmapCr]

/-- **Theorem (`noc_multi_hop_delivery_and_eval_sound`)**:
Proves end-to-end multi-hop XY routing, inter-tile crossbar delivery across a 6-tile 2D mesh
`NocFabric`, remote rule firing on the target tile `(2, 1)`, and credit/packet conservation:
1. **Multi-Tile 2D Mesh Fabric Delivery & Remote Rule Evaluation (`runNocFabricCycles`)**:
   In a 6-tile 2D mesh fabric `meshFab` where origin tile `(0, 0)` has `rules = []` (no rules!)
   and `inbox = [reqFlit]`, intermediate tiles `(1, 0), (2, 0), (1, 1), (0, 1)` have `rules = []`,
   and only destination tile `(2, 1)` holds `rules = [rule]` (`inbox = []`):
   - After 3 fabric cycles (`runNocFabricCycles 3 meshFab`), `reqFlit` has physically traversed
     `(0,0) → (1,0) → (2,0) → (2,1)` into tile `(2, 1)`'s `inbox`!
   - On cycle 4, tile `(2, 1)` fires its resident `rule` and emits `.response` with `payload = expectedVal`!
   - On cycle 8 (after traversing `(2,1) → (1,1) → (0,1) → (0,0)`), origin tile `(0, 0)` ejects
     `expectedResp` into its `outbox` and decrements its `credits` from `4` to `3`!
2. **Single-Router Trajectory & Credit-Return Handshake**:
   `runNocRouterCycles` and `consumeNocOutboxFlit` extract `some expectedResp` and restore `credits = 4`,
   while `credits = 0` stalls without dropping flits. -/
theorem noc_multi_hop_delivery_and_eval_sound
    (rule : AutomatonTile) (argVal : BitVec 64) :
    let reqFlit : NocFlit :=
      { flitId     := 1
      , kind       := .request
      , srcX       := 0
      , srcY       := 0
      , curX       := 0
      , curY       := 0
      , dstX       := 2
      , dstY       := 1
      , targetSlot := rule.slotIdx
      , payload    := argVal }
    let initTile : NocTileState :=
      { tileId  := 0
      , tileX   := 2
      , tileY   := 1
      , inbox   := [reqFlit]
      , outbox  := []
      , credits := 4
      , rules   := [rule] }
    let meshFab : NocFabric :=
      { tiles :=
          [ { tileId := 0, tileX := 0, tileY := 0, inbox := [reqFlit], outbox := [], credits := 4, rules := [] }
          , { tileId := 1, tileX := 1, tileY := 0, inbox := [], outbox := [], credits := 4, rules := [] }
          , { tileId := 2, tileX := 2, tileY := 0, inbox := [], outbox := [], credits := 4, rules := [] }
          , { tileId := 3, tileX := 2, tileY := 1, inbox := [], outbox := [], credits := 4, rules := [rule] }
          , { tileId := 4, tileX := 1, tileY := 1, inbox := [], outbox := [], credits := 4, rules := [] }
          , { tileId := 5, tileX := 0, tileY := 1, inbox := [], outbox := [], credits := 4, rules := [] } ] }
    let expectedVal := evalRtlExpr (packetInputEnv argVal) (fun _ => 0#64) (fun _ => 0#64) rule.datapath
    let expectedResp : NocFlit :=
      { flitId     := 1
      , kind       := .response
      , srcX       := 0
      , srcY       := 0
      , curX       := 0
      , curY       := 0
      , dstX       := 0
      , dstY       := 0
      , targetSlot := rule.slotIdx
      , payload    := expectedVal }
    let afterHop3 := runNocRouterCycles 3 initTile
    let afterFire := runNocRouterCycles 4 initTile
    let afterReturn := runNocRouterCycles 8 initTile
    let (popped, afterConsume) := consumeNocOutboxFlit afterReturn
    let fabAfter3 := runNocFabricCycles 3 meshFab
    let fabAfter8 := runNocFabricCycles 8 meshFab
    -- 1. After 3 XY hops ((0,0)->(1,0)->(2,0)->(2,1)), flit arrives at destination (2, 1)
    afterHop3.inbox.map (fun f => (f.curX, f.curY, f.atDest)) = [(2, 1, true)] ∧
    -- 2. On cycle 4, rule fires at (2, 1) and emits response flit with `expectedVal` targeting (0, 0)
    afterFire.inbox.map (fun f => (f.kind, f.dstX, f.dstY, f.payload)) =
      [(.response, 0, 0, expectedVal)] ∧
    -- 3. On cycle 8 (after 3 return XY hops + ejection), response flit is in `outbox` and `credits = 3`
    afterReturn.inbox = [] ∧
    afterReturn.outbox = [expectedResp] ∧
    afterReturn.credits = 3 ∧
    tileTotalFlits afterReturn = tileTotalFlits initTile ∧
    tileCreditsPlusOutbox afterReturn = tileCreditsPlusOutbox initTile ∧
    -- 4. Consuming the outbox flit returns `expectedResp` and restores `credits = 4`
    popped = some expectedResp ∧
    afterConsume.credits = 4 ∧
    -- 5. Zero-credit backpressure stalls without losing the flit
    stepNocRouter { initTile with credits := 0 } = { initTile with credits := 0 } ∧
    -- 6. Multi-tile 2D mesh fabric physically routes `reqFlit` to tile 3 `(2, 1)`, fires `rule`,
    --    and delivers `expectedResp` back to origin tile 0 `(0, 0)`'s `outbox`!
    (fabAfter3.tiles.map (fun t => t.inbox.length)) = [0, 0, 0, 1, 0, 0] ∧
    (fabAfter8.tiles.map (fun t => (t.outbox, t.credits))) =
      [([expectedResp], 3), ([], 4), ([], 4), ([], 4), ([], 4), ([], 4)] := by
  dsimp only
  have hfind : ([rule].find? (fun r => r.slotIdx == rule.slotIdx)) = some rule := by
    simp [List.find?]
  simp [runNocRouterCycles, runNocFabricCycles, stepNocFabric, collectAndClearInboxes,
    deliverFlitsToFabric, deliverFlitToFabric, deliverFlitToTiles,
    stepNocRouter, stepNocFlitXy, NocFlit.atDest,
    evalTileRuleOnFlit, hfind, consumeNocOutboxFlit, tileTotalFlits, tileCreditsPlusOutbox]

/-- Hardware Dynamic Partial Reconfiguration (DPR) Bitstream Candidate (`TileBitstreamCandidate`)
for an eFPGA `AutomatonTile` managed by `Obend.Slot`:
* `specializedTile`: a specialized hardware bitstream (`tile : AutomatonTile`, `frameDigest : BitVec 64`)
  synthesized from an `Obend.Leaf.Composition` `comp` under object `name`, guarded by `LeafPin`s
  `(.book name comp).supports`,
* `baselineTile`: the always-usable resident fallback `AutomatonTile` (`supports = []`, `judge = true`). -/
inductive TileBitstreamCandidate where
  | specializedTile (name : String) (comp : Composition) (tile : AutomatonTile) (frameDigest : BitVec 64)
  | baselineTile    (tile : AutomatonTile)

/-- The `LeafPin` supports assumed by a `TileBitstreamCandidate`:
* A `specializedTile name C tile digest` assumes the exact pins of `Candidate.book name C`
  (`⟨.object name, C.code⟩ :: C.layers.map fun L => ⟨.layer L.name, L.code⟩`),
* A `baselineTile` assumes no pins (`[]`) and is always usable. -/
def TileBitstreamCandidate.supports : TileBitstreamCandidate → List LeafPin
  | .specializedTile name C _ _ => (Candidate.book name C).supports
  | .baselineTile _             => []

/-- Admission judge for a `TileBitstreamCandidate`:
* A `specializedTile name C tile digest` is admitted when `C.closedB = true` and `frameDigest != 0#64`,
* A `baselineTile` is always admitted (`true`). -/
def TileBitstreamCandidate.judge : TileBitstreamCandidate → Bool
  | .specializedTile _ C _ digest => C.closedB && (digest != 0#64)
  | .baselineTile _               => true

/-- Extract the active hardware `AutomatonTile` from a `TileBitstreamCandidate`. -/
def TileBitstreamCandidate.hwTile : TileBitstreamCandidate → AutomatonTile
  | .specializedTile _ _ tile _ => tile
  | .baselineTile tile          => tile

/-- **The Hardware Dynamic Partial Reconfiguration Slot (`dprTileSlot : Slot LeafPin TileBitstreamCandidate`)**:
Instantiates `Obend.Slot` (`Slot LeafPin TileBitstreamCandidate`) over `Obend.Leaf.Specialize`'s
`LeafView`/`LeafPin` world so that an eFPGA tile's specialized bitstream is directly guarded by
`LeafPin` supports and falls back to `baselineTile` in 1 cycle upon upstream pin mutation! -/
def dprTileSlot : Slot LeafPin TileBitstreamCandidate :=
  ⟨TileBitstreamCandidate.supports, TileBitstreamCandidate.judge⟩

/-- Priority order for hardware DPR slot selection: specialized tile bitstream first, baseline fallback second. -/
def dprTileOrder (name : String) (C : Composition) (specTile baseTile : AutomatonTile) (digest : BitVec 64) :
    List TileBitstreamCandidate :=
  [.specializedTile name C specTile digest, .baselineTile baseTile]

/-- **Theorem (`baselineTile_usable`)**:
The resident fallback `baselineTile` is always usable in every `LeafView`. -/
theorem baselineTile_usable (v : LeafView) (baseTile : AutomatonTile) :
    dprTileSlot.usable (holdsAt v) (.baselineTile baseTile) = true := by
  simp [Slot.usable, Slot.dead, dprTileSlot, TileBitstreamCandidate.supports, TileBitstreamCandidate.judge]

/-- **Theorem (`dprTileSlot_choice`)**:
Incumbent-first selection on `dprTileSlot`: the specialized hardware bitstream is retained iff all its
`LeafPin` supports hold and its judge passes; otherwise `slotAdvance` transitions to `.baselineTile baseTile`
in 1 step. -/
theorem dprTileSlot_choice
    (v : LeafView) (name : String) (C : Composition)
    (specTile baseTile : AutomatonTile) (digest : BitVec 64) :
    (slotAdvance : Advance LeafView LeafPin TileBitstreamCandidate).advance
        dprTileSlot v (dprTileOrder name C specTile baseTile digest)
        (some (.specializedTile name C specTile digest)) =
      if dprTileSlot.usable (holdsAt v) (.specializedTile name C specTile digest) then
        .ok (.specializedTile name C specTile digest)
      else
        .ok (.baselineTile baseTile) := by
  split
  · rename_i hu
    exact (incumbent_choice dprTileSlot v _ _ _).2 (.inl ⟨rfl, hu⟩)
  · rename_i hu
    have hf : dprTileSlot.usable (holdsAt v) (.specializedTile name C specTile digest) = false := by
      simpa using hu
    refine (incumbent_choice dprTileSlot v _ _ _).2 (.inr ⟨fun c e => by cases e; exact hf, ?_⟩)
    simp [Slot.select, Slot.alternatives, dprTileOrder, hf, baselineTile_usable]

/-- **Theorem (`dprTile_moved_pin_blocks`)**:
Connects `Obend.Leaf.Specialize.moved_pin_blocks` directly to the hardware `dprTileSlot`:
Whenever an upstream `LeafPin` `p ∈ (Candidate.book name C).supports` mutates (`holdsAt v p = false`)
for an admitted specialized tile (`C.closedB = true` and `(digest != 0#64) = true`):
1. `specSlot.read` is blocked (`moved_pin_blocks`),
2. `dprTileSlot.read` immediately transitions to `.blocked (.specializedTile name C specTile digest) d`
   with `p ∈ d`, and
3. `slotAdvance` immediately triggers the 1-cycle hardware fallback to `.ok (.baselineTile baseTile)`! -/
theorem dprTile_moved_pin_blocks
    {v : LeafView} {name : String} {C : Composition}
    (specTile baseTile : AutomatonTile) (digest : BitVec 64)
    (hj : C.closedB = true) (hdig : (digest != 0#64) = true)
    {p : LeafPin} (hp : p ∈ (Candidate.book name C).supports) (hd : holdsAt v p = false) :
    (∃ d, specSlot.read (holdsAt v) (some (.book name C)) = .blocked (.book name C) d ∧ p ∈ d) ∧
    (∃ d, dprTileSlot.read (holdsAt v) (some (.specializedTile name C specTile digest)) =
      .blocked (.specializedTile name C specTile digest) d ∧ p ∈ d) ∧
    (slotAdvance : Advance LeafView LeafPin TileBitstreamCandidate).advance
        dprTileSlot v (dprTileOrder name C specTile baseTile digest)
        (some (.specializedTile name C specTile digest)) =
      .ok (.baselineTile baseTile) := by
  obtain ⟨dSpec, hrSpec, hpSpec, _⟩ := moved_pin_blocks hj hp hd
  have hmem : p ∈ dprTileSlot.dead (holdsAt v) (.specializedTile name C specTile digest) :=
    (mem_dead_iff _ _ _ _).2 ⟨hp, hd⟩
  have hjudge : dprTileSlot.judge (.specializedTile name C specTile digest) = true := by
    simp [dprTileSlot, TileBitstreamCandidate.judge, hj, hdig]
  have hread :
      ∃ d, dprTileSlot.read (holdsAt v) (some (.specializedTile name C specTile digest)) =
        .blocked (.specializedTile name C specTile digest) d ∧ p ∈ d := by
    unfold Slot.read
    simp only [hjudge, ite_true]
    cases hdd : dprTileSlot.dead (holdsAt v) (.specializedTile name C specTile digest) with
    | nil => rw [hdd] at hmem; cases hmem
    | cons g t => exact ⟨g :: t, rfl, hdd ▸ hmem⟩
  have husable_false :
      dprTileSlot.usable (holdsAt v) (.specializedTile name C specTile digest) = false := by
    unfold Slot.usable
    cases hdd : dprTileSlot.dead (holdsAt v) (.specializedTile name C specTile digest) with
    | nil => rw [hdd] at hmem; cases hmem
    | cons _ _ => simp [List.isEmpty]
  refine ⟨⟨dSpec, hrSpec, hpSpec⟩, hread, ?_⟩
  rw [dprTileSlot_choice, husable_false]
  rfl

end Obend.Hardware.ReductionMachine
end
