module
/-
# Obend.Hardware.Fabric — Linear Wire-Fanout, 2D eFPGA Mesh, Merkle/Vault Silicon & Hardware Slot

Connects Objective Bend's resource system, 2D eFPGA fabric bitstreams (FABulous eFPGA),
Merkle-dated Receipt verification (`Obend.Receipt.Merkle`), capability-guarded `Vault.Law`
registers (`DeosCounter.obend`), and the 3-tier Hardware Specialization Slot (`Obend.Slot`):

* **Linear & Affine Hardware Wire-Fanout Typechecker**:
  - `linear_or_affine_zero_forks`: `.linear` (`fanout = 1`) and `.affine` (`fanout ≤ 1`) nets require
    `0` elastic `Fork` synchronizers;
  - `quantityOnce_accepted_and_duplicated_refused`: accepts `QuantityOnce.obend` and refuses
    `QuantityDuplicated.obend`.
* **2D Multi-Tile eFPGA Mesh & Configuration Frame Loader**:
  - `stepFrameLoader` (`frameLoader_immutable_when_locked`): shifts configuration frames into the
    2×2 eFPGA array while `cfgLocked = false` and hardware-locks the bitstream once `cfgLocked = true`;
  - `efpga_mesh_twiceReview_sound`: synthesizes `TwiceReview.obend` onto the 2×2 eFPGA mesh (`twiceOfThree = 7`).
* **Hardware Merkle-View Receipt Verifier Engine**:
  - `evalHwMerkleClimb4` (`hwMerkle_climb_complete`): 2-stage positional Merkle tree climber for 4-leaf views.
* **Hardware `DeosCounter.obend` + `Obend.Vault.Law` Register Bank**:
  - `stepDeosHw`: proves uncredentialed `reset` is refused and preserves `count`
    (`deosHw_reset_without_cred_preserves_count`), credentialed `reset` zeros `count`
    (`deosHw_reset_with_cred_zeros_count`), `inc`/`dec` round-trips (`deosHw_inc_dec_roundtrip`),
    and `writeOnce` locks non-zero `cfgTag` (`deosHw_writeOnce_immutable`).
* **3-Tier Hardware Specialization Slot (`HwCandidate`: `.bitstream` → `.book` → `.machine`)**:
  - `hwBitstream_usable_sound`: a usable `.bitstream` candidate at `viewOf k name C'` guarantees both
    PVT static timing closure (`timingSignoff_sound`) and behavioral equivalence (`≈b`) with `C'.object`;
  - `hwMoved_pin_blocks_bitstream`: a moved layer or object pin blocks the hardware `.bitstream` by name.
-/
public import Obend.Hardware.Silicon
public import Obend.Hardware.Process
public import Obend.Leaf.Specialize
@[expose] public section

namespace Obend.Hardware.Fabric
open Obend.Core.Term
open Obend.Equiv
open Obend.Logic
open Obend.Slot
open Obend.Slot.World
open Obend.Leaf
open Obend.Hardware.Process
set_option autoImplicit false

/-! ## 1. Linear & Affine Hardware Wire-Fanout Typechecker -/

inductive Mult where
  | linear
  | affine
  | unrestricted
  deriving DecidableEq, Repr

inductive NetExpr where
  | wire (name : String)
  | const64 (val : Nat)
  | add64 (lhs rhs : NetExpr)
  | sub64 (lhs rhs : NetExpr)
  deriving DecidableEq, Repr

def countFanout (w : String) : NetExpr → Nat
  | .wire n      => if n == w then 1 else 0
  | .const64 _   => 0
  | .add64 a b   => countFanout w a + countFanout w b
  | .sub64 a b   => countFanout w a + countFanout w b

def checkWireMult (m : Mult) (fanout : Nat) : Bool :=
  match m with
  | .linear       => fanout == 1
  | .affine       => fanout ≤ 1
  | .unrestricted => true

def checkNetlistMult (inputs : List (String × Mult)) (e : NetExpr) : Bool :=
  inputs.all (fun (w, m) => checkWireMult m (countFanout w e))

def requiredForkCells (w : String) (e : NetExpr) : Nat :=
  let f := countFanout w e
  if f ≤ 1 then 0 else f - 1

theorem linear_or_affine_zero_forks (w : String) (m : Mult) (e : NetExpr)
    (hm : m = .linear ∨ m = .affine)
    (hok : checkWireMult m (countFanout w e) = true) :
    requiredForkCells w e = 0 := by
  dsimp [requiredForkCells]
  rcases hm with rfl | rfl
  · simp only [checkWireMult, beq_iff_eq] at hok
    simp [hok]
  · simp only [checkWireMult, decide_eq_true_eq] at hok
    simp [hok]

def quantityOnceInputs : List (String × Mult) :=
  [("x", .affine), ("y", .linear)]

def quantityOnceNet : NetExpr :=
  .add64 (.wire "x") (.wire "y")

def quantityDuplicatedInputs : List (String × Mult) :=
  [("x", .affine)]

def quantityDuplicatedNet : NetExpr :=
  .add64 (.wire "x") (.wire "x")

theorem quantityOnce_accepted_and_duplicated_refused :
    checkNetlistMult quantityOnceInputs quantityOnceNet = true ∧
    checkNetlistMult quantityDuplicatedInputs quantityDuplicatedNet = false :=
  ⟨rfl, rfl⟩

/-! ## 2. 2D Multi-Tile eFPGA Mesh, Switch Matrix & Frame Loader -/

inductive SwitchSrc where
  | localIn
  | northIn
  | eastIn
  | southIn
  | westIn
  deriving DecidableEq, Repr

inductive TileAluOp where
  | passA
  | addImm (imm : BitVec 64)
  | addAB
  | subAB
  deriving DecidableEq, Repr

structure EfpgaTileFrame where
  muxA : SwitchSrc
  muxB : SwitchSrc
  op   : TileAluOp
  deriving DecidableEq, Repr

def blankTileFrame : EfpgaTileFrame where
  muxA := .localIn
  muxB := .localIn
  op   := .passA

def evalTileMux (src : SwitchSrc) (loc n e s w : BitVec 64) : BitVec 64 :=
  match src with
  | .localIn => loc
  | .northIn => n
  | .eastIn  => e
  | .southIn => s
  | .westIn  => w

def evalConfiguredTile (frame : EfpgaTileFrame) (loc n e s w : BitVec 64) : BitVec 64 :=
  let a := evalTileMux frame.muxA loc n e s w
  let b := evalTileMux frame.muxB loc n e s w
  match frame.op with
  | .passA      => a
  | .addImm imm => a + imm
  | .addAB      => a + b
  | .subAB      => a - b

structure Mesh2x2Config where
  t00 : EfpgaTileFrame
  t10 : EfpgaTileFrame
  t01 : EfpgaTileFrame
  t11 : EfpgaTileFrame
  deriving DecidableEq, Repr

structure FrameLoaderState where
  mesh      : Mesh2x2Config
  cfgLocked : Bool
  deriving DecidableEq, Repr

def stepFrameLoader (st : FrameLoaderState) (cfgWrEn cfgLockCmd : Bool)
    (tileIdx : Fin 4) (frameIn : EfpgaTileFrame) : FrameLoaderState :=
  if st.cfgLocked then
    st
  else
    let nextMesh :=
      if cfgWrEn then
        match tileIdx.val with
        | 0 => { st.mesh with t00 := frameIn }
        | 1 => { st.mesh with t10 := frameIn }
        | 2 => { st.mesh with t01 := frameIn }
        | _ => { st.mesh with t11 := frameIn }
      else
        st.mesh
    { mesh := nextMesh, cfgLocked := cfgLockCmd }

theorem frameLoader_immutable_when_locked (st : FrameLoaderState) (hlock : st.cfgLocked = true)
    (cfgWrEn cfgLockCmd : Bool) (tileIdx : Fin 4) (frameIn : EfpgaTileFrame) :
    stepFrameLoader st cfgWrEn cfgLockCmd tileIdx frameIn = st := by
  simp [stepFrameLoader, hlock]

def evalMesh2x2Snake (cfg : Mesh2x2Config) (in00 : BitVec 64) : BitVec 64 :=
  let out00 := evalConfiguredTile cfg.t00 in00 0#64 0#64 0#64 0#64
  let out10 := evalConfiguredTile cfg.t10 0#64 0#64 0#64 0#64 out00
  let out11 := evalConfiguredTile cfg.t11 0#64 out10 0#64 0#64 0#64
  let out01 := evalConfiguredTile cfg.t01 0#64 0#64 out11 0#64 0#64
  out01

def twiceReviewMeshConfig : Mesh2x2Config where
  t00 := { muxA := .localIn, muxB := .localIn, op := .addImm 1#64 }
  t10 := { muxA := .westIn,  muxB := .localIn, op := .addImm 1#64 }
  t11 := { muxA := .northIn, muxB := .localIn, op := .addImm 1#64 }
  t01 := { muxA := .eastIn,  muxB := .localIn, op := .addImm 1#64 }

def twiceReviewSpec (v : BitVec 64) : BitVec 64 :=
  let baseReview (x : BitVec 64) := x + 1#64
  let augReview  (x : BitVec 64) := baseReview x + 1#64
  augReview (augReview v)

theorem efpga_mesh_twiceReview_sound (v : BitVec 64) :
    let st0 : FrameLoaderState := { mesh := ⟨blankTileFrame, blankTileFrame, blankTileFrame, blankTileFrame⟩, cfgLocked := false }
    let st1 := stepFrameLoader st0 true false ⟨0, by decide⟩ twiceReviewMeshConfig.t00
    let st2 := stepFrameLoader st1 true false ⟨1, by decide⟩ twiceReviewMeshConfig.t10
    let st3 := stepFrameLoader st2 true false ⟨2, by decide⟩ twiceReviewMeshConfig.t01
    let st4 := stepFrameLoader st3 true true  ⟨3, by decide⟩ twiceReviewMeshConfig.t11
    st4.cfgLocked = true ∧
    evalMesh2x2Snake st4.mesh v = twiceReviewSpec v ∧
    evalMesh2x2Snake st4.mesh 3#64 = 7#64 :=
  ⟨rfl, rfl, rfl⟩

/-! ## 3. Hardware Merkle-View Receipt Verifier Engine (`Obend.Receipt.Merkle`) -/

def hwMix64 (left right : BitVec 64) : BitVec 64 :=
  let sum := left + (right * 0x9E3779B97F4A7C15#64)
  sum ^^^ (sum >>> 17)

def hwMerkleRoot4 (v0 v1 v2 v3 : BitVec 64) : BitVec 64 :=
  hwMix64 (hwMix64 v0 v1) (hwMix64 v2 v3)

structure HwMerkleOpening4 where
  pos0 : Bool
  pos1 : Bool
  val  : BitVec 64
  sib0 : BitVec 64
  sib1 : BitVec 64
  deriving DecidableEq, Repr

def makeHwOpening4 (v0 v1 v2 v3 : BitVec 64) (pos0 pos1 : Bool) : HwMerkleOpening4 :=
  let h01 := hwMix64 v0 v1
  let h23 := hwMix64 v2 v3
  match pos1, pos0 with
  | false, false => { pos0 := false, pos1 := false, val := v0, sib0 := v1, sib1 := h23 }
  | false, true  => { pos0 := true,  pos1 := false, val := v1, sib0 := v0, sib1 := h23 }
  | true,  false => { pos0 := false, pos1 := true,  val := v2, sib0 := v3, sib1 := h01 }
  | true,  true  => { pos0 := true,  pos1 := true,  val := v3, sib0 := v2, sib1 := h01 }

def evalHwMerkleClimb4 (op : HwMerkleOpening4) : BitVec 64 :=
  let lvl1 := if op.pos0 then hwMix64 op.sib0 op.val else hwMix64 op.val op.sib0
  if op.pos1 then hwMix64 op.sib1 lvl1 else hwMix64 lvl1 op.sib1

def verifyHwReceipt4 (datedRoot : BitVec 64) (op : HwMerkleOpening4) (lawOk : Bool) : Bool :=
  (evalHwMerkleClimb4 op == datedRoot) && lawOk

theorem hwMerkle_climb_complete (v0 v1 v2 v3 : BitVec 64) (pos0 pos1 : Bool) :
    evalHwMerkleClimb4 (makeHwOpening4 v0 v1 v2 v3 pos0 pos1) = hwMerkleRoot4 v0 v1 v2 v3 := by
  cases pos0 <;> cases pos1 <;> rfl

/-! ## 4. Hardware `DeosCounter.obend` + `Obend.Vault.Law` Register Bank -/

inductive DeosCmd where
  | inc (delta : Nat)
  | dec (delta : Nat)
  | reset (hasProofCred : Bool)
  | writeTag (newTag : Nat)
  deriving DecidableEq, Repr

structure DeosHwState where
  count        : Nat
  cfgTag       : Nat
  lastAccepted : Bool
  deriving DecidableEq, Repr

def stepDeosHw (st : DeosHwState) : DeosCmd → DeosHwState
  | .inc d =>
    { st with count := st.count + d, lastAccepted := true }
  | .dec d =>
    { st with count := st.count - d, lastAccepted := true }
  | .reset hasCred =>
    if hasCred then
      { st with count := 0, lastAccepted := true }
    else
      { st with lastAccepted := false }
  | .writeTag tag =>
    if st.cfgTag == 0 || tag == st.cfgTag then
      { st with cfgTag := tag, lastAccepted := true }
    else
      { st with lastAccepted := false }

theorem deosHw_reset_without_cred_preserves_count (st : DeosHwState) :
    (stepDeosHw st (.reset false)).count = st.count ∧
    (stepDeosHw st (.reset false)).lastAccepted = false := by
  simp [stepDeosHw]

theorem deosHw_reset_with_cred_zeros_count (st : DeosHwState) :
    (stepDeosHw st (.reset true)).count = 0 ∧
    (stepDeosHw st (.reset true)).lastAccepted = true := by
  simp [stepDeosHw]

theorem deosHw_inc_dec_roundtrip (st : DeosHwState) (d : Nat) :
    (stepDeosHw (stepDeosHw st (.inc d)) (.dec d)).count = st.count := by
  simp [stepDeosHw]

theorem deosHw_writeOnce_immutable (st : DeosHwState) (cmd : DeosCmd) (hne : st.cfgTag ≠ 0) :
    (stepDeosHw st cmd).cfgTag = st.cfgTag := by
  cases cmd with
  | inc d => rfl
  | dec d => rfl
  | reset c => cases c <;> rfl
  | writeTag t =>
    simp only [stepDeosHw]
    split
    · rename_i hcond
      simp only [Bool.or_eq_true, beq_iff_eq] at hcond
      rcases hcond with h0 | hsame
      · exact absurd h0 hne
      · exact hsame
    · rfl

/-! ## 5. 3-Tier Hardware Specialization Slot (`.bitstream` → `.book` → `.machine`) -/

/-- The 3-tier candidates of the hardware specialization slot:
1. `.bitstream`: FPGA / eFPGA / ASIC silicon image pinned to `comp`'s layers + object and judged
   by both `comp.closedB` and PVT static timing signoff (`checkTimingSignoff corner periodPs critPath`);
2. `.book`: software leaf book (`Obend.Leaf.emit comp`);
3. `.machine`: unflattened Core4 reference machine (always usable fallback). -/
inductive HwCandidate where
  | bitstream (name : String) (comp : Composition) (corner : ProcessCorner) (periodPs : Nat) (critPath : TimingPath)
  | book (name : String) (comp : Composition)
  | machine

def HwCandidate.supports : HwCandidate → List LeafPin
  | .bitstream name C _ _ _ => ⟨.object name, C.code⟩ :: C.layers.map fun L => ⟨.layer L.name, L.code⟩
  | .book name C            => ⟨.object name, C.code⟩ :: C.layers.map fun L => ⟨.layer L.name, L.code⟩
  | .machine                => []

def HwCandidate.judge : HwCandidate → Bool
  | .bitstream _ C corner periodPs critPath => C.closedB && checkTimingSignoff corner periodPs critPath
  | .book _ C                               => C.closedB
  | .machine                                => true

def hwSpecSlot : Slot LeafPin HwCandidate := ⟨HwCandidate.supports, HwCandidate.judge⟩

def hwSpecOrder (name : String) (C : Composition) (corner : ProcessCorner) (periodPs : Nat) (critPath : TimingPath) :
    List HwCandidate :=
  [.bitstream name C corner periodPs critPath, .book name C, .machine]

theorem hwMachine_usable (v : LeafView) : hwSpecSlot.usable (holdsAt v) .machine = true := by
  simp [Slot.usable, Slot.dead, hwSpecSlot, HwCandidate.supports, HwCandidate.judge]

/-- **A usable hardware bitstream is both timing-closed and behaviorally sound (`≈b`)**:
When `.bitstream name C corner periodPs critPath` is usable at `viewOf k name C'`,
1. `emit C = emit C'` (the bitstream's pinned composition matches the view's object),
2. `critPath` is free of both setup and hold violations at process corner `corner`, and
3. When `C'` is closed, every member `m` computed by the flattened book/hardware is `≈b` to `C'.object.m`. -/
theorem hwBitstream_usable_sound {k : Nat} {name : String} {C C' : Composition}
    {corner : ProcessCorner} {periodPs : Nat} {critPath : TimingPath}
    (h : hwSpecSlot.usable (holdsAt (viewOf k name C')) (.bitstream name C corner periodPs critPath) = true) :
    emit C = emit C' ∧
    (maxArrivalPs corner critPath + corner.tSetupPs + corner.tSkewPs ≤ periodPs ∧
     corner.tHoldPs + corner.tSkewPs ≤ minArrivalPs corner critPath) ∧
    (C'.closedB = true → ∀ m, .get (emit C).link m ≈b .get C'.object m) := by
  obtain ⟨hjudge, hall⟩ := (usable_iff _ _ _).1 h
  simp only [hwSpecSlot, HwCandidate.judge, Bool.and_eq_true] at hjudge
  have hbook : specSlot.usable (holdsAt (viewOf k name C')) (.book name C) = true :=
    (usable_iff _ _ _).2 ⟨hjudge.1, hall⟩
  obtain ⟨e, hbs⟩ := book_usable_sound hbook
  exact ⟨e, timingSignoff_sound hjudge.2, hbs⟩

/-- **A moved layer or object pin blocks the hardware bitstream by name**:
When a support `p` of an admitted `.bitstream` does not hold at view `v`, the slot's read blocks
the bitstream and names `p` among the dead supports. -/
theorem hwMoved_pin_blocks_bitstream {v : LeafView} {name : String} {C : Composition}
    {corner : ProcessCorner} {periodPs : Nat} {critPath : TimingPath}
    (hj : (C.closedB && checkTimingSignoff corner periodPs critPath) = true)
    {p : LeafPin} (hp : p ∈ (HwCandidate.bitstream name C corner periodPs critPath).supports)
    (hd : holdsAt v p = false) :
    ∃ d, hwSpecSlot.read (holdsAt v) (some (.bitstream name C corner periodPs critPath)) =
      .blocked (.bitstream name C corner periodPs critPath) d ∧ p ∈ d := by
  have hmem : p ∈ hwSpecSlot.dead (holdsAt v) (.bitstream name C corner periodPs critPath) :=
    (mem_dead_iff _ _ _ _).2 ⟨hp, hd⟩
  have hjudge : hwSpecSlot.judge (.bitstream name C corner periodPs critPath) = true := hj
  unfold Slot.read
  simp only [hjudge, ite_true]
  cases hdd : hwSpecSlot.dead (holdsAt v) (.bitstream name C corner periodPs critPath) with
  | nil => rw [hdd] at hmem; cases hmem
  | cons g t => exact ⟨g :: t, rfl, hdd ▸ hmem⟩

end Obend.Hardware.Fabric
end
