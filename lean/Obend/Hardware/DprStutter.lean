module
public import Obend.Category.Refines
public import Obend.Hardware.Fabulous.Net

public section
namespace Obend.Hardware.DprStutter

/-! A canonical ICAP transport format for a six-input LUT4/FF tile bank. The
vendor-specific mapping from this transport to FABulous ConfigBits remains the
readback/LEC boundary in Fabulous.Tile; these are not claimed to be vendor bytes.
CRC-64/ECMA detects corruption, not maliciously recomputed configurations. -/

structure TechmappedTile where
  lut : BitVec 16
  registered : Bool
  a : Fin 6
  b : Fin 6
  c : Fin 6
  d : Fin 6
  deriving DecidableEq, Repr, Inhabited

abbrev DecodedTile := TechmappedTile
abbrev TechmappedFabric := List TechmappedTile

structure TileFrame where
  payload : BitVec 64
  crc : BitVec 64
  deriving DecidableEq, Repr, Inhabited

@[expose] def crcBit (r : BitVec 64) : BitVec 64 :=
  if r.getLsbD 63 then (r <<< 1) ^^^ 0x42F0E1EBA9EA3693#64 else r <<< 1

@[expose] def frameCrc (w : BitVec 64) : BitVec 64 :=
  (List.range 64).foldl (fun r _ => crcBit r) w

@[expose] def encodePayload (t : TechmappedTile) : BitVec 64 :=
  BitVec.ofNat 64 (t.lut.toNat + 65536 * t.registered.toNat +
    131072 * t.a.val + 1048576 * t.b.val + 8388608 * t.c.val +
    67108864 * t.d.val + 536870912 * 0xFAB)

@[expose] def encodeTileFrame (t : TechmappedTile) : TileFrame :=
  let w := encodePayload t
  ⟨w, frameCrc w⟩

@[expose] def decodeTileFrame (f : TileFrame) : Option DecodedTile :=
  let w := f.payload.toNat
  if f.crc = frameCrc f.payload ∧ w / 536870912 = 0xFAB then
    if h : w / 131072 % 8 < 6 ∧ w / 1048576 % 8 < 6 ∧
        w / 8388608 % 8 < 6 ∧ w / 67108864 % 8 < 6 then
      some ⟨BitVec.ofNat 16 w, decide (w / 65536 % 2 = 1),
        ⟨_, h.1⟩, ⟨_, h.2.1⟩, ⟨_, h.2.2.1⟩, ⟨_, h.2.2.2⟩⟩
    else none
  else none

@[expose] def encodeTileFrames (tiles : Array TechmappedTile) : Array TileFrame :=
  tiles.map encodeTileFrame

/-- Exact expected bank size is verifier supplied, including the upper bound.
No truncation, padding, or silently ignored trailing frames. -/
@[expose] def decodeTileFrames (expected : Nat) (frames : Array TileFrame) : Option (Array DecodedTile) :=
  if frames.size = expected then frames.mapM decodeTileFrame else none

theorem payload_fields (t : TechmappedTile) :
    let w := (encodePayload t).toNat
    w % 65536 = t.lut.toNat ∧ w / 65536 % 2 = t.registered.toNat ∧
    w / 131072 % 8 = t.a.val ∧ w / 1048576 % 8 = t.b.val ∧
    w / 8388608 % 8 = t.c.val ∧ w / 67108864 % 8 = t.d.val ∧
    w / 536870912 = 0xFAB := by
  have hl := t.lut.isLt
  have ha := t.a.isLt
  have hb := t.b.isLt
  have hc := t.c.isLt
  have hd := t.d.isLt
  cases h : t.registered <;>
    simp [encodePayload, BitVec.toNat_ofNat, h, Bool.toNat] <;> omega

theorem decodeTileFrame_encode (t : TechmappedTile) :
    decodeTileFrame (encodeTileFrame t) = some t := by
  obtain ⟨hl, hr, ha, hb, hc, hd, hm⟩ := payload_fields t
  have he : BitVec.ofNat 16 (encodePayload t).toNat = t.lut := by
    apply BitVec.eq_of_toNat_eq
    simpa using hl
  have hreg : decide ((encodePayload t).toNat / 65536 % 2 = 1) = t.registered := by
    rw [hr]; cases t.registered <;> rfl
  simp only [decodeTileFrame, encodeTileFrame, hm, ha, hb, hc, hd]
  simp only [t.a.isLt, t.b.isLt, t.c.isLt, t.d.isLt, and_self, ↓reduceIte]
  simp only [he, dite_true, Option.some.injEq]
  congr 1

theorem frame_crc_bit_flip_rejected (t : TechmappedTile) :
    decodeTileFrame { encodeTileFrame t with crc := (encodeTileFrame t).crc ^^^ 1#64 } = none := by
  have hne : frameCrc (encodePayload t) ^^^ 1#64 ≠ frameCrc (encodePayload t) := by
    intro he
    have hb := congrArg (fun w : BitVec 64 => w.getLsbD 0) he
    simp only [BitVec.getLsbD_xor] at hb
    cases (frameCrc (encodePayload t)).getLsbD 0 <;> simp at hb
  simp [decodeTileFrame, encodeTileFrame, hne]

private theorem array_mapM_leftInverse {α β : Type} (enc : α → β) (dec : β → Option α)
    (inverse : ∀ x, dec (enc x) = some x) (xs : Array α) :
    (xs.map enc).mapM dec = some xs := by
  rw [Array.mapM_map]
  have hf : dec ∘ enc = (fun t => (pure t : Option α)) := funext inverse
  rw [hf, Array.mapM_eq_mapM_toList, List.mapM_pure]
  simp

theorem decodeTileFrames_encodeTileFrames (tiles : Array TechmappedTile) :
    decodeTileFrames tiles.size (encodeTileFrames tiles) = some tiles := by
  unfold decodeTileFrames encodeTileFrames
  rw [Array.size_map]
  simp only [↓reduceIte]
  exact array_mapM_leftInverse encodeTileFrame decodeTileFrame decodeTileFrame_encode tiles

/-- PIPs select among four external wires, the preceding tile's register, and
this tile's register. All combinational paths end at inputs or registered edges. -/
def tileInputs (inputs regs : Array Bool) (i : Nat) : Nat → Bool := fun p =>
  if p < 4 then inputs[p]?.getD false
  else if p = 4 then regs[i - 1]?.getD false else regs[i]?.getD false

def evalTechmappedTile (t : TechmappedTile) (inp : Nat → Bool) (reg : Bool) : Bool :=
  if t.registered then reg else
    Obend.Hardware.Fabulous.lut4 t.lut (inp t.a) (inp t.b) (inp t.c) (inp t.d)

def evalDecodedTile (t : DecodedTile) (inp : Nat → Bool) (reg : Bool) : Bool :=
  if t.registered then reg else
    t.lut.getLsbD ((inp t.a).toNat + 2 * (inp t.b).toNat +
      4 * (inp t.c).toNat + 8 * (inp t.d).toNat)

def evalTechmappedSpec (spec : TechmappedFabric) (inputs regs : Array Bool) : List Bool :=
  spec.zipIdx.map fun (t, i) => evalTechmappedTile t (tileInputs inputs regs i) (regs[i]?.getD false)

def evalDecodedFabric (tiles : Array DecodedTile) (inputs regs : Array Bool) : Array Bool :=
  tiles.mapIdx fun i t => evalDecodedTile t (tileInputs inputs regs i) (regs[i]?.getD false)

def verifyDecodedAgainstTechmap (decoded : Array DecodedTile) (spec : TechmappedFabric) : Bool :=
  decide (decoded.toList = spec)

theorem evalDecodedTile_eq (t : TechmappedTile) (inp : Nat → Bool) (reg : Bool) :
    evalDecodedTile t inp reg = evalTechmappedTile t inp reg := by
  simp [evalDecodedTile, evalTechmappedTile, Obend.Hardware.Fabulous.lut4_eq_getLsbD]

theorem evalDecodedFabric_eq_techmapped (expected : Nat) (frames : Array TileFrame)
    (decoded : Array DecodedTile) (spec : TechmappedFabric) (inputs regs : Array Bool)
    (hd : decodeTileFrames expected frames = some decoded)
    (hv : verifyDecodedAgainstTechmap decoded spec = true) :
    frames.size = expected ∧
      (evalDecodedFabric decoded inputs regs).toList = evalTechmappedSpec spec inputs regs := by
  have hsize : frames.size = expected := by
    unfold decodeTileFrames at hd
    split at hd
    · assumption
    · cases hd
  refine ⟨hsize, ?_⟩
  have hs : decoded.toList = spec := of_decide_eq_true hv
  rw [← hs]
  simp [evalDecodedFabric, evalTechmappedSpec, Array.toList_mapIdx,
    List.mapIdx_eq_zipIdx_map, evalDecodedTile_eq]

inductive DprPhase where
  | active | isolateClamped | loadFrames
  deriving DecidableEq, Repr, Inhabited

structure NeighborPacket where
  destination : Nat
  payload : BitVec 64
  hops : Nat
  deriving DecidableEq, Repr, Inhabited

/-- The neighbor bank excludes the target region; logical index i maps to
physical coordinate i if i < specSlot, and i+1 otherwise. -/
structure NeighborState where
  tiles : Array TechmappedTile
  regs : Array Bool
  packets : Array NeighborPacket
  sampledBoundary : Bool
  deriving DecidableEq, Repr, Inhabited

structure DprFabric where
  specSlot : Nat
  phase : DprPhase
  activeTiles : Array TechmappedTile
  sram : Array TileFrame
  pending : Option (Array DecodedTile)
  clampedOut : Bool
  inputs : Array Bool
  targetRegs : Array Bool
  neighbors : NeighborState
  deriving DecidableEq, Repr, Inhabited

def neighborCoordinate (specSlot i : Nat) : Nat := if i < specSlot then i else i + 1

theorem neighborCoordinate_ne (specSlot i : Nat) : neighborCoordinate specSlot i ≠ specSlot := by
  unfold neighborCoordinate; split <;> omega

/-- A corrupt partial configuration may drive arbitrary intermediate wires.
The raw low LUT bit is an explicit such intermediate value. -/
def unfencedBoundary (s : DprFabric) : Bool :=
  if s.phase = .active then
    (evalDecodedFabric s.activeTiles s.inputs s.targetRegs)[0]?.getD false
  else (s.sram[0]?.map fun f => f.payload.getLsbD 0).getD false

def observedBoundaryPort (s : DprFabric) : Bool :=
  if s.phase = .active then unfencedBoundary s else s.clampedOut

/-- Capture the combinational LUT result on a clock edge, even when its
visible output uses the FF mux. Evaluation and register update are distinct. -/
def clockDecodedFabric (tiles : Array DecodedTile) (inputs regs : Array Bool) : Array Bool :=
  tiles.mapIdx fun i t => evalDecodedTile { t with registered := false }
    (tileInputs inputs regs i) (regs[i]?.getD false)

def tickNeighbors (inp : Array Bool) (port : Bool) (n : NeighborState) : NeighborState :=
  { n with
    regs := clockDecodedFabric n.tiles (#[port] ++ inp) n.regs
    packets := n.packets.map fun p => { p with hops := p.hops + 1 }
    sampledBoundary := port }

inductive DprCommand where
  | isolateClamped
  | loadFrames (frames : Array TileFrame)
  | releaseFence
  | compute
  deriving DecidableEq, Repr

/-- Admin commands are clock edges too: neighbors and non-target packets run
on every edge. Loading while active is ignored, and any write revokes pending
validation. Only the successful decoder can arm release. -/
@[expose] def administer (s : DprFabric) : DprCommand → DprFabric
  | .isolateClamped =>
      if s.phase = .active then
        { s with phase := .isolateClamped, clampedOut := observedBoundaryPort s, pending := none }
      else s
  | .loadFrames frames =>
      if s.phase = .active then s else
        match decodeTileFrames s.activeTiles.size frames with
        | none => { s with phase := .isolateClamped, sram := frames, pending := none }
        | some decoded => { s with phase := .loadFrames, sram := frames, pending := some decoded }
  | .releaseFence =>
      match s.phase, s.pending with
      | .loadFrames, some decoded => { s with phase := .active, activeTiles := decoded, pending := none }
      | _, _ => s
  | .compute => if s.phase = .active then
      { s with targetRegs := clockDecodedFabric s.activeTiles s.inputs s.targetRegs } else s

@[expose] def stepDprFabric (s : DprFabric) (cmd : DprCommand) : DprFabric :=
  { administer s cmd with neighbors := tickNeighbors s.inputs (observedBoundaryPort s) s.neighbors }

theorem clampedPortStable (s : DprFabric) (frames : Array TileFrame)
    (h : s.phase ≠ .active) :
    observedBoundaryPort { s with sram := frames } = s.clampedOut ∧
    observedBoundaryPort (stepDprFabric s (.loadFrames frames)) = s.clampedOut := by
  constructor
  · simp [observedBoundaryPort, h]
  · simp only [stepDprFabric, administer, h, ↓reduceIte]
    split <;> simp [observedBoundaryPort]

theorem failed_decode_quarantines (s : DprFabric) (frames : Array TileFrame)
    (h : s.phase ≠ .active) (bad : decodeTileFrames s.activeTiles.size frames = none) :
    (stepDprFabric (stepDprFabric s (.loadFrames frames)) .releaseFence).phase = .isolateClamped := by
  simp [stepDprFabric, administer, h, bad]

theorem release_specialization (s : DprFabric) (frames : Array TileFrame)
    (decoded : Array DecodedTile) (spec : TechmappedFabric)
    (h : s.phase ≠ .active) (hd : decodeTileFrames s.activeTiles.size frames = some decoded)
    (hv : verifyDecodedAgainstTechmap decoded spec = true) :
    let released := stepDprFabric (stepDprFabric s (.loadFrames frames)) .releaseFence
    released.phase = .active ∧
      (evalDecodedFabric released.activeTiles s.inputs s.targetRegs).toList =
        evalTechmappedSpec spec s.inputs s.targetRegs := by
  simp only [stepDprFabric, administer, h, ↓reduceIte, hd]
  exact ⟨True.intro, (evalDecodedFabric_eq_techmapped _ frames decoded spec _ _ hd hv).2⟩

/-- Abstract environment presents a port value at each clock edge. The abstract
fabric contains no configuration SRAM or DPR phase. Matching actions carry the
physical boundary value; the concrete guard forbids inventing that value. -/
structure FabricAction where
  command : DprCommand
  inputs : Array Bool
  boundary : Bool

open Obend.Category

instance : ObsMetric NeighborState Nat where
  dist a b := if a = b then 0 else 1
  dist_self _ := by simp
  dist_triangle a b c := by
    by_cases hab : a = b <;> by_cases hbc : b = c <;> by_cases hac : a = c <;> simp_all

def dprFabricStepSys : StepSystem DprFabric FabricAction NeighborState where
  observe := DprFabric.neighbors
  step s a s' := a.inputs = s.inputs ∧ a.boundary = observedBoundaryPort s ∧
    s' = stepDprFabric s a.command

def abstractNeighborStepSys : StepSystem NeighborState FabricAction NeighborState where
  observe := id
  step s a s' := s' = tickNeighbors a.inputs a.boundary s

/-- Forward simulation covers every actual command, including rejected writes. -/
theorem dpr_forward : Simulates dprFabricStepSys abstractNeighborStepSys
    (fun s n => s.neighbors = n) (0 : Nat) where
  obs_bound h := by subst h; exact ObsMetric.dist_self _
  step_sim := by
    rintro s s' n a hn ⟨hi, hp, rfl⟩
    refine ⟨(stepDprFabric s a.command).neighbors, ?_, rfl⟩
    change _ = tickNeighbors a.inputs a.boundary n
    simp [stepDprFabric, hi, hp, ← hn]

/-- Refines.StutterSimulates lifts steps of its SECOND system into its FIRST.
Thus the uninterrupted neighbor machine realizes each concrete ICAP edge in
one step. This direction quantifies over all concrete commands, not just a
chosen good schedule. The separate port invariant includes arbitrary SRAM. -/
theorem dpr_preserves_neighbor_tiles_stutter (state : DprFabric) (words : Array TileFrame)
    (isolated : state.phase ≠ .active) :
    StutterSimulates abstractNeighborStepSys dprFabricStepSys
      (fun n s => n = s.neighbors) 1 (0 : Nat) ∧
    observedBoundaryPort (stepDprFabric state (.loadFrames words)) = state.clampedOut := by
  constructor
  · refine ⟨by decide, ?_, ?_⟩
    · rintro n s rfl
      exact ObsMetric.dist_self _
    · rintro n s s' a hn ⟨hi, hp, ht⟩
      refine ⟨1, s'.neighbors, by decide, by decide, .succ ?_ (.zero _), rfl⟩
      change s'.neighbors = tickNeighbors a.inputs a.boundary n
      simp [ht, stepDprFabric, hi, hp, hn]
  · exact (clampedPortStable state words isolated).2

/-- Arbitrary finite concrete traces project to exact neighbor traces. -/
theorem dpr_neighbor_trace {s t : DprFabric} {actions : List FabricAction}
    (h : StepTrace dprFabricStepSys s actions t) :
    StepTrace abstractNeighborStepSys s.neighbors actions t.neighbors := by
  induction h with
  | nil => exact .nil _
  | @cons s₁ s₂ s₃ a as hs rest ih =>
    obtain ⟨hi, hp, ht⟩ := hs
    apply StepTrace.cons (s₂ := s₂.neighbors) _ ih
    change s₂.neighbors = tickNeighbors a.inputs a.boundary s₁.neighbors
    simp [ht, stepDprFabric, hi, hp]

/-- Removing isolation exposes a corrupt SRAM bit immediately. -/
theorem unclamped_load_causes_neighbor_glitch (s : DprFabric)
    (h : s.phase ≠ .active) :
    unfencedBoundary { s with sram := #[⟨0#64, 0#64⟩] } = false ∧
    unfencedBoundary { s with sram := #[⟨1#64, 0#64⟩] } = true ∧
    observedBoundaryPort { s with sram := #[⟨0#64, 0#64⟩] } =
      observedBoundaryPort { s with sram := #[⟨1#64, 0#64⟩] } := by
  simp [unfencedBoundary, observedBoundaryPort, h]

end Obend.Hardware.DprStutter
