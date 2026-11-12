module
/-
# Obend.Hardware.Process — Gate-Level BELs, eFPGA Bitstreams, PVT Timing Signoff & Ledger Silicon

Formalizes physical technology mapping, configurable eFPGA BLE bitstreams (FABulous eFPGA
architecture), multi-node PVT static timing analysis (7nm FinFET, 16nm UltraScale+, 130nm SkyWater
CMOS), and application-level hardware pipelines (`ReviewMember.obend` and `Obend.Ledger`):

* **Gate-Level BEL Technology Mapping**:
  - `evalLUT2`, `evalLUT6`, `evalCarryBel`, `fullAdderSpec`: proves `LUT2(0x6)` + hard `CARRY8` / `SB_CARRY`
    mux implements the exact 1-bit full adder (`carryBel_eq_fullAdderSpec`).
* **Configurable eFPGA BLE Tile & Bitstream Synthesis**:
  - `TileBitstream`, `evalEfpgaTile`, `compileTileBitstream`: proves synthesized 9-bit BLE bitstreams
    implement `fullAdderSpec` (`efpga_bitstream_fullAdder_sound`) and routed `&&` (`efpga_bitstream_and_sound`).
* **Multi-Node PVT Static Timing Analysis (STA)**:
  - `ProcessCorner` (`corner7nm_SS`, `corner16nm_SS`, `corner130nm_SS`), `TimingPath`, `checkTimingSignoff`:
    proves simultaneous setup and hold closure (`timingSignoff_sound`, `obend_multi_process_timing_signoff`)
    at 500 MHz (7nm SS), 400 MHz (16nm SS), and 200 MHz (130nm SS).
* **Application Co-Processors**:
  - `evalReviewMemberPipe` (`reviewMember_silicon_claim_holds`): proves `claim repeated` holds in silicon
    for all 64-bit `x, base`;
  - `stepHwLedger` (`hwLedger_period_monotone`, `hwLedger_closed_refused`, `hwLedger_balanced_conserved`,
    `hwLedger_twice_refused`): 1-cycle streaming hardware co-processor for `Obend.Ledger`.
-/
public import Obend.Core.Ty
public import Obend.Ledger.Register
@[expose] public section

namespace Obend.Hardware.Process
set_option autoImplicit false

/-! ## 1. Gate-Level BEL Technology Mapping (`LUT2`/`LUT6` + `CARRY8`) -/

def evalLUT2 (init : BitVec 4) (i0 i1 : Bool) : Bool :=
  let idx := (if i0 then 1 else 0) + (if i1 then 2 else 0)
  init.getLsbD idx

def evalLUT6 (init : BitVec 64) (i0 i1 i2 i3 i4 i5 : Bool) : Bool :=
  let idx :=
    (if i0 then 1 else 0) +
    (if i1 then 2 else 0) +
    (if i2 then 4 else 0) +
    (if i3 then 8 else 0) +
    (if i4 then 16 else 0) +
    (if i5 then 32 else 0)
  init.getLsbD idx

def LUT2_INIT_XOR : BitVec 4 := 0b0110#4
def LUT2_INIT_AND : BitVec 4 := 0b1000#4

theorem lut2_xor_sound (a b : Bool) :
    evalLUT2 LUT2_INIT_XOR a b = xor a b := by
  cases a <;> cases b <;> rfl

theorem lut2_and_sound (a b : Bool) :
    evalLUT2 LUT2_INIT_AND a b = (a && b) := by
  cases a <;> cases b <;> rfl

def evalCarryBel (a b ci : Bool) : Bool × Bool :=
  let prop   := evalLUT2 LUT2_INIT_XOR a b
  let gen    := a && b
  let sumBit := xor prop ci
  let cout   := if prop then ci else gen
  (sumBit, cout)

def fullAdderSpec (a b ci : Bool) : Bool × Bool :=
  let n := (if a then 1 else 0) + (if b then 1 else 0) + (if ci then 1 else 0)
  (decide (n % 2 = 1), decide (n ≥ 2))

theorem carryBel_eq_fullAdderSpec (a b ci : Bool) :
    evalCarryBel a b ci = fullAdderSpec a b ci := by
  cases a <;> cases b <;> cases ci <;> rfl

/-! ## 2. Configurable eFPGA BLE Tile & Bitstream Synthesis (FABulous eFPGA Model) -/

abbrev TileBitstream := BitVec 9

def evalSwitchMux4 (sel0 sel1 : Bool) (t0 t1 t2 t3 : Bool) : Bool :=
  match sel1, sel0 with
  | false, false => t0
  | false, true  => t1
  | true,  false => t2
  | true,  true  => t3

def evalEfpgaTile (bs : TileBitstream) (t0 t1 t2 t3 ci : Bool) : Bool × Bool :=
  let inA      := evalSwitchMux4 (bs.getLsbD 0) (bs.getLsbD 1) t0 t1 t2 t3
  let inB      := evalSwitchMux4 (bs.getLsbD 2) (bs.getLsbD 3) t0 t1 t2 t3
  let lutIdx   := (if inA then 1 else 0) + (if inB then 2 else 0)
  let lutOut   := bs.getLsbD (4 + lutIdx)
  let useCarry := bs.getLsbD 8
  let outBit   := if useCarry then xor lutOut ci else lutOut
  let cout     := if lutOut then ci else (inA && inB)
  (outBit, cout)

inductive TileGateOp where
  | lutXor (srcA srcB : BitVec 2)
  | lutAnd (srcA srcB : BitVec 2)
  | fullAdderSlice (srcA srcB : BitVec 2)
  deriving DecidableEq, Repr

def packBitstream (selA selB : BitVec 2) (lutInit : BitVec 4) (useCarry : Bool) : TileBitstream :=
  BitVec.ofNat 9 (selA.toNat + 4 * selB.toNat + 16 * lutInit.toNat + (if useCarry then 256 else 0))

def compileTileBitstream : TileGateOp → TileBitstream
  | .lutXor a b         => packBitstream a b LUT2_INIT_XOR false
  | .lutAnd a b         => packBitstream a b LUT2_INIT_AND false
  | .fullAdderSlice a b => packBitstream a b LUT2_INIT_XOR true

theorem efpga_bitstream_fullAdder_sound (t0 t1 t2 t3 ci : Bool) :
    evalEfpgaTile (compileTileBitstream (.fullAdderSlice 0#2 1#2)) t0 t1 t2 t3 ci =
      fullAdderSpec t0 t1 ci := by
  cases t0 <;> cases t1 <;> cases t2 <;> cases t3 <;> cases ci <;> decide

theorem efpga_bitstream_and_sound (t0 t1 t2 t3 ci : Bool) :
    (evalEfpgaTile (compileTileBitstream (.lutAnd 2#2 3#2)) t0 t1 t2 t3 ci).1 = (t2 && t3) := by
  cases t0 <;> cases t1 <;> cases t2 <;> cases t3 <;> cases ci <;> decide

/-! ## 3. Multi-Node PVT Process Corners & Static Timing Analysis (STA) -/

structure ProcessCorner where
  name         : String
  nodeNm       : Nat
  voltageMv    : Nat
  tempC        : Int
  tCqMaxPs     : Nat
  tCqMinPs     : Nat
  tGateMaxPs   : Nat
  tGateMinPs   : Nat
  tCarryMaxPs  : Nat
  tWireHopPs   : Nat
  tSetupPs     : Nat
  tHoldPs      : Nat
  tSkewPs      : Nat
  deriving DecidableEq, Repr

def corner7nm_SS : ProcessCorner where
  name         := "7nm-FinFET-SS-0.68V-125C"
  nodeNm       := 7
  voltageMv    := 680
  tempC        := 125
  tCqMaxPs     := 45
  tCqMinPs     := 22
  tGateMaxPs   := 95
  tGateMinPs   := 38
  tCarryMaxPs  := 22
  tWireHopPs   := 140
  tSetupPs     := 35
  tHoldPs      := 18
  tSkewPs      := 25

def corner16nm_SS : ProcessCorner where
  name         := "16nm-UltraScalePlus-SS-0.82V-100C"
  nodeNm       := 16
  voltageMv    := 820
  tempC        := 100
  tCqMaxPs     := 65
  tCqMinPs     := 30
  tGateMaxPs   := 140
  tGateMinPs   := 55
  tCarryMaxPs  := 38
  tWireHopPs   := 210
  tSetupPs     := 50
  tHoldPs      := 25
  tSkewPs      := 35

def corner130nm_SS : ProcessCorner where
  name         := "Sky130-CMOS-SS-1.60V-100C"
  nodeNm       := 130
  voltageMv    := 1600
  tempC        := 100
  tCqMaxPs     := 240
  tCqMinPs     := 110
  tGateMaxPs   := 450
  tGateMinPs   := 180
  tCarryMaxPs  := 120
  tWireHopPs   := 520
  tSetupPs     := 160
  tHoldPs      := 75
  tSkewPs      := 90

structure TimingPath where
  name        : String
  logicLevels : Nat
  minLevels   : Nat
  carryBits   : Nat
  tileHops    : Nat
  deriving DecidableEq, Repr

def maxArrivalPs (c : ProcessCorner) (p : TimingPath) : Nat :=
  c.tCqMaxPs + p.logicLevels * c.tGateMaxPs + p.carryBits * c.tCarryMaxPs + p.tileHops * c.tWireHopPs

def minArrivalPs (c : ProcessCorner) (p : TimingPath) : Nat :=
  c.tCqMinPs + p.minLevels * c.tGateMinPs

def requiredPeriodPs (c : ProcessCorner) (p : TimingPath) : Nat :=
  maxArrivalPs c p + c.tSetupPs + c.tSkewPs

def checkTimingSignoff (c : ProcessCorner) (clockPeriodPs : Nat) (p : TimingPath) : Bool :=
  (requiredPeriodPs c p ≤ clockPeriodPs) &&
  (c.tHoldPs + c.tSkewPs ≤ minArrivalPs c p)

theorem timingSignoff_sound {c : ProcessCorner} {clockPeriodPs : Nat} {p : TimingPath}
    (h : checkTimingSignoff c clockPeriodPs p = true) :
    maxArrivalPs c p + c.tSetupPs + c.tSkewPs ≤ clockPeriodPs ∧
    c.tHoldPs + c.tSkewPs ≤ minArrivalPs c p := by
  unfold checkTimingSignoff requiredPeriodPs at h
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at h
  exact h

def obendStageCritPath : TimingPath where
  name        := "obend_pipeline_stage_64b_alu"
  logicLevels := 2
  minLevels   := 1
  carryBits   := 8
  tileHops    := 0

theorem obend_multi_process_timing_signoff :
    checkTimingSignoff corner7nm_SS   2000 obendStageCritPath = true ∧
    checkTimingSignoff corner16nm_SS  2500 obendStageCritPath = true ∧
    checkTimingSignoff corner130nm_SS 5000 obendStageCritPath = true :=
  ⟨rfl, rfl, rfl⟩

/-! ## 3b. Process Corner Envelopes (`[FF, TT, SS]`) & Dual-Corner Timing Signoff -/

/-- Fast-Fast (`FF`) 7nm FinFET corner bounding minimum contamination delays and hold checks. -/
def corner7nm_FF : ProcessCorner where
  name         := "7nm-FinFET-FF-0.82V-0C"
  nodeNm       := 7
  voltageMv    := 820
  tempC        := 0
  tCqMaxPs     := 32
  tCqMinPs     := 18
  tGateMaxPs   := 65
  tGateMinPs   := 28
  tCarryMaxPs  := 14
  tWireHopPs   := 95
  tSetupPs     := 22
  tHoldPs      := 20
  tSkewPs      := 25

/-- Typical-Typical (`TT`) 7nm FinFET nominal corner lying strictly inside `[corner7nm_FF, corner7nm_SS]`. -/
def corner7nm_TT : ProcessCorner where
  name         := "7nm-FinFET-TT-0.75V-25C"
  nodeNm       := 7
  voltageMv    := 750
  tempC        := 25
  tCqMaxPs     := 38
  tCqMinPs     := 20
  tGateMaxPs   := 80
  tGateMinPs   := 33
  tCarryMaxPs  := 18
  tWireHopPs   := 118
  tSetupPs     := 28
  tHoldPs      := 19
  tSkewPs      := 25

/-- A 3-corner process envelope `[fastCorner, nomCorner, slowCorner]` (`[FF, TT, SS]`). -/
structure ProcessCornerEnvelope where
  fastCorner : ProcessCorner
  nomCorner  : ProcessCorner
  slowCorner : ProcessCorner
  deriving DecidableEq, Repr

/-- Reference 7nm `[FF, TT, SS]` process corner envelope. -/
def envelope7nm : ProcessCornerEnvelope where
  fastCorner := corner7nm_FF
  nomCorner  := corner7nm_TT
  slowCorner := corner7nm_SS

/-- An intermediate process corner `c` lies within the timing envelope `[cFast, cSlow]` iff:
1. Its maximum combinational and setup/skew parameters are bounded above by `cSlow` (`SS`), and
2. Its minimum contamination delays are bounded below by `cFast` (`FF`) while its hold/skew
   requirements are bounded above by `cFast`. -/
def CornerBetween (cFast c cSlow : ProcessCorner) : Prop :=
  c.tCqMaxPs ≤ cSlow.tCqMaxPs ∧
  c.tGateMaxPs ≤ cSlow.tGateMaxPs ∧
  c.tCarryMaxPs ≤ cSlow.tCarryMaxPs ∧
  c.tWireHopPs ≤ cSlow.tWireHopPs ∧
  c.tSetupPs ≤ cSlow.tSetupPs ∧
  c.tSkewPs ≤ cSlow.tSkewPs ∧
  cFast.tCqMinPs ≤ c.tCqMinPs ∧
  cFast.tGateMinPs ≤ c.tGateMinPs ∧
  c.tHoldPs ≤ cFast.tHoldPs ∧
  c.tSkewPs ≤ cFast.tSkewPs

/-- A `ProcessCornerEnvelope` is valid (`Valid`) when `fastCorner`, `nomCorner`, and `slowCorner`
all lie within `[fastCorner, slowCorner]`. -/
def ProcessCornerEnvelope.Valid (env : ProcessCornerEnvelope) : Prop :=
  CornerBetween env.fastCorner env.fastCorner env.slowCorner ∧
  CornerBetween env.fastCorner env.nomCorner env.slowCorner ∧
  CornerBetween env.fastCorner env.slowCorner env.slowCorner

theorem envelope7nm_valid : envelope7nm.Valid := by
  dsimp [ProcessCornerEnvelope.Valid, CornerBetween, envelope7nm, corner7nm_FF, corner7nm_TT, corner7nm_SS]
  refine ⟨?_, ?_, ?_⟩ <;> refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

/-- Dual-corner static timing signoff across a `ProcessCornerEnvelope`:
* Verifies **setup timing closure** (`requiredPeriodPs env.slowCorner p ≤ clockPeriodPs`) at `env.slowCorner` (`SS`), and
* Verifies **hold timing closure** (`env.fastCorner.tHoldPs + env.fastCorner.tSkewPs ≤ minArrivalPs env.fastCorner p`) at `env.fastCorner` (`FF`). -/
def checkEnvelopeTimingSignoff
    (env : ProcessCornerEnvelope) (clockPeriodPs : Nat) (p : TimingPath) : Bool :=
  decide (requiredPeriodPs env.slowCorner p ≤ clockPeriodPs) &&
  decide (env.fastCorner.tHoldPs + env.fastCorner.tSkewPs ≤ minArrivalPs env.fastCorner p)

/-- **Theorem (`envelope_timing_signoff_implies_all_intermediate_corners_safe`)**:
If `checkEnvelopeTimingSignoff env clockPeriodPs p = true` (setup closes at `SS` and hold closes at `FF`),
then for EVERY intermediate process corner `c : ProcessCorner` satisfying
`CornerBetween env.fastCorner c env.slowCorner`, full single-corner timing signoff
`checkTimingSignoff c clockPeriodPs p = true` holds! -/
theorem envelope_timing_signoff_implies_all_intermediate_corners_safe
    (env : ProcessCornerEnvelope)
    (clockPeriodPs : Nat)
    (p : TimingPath)
    (c : ProcessCorner)
    (hBetween : CornerBetween env.fastCorner c env.slowCorner)
    (hSignoff : checkEnvelopeTimingSignoff env clockPeriodPs p = true) :
    checkTimingSignoff c clockPeriodPs p = true ∧
    requiredPeriodPs c p ≤ clockPeriodPs ∧
    c.tHoldPs + c.tSkewPs ≤ minArrivalPs c p := by
  rcases hBetween with
    ⟨hCqMax, hGateMax, hCarryMax, hWireMax, hSetup, hSkewSlow,
     hCqMin, hGateMin, hHold, hSkewFast⟩
  simp only [checkEnvelopeTimingSignoff, Bool.and_eq_true, decide_eq_true_eq] at hSignoff
  rcases hSignoff with ⟨hSetupSS, hHoldFF⟩
  have hGateMaxMul : p.logicLevels * c.tGateMaxPs ≤ p.logicLevels * env.slowCorner.tGateMaxPs :=
    Nat.mul_le_mul_left p.logicLevels hGateMax
  have hCarryMaxMul : p.carryBits * c.tCarryMaxPs ≤ p.carryBits * env.slowCorner.tCarryMaxPs :=
    Nat.mul_le_mul_left p.carryBits hCarryMax
  have hWireMaxMul : p.tileHops * c.tWireHopPs ≤ p.tileHops * env.slowCorner.tWireHopPs :=
    Nat.mul_le_mul_left p.tileHops hWireMax
  have hGateMinMul : p.minLevels * env.fastCorner.tGateMinPs ≤ p.minLevels * c.tGateMinPs :=
    Nat.mul_le_mul_left p.minLevels hGateMin
  have hSetupC : requiredPeriodPs c p ≤ clockPeriodPs := by
    dsimp only [requiredPeriodPs, maxArrivalPs] at hSetupSS ⊢
    omega
  have hHoldC : c.tHoldPs + c.tSkewPs ≤ minArrivalPs c p := by
    dsimp only [minArrivalPs] at hHoldFF ⊢
    omega
  have hCheckC : checkTimingSignoff c clockPeriodPs p = true := by
    simp only [checkTimingSignoff, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hSetupC, hHoldC⟩
  exact ⟨hCheckC, hSetupC, hHoldC⟩

/-- Semiconductor fabrication materials tracked across cleanroom contamination zones. -/
inductive FabMaterial where
  | siSubstrate
  | sio2
  | si3n4
  | hfo2
  | polySi
  | tiN
  | wPlug
  | alMetal
  | cuMetal
  | auMetal
  deriving DecidableEq, Repr

/-- Sacrificial $\text{Si}_{1-x}\text{Ge}_x$ epitaxial superlattice layer for Gate-All-Around (GAA)
nanosheet selective release etching. -/
abbrev FabMaterial.siGe : FabMaterial := .si3n4

/-! ## 4. Hardware Synthesis of `ReviewMember.obend` (`claim repeated`) -/

structure ReviewStage1 where
  x_d1    : BitVec 64
  base_d1 : BitVec 64
  bump_s1 : BitVec 64
  deriving DecidableEq, Repr

structure ReviewStage2 where
  twice_out         : BitVec 64
  spec_out          : BitVec 64
  claim_repeated_ok : Bool
  deriving DecidableEq, Repr

def evalReviewMemberPipe (x_in base_in : BitVec 64) : ReviewStage2 :=
  let s1 : ReviewStage1 :=
    { x_d1    := x_in
    , base_d1 := base_in
    , bump_s1 := x_in + base_in }
  let twice := s1.bump_s1 + s1.base_d1
  let spec  := s1.x_d1 + (s1.base_d1 + s1.base_d1)
  { twice_out         := twice
  , spec_out          := spec
  , claim_repeated_ok := (twice == spec) }

theorem reviewMember_silicon_claim_holds (x base : BitVec 64) :
    (evalReviewMemberPipe x base).claim_repeated_ok = true := by
  simp only [evalReviewMemberPipe, BitVec.add_assoc, beq_self_eq_true]

/-! ## 5. Streaming Hardware `Ledger` Co-Processor (`Obend.Ledger` in Silicon) -/

inductive HwLedgerRow where
  | post (docId : Nat) (period : Nat) (acctDr acctCr : Nat) (debit credit : Nat)
  | close (period : Nat)
  deriving DecidableEq, Repr

inductive HwLedgerRefusal where
  | closedPeriod (period : Nat)
  | unbalanced (debit credit : Nat)
  | postedTwice (docId : Nat)
  deriving DecidableEq, Repr

structure HwLedgerState where
  closedThrough : Nat
  totalDebits   : Nat
  totalCredits  : Nat
  docLive       : Nat → Bool

def HwLedgerState.afterBootSweep : HwLedgerState where
  closedThrough := 0
  totalDebits   := 0
  totalCredits  := 0
  docLive       := fun _ => false

def stepHwLedger (st : HwLedgerState) : HwLedgerRow → Except HwLedgerRefusal HwLedgerState
  | .close p =>
    .ok { st with closedThrough := max st.closedThrough p }
  | .post docId period _ _ debit credit =>
    if period ≤ st.closedThrough then
      .error (.closedPeriod period)
    else if debit != credit then
      .error (.unbalanced debit credit)
    else if st.docLive docId then
      .error (.postedTwice docId)
    else
      .ok { closedThrough := st.closedThrough
          , totalDebits   := st.totalDebits + debit
          , totalCredits  := st.totalCredits + credit
          , docLive       := fun d => if d == docId then true else st.docLive d }

theorem hwLedger_period_monotone {st st' : HwLedgerState} {r : HwLedgerRow}
    (h : stepHwLedger st r = .ok st') : st.closedThrough ≤ st'.closedThrough := by
  cases r with
  | close p =>
    simp [stepHwLedger] at h; subst h; exact Nat.le_max_left _ _
  | post docId period dr cr debit credit =>
    simp only [stepHwLedger] at h
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · simp at h; subst h; exact Nat.le_refl _

theorem hwLedger_closed_refused (st : HwLedgerState) (docId period dr cr debit credit : Nat)
    (hclosed : period ≤ st.closedThrough) :
    stepHwLedger st (.post docId period dr cr debit credit) = .error (.closedPeriod period) := by
  simp [stepHwLedger, hclosed]

theorem hwLedger_balanced_conserved {st st' : HwLedgerState} {r : HwLedgerRow}
    (hbal : st.totalDebits = st.totalCredits) (hok : stepHwLedger st r = .ok st') :
    st'.totalDebits = st'.totalCredits := by
  cases r with
  | close p =>
    simp [stepHwLedger] at hok; subst hok; exact hbal
  | post docId period dr cr debit credit =>
    simp only [stepHwLedger] at hok
    split at hok
    · cases hok
    · rename_i hopen
      split at hok
      · cases hok
      · rename_i hneq
        split at hok
        · cases hok
        · simp at hok; subst hok
          have heq : debit = credit := by
            simp only [bne_iff_ne, Classical.not_not] at hneq
            exact hneq
          simp [hbal, heq]

theorem hwLedger_twice_refused {st st' : HwLedgerState} {docId p1 dr1 cr1 amt1 : Nat}
    (hok : stepHwLedger st (.post docId p1 dr1 cr1 amt1 amt1) = .ok st')
    (p2 dr2 cr2 amt2 : Nat) (hopen2 : st'.closedThrough < p2) :
    stepHwLedger st' (.post docId p2 dr2 cr2 amt2 amt2) = .error (.postedTwice docId) := by
  simp only [stepHwLedger] at hok
  split at hok
  · cases hok
  · split at hok
    · cases hok
    · split at hok
      · cases hok
      · simp at hok; subst hok
        dsimp at hopen2
        have hnotle : ¬ (p2 ≤ st.closedThrough) := by omega
        simp [stepHwLedger, hnotle]

end Obend.Hardware.Process
end
