module
/-
# Obend.Hardware.Silicon — Phase-Erased Bit Layouts, Hard Silicon Macros & Multi-SLR Floorplanning
-/
public import Obend.Core.Ty
public import Obend.Equiv.Demand
public import Obend.Hardware.HDL
@[expose] public section

namespace Obend.Hardware.Silicon
open Obend.Core.Ty (Ty Quantity)
open Obend.Core.Term
open Obend.Equiv
open Obend.Equiv.Demand
set_option autoImplicit false

/-! ## 1. `BitLayout` — Bit-exact wire layouts for Core4 types -/

inductive HwTy where
  | cap (portId : Nat)
  | bit
  | word (w : Nat)
  | pair (fst snd : HwTy)
  | sum (tagBits payloadBits : Nat)
  deriving DecidableEq, Repr

def HwTy.width : HwTy → Nat
  | .cap _ => 0
  | .bit => 1
  | .word w => w
  | .pair a b => a.width + b.width
  | .sum tagW payW => tagW + payW

inductive HwVal : HwTy → Type where
  | cap (id : Nat) : HwVal (.cap id)
  | bit (b : Bool) : HwVal .bit
  | word {w : Nat} (v : BitVec w) : HwVal (.word w)
  | pair {a b : HwTy} (va : HwVal a) (vb : HwVal b) : HwVal (.pair a b)
  | sum {tw pw : Nat} (tag : BitVec tw) (payload : BitVec pw) : HwVal (.sum tw pw)

def concatLsb {w₁ w₂ : Nat} (lo : BitVec w₁) (hi : BitVec w₂) : BitVec (w₁ + w₂) :=
  (hi.append lo).cast (Nat.add_comm w₂ w₁)

def sliceLo (w₁ w₂ : Nat) (bus : BitVec (w₁ + w₂)) : BitVec w₁ :=
  bus.setWidth w₁

def sliceHi (w₁ w₂ : Nat) (bus : BitVec (w₁ + w₂)) : BitVec w₂ :=
  (bus >>> w₁).setWidth w₂

theorem getLsbD_concatLsb {w₁ w₂ : Nat} (lo : BitVec w₁) (hi : BitVec w₂) (i : Nat) :
    (concatLsb lo hi).getLsbD i = if i < w₁ then lo.getLsbD i else hi.getLsbD (i - w₁) := by
  simp [concatLsb, BitVec.getLsbD_cast, BitVec.getLsbD_append]

theorem sliceLo_concatLsb {w₁ w₂ : Nat} (lo : BitVec w₁) (hi : BitVec w₂) :
    sliceLo w₁ w₂ (concatLsb lo hi) = lo := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi_lt
  simp [sliceLo, getLsbD_concatLsb, hi_lt]

theorem sliceHi_concatLsb {w₁ w₂ : Nat} (lo : BitVec w₁) (hi : BitVec w₂) :
    sliceHi w₁ w₂ (concatLsb lo hi) = hi := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi_lt
  rw [sliceHi, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, getLsbD_concatLsb]
  have hnot : ¬ (w₁ + i < w₁) := by omega
  have hsub : w₁ + i - w₁ = i := by omega
  simp [hi_lt, hnot, hsub]

theorem concatLsb_slice {w₁ w₂ : Nat} (bus : BitVec (w₁ + w₂)) :
    concatLsb (sliceLo w₁ w₂ bus) (sliceHi w₁ w₂ bus) = bus := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi_lt
  rw [getLsbD_concatLsb]
  split
  · rename_i hlt
    simp [sliceLo, hlt]
  · rename_i hge
    have hlt2 : i - w₁ < w₂ := by omega
    have hadd : w₁ + (i - w₁) = i := by omega
    simp [sliceHi, BitVec.getLsbD_ushiftRight, hlt2, hadd]

def packVal {T : HwTy} : HwVal T → BitVec T.width
  | .cap _ => 0#0
  | .bit b => BitVec.ofBool b
  | .word v => v
  | .pair va vb => concatLsb (packVal va) (packVal vb)
  | .sum tag pay => concatLsb tag pay

def unpackVal : (T : HwTy) → BitVec T.width → HwVal T
  | .cap id, _ => .cap id
  | .bit, bv => .bit (bv.getLsbD 0)
  | .word _, bv => .word bv
  | .pair a b, bv =>
    .pair (unpackVal a (sliceLo a.width b.width bv))
          (unpackVal b (sliceHi a.width b.width bv))
  | .sum tw pw, bv =>
    .sum (sliceLo tw pw bv) (sliceHi tw pw bv)

theorem unpackVal_packVal {T : HwTy} (v : HwVal T) : unpackVal T (packVal v) = v := by
  induction v with
  | cap id => rfl
  | bit b => cases b <;> rfl
  | word v => rfl
  | pair va vb iha ihb =>
    simp only [packVal, unpackVal, sliceLo_concatLsb, sliceHi_concatLsb, iha, ihb]
  | sum tag pay =>
    simp only [packVal, unpackVal, sliceLo_concatLsb, sliceHi_concatLsb]

theorem packVal_unpackVal : ∀ (T : HwTy) (bv : BitVec T.width), packVal (unpackVal T bv) = bv
  | .cap _, bv => by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi; cases hi
  | .bit, bv => by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rcases Nat.lt_one_iff.1 hi with rfl
    simp only [unpackVal, packVal]
    cases bv.getLsbD 0 <;> rfl
  | .word _, _ => rfl
  | .pair a b, bv => by
    simp only [unpackVal, packVal, packVal_unpackVal]
    exact concatLsb_slice bv
  | .sum tw pw, bv => by
    simp only [unpackVal, packVal]
    exact concatLsb_slice bv

def lowerTy (wordW : Nat := 64) : Ty → Option HwTy
  | .boolean => some .bit
  | .natural => some (.word wordW)
  | .custody id => some (.cap id)
  | .emptyRow => some (.word 0)
  | .field _ member tail => do
    let hm ← lowerTy wordW member
    let ht ← lowerTy wordW tail
    pure (.pair hm ht)
  | .prototype _ target => lowerTy wordW target
  | _ => none

theorem lowerTy_prototype_erases_cold_spine (wordW : Nat) (spec target : Ty) :
    lowerTy wordW (.prototype spec target) = lowerTy wordW target := rfl

theorem lowerTy_custody_zero_bits (wordW id : Nat) :
    ((lowerTy wordW (.custody id)).map HwTy.width) = some 0 := rfl

/-! ## 2. `Silicon` — Adversarial physical FPGA/ASIC primitives (SRL, DSP48/58, URAM/SRAM, SkidBuffer) -/

def stepDataReg {w : Nat} (state : BitVec w) (ce : Bool) (d : BitVec w) : BitVec w :=
  if ce then d else state

theorem stepDataReg_latch_and_hold {w : Nat} (garbage₀ v d_next : BitVec w) :
    stepDataReg (stepDataReg garbage₀ true v) false d_next = v := rfl

structure Pipe2State (w : Nat) where
  s1 : BitVec w
  s2 : BitVec w
  deriving DecidableEq, Repr

def stepPipe2 {w : Nat} (st : Pipe2State w) (din : BitVec w) : Pipe2State w :=
  { s1 := din, s2 := st.s1 }

theorem pipe2_x_free {w : Nat} (st₀ : Pipe2State w) (x₀ x₁ : BitVec w) :
    (stepPipe2 (stepPipe2 st₀ x₀) x₁).s2 = x₀ := rfl

structure DspMacState (w : Nat) where
  a1 : BitVec w
  b1 : BitVec w
  a2 : BitVec w
  b2 : BitVec w
  c2 : BitVec w
  mreg : BitVec w
  c3 : BitVec w
  preg : BitVec w
  deriving DecidableEq, Repr

def stepDspMac {w : Nat} (st : DspMacState w) (a_in b_in c_in : BitVec w) : DspMacState w :=
  { a1 := a_in
  , b1 := b_in
  , a2 := st.a1
  , b2 := st.b1
  , c2 := c_in
  , mreg := st.a2 * st.b2
  , c3 := st.c2
  , preg := st.mreg + st.c3 }

theorem dspMac_latency_4 {w : Nat} (st₀ : DspMacState w)
    (a₀ b₀ c₀ a₁ b₁ c₁ a₂ b₂ c₂ a₃ b₃ c₃ : BitVec w) :
    let s1 := stepDspMac st₀ a₀ b₀ c₀
    let s2 := stepDspMac s1  a₁ b₁ c₁
    let s3 := stepDspMac s2  a₂ b₂ c₂
    let s4 := stepDspMac s3  a₃ b₃ c₃
    s4.preg = a₀ * b₀ + c₁ := rfl

structure SyncRAMState (w : Nat) where
  mem : Nat → BitVec w
  dout : Option (BitVec w)

def writeMem {w : Nat} (mem : Nat → BitVec w) (wrEn : Bool) (wrAddr : Nat) (wrData : BitVec w) : Nat → BitVec w :=
  if wrEn then fun a => if a == wrAddr then wrData else mem a
  else mem

def stepSyncRAM {w bankId : Nat} (_portCap : HwVal (.cap bankId))
    (st : SyncRAMState w) (rdEn : Bool) (rdAddr : Nat) (wrEn : Bool) (wrAddr : Nat) (wrData : BitVec w) :
    SyncRAMState w :=
  let nextMem := writeMem st.mem wrEn wrAddr wrData
  let nextDout :=
    if !rdEn then st.dout
    else if wrEn && (rdAddr == wrAddr) then none
    else some (st.mem rdAddr)
  { mem := nextMem, dout := nextDout }

def runBootSweep {w : Nat} (depth : Nat) (mem₀ : Nat → BitVec w) : Nat → Nat → (Nat → BitVec w)
  | 0, _ => mem₀
  | k + 1, cursor =>
    let mem' := writeMem mem₀ true cursor (0#w)
    runBootSweep depth mem' k (cursor + 1)

theorem writeMem_other {w : Nat} (mem : Nat → BitVec w) (c a : Nat) (v : BitVec w) (hne : a ≠ c) :
    writeMem mem true c v a = mem a := by
  have hb : (a == c) = false := beq_false_of_ne hne
  simp [writeMem, hb]

theorem writeMem_self {w : Nat} (mem : Nat → BitVec w) (c : Nat) (v : BitVec w) :
    writeMem mem true c v c = v := by
  simp [writeMem]

theorem runBootSweep_preserves_below {w : Nat} (depth : Nat) :
    ∀ (k cursor : Nat) (mem : Nat → BitVec w) (a : Nat),
      a < cursor → runBootSweep depth mem k cursor a = mem a
  | 0, _, _, _, _ => rfl
  | k + 1, cursor, mem, a, hlt => by
    simp only [runBootSweep]
    rw [runBootSweep_preserves_below depth k (cursor + 1) _ a (by omega)]
    exact writeMem_other mem cursor a (0#w) (by omega)

theorem runBootSweep_zero_range {w : Nat} (depth : Nat) :
    ∀ (k cursor : Nat) (mem : Nat → BitVec w) (a : Nat),
      cursor ≤ a → a < cursor + k → runBootSweep depth mem k cursor a = 0#w
  | 0, cursor, _, a, hge, hlt => by omega
  | k + 1, cursor, mem, a, hge, hlt => by
    simp only [runBootSweep]
    by_cases heq : a = cursor
    · subst heq
      rw [runBootSweep_preserves_below depth k (a + 1) _ a (by omega)]
      exact writeMem_self mem a (0#w)
    · exact runBootSweep_zero_range depth k (cursor + 1) _ a (by omega) (by omega)

theorem bootSweep_clears_all {w : Nat} (depth : Nat) (mem₀ : Nat → BitVec w) (a : Nat) (ha : a < depth) :
    runBootSweep depth mem₀ depth 0 a = 0#w :=
  runBootSweep_zero_range depth depth 0 mem₀ a (Nat.zero_le a) (by omega)

structure BypassRAMState (w : Nat) where
  ram : SyncRAMState w
  bypassActive : Bool
  bypassData : BitVec w

def stepBypassRAM {w : Nat} {bankId : Nat} (cap : HwVal (.cap bankId))
    (st : BypassRAMState w) (rdEn : Bool) (rdAddr : Nat) (wrEn : Bool) (wrAddr : Nat) (wrData : BitVec w) :
    BypassRAMState w :=
  let collision := rdEn && wrEn && (rdAddr == wrAddr)
  let physRdEn := rdEn && !collision
  let nextRam := stepSyncRAM cap st.ram physRdEn rdAddr wrEn wrAddr wrData
  { ram := nextRam
  , bypassActive := collision
  , bypassData := if collision then wrData else st.bypassData }

def readBypassRAM {w : Nat} (st : BypassRAMState w) : Option (BitVec w) :=
  if st.bypassActive then some st.bypassData else st.ram.dout

theorem bypassRAM_exact_latest_write {w : Nat} {bankId : Nat} (cap : HwVal (.cap bankId))
    (st : BypassRAMState w) (rdAddr : Nat) (wrEn : Bool) (wrAddr : Nat) (wrData : BitVec w) :
    readBypassRAM (stepBypassRAM cap st true rdAddr wrEn wrAddr wrData) =
      some (writeMem st.ram.mem wrEn wrAddr wrData rdAddr) := by
  simp only [stepBypassRAM, readBypassRAM, stepSyncRAM, writeMem]
  cases wrEn <;> by_cases h : (rdAddr == wrAddr) = true <;> simp [h]

structure SkidState (w : Nat) where
  pValid : Bool
  pData : BitVec w
  sValid : Bool
  sData : BitVec w
  deriving DecidableEq, Repr

def SkidState.sReady {w : Nat} (st : SkidState w) : Bool := !st.sValid
def SkidState.mValid {w : Nat} (st : SkidState w) : Bool := st.pValid
def SkidState.mData  {w : Nat} (st : SkidState w) : BitVec w := st.pData

def SkidState.init {w : Nat} (g₁ g₂ : BitVec w) : SkidState w :=
  { pValid := false, pData := g₁, sValid := false, sData := g₂ }

def stepSkid {w : Nat} (st : SkidState w) (sValidIn : Bool) (sDataIn : BitVec w) (mReadyIn : Bool) :
    SkidState w :=
  let accept := sValidIn && st.sReady
  let drain  := st.pValid && mReadyIn
  if st.sValid then
    if drain then
      { pValid := true, pData := st.sData, sValid := false, sData := st.sData }
    else
      st
  else
    if !st.pValid || drain then
      { pValid := accept, pData := if accept then sDataIn else st.pData, sValid := false, sData := st.sData }
    else
      { pValid := true, pData := st.pData, sValid := accept, sData := if accept then sDataIn else st.sData }

def SkidState.queue {w : Nat} (st : SkidState w) : List (BitVec w) :=
  (if st.pValid then [st.pData] else []) ++ (if st.sValid then [st.sData] else [])

def SkidState.Wf {w : Nat} (st : SkidState w) : Prop :=
  st.sValid = true → st.pValid = true

theorem skid_init_wf {w : Nat} (g₁ g₂ : BitVec w) : (SkidState.init g₁ g₂).Wf := by
  intro h; cases h

theorem stepSkid_wf {w : Nat} {st : SkidState w} (hwf : st.Wf)
    (sValidIn : Bool) (sDataIn : BitVec w) (mReadyIn : Bool) :
    (stepSkid st sValidIn sDataIn mReadyIn).Wf := by
  rcases st with ⟨pv, pd, sv, sd⟩
  cases pv <;> cases sv <;> cases sValidIn <;> cases mReadyIn <;>
    simp_all [SkidState.Wf, stepSkid, SkidState.sReady]

theorem stepSkid_queue_conserved {w : Nat} {st : SkidState w} (hwf : st.Wf)
    (sValidIn : Bool) (sDataIn : BitVec w) (mReadyIn : Bool) :
    let popped   := if st.mValid && mReadyIn then [st.mData] else []
    let accepted := if sValidIn && st.sReady then [sDataIn] else []
    popped ++ (stepSkid st sValidIn sDataIn mReadyIn).queue = st.queue ++ accepted := by
  rcases st with ⟨pv, pd, sv, sd⟩
  cases pv <;> cases sv <;> cases sValidIn <;> cases mReadyIn
  all_goals simp_all [SkidState.Wf, stepSkid, SkidState.sReady, SkidState.mValid, SkidState.mData, SkidState.queue]

/-! ## 3. `Layout` — Verified physical floorplanning and SLR crossings -/

structure Coord where
  slr : Nat
  col : Nat
  row : Nat
  deriving DecidableEq, Repr

def natDist (a b : Nat) : Nat :=
  if a ≤ b then b - a else a - b

def Coord.manhattan2D (a b : Coord) : Nat :=
  natDist a.col b.col + natDist a.row b.row

def Coord.slrDist (a b : Coord) : Nat :=
  natDist a.slr b.slr

def Coord.beside (a : Coord) : Coord := { a with col := a.col + 1 }
def Coord.above (a : Coord) : Coord := { a with row := a.row + 1 }
def Coord.crossSLR (a : Coord) : Coord := { a with slr := a.slr + 1 }

structure PlacedChannel where
  name      : String
  src       : Coord
  dst       : Coord
  bitWidth  : Nat
  regStages : Nat
  deriving DecidableEq, Repr

inductive LayoutRefusal where
  | outOfBounds (inst : String) (c : Coord)
  | combCrossesTile (ch : String) (src dst : Coord)
  | unpipelinedHop (ch : String) (dist regStages : Nat)
  | illegalSlrCrossing (ch : String) (src dst : Coord) (regStages : Nat)
  deriving DecidableEq, Repr

def checkChannelHop (ch : PlacedChannel) : Except LayoutRefusal Unit :=
  if ch.src.slrDist ch.dst == 0 then
    let d := ch.src.manhattan2D ch.dst
    if d == 0 then
      .ok ()
    else if ch.regStages == 0 then
      .error (.combCrossesTile ch.name ch.src ch.dst)
    else if ch.regStages < d then
      .error (.unpipelinedHop ch.name d ch.regStages)
    else
      .ok ()
  else if ch.src.slrDist ch.dst == 1 && ch.src.manhattan2D ch.dst == 0 then
    if ch.regStages ≥ 2 then
      .ok ()
    else
      .error (.illegalSlrCrossing ch.name ch.src ch.dst ch.regStages)
  else
    .error (.illegalSlrCrossing ch.name ch.src ch.dst ch.regStages)

theorem natDist_eq_zero {a b : Nat} (h : natDist a b = 0) : a = b := by
  unfold natDist at h; split at h <;> omega

theorem comb_channel_is_tile_local {ch : PlacedChannel}
    (hok : checkChannelHop ch = .ok ()) (hcomb : ch.regStages = 0) :
    ch.src = ch.dst := by
  unfold checkChannelHop at hok
  simp only [hcomb, beq_self_eq_true, ↓reduceIte] at hok
  split at hok
  · rename_i hslr
    split at hok
    · rename_i hman
      simp only [Coord.slrDist, Coord.manhattan2D, beq_iff_eq, Nat.add_eq_zero_iff] at hslr hman
      have hs := natDist_eq_zero hslr
      have hc := natDist_eq_zero hman.1
      have hr := natDist_eq_zero hman.2
      rcases ch with ⟨_, ⟨s1, c1, r1⟩, ⟨s2, c2, r2⟩, _, _⟩
      simp only at hs hc hr
      subst hs hc hr; rfl
    · cases hok
  · split at hok <;> cases hok

theorem slr_crossing_has_laguna_pair {ch : PlacedChannel}
    (hok : checkChannelHop ch = .ok ()) (hcross : ch.src.slr ≠ ch.dst.slr) :
    ch.regStages ≥ 2 ∧ ch.src.manhattan2D ch.dst = 0 := by
  unfold checkChannelHop at hok
  have hslr_ne : (ch.src.slrDist ch.dst == 0) = false := by
    simp only [Coord.slrDist, natDist, beq_eq_false_iff_ne]
    split <;> omega
  rw [hslr_ne] at hok
  simp only [Bool.false_eq_true, ↓reduceIte] at hok
  split at hok
  · rename_i hcond
    simp only [Bool.and_eq_true, beq_iff_eq] at hcond
    split at hok
    · rename_i hge
      exact ⟨hge, hcond.2⟩
    · cases hok
  · cases hok

/-! ## 4. Demand-Driven Wave Chip Refinement (`Obend.Equiv.Demand`) -/

def stepField (κ : List (String × Nat)) : String × FE → Option (String × Nat)
  | (n, .lit v) => some (n, v)
  | (n, .ref m) =>
    match κ.lookup n with
    | some u => some (n, u)
    | none =>
      match κ.lookup m with
      | some u => some (n, u)
      | none => none

def tickNamed (fs : List (String × FE)) (κ : List (String × Nat)) : List (String × Nat) :=
  fs.filterMap (stepField κ)

def runNamed (fs : List (String × FE)) : Nat → List (String × Nat)
  | 0 => []
  | k + 1 => tickNamed fs (runNamed fs k)

theorem lookup_tickNamed {fs : List (String × FE)} (nd : (fs.map Prod.fst).Nodup)
    (κ : List (String × Nat)) (x : String) :
    (tickNamed fs κ).lookup x =
      match look fs x with
      | some (.lit v) => some v
      | some (.ref m) => (κ.lookup x).or (κ.lookup m)
      | none => none := by
  induction fs with
  | nil => simp [tickNamed, look]
  | cons f fs ih =>
    obtain ⟨n, e⟩ := f
    simp only [List.map_cons, List.nodup_cons] at nd
    have ih' := ih nd.2
    by_cases hnx : x = n
    · subst hnx
      have hlook : look ((x, e) :: fs) x = some e := by simp [look]
      rw [hlook]
      cases e with
      | lit v =>
        simp [tickNamed, stepField]
      | ref m =>
        simp only [tickNamed, List.filterMap_cons, stepField]
        cases hkx : κ.lookup x with
        | some u => simp [Option.or]
        | none =>
          cases hkm : κ.lookup m with
          | some u => simp [Option.or]
          | none =>
            simp only [Option.or]
            change (tickNamed fs κ).lookup x = none
            rw [ih']
            have hnone : look fs x = none := by
              cases hl : look fs x with
              | none => rfl
              | some e' => exact absurd (look_mem hl) nd.1
            rw [hnone]
    · have hbeq : (n == x) = false := beq_false_of_ne (Ne.symm hnx)
      have hbeq' : (x == n) = false := beq_false_of_ne hnx
      have hlook : look ((n, e) :: fs) x = look fs x := by simp [look, hbeq]
      rw [hlook, ← ih']
      simp only [tickNamed, List.filterMap_cons]
      cases hstep : stepField κ (n, e) with
      | none => rfl
      | some p =>
        have hp : p.1 = n := by
          cases e with
          | lit v => simp [stepField] at hstep; subst hstep; rfl
          | ref m =>
            simp only [stepField] at hstep
            split at hstep
            · simp at hstep; subst hstep; rfl
            · split at hstep
              · simp at hstep; subst hstep; rfl
              · cases hstep
        obtain ⟨pn, pv⟩ := p
        simp only at hp
        subst hp
        simp [List.lookup, hbeq']

def WfBank (fs : List (String × FE)) (κ : List (String × Nat)) : Prop :=
  ∀ x u, κ.lookup x = some u →
    (∃ m, look fs x = some (.ref m)) ∨ look fs x = some (.lit u)

theorem wfBank_nil (fs : List (String × FE)) : WfBank fs [] := by
  intro x u h; simp at h

theorem wfBank_tick {fs : List (String × FE)} (nd : (fs.map Prod.fst).Nodup)
    {κ : List (String × Nat)} (_hwf : WfBank fs κ) : WfBank fs (tickNamed fs κ) := by
  intro x u h
  rw [lookup_tickNamed nd] at h
  cases hl : look fs x with
  | none => rw [hl] at h; cases h
  | some e =>
    rw [hl] at h
    cases e with
    | lit v => simp at h; subst h; exact .inr rfl
    | ref m => exact .inl ⟨m, rfl⟩

theorem wfBank_run {fs : List (String × FE)} (nd : (fs.map Prod.fst).Nodup) :
    ∀ k, WfBank fs (runNamed fs k)
  | 0 => wfBank_nil fs
  | k + 1 => wfBank_tick nd (wfBank_run nd k)

theorem latch_stable_tick {fs : List (String × FE)} (nd : (fs.map Prod.fst).Nodup)
    {κ : List (String × Nat)} (hwf : WfBank fs κ) {x : String} {u : Nat}
    (h : κ.lookup x = some u) : (tickNamed fs κ).lookup x = some u := by
  rw [lookup_tickNamed nd]
  rcases hwf x u h with ⟨m, hl⟩ | hl
  · rw [hl, h]; rfl
  · rw [hl]

theorem latch_stable_run {fs : List (String × FE)} (nd : (fs.map Prod.fst).Nodup)
    {k : Nat} {x : String} {u : Nat} (h : (runNamed fs k).lookup x = some u) :
    ∀ j, (runNamed fs (k + j)).lookup x = some u
  | 0 => h
  | j + 1 => by
    rw [show k + (j + 1) = (k + j) + 1 by omega]
    exact latch_stable_tick nd (wfBank_run nd (k + j)) (latch_stable_run nd h j)

theorem runNamed_sound {fs : List (String × FE)} (nd : (fs.map Prod.fst).Nodup) :
    ∀ k x u, (runNamed fs k).lookup x = some u → ∃ d, chase fs k x = some (u, d)
  | 0, x, u, h => by simp [runNamed] at h
  | k + 1, x, u, h => by
    simp only [runNamed] at h
    rw [lookup_tickNamed nd] at h
    simp only [chase]
    cases hl : look fs x with
    | none => rw [hl] at h; cases h
    | some e =>
      rw [hl] at h
      cases e with
      | lit v =>
        simp at h; subst h; exact ⟨0, rfl⟩
      | ref m =>
        cases hkx : (runNamed fs k).lookup x with
        | some u0 =>
          rw [hkx] at h; simp [Option.or] at h; subst h
          obtain ⟨d, hch⟩ := runNamed_sound nd k x u0 hkx
          have hch' := (chase_fuel hch).2 (k + 1) (by have := (chase_fuel hch).1; omega)
          simp only [chase, hl] at hch'
          exact ⟨d, hch'⟩
        | none =>
          rw [hkx] at h; simp [Option.or] at h
          obtain ⟨d, hch⟩ := runNamed_sound nd k m u h
          exact ⟨d + 1, by simp [hch]⟩

theorem runNamed_complete {fs : List (String × FE)} (nd : (fs.map Prod.fst).Nodup) :
    ∀ k x u d, chase fs k x = some (u, d) → (runNamed fs k).lookup x = some u
  | 0, x, u, d, h => by simp [chase] at h
  | k + 1, x, u, d, h => by
    simp only [chase] at h
    simp only [runNamed, lookup_tickNamed nd]
    cases hl : look fs x with
    | none => rw [hl] at h; cases h
    | some e =>
      rw [hl] at h
      cases e with
      | lit v =>
        simp at h; obtain ⟨rfl, rfl⟩ := h; rfl
      | ref m =>
        obtain ⟨⟨u', d'⟩, hch, heq⟩ := Option.map_eq_some_iff.1 h
        simp at heq; obtain ⟨rfl, rfl⟩ := heq
        have ih := runNamed_complete nd k m u' d' hch
        cases hkx : (runNamed fs k).lookup x with
        | none => simp [Option.or, ih]
        | some u0 =>
          obtain ⟨d0, hch0⟩ := runNamed_sound nd k x u0 hkx
          have hch_x : chase fs (k + 1) x = some (u', d' + 1) := by simp [chase, hl, hch]
          have := chase_unique hch0 hch_x
          simp at this; obtain ⟨rfl, _⟩ := this
          rfl

theorem chip_lookup_iff_chase {fs : List (String × FE)} (nd : (fs.map Prod.fst).Nodup)
    (k : Nat) (x : String) (u : Nat) :
    (runNamed fs k).lookup x = some u ↔ ∃ d, chase fs k x = some (u, d) :=
  ⟨runNamed_sound nd k x u, fun ⟨d, h⟩ => runNamed_complete nd k x u d h⟩

theorem chip_computes_demand {fs : List (String × FE)} (nd : (fs.map Prod.fst).Nodup)
    (x : String) (u : Nat) :
    (runNamed fs fs.length).lookup x = some u ↔
      ∃ n, CV (.get (obj fs) x) (.nat u) n ∧ ∀ w k, CV (.get (obj fs) x) w k → n ≤ k := by
  rw [chip_lookup_iff_chase nd]
  constructor
  · rintro ⟨d, hch⟩
    refine ⟨headCost fs + 2 * d + 2, ?_⟩
    apply (demand_is_least nd x u (headCost fs + 2 * d + 2)).1
    simp [demand, hch]
  · rintro ⟨n, hcv, hleast⟩
    have hd := (demand_is_least nd x u n).2 ⟨hcv, hleast⟩
    simp only [demand] at hd
    obtain ⟨⟨u', d⟩, hch, heq⟩ := Option.map_eq_some_iff.1 hd
    simp at heq; obtain ⟨rfl, rfl⟩ := heq
    exact ⟨d, hch⟩

theorem chip_never_valid_of_divergent {fs : List (String × FE)} (nd : (fs.map Prod.fst).Nodup)
    (x : String) (hdiv : ∀ w n, ¬ CV (.get (obj fs) x) w n) (k : Nat) :
    (runNamed fs k).lookup x = none := by
  cases h : (runNamed fs k).lookup x with
  | none => rfl
  | some u =>
    obtain ⟨d, hch⟩ := (chip_lookup_iff_chase nd k x u).1 h
    have hshort := chase_short hch
    have hlen := (chase_fuel hch).2 fs.length hshort
    have hd : demand fs x = some (u, headCost fs + 2 * d + 2) := by simp [demand, hlen]
    have hcv := demand_exists nd hd
    exact absurd hcv (hdiv (.nat u) (headCost fs + 2 * d + 2))

/-! ## 5. Multi-Channel Floorplan & SLR Crossing Signoff (`checkAllChannelHops`) -/

/-- Boolean wrapper for `checkChannelHop` used by end-to-end physical silicon signoff. -/
def checkChannelHopBool (ch : PlacedChannel) : Bool :=
  match checkChannelHop ch with
  | .ok () => true
  | .error _ => false

/-- Check that every `PlacedChannel` in a floorplan satisfies tile-distance pipelining and
2-stage Laguna SLR crossing rules. -/
def checkAllChannelHops (channels : List PlacedChannel) : Bool :=
  channels.all checkChannelHopBool

/-- **Theorem (`checkAllChannelHops_sound`)**:
If `checkAllChannelHops channels = true`, then for every channel `ch ∈ channels`:
1. `checkChannelHop ch = .ok ()`,
2. If `ch.regStages = 0`, `ch` is strictly tile-local (`ch.src = ch.dst`), and
3. If `ch` crosses an SLR boundary (`ch.src.slr ≠ ch.dst.slr`), `ch` carries at least `2` Laguna
   register stages (`ch.regStages ≥ 2`) at zero lateral Manhattan offset (`ch.src.manhattan2D ch.dst = 0`). -/
theorem checkAllChannelHops_sound (channels : List PlacedChannel)
    (hAll : checkAllChannelHops channels = true) :
    ∀ ch ∈ channels,
      checkChannelHop ch = .ok () ∧
      (ch.regStages = 0 → ch.src = ch.dst) ∧
      (ch.src.slr ≠ ch.dst.slr → ch.regStages ≥ 2 ∧ ch.src.manhattan2D ch.dst = 0) := by
  intro ch hMem
  simp only [checkAllChannelHops, List.all_eq_true] at hAll
  have hCh := hAll ch hMem
  unfold checkChannelHopBool at hCh
  cases hRes : checkChannelHop ch with
  | error e => rw [hRes] at hCh; cases hCh
  | ok u =>
    refine ⟨rfl, ?_, ?_⟩
    · intro hComb
      exact comb_channel_is_tile_local hRes hComb
    · intro hCross
      exact slr_crossing_has_laguna_pair hRes hCross

/-- Golden floorplanned channel list exercising intra-tile combinational wiring, 1-hop pipelined
tile routing, and 2-stage Laguna SLR crossing. -/
def goldenPlacedChannels : List PlacedChannel :=
  [ { name := "local_comb",   src := ⟨0, 0, 0⟩, dst := ⟨0, 0, 0⟩, bitWidth := 64, regStages := 0 }
  , { name := "adj_tile_hop", src := ⟨0, 0, 0⟩, dst := ⟨0, 0, 1⟩, bitWidth := 64, regStages := 1 }
  , { name := "slr_laguna",   src := ⟨0, 0, 1⟩, dst := ⟨1, 0, 1⟩, bitWidth := 64, regStages := 2 } ]

/-! ## 6. Hierarchical Hard-IP Macro SystemVerilog Emission (`emitHierarchicalSV`) -/

/-- Emit hierarchical SystemVerilog-2012 containing all hard-IP macro modules
(`obend_macro_dsp48e2`, `obend_macro_uram288_bypass`, `obend_macro_axis_skid`,
`obend_macro_icap_dpr_tile`, `obend_macro_noc_router_xy`) alongside a top-level `RtlModule`. -/
def emitHierarchicalSV (m : Obend.Hardware.HDL.RtlModule) : String :=
  Obend.Hardware.HDL.emitHierarchicalSV m

end Obend.Hardware.Silicon
end
