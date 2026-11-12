module
/-
# Obend.Hardware.PipelinedRiscCore — 64-Bit RISC ISA, 5-Stage Pipeline & Burch–Dill Commutator

Formalizes the 64-bit RISC architectural ISA (`IsaInstr`, `IsaState`, `stepIsa`, binary codec
`encodeInstr`/`decodeInstr`), the 5-stage `IF/ID/EX/MEM/WB` hazard-forwarding and interlocked
pipelined microarchitecture (`PipeState`, `forwardOperand`, `detectLoadUseStall`,
`branchTakenFlush`, `stepPipeline`), the Burch–Dill pipeline-flushing equivalence proof
(`burchDill_step_commutes`, `pipelinedRisc_multiCycle_refines_isa`), and bounded no-starvation
liveness (`pipelinedRisc_retires_every_3_cycles`, `burchDill_no_starvation_progress`).
-/
public import Obend.Hardware.HDL

public section
namespace Obend.Hardware.PipelinedRisc

open Obend.Hardware.HDL

set_option autoImplicit false

/-! ## 1. 64-Bit Architectural Register File (`r0 ≡ 0`) & Canonical Sparse 64-Bit Data Memory -/

/-- Architectural register index (`r0..r31`), with `r0` (`0`) hardwired to `0#64`. -/
abbrev RegIdx := Fin 32

@[expose] def r0 : RegIdx := ⟨0, by decide⟩
def r1  : RegIdx := ⟨1,  by decide⟩
def r2  : RegIdx := ⟨2,  by decide⟩
def r3  : RegIdx := ⟨3,  by decide⟩
def r4  : RegIdx := ⟨4,  by decide⟩
def r5  : RegIdx := ⟨5,  by decide⟩
def r6  : RegIdx := ⟨6,  by decide⟩
def r7  : RegIdx := ⟨7,  by decide⟩
def r8  : RegIdx := ⟨8,  by decide⟩
def r9  : RegIdx := ⟨9,  by decide⟩
def r10 : RegIdx := ⟨10, by decide⟩
def r11 : RegIdx := ⟨11, by decide⟩
def r12 : RegIdx := ⟨12, by decide⟩
def r13 : RegIdx := ⟨13, by decide⟩
def r14 : RegIdx := ⟨14, by decide⟩
def r15 : RegIdx := ⟨15, by decide⟩
def r31 : RegIdx := ⟨31, by decide⟩

/-- Non-zero destination guard (`rd != r0`) for register writeback and bypass forwarding. -/
@[expose] def regNonZero (r : RegIdx) : Bool := r != r0

/-- Canonical 32-entry 64-bit register file with `arr[0] = 0#64` enforced by invariant. -/
structure RegFile where
  arr     : Array (BitVec 64)
  size_eq : arr.size = 32
  zero_eq : arr[0]? = some 0#64
  deriving DecidableEq

instance : Repr RegFile where reprPrec rf n := reprPrec rf.arr n

def RegFile.empty : RegFile :=
  { arr := Array.replicate 32 0#64, size_eq := by simp, zero_eq := by decide }

instance : Inhabited RegFile := ⟨RegFile.empty⟩

def RegFile.read (rf : RegFile) (r : RegIdx) : BitVec 64 := rf.arr.getD r.val 0#64

def RegFile.write (rf : RegFile) (rd : RegIdx) (val : BitVec 64) : RegFile :=
  if hZero : regNonZero rd then
    { arr := rf.arr.set! rd.val val
      size_eq := by simp [rf.size_eq]
      zero_eq := by
        have hNe : (0 : Nat) ≠ rd.val := by
          unfold regNonZero r0 at hZero; simp only [bne_iff_ne, ne_eq, Fin.ext_iff] at hZero; omega
        simp [Array.set!_eq_setIfInBounds, Ne.symm hNe, rf.zero_eq] }
  else rf

theorem RegFile.read_r0 (rf : RegFile) : rf.read r0 = 0#64 := by
  unfold RegFile.read r0; simp [Array.getD_eq_getD_getElem?, rf.zero_eq]

theorem RegFile.write_r0 (rf : RegFile) (val : BitVec 64) : rf.write r0 val = rf := by
  unfold RegFile.write regNonZero; simp

theorem RegFile.read_write (rf : RegFile) (rd rs : RegIdx) (val : BitVec 64) :
    (rf.write rd val).read rs = if regNonZero rd && (rd == rs) then val else rf.read rs := by
  unfold RegFile.write RegFile.read
  by_cases hNz : regNonZero rd
  · simp only [hNz, ↓reduceDIte, Bool.true_and]
    have hLt : rd.val < rf.arr.size := by rw [rf.size_eq]; exact rd.isLt
    rw [array_getD_set! rf.arr rd.val rs.val val 0#64 hLt]
    by_cases hEq : rs = rd
    · subst hEq; simp
    · have hValNe : rs.val ≠ rd.val := fun h => hEq (Fin.ext h)
      simp [hValNe, beq_false_of_ne (Ne.symm hEq)]
  · simp [hNz]

theorem RegFile.read_write_same (rf : RegFile) (rd : RegIdx) (val : BitVec 64)
    (hNz : regNonZero rd = true) : (rf.write rd val).read rd = val := by
  rw [RegFile.read_write]; simp [hNz]

theorem RegFile.read_write_other (rf : RegFile) (rd rs : RegIdx) (val : BitVec 64)
    (hNe : rd ≠ rs) : (rf.write rd val).read rs = rf.read rs := by
  rw [RegFile.read_write]; simp [beq_false_of_ne hNe]

@[ext]
theorem RegFile.ext {a b : RegFile} (h : ∀ r : RegIdx, a.read r = b.read r) : a = b := by
  cases a with | mk arrA szA zA =>
  cases b with | mk arrB szB zB =>
  congr; apply Array.ext (by omega); intro i hiA hiB
  simpa [RegFile.read, Array.getD_eq_getD_getElem?, hiA, hiB] using h ⟨i, by omega⟩

/-- Strictly sorted non-zero sparse memory invariant from lower bound `bound`. -/
def memSortedFrom (bound : Option Nat) : List (BitVec 64 × BitVec 64) → Bool
  | [] => true
  | (k, v) :: rest =>
    (v != 0#64) && (match bound with | none => true | some b => decide (b < k.toNat)) &&
    memSortedFrom (some k.toNat) rest

def memLookup (addr : BitVec 64) : List (BitVec 64 × BitVec 64) → BitVec 64
  | [] => 0#64
  | (k, v) :: rest => if addr == k then v else memLookup addr rest

def memErase (addr : BitVec 64) : List (BitVec 64 × BitVec 64) → List (BitVec 64 × BitVec 64)
  | [] => []
  | (k, v) :: rest => if addr == k then rest else (k, v) :: memErase addr rest

def memInsertNonZero (addr val : BitVec 64) :
    List (BitVec 64 × BitVec 64) → List (BitVec 64 × BitVec 64)
  | [] => [(addr, val)]
  | (k, v) :: rest =>
    if addr == k then (addr, val) :: rest
    else if addr.toNat < k.toNat then (addr, val) :: (k, v) :: rest
    else (k, v) :: memInsertNonZero addr val rest

private theorem memSortedFrom_weaken :
    ∀ (xs : List (BitVec 64 × BitVec 64)) (b1 b2 : Nat),
      b1 ≤ b2 → memSortedFrom (some b2) xs = true → memSortedFrom (some b1) xs = true
  | [], _, _, _, _ => rfl
  | _ :: _, _, _, _, hSort => by
    simp only [memSortedFrom, Bool.and_eq_true, decide_eq_true_eq] at hSort ⊢
    exact ⟨⟨hSort.1.1, by omega⟩, hSort.2⟩

private theorem memSortedFrom_some_imp_none (xs : List (BitVec 64 × BitVec 64)) (b : Nat)
    (h : memSortedFrom (some b) xs = true) : memSortedFrom none xs = true := by
  cases xs with
  | nil => rfl
  | cons _ _ => simp only [memSortedFrom, Bool.and_eq_true] at h ⊢; exact ⟨⟨h.1.1, trivial⟩, h.2⟩

private theorem memErase_sorted :
    ∀ (xs : List (BitVec 64 × BitVec 64)) (bound : Option Nat) (addr : BitVec 64),
      memSortedFrom bound xs = true → memSortedFrom bound (memErase addr xs) = true
  | [], _, _, _ => rfl
  | (k, _) :: rest, bound, addr, hSort => by
    simp only [memSortedFrom, Bool.and_eq_true] at hSort; unfold memErase
    by_cases hEq : addr == k
    · simp only [hEq, ↓reduceIte]
      cases bound with
      | none => exact memSortedFrom_some_imp_none rest k.toNat hSort.2
      | some b =>
        exact memSortedFrom_weaken rest b k.toNat (Nat.le_of_lt (of_decide_eq_true hSort.1.2)) hSort.2
    · simp only [hEq, Bool.false_eq_true, ↓reduceIte, memSortedFrom, Bool.and_eq_true]
      exact ⟨hSort.1, memErase_sorted rest (some k.toNat) addr hSort.2⟩

private theorem memInsertNonZero_sorted :
    ∀ (xs : List (BitVec 64 × BitVec 64)) (bound : Option Nat) (addr val : BitVec 64),
      (val != 0#64) = true →
      (match bound with | none => true | some b => decide (b < addr.toNat)) = true →
      memSortedFrom bound xs = true → memSortedFrom bound (memInsertNonZero addr val xs) = true
  | [], bound, addr, val, hVal, hBound, _ => by simp [memInsertNonZero, memSortedFrom, hVal, hBound]
  | (k, _) :: rest, bound, addr, val, hVal, hBound, hSort => by
    simp only [memSortedFrom, Bool.and_eq_true] at hSort; unfold memInsertNonZero
    by_cases hEq : addr == k
    · have hAddr := eq_of_beq hEq; subst hAddr; simp [memSortedFrom, hVal, hBound, hSort.2]
    · simp only [hEq, Bool.false_eq_true, ↓reduceIte]
      have hNe : addr.toNat ≠ k.toNat := fun h => hEq (beq_iff_eq.mpr (BitVec.eq_of_toNat_eq h))
      by_cases hLt : addr.toNat < k.toNat
      · simp [hLt, memSortedFrom, hVal, hBound, hSort.1.1, hSort.2]
      · simp only [hLt, ↓reduceIte, memSortedFrom, Bool.and_eq_true]
        exact ⟨hSort.1, memInsertNonZero_sorted rest (some k.toNat) addr val hVal
          (decide_eq_true (by omega)) hSort.2⟩

private theorem memLookup_zero_of_le_bound :
    ∀ (xs : List (BitVec 64 × BitVec 64)) (b : Nat) (addr : BitVec 64),
      memSortedFrom (some b) xs = true → addr.toNat ≤ b → memLookup addr xs = 0#64
  | [], _, _, _, _ => rfl
  | (k, _) :: rest, b, addr, hSort, hLe => by
    simp only [memSortedFrom, Bool.and_eq_true, decide_eq_true_eq] at hSort
    have hNe : (addr == k) = false := beq_false_of_ne (fun h : addr = k => by subst h; omega)
    unfold memLookup; rw [hNe]
    exact memLookup_zero_of_le_bound rest k.toNat addr hSort.2 (by omega)

private theorem memLookup_erase :
    ∀ (xs : List (BitVec 64 × BitVec 64)) (bound : Option Nat) (a q : BitVec 64),
      memSortedFrom bound xs = true →
      memLookup q (memErase a xs) = (if q == a then 0#64 else memLookup q xs)
  | [], _, a, q, _ => by simp [memErase, memLookup]
  | (k, _) :: rest, bound, a, q, hSort => by
    simp only [memSortedFrom, Bool.and_eq_true] at hSort; unfold memErase
    by_cases hAK : a == k
    · have hEq := eq_of_beq hAK; subst hEq; simp only [beq_self_eq_true, ↓reduceIte]
      by_cases hQA : q == a
      · have hEq2 := eq_of_beq hQA; subst hEq2
        simp [memLookup_zero_of_le_bound rest q.toNat q hSort.2 (Nat.le_refl _)]
      · simp [memLookup, hQA]
    · simp only [hAK, Bool.false_eq_true, ↓reduceIte, memLookup]
      by_cases hQK : q == k
      · have hEq2 := eq_of_beq hQK; subst hEq2
        simp [beq_false_of_ne (fun h : q = a => by simp [h] at hAK)]
      · simp [hQK, memLookup_erase rest (some k.toNat) a q hSort.2]

private theorem memLookup_insertNonZero :
    ∀ (xs : List (BitVec 64 × BitVec 64)) (a val q : BitVec 64),
      memLookup q (memInsertNonZero a val xs) = (if q == a then val else memLookup q xs)
  | [], a, val, q => by simp [memInsertNonZero, memLookup]
  | (k, _) :: rest, a, val, q => by
    unfold memInsertNonZero
    by_cases hAK : a == k
    · have hEq := eq_of_beq hAK; subst hEq; by_cases hQA : q == a <;> simp [memLookup, hQA]
    · simp only [hAK, Bool.false_eq_true, ↓reduceIte]
      by_cases hLt : a.toNat < k.toNat
      · by_cases hQA : q == a <;> simp [hLt, memLookup, hQA]
      · simp only [hLt, ↓reduceIte, memLookup]
        by_cases hQK : q == k
        · have hEq2 := eq_of_beq hQK; subst hEq2
          simp [beq_false_of_ne (fun h : q = a => by simp [h] at hAK)]
        · simp [hQK, memLookup_insertNonZero rest a val q]

private theorem memSortedFrom_ext :
    ∀ (xs ys : List (BitVec 64 × BitVec 64)) (bound : Option Nat),
      memSortedFrom bound xs = true → memSortedFrom bound ys = true →
      (∀ a : BitVec 64, memLookup a xs = memLookup a ys) → xs = ys
  | [], [], _, _, _, _ => rfl
  | [], (k, v) :: _, _, _, hY, hEq => by
    simp only [memSortedFrom, Bool.and_eq_true, bne_iff_ne, ne_eq] at hY
    have hK := hEq k; simp [memLookup] at hK; exact False.elim (hY.1.1 hK.symm)
  | (k, v) :: _, [], _, hX, _, hEq => by
    simp only [memSortedFrom, Bool.and_eq_true, bne_iff_ne, ne_eq] at hX
    have hK := hEq k; simp [memLookup] at hK; exact False.elim (hX.1.1 hK)
  | (k1, v1) :: r1, (k2, v2) :: r2, _, hX, hY, hEq => by
    simp only [memSortedFrom, Bool.and_eq_true] at hX hY
    have hNoLt12 : ¬(k1.toNat < k2.toNat) := fun hLt => by
      have hK1 := hEq k1
      have hNe : (k1 == k2) = false := beq_false_of_ne (fun h : k1 = k2 => by subst h; omega)
      simp [memLookup, hNe, memLookup_zero_of_le_bound r2 k2.toNat k1 hY.2 (Nat.le_of_lt hLt)] at hK1
      exact (by simpa using hX.1.1 : v1 ≠ 0#64) hK1
    have hNoLt21 : ¬(k2.toNat < k1.toNat) := fun hLt => by
      have hK2 := hEq k2
      have hNe : (k2 == k1) = false := beq_false_of_ne (fun h : k2 = k1 => by subst h; omega)
      simp [memLookup, hNe, memLookup_zero_of_le_bound r1 k1.toNat k2 hX.2 (Nat.le_of_lt hLt)] at hK2
      exact (by simpa using hY.1.1 : v2 ≠ 0#64) hK2.symm
    have hKEq : k1 = k2 := BitVec.eq_of_toNat_eq (by omega)
    subst hKEq
    have hVEq : v1 = v2 := by simpa [memLookup] using hEq k1
    subst hVEq; congr 1
    apply memSortedFrom_ext r1 r2 (some k1.toNat) hX.2 hY.2; intro a
    by_cases hLe : a.toNat ≤ k1.toNat
    · rw [memLookup_zero_of_le_bound r1 k1.toNat a hX.2 hLe,
          memLookup_zero_of_le_bound r2 k1.toNat a hY.2 hLe]
    · have hNe : (a == k1) = false := beq_false_of_ne (fun h : a = k1 => by subst h; omega)
      simpa [memLookup, hNe] using hEq a

/-- Canonical 64-bit word-addressed data memory (`BitVec 64 → BitVec 64`, finitely supported). -/
structure DataMem where
  entries   : List (BitVec 64 × BitVec 64)
  canonical : memSortedFrom none entries = true
  deriving DecidableEq

instance : Repr DataMem where reprPrec m n := reprPrec m.entries n

def DataMem.empty : DataMem := ⟨[], rfl⟩
instance : Inhabited DataMem := ⟨DataMem.empty⟩

def DataMem.read (m : DataMem) (addr : BitVec 64) : BitVec 64 := memLookup addr m.entries

def DataMem.write (m : DataMem) (addr val : BitVec 64) : DataMem :=
  if hNz : val != 0#64 then
    ⟨memInsertNonZero addr val m.entries,
     memInsertNonZero_sorted m.entries none addr val hNz rfl m.canonical⟩
  else
    ⟨memErase addr m.entries, memErase_sorted m.entries none addr m.canonical⟩

theorem DataMem.read_empty (addr : BitVec 64) : DataMem.empty.read addr = 0#64 := by rfl

theorem DataMem.read_write (m : DataMem) (addr q : BitVec 64) (val : BitVec 64) :
    (m.write addr val).read q = if q == addr then val else m.read q := by
  unfold DataMem.write DataMem.read
  by_cases hNz : (val != 0#64) = true
  · simp [hNz, memLookup_insertNonZero]
  · simp only [Bool.not_eq_true] at hNz
    have hValZero : val = 0#64 := by simpa [bne_eq_false_iff_eq] using hNz
    subst hValZero; simp [memLookup_erase m.entries none addr q m.canonical]

@[ext]
theorem DataMem.ext {m1 m2 : DataMem} (h : ∀ a : BitVec 64, m1.read a = m2.read a) : m1 = m2 := by
  cases m1 with | mk e1 c1 => cases m2 with | mk e2 c2 =>
  congr; exact memSortedFrom_ext e1 e2 none c1 c2 h

/-! ## 2. Clean 64-Bit RISC Architectural ISA (`IsaInstr`, `IsaState`, `stepIsa`) & Binary Codec -/

/-- Architectural 64-bit RISC instruction set: ALU/immediate, load/store, branch/jump, and NOP. -/
inductive IsaInstr where
  | ADD  (rd rs1 rs2 : RegIdx)
  | SUB  (rd rs1 rs2 : RegIdx)
  | AND  (rd rs1 rs2 : RegIdx)
  | OR   (rd rs1 rs2 : RegIdx)
  | XOR  (rd rs1 rs2 : RegIdx)
  | SLT  (rd rs1 rs2 : RegIdx)
  | ADDI (rd rs1 : RegIdx) (imm : BitVec 64)
  | LD   (rd rs1 : RegIdx) (offset : BitVec 64)
  | ST   (rs1 rs2 : RegIdx) (offset : BitVec 64)
  | BEQ  (rs1 rs2 : RegIdx) (offset : BitVec 64)
  | BNE  (rs1 rs2 : RegIdx) (offset : BitVec 64)
  | JAL  (rd : RegIdx) (offset : BitVec 64)
  | NOP
  deriving DecidableEq, Repr, Inhabited

/-- Architectural ISA state (`pc`, 32×64-bit `regs` with `r0 ≡ 0`, and 64-bit `dmem`). -/
structure IsaState where
  pc   : BitVec 64
  regs : RegFile
  dmem : DataMem
  deriving DecidableEq, Repr, Inhabited

@[ext]
theorem IsaState.ext {s1 s2 : IsaState}
    (hPc : s1.pc = s2.pc) (hRegs : s1.regs = s2.regs) (hMem : s1.dmem = s2.dmem) : s1 = s2 := by
  cases s1; cases s2; subst hPc hRegs hMem; rfl

private theorem isaState_eta_pc (s : IsaState) (pc' : BitVec 64) (h : s.pc = pc') :
    { pc := pc', regs := s.regs, dmem := s.dmem } = s := by cases s; subst h; rfl

abbrev InstrMem := BitVec 64 → IsaInstr

/-- Lift a sequential instruction array (`pc = 0, 4, 8, ...`) to an `InstrMem` (`NOP` outside). -/
def progToImem (prog : Array IsaInstr) (pc : BitVec 64) : IsaInstr :=
  if pc.toNat % 4 == 0 then prog.getD (pc.toNat / 4) .NOP else .NOP

def instrOpcode : IsaInstr → Nat
  | .NOP => 0 | .ADD .. => 1 | .SUB .. => 2 | .AND .. => 3 | .OR .. => 4
  | .XOR .. => 5 | .SLT .. => 6 | .ADDI .. => 7 | .LD .. => 8 | .ST .. => 9
  | .BEQ .. => 10 | .BNE .. => 11 | .JAL .. => 12

def instrRd : IsaInstr → RegIdx
  | .ADD rd _ _ | .SUB rd _ _ | .AND rd _ _ | .OR rd _ _ | .XOR rd _ _ | .SLT rd _ _
  | .ADDI rd _ _ | .LD rd _ _ | .JAL rd _ => rd
  | .ST .. | .BEQ .. | .BNE .. | .NOP => r0

def instrRs1 : IsaInstr → RegIdx
  | .ADD _ rs1 _ | .SUB _ rs1 _ | .AND _ rs1 _ | .OR _ rs1 _ | .XOR _ rs1 _ | .SLT _ rs1 _
  | .ADDI _ rs1 _ | .LD _ rs1 _ | .ST rs1 _ _ | .BEQ rs1 _ _ | .BNE rs1 _ _ => rs1
  | .JAL .. | .NOP => r0

def instrRs2 : IsaInstr → RegIdx
  | .ADD _ _ rs2 | .SUB _ _ rs2 | .AND _ _ rs2 | .OR _ _ rs2 | .XOR _ _ rs2 | .SLT _ _ rs2
  | .ST _ rs2 _ | .BEQ _ rs2 _ | .BNE _ rs2 _ => rs2
  | .ADDI .. | .LD .. | .JAL .. | .NOP => r0

def instrImm : IsaInstr → BitVec 64
  | .ADDI _ _ imm | .LD _ _ imm | .ST _ _ imm
  | .BEQ _ _ imm  | .BNE _ _ imm | .JAL _ imm => imm
  | .ADD .. | .SUB .. | .AND .. | .OR .. | .XOR .. | .SLT .. | .NOP => 0#64

def instrWritesReg : IsaInstr → Bool
  | .ADD .. | .SUB .. | .AND .. | .OR .. | .XOR .. | .SLT ..
  | .ADDI .. | .LD .. | .JAL .. => true
  | .ST .. | .BEQ .. | .BNE .. | .NOP => false

def instrIsLoad  : IsaInstr → Bool | .LD .. => true | _ => false
def instrIsStore : IsaInstr → Bool | .ST .. => true | _ => false

/-- Execute-stage ALU / effective-address / link-address evaluator. -/
def exAluResult (pc : BitVec 64) (instr : IsaInstr) (v1 v2 : BitVec 64) : BitVec 64 :=
  match instr with
  | .ADD .. => v1 + v2 | .SUB .. => v1 - v2 | .AND .. => v1 &&& v2
  | .OR  .. => v1 ||| v2 | .XOR .. => v1 ^^^ v2
  | .SLT .. => if BitVec.slt v1 v2 then 1#64 else 0#64
  | .ADDI _ _ imm => v1 + imm | .LD _ _ off => v1 + off | .ST _ _ off => v1 + off
  | .JAL _ _ => pc + 4#64 | .BEQ .. | .BNE .. | .NOP => 0#64

/-- Architectural branch/jump condition (`BEQ`, `BNE`, `JAL`). -/
def evalBranchCond (instr : IsaInstr) (v1 v2 : BitVec 64) : Bool :=
  match instr with
  | .BEQ .. => v1 == v2 | .BNE .. => v1 != v2 | .JAL .. => true | _ => false

/-- Control-hazard squash resolver in `EX`: fires when a valid `BEQ`, `BNE`, or `JAL` redirects `PC`. -/
@[expose] def branchTakenFlush (valid : Bool) (instr : IsaInstr) (v1 v2 : BitVec 64) : Bool :=
  valid && evalBranchCond instr v1 v2

def exBranchTarget (pc : BitVec 64) (instr : IsaInstr) : BitVec 64 := pc + instrImm instr

/-- Execute one architectural instruction `instr` against `s : IsaState`. -/
def execInstr (instr : IsaInstr) (s : IsaState) : IsaState :=
  let v1 := s.regs.read (instrRs1 instr)
  let v2 := s.regs.read (instrRs2 instr)
  let aluOut := exAluResult s.pc instr v1 v2
  let nextPc := if evalBranchCond instr v1 v2 then exBranchTarget s.pc instr else s.pc + 4#64
  let nextDmem := if instrIsStore instr then s.dmem.write aluOut v2 else s.dmem
  let wbVal := if instrIsLoad instr then s.dmem.read aluOut else aluOut
  let nextRegs := if instrWritesReg instr then s.regs.write (instrRd instr) wbVal else s.regs
  { pc := nextPc, regs := nextRegs, dmem := nextDmem }

/-- Single-step architectural ISA semantics. -/
@[expose] def stepIsa (imem : InstrMem) (s : IsaState) : IsaState := execInstr (imem s.pc) s

/-- `n`-step architectural ISA execution. -/
@[expose] def stepIsaN (imem : InstrMem) : Nat → IsaState → IsaState
  | 0, s     => s
  | n + 1, s => stepIsaN imem n (stepIsa imem s)

theorem stepIsaN_add (imem : InstrMem) (a b : Nat) (s : IsaState) :
    stepIsaN imem (a + b) s = stepIsaN imem b (stepIsaN imem a s) := by
  induction a generalizing s with
  | zero => simp [stepIsaN]
  | succ a ih => simp [Nat.succ_add, stepIsaN, ih]

theorem stepIsaN_one (imem : InstrMem) (s : IsaState) : stepIsaN imem 1 s = stepIsa imem s := by rfl

theorem isLoad_disjoint (instr : IsaInstr) (valid : Bool) (v1 v2 : BitVec 64)
    (hLoad : instrIsLoad instr = true) :
    instrWritesReg instr = true ∧ instrIsStore instr = false ∧
    branchTakenFlush valid instr v1 v2 = false := by
  cases instr <;> simp [instrIsLoad, instrWritesReg, instrIsStore, branchTakenFlush, evalBranchCond] at hLoad ⊢

theorem branchTaken_not_load (instr : IsaInstr) (valid : Bool) (v1 v2 : BitVec 64)
    (hBr : branchTakenFlush valid instr v1 v2 = true) :
    valid = true ∧ evalBranchCond instr v1 v2 = true ∧
    instrIsLoad instr = false ∧ instrIsStore instr = false := by
  cases valid <;> cases instr <;>
    simp [branchTakenFlush, evalBranchCond, instrIsLoad, instrIsStore] at hBr ⊢ <;> exact hBr

/-- Immediate fits in a signed 44-bit field (`bits [63:20]` of a 64-bit instruction word). -/
def FitsSigned44 (imm : BitVec 64) : Bool := BitVec.sshiftRight (imm <<< 20) 20 == imm

/-- Encode an `IsaInstr` into a 64-bit instruction word (`[3:0]` op, `[8:4]` rd, `[13:9]` rs1,
    `[18:14]` rs2, `[63:20]` signed 44-bit immediate). -/
def encodeInstr (instr : IsaInstr) : BitVec 64 :=
  let low20 := BitVec.ofNat 64
    (instrOpcode instr + 16 * (instrRd instr).val +
     512 * (instrRs1 instr).val + 16384 * (instrRs2 instr).val)
  ((instrImm instr) <<< 20) ||| low20

/-- Decode a 64-bit hardware instruction word into an `IsaInstr`. -/
def decodeInstr (w : BitVec 64) : IsaInstr :=
  let op  := (w &&& 15#64).toNat
  let rd  : RegIdx := ⟨((w >>> 4) &&& 31#64).toNat % 32, Nat.mod_lt _ (by decide)⟩
  let rs1 : RegIdx := ⟨((w >>> 9) &&& 31#64).toNat % 32, Nat.mod_lt _ (by decide)⟩
  let rs2 : RegIdx := ⟨((w >>> 14) &&& 31#64).toNat % 32, Nat.mod_lt _ (by decide)⟩
  let imm := BitVec.sshiftRight w 20
  match op with
  | 1 => .ADD rd rs1 rs2 | 2 => .SUB rd rs1 rs2 | 3 => .AND rd rs1 rs2
  | 4 => .OR  rd rs1 rs2 | 5 => .XOR rd rs1 rs2 | 6 => .SLT rd rs1 rs2
  | 7 => .ADDI rd rs1 imm | 8 => .LD rd rs1 imm | 9 => .ST rs1 rs2 imm
  | 10 => .BEQ rs1 rs2 imm | 11 => .BNE rs1 rs2 imm | 12 => .JAL rd imm
  | _ => .NOP

/-- Bit-slice extraction theorem for `encodeInstr` (`w_0..w_4`). -/
theorem encodeInstr_bit_slices (instr : IsaInstr) (hImm : FitsSigned44 (instrImm instr) = true) :
    let w := encodeInstr instr
    (w &&& 15#64) = BitVec.ofNat 64 (instrOpcode instr) ∧
    ((w >>> 4) &&& 31#64) = BitVec.ofNat 64 (instrRd instr).val ∧
    ((w >>> 9) &&& 31#64) = BitVec.ofNat 64 (instrRs1 instr).val ∧
    ((w >>> 14) &&& 31#64) = BitVec.ofNat 64 (instrRs2 instr).val ∧
    BitVec.sshiftRight w 20 = instrImm instr := by
  intro w
  have hOpLt : instrOpcode instr < 16 := by cases instr <;> simp [instrOpcode]
  have hRdLt : (instrRd instr).val < 32 := (instrRd instr).isLt
  have hRs1Lt : (instrRs1 instr).val < 32 := (instrRs1 instr).isLt
  have hRs2Lt : (instrRs2 instr).val < 32 := (instrRs2 instr).isLt
  let lowVal := instrOpcode instr + 16 * (instrRd instr).val +
    512 * (instrRs1 instr).val + 16384 * (instrRs2 instr).val
  let low20 := BitVec.ofNat 64 lowVal
  have hLowLt : lowVal < 2 ^ 20 := by omega
  have hLowToNat : low20.toNat = lowVal := by simp [low20, BitVec.toNat_ofNat]; omega
  have hLowBits : ∀ j : Nat, j < 20 → w.getLsbD j = low20.getLsbD j := fun j hj => by
    have hj64 : j < 64 := by omega
    dsimp only [w, encodeInstr]
    rw [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]; simp [hj64, hj, low20, lowVal]
  have hHighZero : ∀ j : Nat, 20 ≤ j → low20.getLsbD j = false := fun j hj => by
    have hDiv : lowVal / 2 ^ j = 0 :=
      Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hLowLt (Nat.pow_le_pow_right (by decide) hj))
    simp [low20, BitVec.getLsbD_ofNat, Nat.testBit, Nat.shiftRight_eq_div_pow, hDiv]
  have hMask4 : ∀ i : Nat, ¬(i < 4) → (15#64 : BitVec 64).getLsbD i = false := fun i hi => by
    by_cases h64 : i < 64
    · revert hi; revert i; decide
    · exact BitVec.getLsbD_of_ge 15#64 i (by omega)
  have hMask5 : ∀ i : Nat, ¬(i < 5) → (31#64 : BitVec 64).getLsbD i = false := fun i hi => by
    by_cases h64 : i < 64
    · revert hi; revert i; decide
    · exact BitVec.getLsbD_of_ge 31#64 i (by omega)
  have hSlice5 : ∀ sh : Nat, sh + 5 ≤ 20 → ((w >>> sh) &&& 31#64) = ((low20 >>> sh) &&& 31#64) :=
    fun sh _ => by
      apply BitVec.eq_of_getLsbD_eq; intro i _
      simp only [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight]
      by_cases hi5 : i < 5
      · rw [hLowBits (sh + i) (by omega)]
      · simp [hMask5 i hi5]
  have hAnd15 : ∀ x : Nat, x &&& 15 = x % 16 := fun x => Nat.and_two_pow_sub_one_eq_mod x 4
  have hAnd31 : ∀ x : Nat, x &&& 31 = x % 32 := fun x => Nat.and_two_pow_sub_one_eq_mod x 5
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hS0 : (w &&& 15#64) = (low20 &&& 15#64) := by
      apply BitVec.eq_of_getLsbD_eq; intro i _; simp only [BitVec.getLsbD_and]
      by_cases hi4 : i < 4
      · rw [hLowBits i (by omega)]
      · simp [hMask4 i hi4]
    rw [hS0]; apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and, BitVec.toNat_ofNat, hLowToNat, hAnd15]; dsimp only [lowVal]; omega
  · rw [hSlice5 4 (by decide)]; apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, hLowToNat,
      Nat.shiftRight_eq_div_pow, hAnd31]; dsimp only [lowVal]; omega
  · rw [hSlice5 9 (by decide)]; apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, hLowToNat,
      Nat.shiftRight_eq_div_pow, hAnd31]; dsimp only [lowVal]; omega
  · rw [hSlice5 14 (by decide)]; apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, hLowToNat,
      Nat.shiftRight_eq_div_pow, hAnd31]; dsimp only [lowVal]; omega
  · have hEqShift : BitVec.sshiftRight w 20 = BitVec.sshiftRight ((instrImm instr) <<< 20) 20 := by
      apply BitVec.eq_of_getLsbD_eq; intro i _
      have hHighEq : ∀ j : Nat, 20 ≤ j → w.getLsbD j = ((instrImm instr) <<< 20).getLsbD j :=
        fun j hj => by dsimp only [w, encodeInstr]; rw [BitVec.getLsbD_or, hHighZero j hj, Bool.or_false]
      rw [BitVec.getLsbD_sshiftRight, BitVec.getLsbD_sshiftRight,
          BitVec.msb_eq_getLsbD_last, BitVec.msb_eq_getLsbD_last]
      by_cases hLt : 20 + i < 64
      · simp only [hLt, ↓reduceIte, hHighEq (20 + i) (by omega)]
      · simp only [hLt, ↓reduceIte]; rw [hHighEq 63 (by decide)]
    rw [hEqShift]; exact eq_of_beq hImm

theorem decodeInstr_encodeInstr (instr : IsaInstr) (hImm : FitsSigned44 (instrImm instr) = true) :
    decodeInstr (encodeInstr instr) = instr := by
  obtain ⟨h0, h4, h9, h14, h20⟩ := encodeInstr_bit_slices instr hImm
  have hOpLt : instrOpcode instr < 16 := by cases instr <;> simp [instrOpcode]
  have hRegToNat : ∀ r : RegIdx, (BitVec.ofNat 64 r.val).toNat % 32 = r.val := fun r => by
    have hr := r.isLt; simp only [BitVec.toNat_ofNat]; omega
  unfold decodeInstr; simp only [h0, h4, h9, h14, h20, hRegToNat, Fin.eta]
  have hOpNat : (BitVec.ofNat 64 (instrOpcode instr)).toNat = instrOpcode instr := by
    simp only [BitVec.toNat_ofNat]; omega
  rw [hOpNat]; cases instr <;> rfl

/-! ## 3. 5-Stage `IF/ID/EX/MEM/WB` Forwarding & Interlocked Pipeline (`PipeState`, `stepPipeline`) -/

structure IfIdLatch where
  valid : Bool
  pc    : BitVec 64
  instr : IsaInstr
  deriving DecidableEq, Repr, Inhabited

def IfIdLatch.bubble : IfIdLatch := { valid := false, pc := 0#64, instr := .NOP }

structure IdExLatch where
  valid : Bool
  pc    : BitVec 64
  instr : IsaInstr
  rs1   : RegIdx
  rs2   : RegIdx
  v1    : BitVec 64
  v2    : BitVec 64
  deriving DecidableEq, Repr, Inhabited

def IdExLatch.bubble : IdExLatch :=
  { valid := false, pc := 0#64, instr := .NOP, rs1 := r0, rs2 := r0, v1 := 0#64, v2 := 0#64 }

structure ExMemLatch where
  valid    : Bool
  pc       : BitVec 64
  instr    : IsaInstr
  rd       : RegIdx
  regWrite : Bool
  isLoad   : Bool
  isStore  : Bool
  aluVal   : BitVec 64
  storeVal : BitVec 64
  deriving DecidableEq, Repr, Inhabited

def ExMemLatch.bubble : ExMemLatch :=
  { valid := false, pc := 0#64, instr := .NOP, rd := r0,
    regWrite := false, isLoad := false, isStore := false, aluVal := 0#64, storeVal := 0#64 }

structure MemWbLatch where
  valid    : Bool
  rd       : RegIdx
  regWrite : Bool
  wbVal    : BitVec 64
  deriving DecidableEq, Repr, Inhabited

def MemWbLatch.bubble : MemWbLatch :=
  { valid := false, rd := r0, regWrite := false, wbVal := 0#64 }

@[simp] theorem ifId_bubble_valid  : IfIdLatch.bubble.valid  = false := by rfl
@[simp] theorem idEx_bubble_valid  : IdExLatch.bubble.valid  = false := by rfl
@[simp] theorem exMem_bubble_valid : ExMemLatch.bubble.valid = false := by rfl
@[simp] theorem memWb_bubble_valid : MemWbLatch.bubble.valid = false := by rfl

/-- Complete 5-stage pipelined processor state (`IF/ID`, `ID/EX`, `EX/MEM`, `MEM/WB`, `regs`, `dmem`,
    plus monotone `retiredCount` of valid instructions retiring at `WB`). -/
structure PipeState where
  fetchPc      : BitVec 64
  ifId         : IfIdLatch
  idEx         : IdExLatch
  exMem        : ExMemLatch
  memWb        : MemWbLatch
  regs         : RegFile
  dmem         : DataMem
  retiredCount : Nat
  deriving DecidableEq, Repr, Inhabited

def initPipeState (s : IsaState) : PipeState :=
  { fetchPc := s.pc, ifId := .bubble, idEx := .bubble, exMem := .bubble, memWb := .bubble,
    regs := s.regs, dmem := s.dmem, retiredCount := 0 }

/-- Full priority bypass forwarding mux (`EX/MEM → EX` primary, `MEM/WB → EX` secondary,
    suppressing forwarding on `r0` via `regNonZero`). -/
@[expose] def forwardOperand
    (rs : RegIdx) (idVal : BitVec 64) (exMem : ExMemLatch) (memWb : MemWbLatch) : BitVec 64 :=
  if exMem.valid && exMem.regWrite && !exMem.isLoad && regNonZero exMem.rd && (exMem.rd == rs) then
    exMem.aluVal
  else if memWb.valid && memWb.regWrite && regNonZero memWb.rd && (memWb.rd == rs) then
    memWb.wbVal
  else idVal

/-- Load-use interlock detector: stalls `PC` and `IF/ID` for 1 cycle and injects a bubble into
    `ID/EX` when `ID/EX` holds a valid `LD rd` (`rd != r0`) read by a valid `IF/ID` instruction. -/
@[expose] def detectLoadUseStall (idEx : IdExLatch) (ifId : IfIdLatch) : Bool :=
  let ldRd := instrRd idEx.instr
  idEx.valid && ifId.valid && instrIsLoad idEx.instr && regNonZero ldRd &&
    ((ldRd == instrRs1 ifId.instr) || (ldRd == instrRs2 ifId.instr))

def applyWb (regs : RegFile) (memWb : MemWbLatch) : RegFile :=
  if memWb.valid && memWb.regWrite then regs.write memWb.rd memWb.wbVal else regs

def applyExMemMem (dmem : DataMem) (exMem : ExMemLatch) : DataMem :=
  if exMem.valid && exMem.isStore then dmem.write exMem.aluVal exMem.storeVal else dmem

def memStepWb (dmem : DataMem) (exMem : ExMemLatch) : MemWbLatch :=
  if exMem.valid then
    let wbVal := if exMem.isLoad then dmem.read exMem.aluVal else exMem.aluVal
    { valid := true, rd := exMem.rd, regWrite := exMem.regWrite, wbVal := wbVal }
  else .bubble

@[simp] theorem applyWb_bubble (r : RegFile) : applyWb r .bubble = r := by rfl
@[simp] theorem applyExMemMem_bubble (m : DataMem) : applyExMemMem m .bubble = m := by rfl
@[simp] theorem memStepWb_bubble (m : DataMem) : memStepWb m .bubble = .bubble := by rfl

/-- Unified 5-stage clock edge (`fetchEn = true` for `stepPipeline`, `false` for `stepFlush`). -/
def stepCore (fetchEn : Bool) (imem : InstrMem) (p : PipeState) : PipeState :=
  let regsAfterWb := applyWb p.regs p.memWb
  let nextRetired := if p.memWb.valid then p.retiredCount + 1 else p.retiredCount
  let nextDmem    := applyExMemMem p.dmem p.exMem
  let nextMemWb   := memStepWb p.dmem p.exMem
  let fwd1   := forwardOperand p.idEx.rs1 p.idEx.v1 p.exMem p.memWb
  let fwd2   := forwardOperand p.idEx.rs2 p.idEx.v2 p.exMem p.memWb
  let squash := branchTakenFlush p.idEx.valid p.idEx.instr fwd1 fwd2
  let stall  := detectLoadUseStall p.idEx p.ifId
  let nextExMem : ExMemLatch :=
    if p.idEx.valid then
      { valid := true, pc := p.idEx.pc, instr := p.idEx.instr,
        rd := instrRd p.idEx.instr, regWrite := instrWritesReg p.idEx.instr,
        isLoad := instrIsLoad p.idEx.instr, isStore := instrIsStore p.idEx.instr,
        aluVal := exAluResult p.idEx.pc p.idEx.instr fwd1 fwd2, storeVal := fwd2 }
    else .bubble
  let nextIdEx : IdExLatch :=
    if squash || stall || !p.ifId.valid then .bubble
    else
      let rs1 := instrRs1 p.ifId.instr
      let rs2 := instrRs2 p.ifId.instr
      { valid := true, pc := p.ifId.pc, instr := p.ifId.instr,
        rs1 := rs1, rs2 := rs2, v1 := regsAfterWb.read rs1, v2 := regsAfterWb.read rs2 }
  let nextIfId : IfIdLatch :=
    if squash then .bubble
    else if stall then p.ifId
    else if fetchEn then { valid := true, pc := p.fetchPc, instr := imem p.fetchPc }
    else .bubble
  let nextFetchPc : BitVec 64 :=
    if squash then exBranchTarget p.idEx.pc p.idEx.instr
    else if stall then p.fetchPc
    else if fetchEn then p.fetchPc + 4#64
    else p.fetchPc
  { fetchPc := nextFetchPc, ifId := nextIfId, idEx := nextIdEx, exMem := nextExMem,
    memWb := nextMemWb, regs := regsAfterWb, dmem := nextDmem, retiredCount := nextRetired }

/-- Single-cycle hardware step of the 5-stage forwarding/interlocked pipeline. -/
@[expose] def stepPipeline (imem : InstrMem) (p : PipeState) : PipeState := stepCore true imem p

/-- `n`-cycle hardware execution of the 5-stage pipeline. -/
def stepPipelineN (imem : InstrMem) : Nat → PipeState → PipeState
  | 0, p     => p
  | n + 1, p => stepPipelineN imem n (stepPipeline imem p)

theorem stepPipelineN_add (imem : InstrMem) (a b : Nat) (p : PipeState) :
    stepPipelineN imem (a + b) p = stepPipelineN imem b (stepPipelineN imem a p) := by
  induction a generalizing p with
  | zero => simp [stepPipelineN]
  | succ a ih => simp [Nat.succ_add, stepPipelineN, ih]

/-! ## 4. Burch–Dill Pipeline Flushing Projection (`flushPipeline`) & Commutator Proof -/

def stepFlush (p : PipeState) : PipeState := stepCore false (fun _ => .NOP) p

def stepFlushN : Nat → PipeState → PipeState
  | 0, p     => p
  | n + 1, p => stepFlushN n (stepFlush p)

def extractIsa (p : PipeState) : IsaState := { pc := p.fetchPc, regs := p.regs, dmem := p.dmem }

/-- Burch–Dill hardware pipeline drain/flush projection: clocks `WB`, `MEM`, `EX`, `ID` to
    completion in 5 bubble-fed drain cycles without fetching new instructions. -/
@[expose] def flushPipeline (p : PipeState) : IsaState := extractIsa (stepFlushN 5 p)

/-- Structural well-formedness invariant of reachable 5-stage `PipeState`s (`PipeWf p`). -/
structure PipeWf (p : PipeState) : Prop where
  idEx_decode :
    p.idEx.valid = true →
      p.idEx.rs1 = instrRs1 p.idEx.instr ∧ p.idEx.rs2 = instrRs2 p.idEx.instr ∧
      p.idEx.v1 = p.regs.read p.idEx.rs1 ∧ p.idEx.v2 = p.regs.read p.idEx.rs2
  exMem_decode :
    p.exMem.valid = true →
      p.exMem.rd = instrRd p.exMem.instr ∧ p.exMem.regWrite = instrWritesReg p.exMem.instr ∧
      p.exMem.isLoad = instrIsLoad p.exMem.instr ∧ p.exMem.isStore = instrIsStore p.exMem.instr
  no_load_use_in_ex :
    p.idEx.valid = true → p.exMem.valid = true → p.exMem.isLoad = true →
    regNonZero p.exMem.rd = true → p.exMem.rd ≠ p.idEx.rs1 ∧ p.exMem.rd ≠ p.idEx.rs2
  ifId_pc_seq :
    p.ifId.valid = true → p.fetchPc = p.ifId.pc + 4#64
  idEx_pc_seq_when_ifId_empty :
    p.idEx.valid = true → p.ifId.valid = false → p.fetchPc = p.idEx.pc + 4#64

theorem initPipeState_wf (s : IsaState) : PipeWf (initPipeState s) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [initPipeState]

example : ∃ p : PipeState, PipeWf p := ⟨initPipeState default, initPipeState_wf default⟩

/-- Closed-form stage-by-stage architectural drain (`WB → MEM → EX → ID`). -/
def drainStages (p : PipeState) : IsaState :=
  let regs1 := applyWb p.regs p.memWb
  let dmem2 := applyExMemMem p.dmem p.exMem
  let regs2 := applyWb regs1 (memStepWb p.dmem p.exMem)
  if p.idEx.valid then
    let sEx := execInstr p.idEx.instr { pc := p.idEx.pc, regs := regs2, dmem := dmem2 }
    if evalBranchCond p.idEx.instr (regs2.read (instrRs1 p.idEx.instr)) (regs2.read (instrRs2 p.idEx.instr)) then
      sEx
    else if p.ifId.valid then
      execInstr p.ifId.instr { pc := p.ifId.pc, regs := sEx.regs, dmem := sEx.dmem }
    else sEx
  else if p.ifId.valid then
    execInstr p.ifId.instr { pc := p.ifId.pc, regs := regs2, dmem := dmem2 }
  else { pc := p.fetchPc, regs := regs2, dmem := dmem2 }

/-- Core forwarding correctness lemma: under no-load-use-in-EX, `forwardOperand` computes the
    exact architectural value in `regs` after `memWb` and `exMem` write back! -/
theorem forwardOperand_eq_drained_reg
    (regs : RegFile) (dmem : DataMem) (exMem : ExMemLatch) (memWb : MemWbLatch) (rs : RegIdx)
    (hNoLoadHazard : exMem.valid = true → exMem.isLoad = true → regNonZero exMem.rd = true → exMem.rd ≠ rs) :
    forwardOperand rs (regs.read rs) exMem memWb =
      (applyWb (applyWb regs memWb) (memStepWb dmem exMem)).read rs := by
  have hWb1 : (applyWb regs memWb).read rs =
      if memWb.valid && memWb.regWrite && regNonZero memWb.rd && (memWb.rd == rs) then
        memWb.wbVal else regs.read rs := by
    unfold applyWb; cases hV : memWb.valid <;> cases hW : memWb.regWrite <;> simp [RegFile.read_write]
  unfold forwardOperand applyWb memStepWb
  cases hExV : exMem.valid
  · simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]; exact hWb1.symm
  · simp only [Bool.true_and, ↓reduceIte]
    cases hExW : exMem.regWrite
    · simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]; exact hWb1.symm
    · simp only [Bool.true_and, ↓reduceIte]; rw [RegFile.read_write]
      cases hExLoad : exMem.isLoad
      · simp only [Bool.not_false, Bool.true_and]
        by_cases hMatch : regNonZero exMem.rd && (exMem.rd == rs)
        · simp [hMatch]
        · simp only [hMatch, Bool.false_eq_true, ↓reduceIte]; exact hWb1.symm
      · simp only [Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
        have hNoMatch : (regNonZero exMem.rd && (exMem.rd == rs)) = false := by
          cases hNz : regNonZero exMem.rd
          · simp
          · simp [beq_false_of_ne (hNoLoadHazard hExV hExLoad hNz)]
        rw [hNoMatch]; simp only [Bool.false_eq_true, ↓reduceIte]; exact hWb1.symm

/-- Both `stepPipeline` (`fetchEn = true`) and `stepFlush` (`fetchEn = false`) preserve `PipeWf`! -/
theorem stepCore_preserves_wf (fetchEn : Bool) (imem : InstrMem) (p : PipeState) (hWf : PipeWf p) :
    PipeWf (stepCore fetchEn imem p) := by
  dsimp only [stepCore]
  generalize hSqEq : branchTakenFlush p.idEx.valid p.idEx.instr
    (forwardOperand p.idEx.rs1 p.idEx.v1 p.exMem p.memWb)
    (forwardOperand p.idEx.rs2 p.idEx.v2 p.exMem p.memWb) = squash
  generalize hStEq : detectLoadUseStall p.idEx p.ifId = stall
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · cases squash <;> cases stall <;> cases hIf : p.ifId.valid <;> simp
  · cases hEx : p.idEx.valid <;> simp
  · cases squash <;> cases stall <;> cases hIf : p.ifId.valid
    · simp
    · cases hEx : p.idEx.valid
      · simp
      · simp only [Bool.false_or, Bool.not_true, Bool.false_eq_true, ↓reduceIte, forall_const]
        intro hLoad hNz
        unfold detectLoadUseStall at hStEq
        simp only [hEx, hIf, hLoad, hNz, Bool.true_and, Bool.or_eq_false_iff,
          beq_eq_false_iff_ne, ne_eq] at hStEq
        exact hStEq
    all_goals simp
  · cases squash
    · cases stall
      · cases fetchEn <;> simp
      · simp only [Bool.false_eq_true, ↓reduceIte]; exact hWf.ifId_pc_seq
    · simp
  · cases squash
    · cases stall
      · cases fetchEn
        · cases hIf : p.ifId.valid
          · simp
          · simp only [Bool.false_or, Bool.not_true, Bool.false_eq_true, ↓reduceIte, ifId_bubble_valid]
            intro _ _; exact hWf.ifId_pc_seq hIf
        · simp
      · simp
    · simp

theorem stepPipeline_preserves_wf (imem : InstrMem) (p : PipeState) (hWf : PipeWf p) :
    PipeWf (stepPipeline imem p) := stepCore_preserves_wf true imem p hWf

theorem stepFlush_preserves_wf (p : PipeState) (hWf : PipeWf p) :
    PipeWf (stepFlush p) := stepCore_preserves_wf false (fun _ => .NOP) p hWf

/-- Five `stepFlush` edges unconditionally empty all four pipeline latches (`IF/ID`, `ID/EX`, `EX/MEM`, `MEM/WB`). -/
theorem stepFlushN_5_all_bubbles (p : PipeState) :
    let q := stepFlushN 5 p
    q.ifId.valid = false ∧ q.idEx.valid = false ∧
    q.exMem.valid = false ∧ q.memWb.valid = false := by
  have hStep : ∀ s : PipeState, (s.ifId.valid = false ∨ s.idEx.valid = false) →
      (stepFlush s).ifId.valid = false ∧
      (stepFlush s).idEx.valid =
        (!branchTakenFlush s.idEx.valid s.idEx.instr
          (forwardOperand s.idEx.rs1 s.idEx.v1 s.exMem s.memWb)
          (forwardOperand s.idEx.rs2 s.idEx.v2 s.exMem s.memWb) && s.ifId.valid) ∧
      (stepFlush s).exMem.valid = s.idEx.valid ∧
      (stepFlush s).memWb.valid = s.exMem.valid := fun s hDisj => by
    have hNs : detectLoadUseStall s.idEx s.ifId = false := by
      unfold detectLoadUseStall
      rcases hDisj with hIf | hEx
      · simp [hIf]
      · simp [hEx]
    dsimp only [stepFlush, stepCore, memStepWb]; rw [hNs]
    generalize branchTakenFlush s.idEx.valid s.idEx.instr _ _ = sq
    cases sq <;> cases hIf : s.ifId.valid <;> cases hEx : s.idEx.valid <;> cases hEm : s.exMem.valid <;> simp
  have h1 : (stepFlush p).ifId.valid = false ∨ (stepFlush p).idEx.valid = false := by
    dsimp only [stepFlush, stepCore]
    generalize branchTakenFlush p.idEx.valid p.idEx.instr _ _ = sq
    generalize detectLoadUseStall p.idEx p.ifId = st
    cases sq <;> cases st <;> simp
  have s2 := hStep (stepFlush p) h1
  have s3 := hStep _ (Or.inl s2.1)
  have h3Ex : (stepFlush (stepFlush (stepFlush p))).idEx.valid = false := by
    rw [s3.2.1, s2.1, Bool.and_false]
  have s4 := hStep _ (Or.inl s3.1)
  have h4Ex : (stepFlush (stepFlush (stepFlush (stepFlush p)))).idEx.valid = false := by
    rw [s4.2.1, s3.1, Bool.and_false]
  have h4Em : (stepFlush (stepFlush (stepFlush (stepFlush p)))).exMem.valid = false := s4.2.2.1.trans h3Ex
  have s5 := hStep _ (Or.inl s4.1)
  have h5Ex : (stepFlushN 5 p).idEx.valid = false := by
    change (stepFlush _).idEx.valid = false; rw [s5.2.1, s4.1, Bool.and_false]
  exact ⟨s5.1, h5Ex, s5.2.2.1.trans h4Ex, s5.2.2.2.trans h4Em⟩

private theorem idEx_forwarded_eq_regs2 (p : PipeState) (hWf : PipeWf p) (hEx : p.idEx.valid = true) :
    forwardOperand p.idEx.rs1 p.idEx.v1 p.exMem p.memWb =
      (applyWb (applyWb p.regs p.memWb) (memStepWb p.dmem p.exMem)).read (instrRs1 p.idEx.instr) ∧
    forwardOperand p.idEx.rs2 p.idEx.v2 p.exMem p.memWb =
      (applyWb (applyWb p.regs p.memWb) (memStepWb p.dmem p.exMem)).read (instrRs2 p.idEx.instr) := by
  obtain ⟨hRs1, hRs2, hV1, hV2⟩ := hWf.idEx_decode hEx
  have hNoLd := hWf.no_load_use_in_ex hEx
  exact ⟨by rw [hV1, hRs1]; exact forwardOperand_eq_drained_reg _ _ _ _ _ (fun hEm hLd hNz => hRs1 ▸ (hNoLd hEm hLd hNz).1),
         by rw [hV2, hRs2]; exact forwardOperand_eq_drained_reg _ _ _ _ _ (fun hEm hLd hNz => hRs2 ▸ (hNoLd hEm hLd hNz).2)⟩

private theorem exMem_from_idEx_agrees
    (pc : BitVec 64) (instr : IsaInstr) (regs2 : RegFile) (dmem2 : DataMem) :
    applyExMemMem dmem2
      { valid := true, pc := pc, instr := instr, rd := instrRd instr,
        regWrite := instrWritesReg instr, isLoad := instrIsLoad instr,
        isStore := instrIsStore instr,
        aluVal := exAluResult pc instr (regs2.read (instrRs1 instr)) (regs2.read (instrRs2 instr)),
        storeVal := regs2.read (instrRs2 instr) } =
      (execInstr instr { pc := pc, regs := regs2, dmem := dmem2 }).dmem ∧
    applyWb regs2 (memStepWb dmem2
      { valid := true, pc := pc, instr := instr, rd := instrRd instr,
        regWrite := instrWritesReg instr, isLoad := instrIsLoad instr,
        isStore := instrIsStore instr,
        aluVal := exAluResult pc instr (regs2.read (instrRs1 instr)) (regs2.read (instrRs2 instr)),
        storeVal := regs2.read (instrRs2 instr) }) =
      (execInstr instr { pc := pc, regs := regs2, dmem := dmem2 }).regs := by
  simp [applyExMemMem, applyWb, memStepWb, execInstr]

private theorem idEx_step_bundle (p : PipeState) (hWf : PipeWf p) (hEx : p.idEx.valid = true)
    (squash : Bool)
    (hSq : branchTakenFlush p.idEx.valid p.idEx.instr
      (forwardOperand p.idEx.rs1 p.idEx.v1 p.exMem p.memWb)
      (forwardOperand p.idEx.rs2 p.idEx.v2 p.exMem p.memWb) = squash) :
    let regs2 := applyWb (applyWb p.regs p.memWb) (memStepWb p.dmem p.exMem)
    let dmem2 := applyExMemMem p.dmem p.exMem
    forwardOperand p.idEx.rs1 p.idEx.v1 p.exMem p.memWb = regs2.read (instrRs1 p.idEx.instr) ∧
    forwardOperand p.idEx.rs2 p.idEx.v2 p.exMem p.memWb = regs2.read (instrRs2 p.idEx.instr) ∧
    evalBranchCond p.idEx.instr (regs2.read (instrRs1 p.idEx.instr)) (regs2.read (instrRs2 p.idEx.instr)) = squash ∧
    applyExMemMem dmem2
      { valid := true, pc := p.idEx.pc, instr := p.idEx.instr, rd := instrRd p.idEx.instr,
        regWrite := instrWritesReg p.idEx.instr, isLoad := instrIsLoad p.idEx.instr,
        isStore := instrIsStore p.idEx.instr,
        aluVal := exAluResult p.idEx.pc p.idEx.instr (regs2.read (instrRs1 p.idEx.instr)) (regs2.read (instrRs2 p.idEx.instr)),
        storeVal := regs2.read (instrRs2 p.idEx.instr) } =
      (execInstr p.idEx.instr { pc := p.idEx.pc, regs := regs2, dmem := dmem2 }).dmem ∧
    applyWb regs2 (memStepWb dmem2
      { valid := true, pc := p.idEx.pc, instr := p.idEx.instr, rd := instrRd p.idEx.instr,
        regWrite := instrWritesReg p.idEx.instr, isLoad := instrIsLoad p.idEx.instr,
        isStore := instrIsStore p.idEx.instr,
        aluVal := exAluResult p.idEx.pc p.idEx.instr (regs2.read (instrRs1 p.idEx.instr)) (regs2.read (instrRs2 p.idEx.instr)),
        storeVal := regs2.read (instrRs2 p.idEx.instr) }) =
      (execInstr p.idEx.instr { pc := p.idEx.pc, regs := regs2, dmem := dmem2 }).regs := by
  obtain ⟨hFwd1, hFwd2⟩ := idEx_forwarded_eq_regs2 p hWf hEx
  have hBr2 : evalBranchCond p.idEx.instr
      ((applyWb (applyWb p.regs p.memWb) (memStepWb p.dmem p.exMem)).read (instrRs1 p.idEx.instr))
      ((applyWb (applyWb p.regs p.memWb) (memStepWb p.dmem p.exMem)).read (instrRs2 p.idEx.instr)) = squash := by
    rw [← hFwd1, ← hFwd2]; simpa [branchTakenFlush, hEx] using hSq
  obtain ⟨hMemEq, hRegEq⟩ := exMem_from_idEx_agrees p.idEx.pc p.idEx.instr
    (applyWb (applyWb p.regs p.memWb) (memStepWb p.dmem p.exMem))
    (applyExMemMem p.dmem p.exMem)
  exact ⟨hFwd1, hFwd2, hBr2, hMemEq, hRegEq⟩

/-- Key invariance lemma: one `stepFlush` drain step leaves `drainStages` strictly unchanged! -/
theorem drainStages_stepFlush (p : PipeState) (hWf : PipeWf p) :
    drainStages (stepFlush p) = drainStages p := by
  dsimp only [stepFlush, stepCore, drainStages]
  generalize hSq : branchTakenFlush p.idEx.valid p.idEx.instr
    (forwardOperand p.idEx.rs1 p.idEx.v1 p.exMem p.memWb)
    (forwardOperand p.idEx.rs2 p.idEx.v2 p.exMem p.memWb) = squash
  generalize hSt : detectLoadUseStall p.idEx p.ifId = stall
  cases squash
  · cases stall
    · cases hExV : p.idEx.valid
      · cases hIfV : p.ifId.valid <;> simp
      · obtain ⟨hFwd1, hFwd2, hBr2, hMemEq, hRegEq⟩ := idEx_step_bundle p hWf hExV false hSq
        cases hIfV : p.ifId.valid
        · have hPcSeq := hWf.idEx_pc_seq_when_ifId_empty hExV hIfV
          simp only [Bool.false_or, Bool.not_false, Bool.false_eq_true, ↓reduceIte,
            ifId_bubble_valid, idEx_bubble_valid, hFwd1, hFwd2, hBr2]
          rw [hMemEq, hRegEq, hPcSeq]; simp [execInstr, hBr2]
        · simp only [Bool.false_or, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
            ifId_bubble_valid, hFwd1, hFwd2, hBr2]
          rw [hMemEq, hRegEq]; simp only [ite_self]
    · have hExV : p.idEx.valid = true := by
        unfold detectLoadUseStall at hSt; cases h : p.idEx.valid <;> simp [h] at hSt; rfl
      have hIfV : p.ifId.valid = true := by
        unfold detectLoadUseStall at hSt; cases h : p.ifId.valid <;> simp [h] at hSt; rfl
      obtain ⟨hFwd1, hFwd2, hBr2, hMemEq, hRegEq⟩ := idEx_step_bundle p hWf hExV false hSq
      simp only [hExV, hIfV, Bool.false_or, Bool.true_or, ↓reduceIte, idEx_bubble_valid,
        Bool.false_eq_true, hFwd1, hFwd2, hBr2]
      rw [hMemEq, hRegEq]
  · have hExV := (branchTaken_not_load _ _ _ _ hSq).1
    obtain ⟨hFwd1, hFwd2, hBr2, hMemEq, hRegEq⟩ := idEx_step_bundle p hWf hExV true hSq
    simp only [hExV, Bool.true_or, ↓reduceIte, ifId_bubble_valid, idEx_bubble_valid,
      Bool.false_eq_true, hFwd1, hFwd2, hBr2]
    rw [hMemEq, hRegEq]; simp [execInstr, hBr2]

/-- Operational 5-cycle hardware drain `flushPipeline` equals closed-form `drainStages` on every `PipeWf` state! -/
theorem flushPipeline_eq_drainStages (p : PipeState) (hWf : PipeWf p) :
    flushPipeline p = drainStages p := by
  have hWf1 := stepFlush_preserves_wf p hWf
  have hWf2 := stepFlush_preserves_wf _ hWf1
  have hWf3 := stepFlush_preserves_wf _ hWf2
  have hWf4 := stepFlush_preserves_wf _ hWf3
  have hEq : drainStages (stepFlushN 5 p) = drainStages p := by
    simp only [stepFlushN]
    rw [drainStages_stepFlush _ hWf4, drainStages_stepFlush _ hWf3,
        drainStages_stepFlush _ hWf2, drainStages_stepFlush _ hWf1, drainStages_stepFlush _ hWf]
  rw [← hEq]
  obtain ⟨hB1, hB2, hB3, hB4⟩ := stepFlushN_5_all_bubbles p
  unfold flushPipeline extractIsa drainStages
  simp [hB1, hB2, hB3, hB4, applyWb, applyExMemMem, memStepWb]

theorem flushPipeline_initPipeState (s : IsaState) : flushPipeline (initPipeState s) = s := by
  rw [flushPipeline_eq_drainStages _ (initPipeState_wf s)]
  simp only [initPipeState, drainStages, ifId_bubble_valid, idEx_bubble_valid, Bool.false_eq_true,
    ↓reduceIte, applyWb_bubble, applyExMemMem_bubble, memStepWb_bubble]

/-- Explicit computable Burch–Dill step count (`0` on squash/stall/wrong-path fetch, `1` on retire-bound fetch). -/
def burchDillStepCount (p : PipeState) : Nat :=
  let regs1 := applyWb p.regs p.memWb
  let dmem2 := applyExMemMem p.dmem p.exMem
  let regs2 := applyWb regs1 (memStepWb p.dmem p.exMem)
  let fwd1  := forwardOperand p.idEx.rs1 p.idEx.v1 p.exMem p.memWb
  let fwd2  := forwardOperand p.idEx.rs2 p.idEx.v2 p.exMem p.memWb
  if branchTakenFlush p.idEx.valid p.idEx.instr fwd1 fwd2 then 0
  else if detectLoadUseStall p.idEx p.ifId then 0
  else if p.ifId.valid then
    let regs3 :=
      if p.idEx.valid then (execInstr p.idEx.instr { pc := p.idEx.pc, regs := regs2, dmem := dmem2 }).regs
      else regs2
    if evalBranchCond p.ifId.instr (regs3.read (instrRs1 p.ifId.instr)) (regs3.read (instrRs2 p.ifId.instr)) then 0
    else 1
  else 1

theorem burchDillStepCount_zero_or_one (p : PipeState) :
    burchDillStepCount p = 0 ∨ burchDillStepCount p = 1 := by
  dsimp only [burchDillStepCount]
  repeat (first | exact Or.inl rfl | exact Or.inr rfl | split)

/-- Exact functional Burch–Dill commutation law with explicit `burchDillStepCount p ∈ {0, 1}`. -/
theorem burchDill_step_eq (imem : InstrMem) (p : PipeState) (hWf : PipeWf p) :
    flushPipeline (stepPipeline imem p) =
      stepIsaN imem (burchDillStepCount p) (flushPipeline p) := by
  rw [flushPipeline_eq_drainStages (stepPipeline imem p) (stepPipeline_preserves_wf imem p hWf),
      flushPipeline_eq_drainStages p hWf]
  dsimp only [stepPipeline, stepCore, burchDillStepCount, drainStages]
  generalize hSq : branchTakenFlush p.idEx.valid p.idEx.instr
    (forwardOperand p.idEx.rs1 p.idEx.v1 p.exMem p.memWb)
    (forwardOperand p.idEx.rs2 p.idEx.v2 p.exMem p.memWb) = squash
  generalize hSt : detectLoadUseStall p.idEx p.ifId = stall
  cases squash
  · cases stall
    · cases hExV : p.idEx.valid
      · cases hIfV : p.ifId.valid
        · simp [stepIsaN, stepIsa]
        · have hPcSeq := hWf.ifId_pc_seq hIfV
          simp only [Bool.false_or, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
            applyExMemMem_bubble, memStepWb_bubble, applyWb_bubble]
          by_cases hIfBr : evalBranchCond p.ifId.instr
              ((applyWb (applyWb p.regs p.memWb) (memStepWb p.dmem p.exMem)).read (instrRs1 p.ifId.instr))
              ((applyWb (applyWb p.regs p.memWb) (memStepWb p.dmem p.exMem)).read (instrRs2 p.ifId.instr)) = true
          · simp [hIfBr, stepIsaN]
          · simp only [Bool.not_eq_true] at hIfBr
            simp only [hIfBr, Bool.false_eq_true, ↓reduceIte, stepIsaN, stepIsa]
            have hPc : (execInstr p.ifId.instr
                { pc := p.ifId.pc
                  regs := applyWb (applyWb p.regs p.memWb) (memStepWb p.dmem p.exMem)
                  dmem := applyExMemMem p.dmem p.exMem }).pc = p.fetchPc := by
              simp [execInstr, hIfBr, hPcSeq]
            rw [hPc, isaState_eta_pc _ _ hPc]
      · obtain ⟨hFwd1, hFwd2, hBr2, hMemEq, hRegEq⟩ := idEx_step_bundle p hWf hExV false hSq
        cases hIfV : p.ifId.valid
        · have hPcSeq := hWf.idEx_pc_seq_when_ifId_empty hExV hIfV
          simp only [Bool.false_or, Bool.not_false, Bool.false_eq_true, ↓reduceIte,
            idEx_bubble_valid, hFwd1, hFwd2, hBr2, stepIsaN, stepIsa]
          rw [hMemEq, hRegEq]
          have hPc : (execInstr p.idEx.instr
              { pc := p.idEx.pc
                regs := applyWb (applyWb p.regs p.memWb) (memStepWb p.dmem p.exMem)
                dmem := applyExMemMem p.dmem p.exMem }).pc = p.fetchPc := by
            simp [execInstr, hBr2, hPcSeq]
          rw [hPc, isaState_eta_pc _ _ hPc]
        · have hPcSeq := hWf.ifId_pc_seq hIfV
          simp only [Bool.false_or, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hFwd1, hFwd2, hBr2]
          rw [hMemEq, hRegEq]
          let sEx := execInstr p.idEx.instr
            { pc := p.idEx.pc
              regs := applyWb (applyWb p.regs p.memWb) (memStepWb p.dmem p.exMem)
              dmem := applyExMemMem p.dmem p.exMem }
          by_cases hIfBr : evalBranchCond p.ifId.instr
              (sEx.regs.read (instrRs1 p.ifId.instr)) (sEx.regs.read (instrRs2 p.ifId.instr)) = true
          · simp [sEx, hIfBr, stepIsaN]
          · simp only [Bool.not_eq_true] at hIfBr
            simp only [sEx, hIfBr, Bool.false_eq_true, ↓reduceIte, stepIsaN]
            unfold stepIsa
            have hPc : (execInstr p.ifId.instr { pc := p.ifId.pc, regs := sEx.regs, dmem := sEx.dmem }).pc =
                p.fetchPc := by simp [execInstr, hIfBr, hPcSeq]
            rw [hPc, isaState_eta_pc _ _ hPc]
    · have hExV : p.idEx.valid = true := by
        unfold detectLoadUseStall at hSt; cases h : p.idEx.valid <;> simp [h] at hSt; rfl
      have hIfV : p.ifId.valid = true := by
        unfold detectLoadUseStall at hSt; cases h : p.ifId.valid <;> simp [h] at hSt; rfl
      obtain ⟨hFwd1, hFwd2, hBr2, hMemEq, hRegEq⟩ := idEx_step_bundle p hWf hExV false hSq
      simp only [hExV, hIfV, Bool.false_or, Bool.true_or, ↓reduceIte, idEx_bubble_valid,
        Bool.false_eq_true, hFwd1, hFwd2, hBr2, stepIsaN]
      rw [hMemEq, hRegEq]
  · have hExV := (branchTaken_not_load _ _ _ _ hSq).1
    obtain ⟨hFwd1, hFwd2, hBr2, hMemEq, hRegEq⟩ := idEx_step_bundle p hWf hExV true hSq
    simp only [hExV, Bool.true_or, ↓reduceIte, ifId_bubble_valid, idEx_bubble_valid,
      Bool.false_eq_true, hFwd1, hFwd2, hBr2, stepIsaN]
    rw [hMemEq, hRegEq]; simp [execInstr, hBr2]

/-- **Burch–Dill Pipeline Flushing Commutator Theorem (`burchDill_step_commutes`).**
    For every well-formed 5-stage pipeline state `p`, advancing one clock cycle `stepPipeline imem p`
    followed by draining in-flight stages via `flushPipeline` equals executing `k ∈ {0, 1}`
    architectural `stepIsa imem` steps from `flushPipeline p`. -/
theorem burchDill_step_commutes (imem : InstrMem) (p : PipeState) (hWf : PipeWf p) :
    ∃ k, (k = 0 ∨ k = 1) ∧
      flushPipeline (stepPipeline imem p) = stepIsaN imem k (flushPipeline p) :=
  ⟨burchDillStepCount p, burchDillStepCount_zero_or_one p, burchDill_step_eq imem p hWf⟩

/-- Multi-cycle architectural step accumulator along an `n`-cycle hardware run. -/
def burchDillStepsN (imem : InstrMem) : Nat → PipeState → Nat
  | 0, _     => 0
  | n + 1, p => burchDillStepCount p + burchDillStepsN imem n (stepPipeline imem p)

theorem burchDillStepsN_le (imem : InstrMem) : ∀ (n : Nat) (p : PipeState),
    burchDillStepsN imem n p ≤ n
  | 0, _ => Nat.le_refl 0
  | n + 1, p => by
    unfold burchDillStepsN
    rcases burchDillStepCount_zero_or_one p with h0 | h1
    · have := burchDillStepsN_le imem n (stepPipeline imem p); omega
    · have := burchDillStepsN_le imem n (stepPipeline imem p); omega

theorem burchDill_multiCycle_eq (imem : InstrMem) (n : Nat) (p : PipeState) (hWf : PipeWf p) :
    PipeWf (stepPipelineN imem n p) ∧
    flushPipeline (stepPipelineN imem n p) = stepIsaN imem (burchDillStepsN imem n p) (flushPipeline p) := by
  induction n generalizing p with
  | zero => exact ⟨hWf, by simp [stepPipelineN, burchDillStepsN, stepIsaN]⟩
  | succ n ih =>
    obtain ⟨hWfN, hEqN⟩ := ih (stepPipeline imem p) (stepPipeline_preserves_wf imem p hWf)
    refine ⟨hWfN, ?_⟩; simp only [stepPipelineN, burchDillStepsN]
    rw [hEqN, stepIsaN_add, burchDill_step_eq imem p hWf]

/-- **Multi-Cycle Burch–Dill Refinement Theorem (`pipelinedRisc_multiCycle_refines_isa`).**
    Across arbitrary `n`-cycle executions (spanning RAW bypass chains, load-use stalls, taken branch
    loops, and memory loads/stores), `PipeWf` is maintained and draining the pipeline equals `k ≤ n`
    architectural `stepIsa` steps! -/
theorem pipelinedRisc_multiCycle_refines_isa
    (imem : InstrMem) (n : Nat) (p : PipeState) (hWf : PipeWf p) :
    ∃ k, k ≤ n ∧
      PipeWf (stepPipelineN imem n p) ∧
      flushPipeline (stepPipelineN imem n p) = stepIsaN imem k (flushPipeline p) :=
  ⟨burchDillStepsN imem n p, burchDillStepsN_le imem n p, burchDill_multiCycle_eq imem n p hWf⟩

/-- End-to-end architectural equivalence from reset/initialized pipeline state `initPipeState s`. -/
theorem pipelinedRisc_run_and_drain_eq_stepIsaN (imem : InstrMem) (n : Nat) (s : IsaState) :
    flushPipeline (stepPipelineN imem n (initPipeState s)) =
      stepIsaN imem (burchDillStepsN imem n (initPipeState s)) s := by
  rw [(burchDill_multiCycle_eq imem n (initPipeState s) (initPipeState_wf s)).2,
      flushPipeline_initPipeState]

/-! ## 5. Bounded Liveness & No-Starvation Theorems (`≤ 3` Cycles per Retirement) -/

/-- **EX Commit Bounded Liveness (`≤ 3` Cycles):** In EVERY 3-cycle window, at least one cycle holds
    a valid instruction in `ID/EX` (the pipeline never injects 3 consecutive bubbles into `EX`). -/
theorem pipelinedRisc_ex_valid_within_3_cycles (imem : InstrMem) (p : PipeState) :
    p.idEx.valid = true ∨
    (stepPipeline imem p).idEx.valid = true ∨
    (stepPipelineN imem 2 p).idEx.valid = true := by
  cases hEx0 : p.idEx.valid
  · right
    have hNoSq0 : branchTakenFlush p.idEx.valid p.idEx.instr
        (forwardOperand p.idEx.rs1 p.idEx.v1 p.exMem p.memWb)
        (forwardOperand p.idEx.rs2 p.idEx.v2 p.exMem p.memWb) = false := by
      simp [branchTakenFlush, hEx0]
    have hNoSt0 : detectLoadUseStall p.idEx p.ifId = false := by simp [detectLoadUseStall, hEx0]
    cases hIf0 : p.ifId.valid
    · right
      have hP1 : (stepPipeline imem p).idEx.valid = false ∧ (stepPipeline imem p).ifId.valid = true := by
        unfold stepPipeline stepCore; simp [hNoSq0, hNoSt0, hIf0]
      let p1 := stepPipeline imem p
      have hNoSq1 : branchTakenFlush p1.idEx.valid p1.idEx.instr
          (forwardOperand p1.idEx.rs1 p1.idEx.v1 p1.exMem p1.memWb)
          (forwardOperand p1.idEx.rs2 p1.idEx.v2 p1.exMem p1.memWb) = false := by
        simp [branchTakenFlush, p1, hP1.1]
      have hNoSt1 : detectLoadUseStall p1.idEx p1.ifId = false := by simp [detectLoadUseStall, p1, hP1.1]
      change (stepPipeline imem p1).idEx.valid = true
      unfold stepPipeline stepCore; simp [hNoSq1, hNoSt1, p1, hP1.2]
    · left; unfold stepPipeline stepCore; simp [hNoSq0, hNoSt0, hIf0]
  · left; rfl

theorem wb_valid_after_2_cycles_eq_idEx_valid (imem : InstrMem) (p : PipeState) :
    (stepPipelineN imem 2 p).memWb.valid = p.idEx.valid := by
  have h1 : (stepPipeline imem p).exMem.valid = p.idEx.valid := by
    dsimp only [stepPipeline, stepCore]; cases h : p.idEx.valid <;> rfl
  have h2 : ∀ q : PipeState, (stepPipeline imem q).memWb.valid = q.exMem.valid := by
    intro q; dsimp only [stepPipeline, stepCore, memStepWb]; cases h : q.exMem.valid <;> rfl
  simp only [stepPipelineN]; rw [h2, h1]

theorem retiredCount_step (imem : InstrMem) (p : PipeState) :
    (stepPipeline imem p).retiredCount =
      if p.memWb.valid then p.retiredCount + 1 else p.retiredCount := by rfl

/-- **Bounded Retirement Liveness (`≤ 3` Cycles, Zero Starvation):**
    After the 2-cycle pipeline fill (`q := stepPipelineN imem 2 p`), **at least 1 architectural
    instruction retires in `WB` every `≤ 3` clock cycles** (`retiredCount` strictly increases). -/
theorem pipelinedRisc_retires_every_3_cycles (imem : InstrMem) (p : PipeState) :
    let q := stepPipelineN imem 2 p
    q.retiredCount + 1 ≤ (stepPipelineN imem 3 q).retiredCount := by
  intro q
  have hEx := pipelinedRisc_ex_valid_within_3_cycles imem p
  have hWb0 : q.memWb.valid = p.idEx.valid := wb_valid_after_2_cycles_eq_idEx_valid imem p
  have hWb1 : (stepPipeline imem q).memWb.valid = (stepPipeline imem p).idEx.valid := by
    simpa [q, stepPipelineN] using wb_valid_after_2_cycles_eq_idEx_valid imem (stepPipeline imem p)
  have hWb2 : (stepPipeline imem (stepPipeline imem q)).memWb.valid = (stepPipelineN imem 2 p).idEx.valid := by
    simpa [q, stepPipelineN] using wb_valid_after_2_cycles_eq_idEx_valid imem (stepPipelineN imem 2 p)
  change q.retiredCount + 1 ≤ (stepPipeline imem (stepPipeline imem (stepPipeline imem q))).retiredCount
  rw [retiredCount_step, retiredCount_step, retiredCount_step, hWb0, hWb1, hWb2]
  rcases hEx with h0 | h1 | h2'
  · simp only [h0, ↓reduceIte]; split <;> (try split) <;> omega
  · simp only [h1, ↓reduceIte]; split <;> (try split) <;> omega
  · simp only [h2', ↓reduceIte]; split <;> (try split) <;> omega

/-- **Burch–Dill Front-End Progress Liveness:** From any non-stalling `PipeWf` state, `burchDillStepsN`
    advances by `≥ 1` architectural `stepIsa` step within `≤ 3` cycles, and from **every** `PipeWf`
    state (including a load-use stall directly into a taken branch) within `≤ 4` cycles! -/
theorem burchDill_no_starvation_progress (imem : InstrMem) (p : PipeState) (hWf : PipeWf p) :
    (detectLoadUseStall p.idEx p.ifId = false → 1 ≤ burchDillStepsN imem 3 p) ∧
    1 ≤ burchDillStepsN imem 4 p := by
  have hNonStall3 : ∀ q : PipeState, PipeWf q → detectLoadUseStall q.idEx q.ifId = false →
      1 ≤ burchDillStepsN imem 3 q := by
    intro q hWfQ hNoSt
    by_cases hC0 : burchDillStepCount q = 1
    · simp only [burchDillStepsN, hC0]; omega
    · have hZ0 : burchDillStepCount q = 0 := by
        rcases burchDillStepCount_zero_or_one q with h | h
        · exact h
        · exact False.elim (hC0 h)
      dsimp only [burchDillStepCount] at hZ0
      by_cases hSq0 : branchTakenFlush q.idEx.valid q.idEx.instr
          (forwardOperand q.idEx.rs1 q.idEx.v1 q.exMem q.memWb)
          (forwardOperand q.idEx.rs2 q.idEx.v2 q.exMem q.memWb) = true
      · have hQ1 : (stepPipeline imem q).idEx.valid = false ∧ (stepPipeline imem q).ifId.valid = false := by
          dsimp only [stepPipeline, stepCore]; simp [hSq0]
        have hC1 : burchDillStepCount (stepPipeline imem q) = 1 := by
          dsimp only [burchDillStepCount]; simp [hQ1.1, hQ1.2, branchTakenFlush, detectLoadUseStall]
        simp only [burchDillStepsN, hC1]; omega
      · simp only [Bool.not_eq_true] at hSq0
        simp only [hSq0, hNoSt, Bool.false_eq_true, ↓reduceIte] at hZ0
        cases hIfV : q.ifId.valid
        · simp [hIfV] at hZ0
        · simp only [hIfV, ↓reduceIte] at hZ0
          let regs2Q := applyWb (applyWb q.regs q.memWb) (memStepWb q.dmem q.exMem)
          let dmem2Q := applyExMemMem q.dmem q.exMem
          let regs3Q := if q.idEx.valid then
              (execInstr q.idEx.instr { pc := q.idEx.pc, regs := regs2Q, dmem := dmem2Q }).regs
            else regs2Q
          have hIfCond : evalBranchCond q.ifId.instr
              (regs3Q.read (instrRs1 q.ifId.instr)) (regs3Q.read (instrRs2 q.ifId.instr)) = true := by
            change (if evalBranchCond q.ifId.instr (regs3Q.read _) (regs3Q.read _) = true then 0 else 1) = 0 at hZ0
            generalize evalBranchCond q.ifId.instr _ _ = bc at hZ0 ⊢
            cases bc <;> simp at hZ0 ⊢
          let q1 := stepPipeline imem q
          have hWf1 := stepPipeline_preserves_wf imem q hWfQ
          have hQ1ExV : q1.idEx.valid = true ∧ q1.idEx.instr = q.ifId.instr := by
            dsimp only [q1, stepPipeline, stepCore]; simp [hSq0, hNoSt, hIfV]
          obtain ⟨hQ1Fwd1, hQ1Fwd2⟩ := idEx_forwarded_eq_regs2 q1 hWf1 hQ1ExV.1
          have hQ1Regs2 : applyWb (applyWb q1.regs q1.memWb) (memStepWb q1.dmem q1.exMem) = regs3Q := by
            cases hExV : q.idEx.valid
            · dsimp only [q1, regs3Q, regs2Q, stepPipeline, stepCore]; simp [hExV]
            · obtain ⟨hF1, hF2, _, _, hRegEq⟩ := idEx_step_bundle q hWfQ hExV false hSq0
              dsimp only [q1, regs3Q, regs2Q, dmem2Q, stepPipeline, stepCore]
              simp only [hExV, ↓reduceIte, hF1, hF2]; exact hRegEq
          have hQ1Sq : branchTakenFlush q1.idEx.valid q1.idEx.instr
              (forwardOperand q1.idEx.rs1 q1.idEx.v1 q1.exMem q1.memWb)
              (forwardOperand q1.idEx.rs2 q1.idEx.v2 q1.exMem q1.memWb) = true := by
            simp only [branchTakenFlush, hQ1ExV.1, hQ1ExV.2, Bool.true_and, hQ1Fwd1, hQ1Fwd2, hQ1Regs2]
            exact hIfCond
          let q2 := stepPipeline imem q1
          have hQ2Empty : q2.idEx.valid = false ∧ q2.ifId.valid = false := by
            dsimp only [q2, stepPipeline, stepCore]; simp [hQ1Sq]
          have hC2 : burchDillStepCount q2 = 1 := by
            dsimp only [burchDillStepCount]; simp [hQ2Empty.1, hQ2Empty.2, branchTakenFlush, detectLoadUseStall]
          change 1 ≤ burchDillStepCount q + (burchDillStepCount q1 + (burchDillStepCount q2 + 0))
          omega
  refine ⟨hNonStall3 p hWf, ?_⟩
  by_cases hSt0 : detectLoadUseStall p.idEx p.ifId = false
  · have h3 := hNonStall3 p hWf hSt0
    have hMono : ∀ (m : Nat) (r : PipeState), burchDillStepsN imem m r ≤ burchDillStepsN imem (m + 1) r := by
      intro m; induction m with
      | zero => intro r; simp [burchDillStepsN]
      | succ m ih => intro r; exact Nat.add_le_add_left (ih (stepPipeline imem r)) (burchDillStepCount r)
    exact Nat.le_trans h3 (hMono 3 p)
  · simp only [Bool.not_eq_false] at hSt0
    have hSq0 : branchTakenFlush p.idEx.valid p.idEx.instr
        (forwardOperand p.idEx.rs1 p.idEx.v1 p.exMem p.memWb)
        (forwardOperand p.idEx.rs2 p.idEx.v2 p.exMem p.memWb) = false := by
      have hLd : instrIsLoad p.idEx.instr = true := by
        unfold detectLoadUseStall at hSt0; cases h : instrIsLoad p.idEx.instr <;> simp [h] at hSt0; rfl
      exact (isLoad_disjoint p.idEx.instr p.idEx.valid _ _ hLd).2.2
    have hP1NoStall : detectLoadUseStall (stepPipeline imem p).idEx (stepPipeline imem p).ifId = false := by
      have hP1Ex : (stepPipeline imem p).idEx.valid = false := by
        dsimp only [stepPipeline, stepCore]; simp [hSq0, hSt0]
      unfold detectLoadUseStall; simp [hP1Ex]
    have h3 := hNonStall3 (stepPipeline imem p) (stepPipeline_preserves_wf imem p hWf) hP1NoStall
    change 1 ≤ burchDillStepCount p + burchDillStepsN imem 3 (stepPipeline imem p); omega

end Obend.Hardware.PipelinedRisc
end
