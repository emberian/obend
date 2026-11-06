/-
# Obend.Hardware.Gpu.Rdna2.Semantics — a wave64 model of the RDNA2 instructions RADV emits for our kernels

The state is one wave's (`WaveState`): the SGPRs, VCC, EXEC and SCC (manual chapter 3: "Kernel State",
3.3 EXEC, 3.8 SCC, 3.9 VCC), M0, the VGPRs per lane (64 lanes: RADV compiles our compute shaders as
wave64, which the dumps show in `s_mov_b64 exec` and the 64-bit masks), a program counter in dwords,
dword-addressed memory, and an error field after LNSym's `ArmState` (github.com/leanprover/LNSym,
`Arm/State.lean`): a model error is a refusal, never a guess, and any execution that set it is invalid.
As in LNSym the state is read and written only through accessors (`readSgpr`, `writeVgpr`, ...), `step`
decodes and executes one instruction, `run` iterates it, and the instruction semantics are pure
functions on words (`addCo`, `mulHi`, ...) about which the universal theorems below are stated. The
stores are arrays rather than LNSym's functions so that the compiled check over a 70,000-instruction
dump runs in seconds; the accessor discipline is what their simp sets need.

Each instruction's semantics follows the pseudo-code of the RDNA 2 Instruction Set Architecture
Reference Guide (AMD, "RDNA 2" ISA, chapter 12, cited per instruction below as "manual 12.x <NAME>"),
and, where the same instruction exists in gem5's executable Vega model
(github.com/gem5/gem5 `src/arch/amdgpu/vega/insts/*.cc`, the twin named per instruction), was
checked against it: `hardware/gpu/rdna2/gem5_vectors.tsv` holds random register states and the outputs
gem5's `execute` bodies give, replayed through `step` by `Obend.Teeth.Hardware.Rdna2Runs`. Instructions
with no Vega twin (V_ADD_NC_U32, V_ADD_CO_CI_U32, V_SUB_CO_CI_U32 under those names; S_CLAUSE) rest on
the manual, and where RDNA2 departs from Vega the departure is named (V_CMPX writes EXEC only, manual
12.9; Vega's also wrote VCC). Encodings and operand codes come from AMD's XML through `Decode`;
operand code tables are manual 5.2 Table 10 and 6.2 Table 20.

What the model does not do, named: it completes every memory access when the instruction executes, so
`S_WAITCNT` and `S_CLAUSE` are no-ops (manual 4.4: the counters order completion; a program that
forgot a wait would read stale registers on the device and fresh ones here; the device run of
`verify_gpu.sh` is what catches that); it runs the waves of a dispatch one after another (sound for
rung G1's programs, whose stages write no word that the stage reads and whose threads own disjoint
words, `Obend.Hardware.Gpu.lowerArrayToGpu_sound`); it refuses, by setting the error, any instruction
outside the subset, any operand code it does not model (trap temporaries, inline floats, DPP, SDWA),
VOP3 input or output modifiers on integer instructions, swizzled or indexed buffers, and any access to
an address the memory does not hold.
-/
module
public import Obend.Hardware.Gpu.Rdna2.Decode
public import Std.Data.HashMap
@[expose] public section

namespace Obend.Hardware.Gpu.Rdna2

/-! ## 1. State -/

/-- Memory as RDNA2's dword-aligned loads and stores see it: dword address (byte address / 4) to dword. -/
abbrev Memory := Std.HashMap UInt64 UInt32

def lanes : Nat := 64
def sgprCount : Nat := 106
def vgprCount : Nat := 256

structure WaveState where
  sgpr : Array UInt32
  vcc : UInt64
  exec : UInt64
  scc : Bool
  m0 : UInt32
  /-- `vgpr[r * 64 + lane]`. -/
  vgpr : Array UInt32
  /-- In dwords from the program's start (manual 3.2: PC is a byte address; every instruction here is
  dword-aligned, so dwords index the program). -/
  pc : Nat
  mem : Memory
  halted : Bool
  err : Option String

def WaveState.init (mem : Memory) : WaveState :=
  { sgpr := Array.replicate sgprCount 0, vcc := 0, exec := 0xFFFFFFFFFFFFFFFF, scc := false, m0 := 0,
    vgpr := Array.replicate (vgprCount * lanes) 0, pc := 0, mem := mem, halted := false, err := none }

def WaveState.fail (s : WaveState) (msg : String) : WaveState :=
  if s.err.isSome then s else { s with err := some s!"pc {s.pc}: {msg}" }

def readSgpr (s : WaveState) (n : Nat) : UInt32 := s.sgpr.getD n 0
def writeSgpr (s : WaveState) (n : Nat) (v : UInt32) : WaveState :=
  if n < sgprCount then { s with sgpr := s.sgpr.set! n v } else s
def readVgpr (s : WaveState) (r lane : Nat) : UInt32 := s.vgpr.getD (r * lanes + lane) 0
def writeVgpr (s : WaveState) (r lane : Nat) (v : UInt32) : WaveState :=
  if r < vgprCount then { s with vgpr := s.vgpr.set! (r * lanes + lane) v } else s
def execBit (s : WaveState) (lane : Nat) : Bool := (s.exec >>> lane.toUInt64) &&& 1 == 1
def readMem32 (s : WaveState) (byteAddr : UInt64) : Option UInt32 := s.mem.get? (byteAddr >>> 2)
def writeMem32 (s : WaveState) (byteAddr : UInt64) (v : UInt32) : WaveState :=
  { s with mem := s.mem.insert (byteAddr >>> 2) v }

theorem readSgpr_writeSgpr_same (s : WaveState) (n : Nat) (v : UInt32) (h : n < sgprCount)
    (hs : s.sgpr.size = sgprCount) : readSgpr (writeSgpr s n v) n = v := by
  simp [readSgpr, writeSgpr, h, Array.getD_eq_getD_getElem?, Array.set!, hs]

theorem readSgpr_writeSgpr_other (s : WaveState) (n m : Nat) (v : UInt32) (hnm : n ≠ m) :
    readSgpr (writeSgpr s n v) m = readSgpr s m := by
  unfold readSgpr writeSgpr
  split <;> simp [Array.getD_eq_getD_getElem?, Array.set!, hnm]

theorem readVgpr_writeVgpr_same (s : WaveState) (r lane : Nat) (v : UInt32) (hr : r < vgprCount)
    (hl : lane < lanes) (hs : s.vgpr.size = vgprCount * lanes) : readVgpr (writeVgpr s r lane v) r lane = v := by
  have : r * lanes + lane < vgprCount * lanes := by
    have : (r + 1) * lanes ≤ vgprCount * lanes := Nat.mul_le_mul_right _ hr
    rw [Nat.add_mul, Nat.one_mul] at this
    omega
  simp [readVgpr, writeVgpr, hr, Array.getD_eq_getD_getElem?, Array.set!, hs, this]

/-! ## 2. Operand codes (manual 5.2 Table 10, 6.2 Table 20) -/

/-- The scalar value an 8/9-bit source code names, at the SALU or as a VALU broadcast: SGPRs, VCC and
EXEC halves, M0, NULL (reads zero), the inline integers 0..64 and -1..-16, VCCZ/EXECZ/SCC, the literal
dword; `none` for codes the model does not carry (trap temporaries, apertures, inline floats, LDS
direct, DPP/SDWA selectors). -/
def scalarSource (s : WaveState) (code : Nat) (lit : Option UInt32) : Option UInt32 :=
  if code ≤ 105 then some (readSgpr s code)
  else if code == 106 then some s.vcc.toUInt32
  else if code == 107 then some (s.vcc >>> 32).toUInt32
  else if code == 124 then some s.m0
  else if code == 125 then some 0
  else if code == 126 then some s.exec.toUInt32
  else if code == 127 then some (s.exec >>> 32).toUInt32
  else if code == 128 then some 0
  else if code ≤ 192 then some (UInt32.ofNat (code - 128))
  else if code ≤ 208 then some (0 - UInt32.ofNat (code - 192))
  else if code == 251 then some (if s.vcc == 0 then 1 else 0)
  else if code == 252 then some (if s.exec == 0 then 1 else 0)
  else if code == 253 then some (if s.scc then 1 else 0)
  else if code == 255 then lit
  else none

/-- A 32-bit VALU source: a VGPR (codes 256..511) per lane, else the scalar broadcast. -/
def vectorSource (s : WaveState) (code : Nat) (lit : Option UInt32) (lane : Nat) : Option UInt32 :=
  if 256 ≤ code && code ≤ 511 then some (readVgpr s (code - 256) lane) else scalarSource s code lit

/-- A 64-bit source: an SGPR pair (even code), VCC, EXEC, NULL, a VGPR pair, or an inline integer
sign-extended to 64 bits (manual 6.2, "Literal Expansion to 64 bits": signed integers sign-extend;
LLVM AMDGPUUsage, integer inline constants in 64-bit operands); a literal is refused (its expansion
depends on the instruction's type and none of ours takes one). -/
def source64 (s : WaveState) (code : Nat) (lane : Nat) : Option UInt64 :=
  if code ≤ 105 then some ((readSgpr s code).toUInt64 ||| ((readSgpr s (code + 1)).toUInt64 <<< 32))
  else if code == 106 then some s.vcc
  else if code == 125 then some 0
  else if code == 126 then some s.exec
  else if code == 128 then some 0
  else if code ≤ 192 then some (UInt64.ofNat (code - 128))
  else if code ≤ 208 then some (0 - UInt64.ofNat (code - 192))
  else if 256 ≤ code && code ≤ 511 then
    some ((readVgpr s (code - 256) lane).toUInt64 ||| ((readVgpr s (code - 255) lane).toUInt64 <<< 32))
  else none

/-- A 64-bit mask source as the VALU's carry-in or CNDMASK selector reads it (manual 6.2.3: a mask in
SGPRs is two consecutive SGPRs, VCC, or EXEC). -/
def maskSource (s : WaveState) (code : Nat) : Option UInt64 :=
  if code ≤ 105 then some ((readSgpr s code).toUInt64 ||| ((readSgpr s (code + 1)).toUInt64 <<< 32))
  else if code == 106 then some s.vcc
  else if code == 125 then some 0
  else if code == 126 then some s.exec
  else none

/-- A scalar destination code (7 bits): SGPR, VCC halves, M0, NULL (discarded), EXEC halves. -/
def writeScalarDst (s : WaveState) (code : Nat) (v : UInt32) : WaveState :=
  if code ≤ 105 then writeSgpr s code v
  else if code == 106 then { s with vcc := (s.vcc &&& (0xFFFFFFFF00000000 : UInt64)) ||| v.toUInt64 }
  else if code == 107 then { s with vcc := (s.vcc &&& (0x00000000FFFFFFFF : UInt64)) ||| (v.toUInt64 <<< 32) }
  else if code == 124 then { s with m0 := v }
  else if code == 125 then s
  else if code == 126 then { s with exec := (s.exec &&& (0xFFFFFFFF00000000 : UInt64)) ||| v.toUInt64 }
  else if code == 127 then { s with exec := (s.exec &&& (0x00000000FFFFFFFF : UInt64)) ||| (v.toUInt64 <<< 32) }
  else s.fail s!"scalar destination code {code} is not modelled"

def writeScalarDst64 (s : WaveState) (code : Nat) (v : UInt64) : WaveState :=
  if code ≤ 105 then writeSgpr (writeSgpr s code v.toUInt32) (code + 1) (v >>> 32).toUInt32
  else if code == 106 then { s with vcc := v }
  else if code == 125 then s
  else if code == 126 then { s with exec := v }
  else s.fail s!"64-bit scalar destination code {code} is not modelled"

/-! ## 3. The arithmetic, as pure functions on words, with the manual's pseudo-code -/

/-- V_ADD_CO_U32 (manual 12.11): `D.u32 = S0.u32 + S1.u32; VCC = S0.u + S1.u >= 0x100000000 ? 1 : 0`. -/
def addCo (a b : UInt32) : UInt32 × Bool := (a + b, decide (2 ^ 32 ≤ a.toNat + b.toNat))

/-- V_ADD_CO_CI_U32 (manual 12.7): `D = S0 + S1 + VCC; VCC = S0 + S1 + VCC >= 0x100000000`. -/
def addCi (a b : UInt32) (ci : Bool) : UInt32 × Bool :=
  (a + b + (if ci then 1 else 0), decide (2 ^ 32 ≤ a.toNat + b.toNat + (if ci then 1 else 0)))

/-- V_SUB_CO_U32 (manual 12.11): `D.u = S0.u - S1.u; VCC = S1.u > S0.u`. -/
def subCo (a b : UInt32) : UInt32 × Bool := (a - b, decide (a.toNat < b.toNat))

/-- V_SUB_CO_CI_U32 (manual 12.7): `D = S0 - S1 - VCC; VCC = S1 + VCC > S0`. -/
def subCi (a b : UInt32) (ci : Bool) : UInt32 × Bool :=
  (a - b - (if ci then 1 else 0), decide (a.toNat < b.toNat + (if ci then 1 else 0)))

/-- V_MUL_LO_U32 (manual 12.11): `D.u = S0.u * S1.u`. -/
def mulLo (a b : UInt32) : UInt32 := a * b

/-- V_MUL_HI_U32 (manual 12.11): `D.u = (S0.u * S1.u) >> 32`. -/
def mulHi (a b : UInt32) : UInt32 := UInt32.ofNat ((a.toNat * b.toNat) >>> 32)

/-- V_LSHLREV_B32 (manual 12.7): `D.u32 = S1.u32 << S0[4:0]`. -/
def lshlrev32 (count val : UInt32) : UInt32 := val <<< (count &&& 31)

/-- V_LSHLREV_B64 / V_LSHRREV_B64 (manual 12.11): `D.u64 = S1.u64 << S0.u[5:0]`, `>>` logical. -/
def lshlrev64 (count : UInt32) (val : UInt64) : UInt64 := val <<< (count.toUInt64 &&& 63)
def lshrrev64 (count : UInt32) (val : UInt64) : UInt64 := val >>> (count.toUInt64 &&& 63)

/-- V_LSHL_ADD_U32 (manual 12.11): `D.u = (S0.u << S1.u[4:0]) + S2.u`. -/
def lshlAdd (a sh c : UInt32) : UInt32 := (a <<< (sh &&& 31)) + c

/-- V_ADD3_U32 (manual 12.11): `D.u = S0.u + S1.u + S2.u`. -/
def add3 (a b c : UInt32) : UInt32 := a + b + c

/-- V_CNDMASK_B32 (manual 12.7): `D.u32 = VCC ? S1.u32 : S0.u32`, VCC's bit for the lane. -/
def cndmask (sel : Bool) (s0 s1 : UInt32) : UInt32 := if sel then s1 else s0

/-- `mulHi` and `mulLo` are the two halves of the 64-bit product: the fact the Goldilocks multiply of
`glmul-256` and the NTTs is built on. -/
theorem mulHi_mulLo (a b : UInt32) : (mulHi a b).toNat * 2 ^ 32 + (mulLo a b).toNat = a.toNat * b.toNat := by
  have hlt : a.toNat * b.toNat < 2 ^ 64 := by
    have := Nat.mul_lt_mul'' a.toNat_lt b.toNat_lt
    simpa using this
  have hdiv : (a.toNat * b.toNat) / 2 ^ 32 < 2 ^ 32 := by
    rw [Nat.div_lt_iff_lt_mul (by decide)]; simpa using hlt
  simp only [mulHi, mulLo, UInt32.toNat_ofNat', UInt32.toNat_mul, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt hdiv, Nat.mul_comm, Nat.div_add_mod]

/-- The carry of `addCo` is exactly the bit the 32-bit sum drops: `a + b` as naturals is the result
plus `2^32` times the carry (how `v_add_co_u32`/`v_add_co_ci_u32` chain a 64-bit add). -/
theorem addCo_spec (a b : UInt32) :
    (addCo a b).1.toNat + (if (addCo a b).2 then 2 ^ 32 else 0) = a.toNat + b.toNat := by
  simp only [addCo, UInt32.toNat_add]
  have ha := a.toNat_lt; have hb := b.toNat_lt
  by_cases h : 2 ^ 32 ≤ a.toNat + b.toNat
  · simp only [h, decide_true, ↓reduceIte]
    rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]; omega
  · simp only [h, decide_false]
    exact Nat.mod_eq_of_lt (by omega)

theorem addCi_spec (a b : UInt32) (ci : Bool) :
    (addCi a b ci).1.toNat + (if (addCi a b ci).2 then 2 ^ 32 else 0) =
      a.toNat + b.toNat + (if ci then 1 else 0) := by
  have ha := a.toNat_lt; have hb := b.toNat_lt
  cases ci
  · simp only [addCi, Bool.false_eq_true, ↓reduceIte, Nat.add_zero, UInt32.add_zero]
    exact addCo_spec a b
  · simp only [addCi, ↓reduceIte, UInt32.toNat_add, UInt32.toNat_one]
    by_cases h : 2 ^ 32 ≤ a.toNat + b.toNat + 1
    · simp only [h, decide_true, ↓reduceIte]
      rcases Nat.lt_or_ge (a.toNat + b.toNat) (2 ^ 32) with hlt | hge
      · rw [Nat.mod_eq_of_lt hlt]
        have : a.toNat + b.toNat + 1 = 2 ^ 32 := by omega
        rw [this, Nat.mod_self]
      · rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
    · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

/-- `subCo` borrows exactly when the subtraction would go below zero. -/
theorem subCo_spec (a b : UInt32) :
    (subCo a b).1.toNat = (if (subCo a b).2 then a.toNat + 2 ^ 32 - b.toNat else a.toNat - b.toNat) := by
  have ha := a.toNat_lt; have hb := b.toNat_lt
  by_cases h : a.toNat < b.toNat
  · simp only [subCo, h, decide_true, ↓reduceIte, UInt32.toNat_sub]
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  · simp only [subCo, h, decide_false]
    exact UInt32.toNat_sub_of_le a b (UInt32.le_iff_toNat_le.mpr (by omega))

/-! ## 4. Executing one instruction -/

def Inst.fam (i : Inst) : String := family i.enc.name

/-- The source codes of a VALU instruction as the encoding carries them: VOP2's and VOPC's `VSRC1` is a
VGPR number, made a 256+ code here so that every family reads through `vectorSource`. -/
def srcCode (i : Inst) (k : Nat) : Nat :=
  match k with
  | 0 => i.field "SRC0"
  | 1 => if i.fam == "VOP3" then i.field "SRC1" else 256 + i.field "VSRC1"
  | _ => i.field "SRC2"

/-- Where a VALU writes its mask (carry-out or compare): VCC in the 32-bit forms, the SGPR pair of
`SDST` (VOP3B) or `VDST` (a compare in VOP3) in the 64-bit form (manual 6.2.2). -/
def maskDst (i : Inst) : Nat :=
  if i.enc.name == "VOP3_SDST_ENC" || i.enc.name == "VOP3_SDST_ENC_INST_LITERAL" then i.field "SDST"
  else if i.fam == "VOP3" then i.field "VDST"
  else 106

/-- The mask a carry-in or CNDMASK reads: VCC in VOP2, `SRC2`'s pair in VOP3. -/
def maskSrcCode (i : Inst) : Nat := if i.fam == "VOP3" then i.field "SRC2" else 106

/-- VOP3 modifiers are floating-point operations' (manual 6.2.1/6.2.2); on the integer subset they are
refused rather than interpreted. -/
def modifiersClear (i : Inst) : Bool :=
  i.fam != "VOP3" || (i.field "NEG" == 0 && i.field "ABS" == 0 && i.field "CLAMP" == 0 && i.field "OMOD" == 0 && i.field "OP_SEL" == 0)

/-- A per-lane 32-bit VALU operation over active lanes (manual 6.2.2: a thread writes only if its EXEC
bit is set). `f` sees the lane's sources; `none` from a source is a refused operand code. -/
def valuLanes (i : Inst) (s : WaveState) (nSrc : Nat) (f : List UInt32 → Nat → UInt32) : WaveState := Id.run do
  let mut st := s
  let dst := i.field "VDST"
  for lane in [0:lanes] do
    if execBit s lane then
      let mut srcs : List UInt32 := []
      let mut bad := false
      for k in [0:nSrc] do
        match vectorSource s (srcCode i k) i.literal lane with
        | some v => srcs := srcs ++ [v]
        | none => bad := true
      if bad then return s.fail s!"{i.name}: an operand code is not modelled"
      st := writeVgpr st dst lane (f srcs lane)
  return st

/-- A VALU operation producing a per-lane result and a mask bit (carry): the result to `VDST` for active
lanes, the mask fully written with inactive lanes zero (manual 3.9: "VCC is fully written"). -/
def valuLanesCarry (i : Inst) (s : WaveState) (ci : Option UInt64) (f : UInt32 → UInt32 → Bool → UInt32 × Bool) : WaveState := Id.run do
  let mut st := s
  let dst := i.field "VDST"
  let mut mask : UInt64 := 0
  for lane in [0:lanes] do
    if execBit s lane then
      match vectorSource s (srcCode i 0) i.literal lane, vectorSource s (srcCode i 1) i.literal lane with
      | some a, some b =>
        let cin := match ci with | some m => (m >>> lane.toUInt64) &&& 1 == 1 | none => false
        let (r, c) := f a b cin
        st := writeVgpr st dst lane r
        if c then mask := mask ||| (1 <<< lane.toUInt64)
      | _, _ => return s.fail s!"{i.name}: an operand code is not modelled"
  return writeScalarDst64 st (maskDst i) mask

/-- A compare: the mask of active lanes passing, written whole to VCC / an SGPR pair, or to EXEC for
V_CMPX (manual 12.9: `D[threadId] = test`, `EXEC[threadId] = test` for CMPX; 3.9: `VCC[n] = EXEC[n] &
test`). `width` 32 or 64 selects the source reading. -/
def valuCompare (i : Inst) (s : WaveState) (width : Nat) (test : UInt64 → UInt64 → Bool) : WaveState := Id.run do
  let mut mask : UInt64 := 0
  for lane in [0:lanes] do
    if execBit s lane then
      let a := if width == 64 then source64 s (srcCode i 0) lane else (vectorSource s (srcCode i 0) i.literal lane).map (·.toUInt64)
      let b := if width == 64 then source64 s (srcCode i 1) lane else (vectorSource s (srcCode i 1) i.literal lane).map (·.toUInt64)
      match a, b with
      | some x, some y => if test x y then mask := mask ||| (1 <<< lane.toUInt64)
      | _, _ => return s.fail s!"{i.name}: an operand code is not modelled"
  if i.name.startsWith "V_CMPX" then return { s with exec := mask }
  return writeScalarDst64 s (maskDst i) mask

/-- A 64-bit shift per lane: `VDST` is a VGPR pair. -/
def valuShift64 (i : Inst) (s : WaveState) (f : UInt32 → UInt64 → UInt64) : WaveState := Id.run do
  let mut st := s
  let dst := i.field "VDST"
  for lane in [0:lanes] do
    if execBit s lane then
      match vectorSource s (srcCode i 0) i.literal lane, source64 s (srcCode i 1) lane with
      | some c, some v =>
        let r := f c v
        st := writeVgpr (writeVgpr st dst lane r.toUInt32) (dst + 1) lane (r >>> 32).toUInt32
      | _, _ => return s.fail s!"{i.name}: an operand code is not modelled"
  return st

/-- The buffer resource constant (manual 8.1.8 Table 37) in four SGPRs: base address (47:0), stride
(61:48), swizzle enable (63), num_records (95:64), add-tid (119), OOB_SELECT (125:124). -/
structure BufferResource where
  base : UInt64
  stride : Nat
  swizzle : Bool
  numRecords : Nat
  addTid : Bool
  oobSelect : Nat

def readResource (s : WaveState) (sgpr : Nat) : BufferResource :=
  let d0 := readSgpr s sgpr
  let d1 := readSgpr s (sgpr + 1)
  let d2 := readSgpr s (sgpr + 2)
  let d3 := readSgpr s (sgpr + 3)
  { base := d0.toUInt64 ||| ((d1 &&& 0xFFFF).toUInt64 <<< 32)
    stride := ((d1 >>> 16) &&& 0x3FFF).toNat
    swizzle := (d1 >>> 31) == 1
    numRecords := d2.toNat
    addTid := ((d3 >>> 23) &&& 1) == 1
    oobSelect := ((d3 >>> 28) &&& 3).toNat }

/-- Range checking of one dword at byte offset `off` of a linear buffer with index 0 (manual 8.1.5
Table 35; `BUFFER_LOAD/STORE_DWORDx{2,3,4}` are range-checked per component, note 4). -/
def inRange (r : BufferResource) (off : Nat) : Bool :=
  match r.oobSelect with
  | 0 => !(r.numRecords == 0 || off ≥ r.stride)
  | 1 => !(r.numRecords == 0)
  | 2 => !(r.numRecords == 0)
  | _ => !(off + 4 > r.numRecords)

/-- MUBUF loads and stores of 1, 2 or 4 dwords (manual 8.1: address `base + sgpr_offset + offset`
for a linear buffer with no index, `offset = (OFFEN ? VGPR : 0) + inst_offset`; 8.1.7: the two LSBs of
the address are ignored; out-of-range reads return zero and writes are dropped). Swizzled, indexed and
tid-added buffers, LDS returns and TFE are refused. -/
def execMubuf (i : Inst) (s : WaveState) (isStore : Bool) : WaveState := Id.run do
  let some vdata := i.ie.operands.find? (·.field == "VDATA") | return s.fail s!"{i.name}: no VDATA operand"
  let n := vdata.size / 32
  let r := readResource s (4 * i.field "SRSRC")
  if r.swizzle || r.addTid || i.field "IDXEN" == 1 || i.field "LDS" == 1 || i.field "TFE" == 1 then
    return s.fail s!"{i.name}: swizzled, indexed, tid-added, LDS or TFE buffer access is not modelled"
  let some soff := scalarSource s (i.field "SOFFSET") none | return s.fail s!"{i.name}: SOFFSET code not modelled"
  let vd := i.field "VDATA"
  let mut st := s
  for lane in [0:lanes] do
    if execBit s lane then
      let voff := if i.field "OFFEN" == 1 then (readVgpr s (i.field "VADDR") lane).toNat else 0
      for k in [0:n] do
        let off := voff + i.field "OFFSET" + 4 * k
        let addr := (r.base + soff.toUInt64 + UInt64.ofNat off) &&& 0xFFFFFFFFFFFFFFFC
        if inRange r off then
          if isStore then
            st := writeMem32 st addr (readVgpr s (vd + k) lane)
          else
            match readMem32 s addr with
            | some v => st := writeVgpr st (vd + k) lane v
            | none => return s.fail s!"{i.name}: load from address 0x{String.ofList (Nat.toDigits 16 addr.toNat)} outside the memory"
        else if !isStore then
          st := writeVgpr st (vd + k) lane 0
  return st

/-- SMEM loads (manual 7.2.1): `ADDR = SGPR[base] + inst_offset + {M0 or SGPR[offset] or zero}`, the two
LSBs ignored, `N` dwords to `SDATA..`; `S_BUFFER_LOAD` reads base and num_records from the V# at
`SBASE` (stride must be zero: the manual's clamp for a non-zero stride is not modelled). Alignment of
SDATA (7.5) is required. -/
def execSmem (i : Inst) (s : WaveState) : WaveState := Id.run do
  let some sdata := i.ie.operands.find? (·.field == "SDATA") | return s.fail s!"{i.name}: no SDATA operand"
  let n := sdata.size / 32
  let sd := i.field "SDATA"
  if (n == 2 && sd % 2 != 0) || (n ≥ 4 && sd % 4 != 0) then return s.fail s!"{i.name}: SDATA s{sd} is not aligned for {n} dwords"
  let soffCode := i.field "SOFFSET"
  let soff : Nat := if soffCode == 125 then 0 else match scalarSource s soffCode none with | some v => v.toNat | none => 0
  if soffCode != 125 && (scalarSource s soffCode none).isNone then return s.fail s!"{i.name}: SOFFSET code not modelled"
  let imm := signed21 (i.field "OFFSET")
  let sbase := 2 * i.field "SBASE"
  let isBuffer := i.name.startsWith "S_BUFFER_LOAD"
  let mut st := s
  if isBuffer then
    let r := readResource s sbase
    if r.stride != 0 then return s.fail s!"{i.name}: a strided buffer constant is not modelled"
    if imm < 0 then return s.fail s!"{i.name}: negative offset with a buffer constant"
    let off := imm.toNat + soff
    for k in [0:n] do
      let o := off + 4 * k
      if o + 4 ≤ r.numRecords then
        let addr := (r.base + UInt64.ofNat o) &&& 0xFFFFFFFFFFFFFFFC
        match readMem32 s addr with
        | some v => st := writeSgpr st (sd + k) v
        | none => return s.fail s!"{i.name}: load outside the memory"
      else
        st := writeSgpr st (sd + k) 0
  else
    let base := (readSgpr s sbase).toUInt64 ||| ((readSgpr s (sbase + 1)).toUInt64 <<< 32)
    let addr0 : UInt64 := if imm < 0 then base - UInt64.ofNat (-imm).toNat + UInt64.ofNat soff else base + UInt64.ofNat imm.toNat + UInt64.ofNat soff
    for k in [0:n] do
      let addr := (addr0 + UInt64.ofNat (4 * k)) &&& 0xFFFFFFFFFFFFFFFC
      match readMem32 s addr with
      | some v => st := writeSgpr st (sd + k) v
      | none => return s.fail s!"{i.name}: load from 0x{String.ofList (Nat.toDigits 16 addr.toNat)} outside the memory"
  return st

/-- The scalar sources of SOP1/SOP2 (8-bit codes, with the literal). -/
def ssrc (i : Inst) (s : WaveState) (k : Nat) : Option UInt32 :=
  scalarSource s (i.field (if k == 0 then "SSRC0" else "SSRC1")) i.literal

def ssrc64 (i : Inst) (s : WaveState) (k : Nat) : Option UInt64 :=
  let code := i.field (if k == 0 then "SSRC0" else "SSRC1")
  if code == 255 then none else source64 s code 0

/-- One instruction. `s.pc` already points past it (branches add their offset to that, manual 12.5:
`PC = PC + signext(SIMM16 * 4) + 4`). -/
def execInst (i : Inst) (s : WaveState) : WaveState :=
  let name := i.name
  let unmod := modifiersClear i
  if !unmod then s.fail s!"{name}: VOP3 modifiers on an integer instruction are not modelled" else
  match name with
  -- Scalar ALU (manual 12.1 SOP2, 12.2 SOPK, 12.3 SOP1); gem5 twins sop1.cc S_MOV_B32/B64, sopk.cc S_MOVK_I32, sop2.cc S_AND_B64
  | "S_MOV_B32" => match ssrc i s 0 with
    | some v => writeScalarDst s (i.field "SDST") v
    | none => s.fail "S_MOV_B32: source code not modelled"
  | "S_MOV_B64" => match ssrc64 i s 0 with
    | some v => writeScalarDst64 s (i.field "SDST") v
    | none => s.fail "S_MOV_B64: source code not modelled"
  | "S_MOVK_I32" =>
    -- manual 12.2: D.i32 = signext(SIMM16[15:0])
    let v := i.field "SIMM16"
    writeScalarDst s (i.field "SDST") (if v ≥ 32768 then UInt32.ofNat (v + 0xFFFF0000) else UInt32.ofNat v)
  | "S_AND_B64" => match ssrc64 i s 0, ssrc64 i s 1 with
    -- manual 12.1: D = S0 & S1; SCC = (D != 0)
    | some a, some b => let d := a &&& b; { writeScalarDst64 s (i.field "SDST") d with scc := d != 0 }
    | _, _ => s.fail "S_AND_B64: source code not modelled"
  -- Program flow (manual 12.5 SOPP); gem5 twins sopp.cc S_CBRANCH_EXECZ, S_ENDPGM, S_WAITCNT
  | "S_CBRANCH_EXECZ" =>
    if s.exec == 0 then { s with pc := (Int.ofNat s.pc + signed16 (i.field "SIMM16")).toNat } else s
  | "S_ENDPGM" => { s with halted := true }
  | "S_WAITCNT" => s
  | "S_CLAUSE" => s
  -- Scalar memory (manual 12.6 SMEM); gem5 twins smem.cc S_LOAD_DWORDX4, S_BUFFER_LOAD_DWORDX2 (address only)
  | "S_LOAD_DWORD" | "S_LOAD_DWORDX2" | "S_LOAD_DWORDX4" | "S_LOAD_DWORDX8" | "S_LOAD_DWORDX16"
  | "S_BUFFER_LOAD_DWORD" | "S_BUFFER_LOAD_DWORDX2" | "S_BUFFER_LOAD_DWORDX4" => execSmem i s
  -- Vector memory (manual 12.14 MUBUF); gem5 twins mubuf.cc BUFFER_LOAD_DWORD/DWORDX2, BUFFER_STORE_DWORDX2
  | "BUFFER_LOAD_DWORD" | "BUFFER_LOAD_DWORDX2" | "BUFFER_LOAD_DWORDX4" => execMubuf i s false
  | "BUFFER_STORE_DWORD" | "BUFFER_STORE_DWORDX2" | "BUFFER_STORE_DWORDX4" => execMubuf i s true
  -- Vector ALU, 32-bit (manual 12.7 VOP2, 12.8 VOP1, 12.11 VOP3); gem5 twins vop1.cc/vop2.cc/vop3.cc
  | "V_MOV_B32" => valuLanes i s 1 fun src _ => src.getD 0 0
  | "V_ADD_NC_U32" => valuLanes i s 2 fun src _ => src.getD 0 0 + src.getD 1 0   -- gem5 twin V_ADD_U32
  | "V_AND_B32" => valuLanes i s 2 fun src _ => src.getD 0 0 &&& src.getD 1 0
  | "V_OR_B32" => valuLanes i s 2 fun src _ => src.getD 0 0 ||| src.getD 1 0
  | "V_LSHLREV_B32" => valuLanes i s 2 fun src _ => lshlrev32 (src.getD 0 0) (src.getD 1 0)
  | "V_LSHL_ADD_U32" => valuLanes i s 3 fun src _ => lshlAdd (src.getD 0 0) (src.getD 1 0) (src.getD 2 0)
  | "V_ADD3_U32" => valuLanes i s 3 fun src _ => add3 (src.getD 0 0) (src.getD 1 0) (src.getD 2 0)
  | "V_MUL_LO_U32" => valuLanes i s 2 fun src _ => mulLo (src.getD 0 0) (src.getD 1 0)
  | "V_MUL_HI_U32" => valuLanes i s 2 fun src _ => mulHi (src.getD 0 0) (src.getD 1 0)
  | "V_CNDMASK_B32" => match maskSource s (maskSrcCode i) with
    | some m => valuLanes i s 2 fun src lane => cndmask ((m >>> lane.toUInt64) &&& 1 == 1) (src.getD 0 0) (src.getD 1 0)
    | none => s.fail "V_CNDMASK_B32: mask code not modelled"
  | "V_ADD_CO_U32" => valuLanesCarry i s none fun a b _ => addCo a b
  | "V_SUB_CO_U32" => valuLanesCarry i s none fun a b _ => subCo a b
  | "V_ADD_CO_CI_U32" => match maskSource s (maskSrcCode i) with      -- gem5 twin V_ADDC_CO_U32
    | some m => valuLanesCarry i s (some m) fun a b ci => addCi a b ci
    | none => s.fail "V_ADD_CO_CI_U32: carry-in code not modelled"
  | "V_SUB_CO_CI_U32" => match maskSource s (maskSrcCode i) with      -- gem5 twin V_SUBB_CO_U32
    | some m => valuLanesCarry i s (some m) fun a b ci => subCi a b ci
    | none => s.fail "V_SUB_CO_CI_U32: carry-in code not modelled"
  | "V_LSHLREV_B64" => valuShift64 i s lshlrev64
  | "V_LSHRREV_B64" => valuShift64 i s lshrrev64
  -- Compares (manual 12.9 VOPC, in VOP3 12.11); gem5 twins vopc.cc / vop3_cmp.cc; V_CMPX writes EXEC only here
  | "V_CMP_LE_U32" => valuCompare i s 32 fun a b => a ≤ b
  | "V_CMP_GT_U32" => valuCompare i s 32 fun a b => a > b
  | "V_CMPX_GT_U32" => valuCompare i s 32 fun a b => a > b
  | "V_CMP_LT_U64" => valuCompare i s 64 fun a b => a < b
  | "V_CMP_NE_I64" => valuCompare i s 64 fun a b => a != b
  | _ => s.fail s!"{name}: no semantics (refused, not guessed)"

/-! ## 5. Stepping -/

/-- A decoded program: `prog[d]` is the instruction at dword `d`. -/
abbrev Program := Array (Option Inst)

def step (prog : Program) (s : WaveState) : WaveState :=
  if s.halted || s.err.isSome then s else
  match prog[s.pc]? with
  | none => s.fail "pc outside the program"
  | some none => s.fail "pc inside an instruction"
  | some (some i) => execInst i { s with pc := s.pc + i.words.length }

/-- `fuel` steps, or until the wave halts or fails. -/
def run (prog : Program) : Nat → WaveState → WaveState
  | 0, s => if s.halted || s.err.isSome then s else s.fail "the wave did not halt within its step budget"
  | n + 1, s => if s.halted || s.err.isSome then s else run prog n (step prog s)

theorem run_halted (prog : Program) (n : Nat) (s : WaveState) (h : s.halted = true) : run prog n s = s := by
  cases n <;> simp [run, h]

theorem run_succ (prog : Program) (n : Nat) (s : WaveState) (h : s.halted = false) (he : s.err = none) :
    run prog (n + 1) s = run prog n (step prog s) := by
  simp [run, h, he]

end Obend.Hardware.Gpu.Rdna2
