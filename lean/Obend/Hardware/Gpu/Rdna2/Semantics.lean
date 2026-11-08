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

Two Lean GPU models of the same month set the shape this sits beside: Koska, Koska and Koska,
"Formalizing PTX in Lean to Prove GPU Kernel Correctness" (arXiv 2611.04447) models the possible
executions of a PTX kernel with its memory model, proxies and data-dependent control flow, and proves
kernels against specifications; LARK (arXiv 2611.02028) formalizes a GPU machine model and operator
semantics once per target language, human-verified, and derives every incoming kernel's semantics from
them. This module is the RDNA2 point of that division: the instruction semantics are written and
checked once, here, and each dumped kernel's meaning is derived by `step` and checked by `Check`; the
NVIDIA point of the program is to adopt theirs rather than write its own.

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
public import Std.Tactic.BVDecide
public meta import Std.Tactic.BVDecide.Reflect
@[expose] public section

namespace Obend.Hardware.Gpu.Rdna2

/-! ## 1. The arithmetic, as pure functions on words, with the manual's pseudo-code -/

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

/-- V_AND_OR_B32 (manual 12.11): `D.u = (S0.u & S1.u) | S2.u`. -/
def andOr (a b c : UInt32) : UInt32 := (a &&& b) ||| c

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

/-- A bit as a word, `0` or `1`, and a word as a bit, nonzero (the convention of every mask bit below). -/
@[inline] def b2w (b : Bool) : UInt32 := if b then 1 else 0
@[inline] def w2b (x : UInt32) : Bool := x != 0

/-- The 64-bit value of a register pair, low dword first. -/
@[inline] def join64 (lo hi : UInt32) : UInt64 := lo.toUInt64 ||| (hi.toUInt64 <<< 32)

/-! ## 2. The value domain

The semantics below is written once, over a domain of 32-bit values `V` (a mask bit or a compare result
is a value `0` or `1`) and a memory `M`. Every operation on data goes through `Dom`; every decision the
hardware makes on a value (an address, an EXEC write, `VCCZ`) goes through `Dom.conc`, which answers
only when the value is known. The concrete instance (`UInt32`, the hash map) is the model the gem5
vectors and the dump runs test; the symbolic instance (`Obend.Hardware.Gpu.Rdna2.Term`) runs the same
code on terms, and `Obend.Hardware.Gpu.Rdna2.Natural` proves that the two agree. -/

class Dom (V : Type) where
  lit : UInt32 → V
  conc : V → Option UInt32
  add : V → V → V
  sub : V → V → V
  mul : V → V → V
  mulHi : V → V → V
  band : V → V → V
  bor : V → V → V
  /-- `x <<< (amount & 31)`, value first. -/
  shl : V → V → V
  /-- `c ≠ 0 ? a : b`. -/
  ite : V → V → V → V
  carry : V → V → V
  borrow : V → V → V
  addc : V → V → V → V
  carryc : V → V → V → V
  subc : V → V → V → V
  borrowc : V → V → V → V
  ule : V → V → V
  ugt : V → V → V
  ult64 : V → V → V → V → V
  ne64 : V → V → V → V → V
  /-- bit `k` (`k < 32`) as `0`/`1`. -/
  bit : V → Nat → V
  /-- 32 bits, least significant first, each `≠ 0`. -/
  pack : List V → V
  /-- `(lo, hi) <<< (count & 63)` and `>>>`, count first. -/
  shl64 : V → V → V → V × V
  lshr64 : V → V → V → V × V
  /-- `(lo, hi) ≠ 0` as `0`/`1`. -/
  nez64 : V → V → V

class MemDom (M : Type) (V : Type) where
  /-- The dword at a dword address, if the memory holds it. -/
  load : M → UInt64 → Option V
  store : M → UInt64 → V → M

/-- Bit packing on words: bit `i` of the result is `bs[i] ≠ 0` (least significant first). -/
def packWord : List UInt32 → UInt32
  | [] => 0
  | b :: bs => b2w (w2b b) ||| (packWord bs <<< 1)

instance : Dom UInt32 where
  lit x := x
  conc x := some x
  add a b := a + b
  sub a b := a - b
  mul a b := mulLo a b
  mulHi a b := mulHi a b
  band a b := a &&& b
  bor a b := a ||| b
  shl x a := x <<< (a &&& 31)
  ite c a b := if w2b c then a else b
  carry a b := b2w (addCo a b).2
  borrow a b := b2w (subCo a b).2
  addc a b c := (addCi a b (w2b c)).1
  carryc a b c := b2w (addCi a b (w2b c)).2
  subc a b c := (subCi a b (w2b c)).1
  borrowc a b c := b2w (subCi a b (w2b c)).2
  ule a b := b2w (a ≤ b)
  ugt a b := b2w (a > b)
  ult64 a0 a1 b0 b1 := b2w (join64 a0 a1 < join64 b0 b1)
  ne64 a0 a1 b0 b1 := b2w (join64 a0 a1 != join64 b0 b1)
  bit x k := (x >>> k.toUInt32) &&& 1
  pack bs := packWord bs
  shl64 c lo hi := let r := lshlrev64 c (join64 lo hi); (r.toUInt32, (r >>> 32).toUInt32)
  lshr64 c lo hi := let r := lshrrev64 c (join64 lo hi); (r.toUInt32, (r >>> 32).toUInt32)
  nez64 a b := b2w (a != 0 || b != 0)

/-- Memory as RDNA2's dword-aligned loads and stores see it: dword address (byte address / 4) to dword. -/
abbrev Memory := Std.HashMap UInt64 UInt32

instance : MemDom Memory UInt32 where
  load m a := m.get? a
  store m a v := m.insert a v

/-! ## 3. State -/

def lanes : Nat := 64
/-- SGPRs 0..105, then VCC_LO and VCC_HI at 106 and 107 (manual 3.9: "VCC physically resides in the
SGPR register file"). -/
def sgprCount : Nat := 108
def vgprCount : Nat := 256

structure GWave (V M : Type) where
  sgpr : Array V
  /-- EXEC is always known: it is written only from known values, and every write from an unknown
  value is refused (a data-dependent EXEC is outside what the model claims). -/
  exec : UInt64
  scc : V
  m0 : V
  /-- `vgpr[r * 64 + lane]`. -/
  vgpr : Array V
  /-- In dwords from the program's start (manual 3.2: PC is a byte address; every instruction here is
  dword-aligned, so dwords index the program). -/
  pc : Nat
  mem : M
  halted : Bool
  err : Option String

variable {V M : Type} [Dom V] [MemDom M V]

def GWave.init (mem : M) : GWave V M :=
  { sgpr := Array.replicate sgprCount (Dom.lit 0), exec := 0xFFFFFFFFFFFFFFFF, scc := Dom.lit 0,
    m0 := Dom.lit 0, vgpr := Array.replicate (vgprCount * lanes) (Dom.lit 0), pc := 0, mem := mem,
    halted := false, err := none }

def GWave.fail (s : GWave V M) (msg : String) : GWave V M :=
  if s.err.isSome then s else { s with err := some s!"pc {s.pc}: {msg}" }

/-- Continue with the value, or fail with `msg`: every refusal of the model on a value it does not know
goes through here (so that `Natural` can treat refusals once). -/
@[inline] def GWave.withSome {α : Type} (s : GWave V M) (o : Option α) (msg : String) (k : α → GWave V M) : GWave V M :=
  match o with
  | some v => k v
  | none => s.fail msg

def readSgpr (s : GWave V M) (n : Nat) : V := s.sgpr.getD n (Dom.lit 0)
def writeSgpr (s : GWave V M) (n : Nat) (v : V) : GWave V M :=
  if n < sgprCount then { s with sgpr := s.sgpr.set! n v } else s
def readVgpr (s : GWave V M) (r lane : Nat) : V := s.vgpr.getD (r * lanes + lane) (Dom.lit 0)
def writeVgpr (s : GWave V M) (r lane : Nat) (v : V) : GWave V M :=
  if r < vgprCount then { s with vgpr := s.vgpr.set! (r * lanes + lane) v } else s
def execBit (s : GWave V M) (lane : Nat) : Bool := (s.exec >>> lane.toUInt64) &&& 1 == 1

/-! ## 4. Operand codes (manual 5.2 Table 10, 6.2 Table 20) -/

/-- What a scalar source code names (manual 5.2 Table 10, 6.2 Table 20): SGPRs and VCC halves, M0,
NULL and the inline integers 0..64 and -1..-16 (as literals), the EXEC halves, VCCZ, EXECZ, SCC, the
literal dword; codes the model does not carry (trap temporaries, apertures, inline floats, LDS direct,
DPP/SDWA selectors) are `none`. -/
inductive SrcKind where
  | sgpr (n : Nat) | m0 | lit (v : UInt32) | execLo | execHi | vccz | execz | scc | literal | none
  deriving DecidableEq, Repr

def srcKind (code : Nat) : SrcKind :=
  if code ≤ 107 then .sgpr code
  else if code == 124 then .m0
  else if code == 125 then .lit 0
  else if code == 126 then .execLo
  else if code == 127 then .execHi
  else if code == 128 then .lit 0
  else if code ≤ 192 then .lit (UInt32.ofNat (code - 128))
  else if code ≤ 208 then .lit (0 - UInt32.ofNat (code - 192))
  else if code == 251 then .vccz
  else if code == 252 then .execz
  else if code == 253 then .scc
  else if code == 255 then .literal
  else .none

/-- The scalar value a source code names, at the SALU or as a VALU broadcast; VCCZ only when VCC is
known. -/
def scalarSource (s : GWave V M) (code : Nat) (lit : Option UInt32) : Option V :=
  match srcKind code with
  | .sgpr n => some (readSgpr s n)
  | .m0 => some s.m0
  | .lit v => some (Dom.lit v)
  | .execLo => some (Dom.lit s.exec.toUInt32)
  | .execHi => some (Dom.lit (s.exec >>> 32).toUInt32)
  | .vccz => (Dom.conc (readSgpr s 106)).bind fun lo => (Dom.conc (readSgpr s 107)).map fun hi => Dom.lit (b2w (lo == 0 && hi == 0))
  | .execz => some (Dom.lit (b2w (s.exec == 0)))
  | .scc => some s.scc
  | .literal => lit.map Dom.lit
  | .none => none

/-- A 32-bit VALU source: a VGPR (codes 256..511) per lane, else the scalar broadcast. -/
def vectorSource (s : GWave V M) (code : Nat) (lit : Option UInt32) (lane : Nat) : Option V :=
  if 256 ≤ code && code ≤ 511 then some (readVgpr s (code - 256) lane) else scalarSource s code lit

/-- What a 64-bit source code names: an SGPR pair, VCC, EXEC, NULL, a VGPR pair, or an inline integer
sign-extended to 64 bits (manual 6.2, "Literal Expansion to 64 bits": signed integers sign-extend;
LLVM AMDGPUUsage, integer inline constants in 64-bit operands); a literal is refused (its expansion
depends on the instruction's type and none of ours takes one). `mask` restricts to what a carry-in or
CNDMASK selector may read (manual 6.2.3: two consecutive SGPRs, VCC, or EXEC). -/
inductive Src64Kind where
  | sgprPair (n : Nat) | exec | lit (lo hi : UInt32) | vgprPair (r : Nat) | none
  deriving DecidableEq, Repr

def src64Kind (code : Nat) : Src64Kind :=
  if code ≤ 106 then .sgprPair code
  else if code == 125 then .lit 0 0
  else if code == 126 then .exec
  else if code == 128 then .lit 0 0
  else if code ≤ 192 then .lit (UInt32.ofNat (code - 128)) 0
  else if code ≤ 208 then .lit (0 - UInt32.ofNat (code - 192)) 0xFFFFFFFF
  else if 256 ≤ code && code ≤ 511 then .vgprPair (code - 256)
  else .none

def maskKind (code : Nat) : Src64Kind :=
  if code ≤ 106 then .sgprPair code
  else if code == 125 then .lit 0 0
  else if code == 126 then .exec
  else .none

def resolve64 (s : GWave V M) (k : Src64Kind) (lane : Nat) : Option (V × V) :=
  match k with
  | .sgprPair n => some (readSgpr s n, readSgpr s (n + 1))
  | .exec => some (Dom.lit s.exec.toUInt32, Dom.lit (s.exec >>> 32).toUInt32)
  | .lit lo hi => some (Dom.lit lo, Dom.lit hi)
  | .vgprPair r => some (readVgpr s r lane, readVgpr s (r + 1) lane)
  | .none => none

def source64 (s : GWave V M) (code : Nat) (lane : Nat) : Option (V × V) := resolve64 s (src64Kind code) lane

def maskSource (s : GWave V M) (code : Nat) : Option (V × V) := resolve64 s (maskKind code) 0

/-- A lane's bit of a mask pair. -/
def maskBit (m : V × V) (lane : Nat) : V := if lane < 32 then Dom.bit m.1 lane else Dom.bit m.2 (lane - 32)

/-- EXEC from a known pair; a pair not known is refused. -/
def writeExec (s : GWave V M) (lo hi : V) : GWave V M :=
  s.withSome ((Dom.conc lo).bind fun l => (Dom.conc hi).map fun h => join64 l h)
    "EXEC written from a value the model does not know" fun e => { s with exec := e }

/-- What a scalar destination code (7 bits) names: SGPR or VCC half, M0, NULL (discarded), EXEC halves. -/
inductive DstKind where
  | sgpr (n : Nat) | m0 | null | execLo | execHi | none
  deriving DecidableEq, Repr

def dstKind (code : Nat) : DstKind :=
  if code ≤ 107 then .sgpr code
  else if code == 124 then .m0
  else if code == 125 then .null
  else if code == 126 then .execLo
  else if code == 127 then .execHi
  else .none

def writeScalarDst (s : GWave V M) (code : Nat) (v : V) : GWave V M :=
  match dstKind code with
  | .sgpr n => writeSgpr s n v
  | .m0 => { s with m0 := v }
  | .null => s
  | .execLo => writeExec s v (Dom.lit (s.exec >>> 32).toUInt32)
  | .execHi => writeExec s (Dom.lit s.exec.toUInt32) v
  | .none => s.fail s!"scalar destination code {code} is not modelled"

/-- A 64-bit scalar destination: an SGPR pair (VCC at 106), NULL, EXEC. -/
def writeScalarDst64 (s : GWave V M) (code : Nat) (v : V × V) : GWave V M :=
  match dst64Kind code with
  | .sgpr n => writeSgpr (writeSgpr s n v.1) (n + 1) v.2
  | .null => s
  | .execLo => writeExec s v.1 v.2
  | _ => s.fail s!"64-bit scalar destination code {code} is not modelled"
where
  dst64Kind (code : Nat) : DstKind :=
    if code ≤ 106 then .sgpr code else if code == 125 then .null else if code == 126 then .execLo else .none

/-! ## 5. Executing one instruction -/

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

/-- The active lanes, in order. -/
def activeLanes (s : GWave V M) : List Nat := (List.range lanes).filter (execBit s)

/-- The first `n` sources of a VALU instruction at a lane. -/
def laneSources (i : Inst) (s : GWave V M) (n : Nat) (lane : Nat) : Option (List V) :=
  (List.range n).mapM fun k => vectorSource s (srcCode i k) i.literal lane

/-- Write `(lane, value)` results to VGPR `dst`. -/
def writeLanes (s : GWave V M) (dst : Nat) (rs : List (Nat × V)) : GWave V M :=
  rs.foldl (fun st (lane, v) => writeVgpr st dst lane v) s

/-- A per-lane 32-bit VALU operation over active lanes (manual 6.2.2: a thread writes only if its EXEC
bit is set). `f` sees the lane's sources; a source the model does not carry refuses the instruction.
The results are computed from `s` first and then written, so the register file updates in place. -/
def valuLanes (i : Inst) (s : GWave V M) (nSrc : Nat) (f : List V → Nat → V) : GWave V M :=
  s.withSome ((activeLanes s).mapM (fun lane => (laneSources i s nSrc lane).map fun src => (lane, f src lane)))
    s!"{i.name}: an operand code is not modelled" fun rs => writeLanes s (i.field "VDST") rs

/-- The mask a lane-wise bit computation leaves: inactive lanes `0`. -/
def maskOf (s : GWave V M) (bits : Nat → V) : V × V :=
  ((List.range 32).map (fun l => if execBit s l then bits l else Dom.lit 0) |> Dom.pack,
   (List.range 32).map (fun l => if execBit s (l + 32) then bits (l + 32) else Dom.lit 0) |> Dom.pack)

/-- A VALU operation producing a per-lane result and a mask bit (carry): the result to `VDST` for active
lanes, the mask fully written with inactive lanes zero (manual 3.9: "VCC is fully written"). -/
def valuLanesCarry (i : Inst) (s : GWave V M) (f : V → V → Nat → V × V) : GWave V M :=
  s.withSome ((activeLanes s).mapM (fun lane => (laneSources i s 2 lane).map fun src =>
      (lane, f (src.getD 0 (Dom.lit 0)) (src.getD 1 (Dom.lit 0)) lane)))
    s!"{i.name}: an operand code is not modelled" fun rs =>
    let carries : Nat → V := fun lane => ((rs.find? (·.1 == lane)).map (·.2.2)).getD (Dom.lit 0)
    writeScalarDst64 (writeLanes s (i.field "VDST") (rs.map fun (l, r) => (l, r.1))) (maskDst i) (maskOf s carries)

/-- A compare: the mask of active lanes passing, written whole to VCC / an SGPR pair, or to EXEC for
V_CMPX (manual 12.9: `D[threadId] = test`, `EXEC[threadId] = test` for CMPX; 3.9: `VCC[n] = EXEC[n] &
test`). `wide` selects 64-bit sources. -/
def valuCompare (i : Inst) (s : GWave V M) (wide : Bool) (test : List V → V) : GWave V M :=
  let srcs (lane : Nat) : Option (List V) :=
    if wide then
      (source64 s (srcCode i 0) lane).bind fun a => (source64 s (srcCode i 1) lane).map fun b => [a.1, a.2, b.1, b.2]
    else laneSources i s 2 lane
  s.withSome ((activeLanes s).mapM (fun lane => (srcs lane).map fun src => (lane, test src)))
    s!"{i.name}: an operand code is not modelled" fun rs =>
    let bits : Nat → V := fun lane => ((rs.find? (·.1 == lane)).map (·.2)).getD (Dom.lit 0)
    let m := maskOf s bits
    if i.name.startsWith "V_CMPX" then writeExec s m.1 m.2 else writeScalarDst64 s (maskDst i) m

/-- A 64-bit shift per lane: `VDST` is a VGPR pair. -/
def valuShift64 (i : Inst) (s : GWave V M) (f : V → V → V → V × V) : GWave V M :=
  s.withSome ((activeLanes s).mapM (fun lane =>
      (vectorSource s (srcCode i 0) i.literal lane).bind fun c =>
        (source64 s (srcCode i 1) lane).map fun p => (lane, f c p.1 p.2)))
    s!"{i.name}: an operand code is not modelled" fun rs =>
    let dst := i.field "VDST"
    writeLanes (writeLanes s dst (rs.map fun (l, r) => (l, r.1))) (dst + 1) (rs.map fun (l, r) => (l, r.2))

/-- The buffer resource constant (manual 8.1.8 Table 37) in four SGPRs: base address (47:0), stride
(61:48), swizzle enable (63), num_records (95:64), add-tid (119), OOB_SELECT (125:124). -/
structure BufferResource where
  base : UInt64
  stride : Nat
  swizzle : Bool
  numRecords : Nat
  addTid : Bool
  oobSelect : Nat

def resourceOfWords (d0 d1 d2 d3 : UInt32) : BufferResource :=
  { base := d0.toUInt64 ||| ((d1 &&& 0xFFFF).toUInt64 <<< 32)
    stride := ((d1 >>> 16) &&& 0x3FFF).toNat
    swizzle := (d1 >>> 31) == 1
    numRecords := d2.toNat
    addTid := ((d3 >>> 23) &&& 1) == 1
    oobSelect := ((d3 >>> 28) &&& 3).toNat }

/-- The resource constant at four SGPRs, if they are known. -/
def readResource (s : GWave V M) (sgpr : Nat) : Option BufferResource :=
  (Dom.conc (readSgpr s sgpr)).bind fun d0 => (Dom.conc (readSgpr s (sgpr + 1))).bind fun d1 =>
    (Dom.conc (readSgpr s (sgpr + 2))).bind fun d2 => (Dom.conc (readSgpr s (sgpr + 3))).map fun d3 =>
      resourceOfWords d0 d1 d2 d3

/-- Range checking of one dword at byte offset `off` of a linear buffer with index 0 (manual 8.1.5
Table 35; `BUFFER_LOAD/STORE_DWORDx{2,3,4}` are range-checked per component, note 4). -/
def inRange (r : BufferResource) (off : Nat) : Bool :=
  match r.oobSelect with
  | 0 => !(r.numRecords == 0 || off ≥ r.stride)
  | 1 => !(r.numRecords == 0)
  | 2 => !(r.numRecords == 0)
  | _ => !(off + 4 > r.numRecords)

/-- One MUBUF access of one lane: per dword `k`, `some addr` if in range (else the load reads zero and
the store is dropped). -/
def mubufAddrs (i : Inst) (r : BufferResource) (soff : UInt32) (voff : Nat) (n : Nat) : List (Option UInt64) :=
  (List.range n).map fun k =>
    let off := voff + i.field "OFFSET" + 4 * k
    if inRange r off then some (((r.base + soff.toUInt64 + UInt64.ofNat off) &&& 0xFFFFFFFFFFFFFFFC) >>> 2) else none

/-- The per-lane address lists of a MUBUF instruction, if every address is known. -/
def mubufLaneAddrs (i : Inst) (s : GWave V M) (r : BufferResource) (soff : UInt32) (n : Nat) :
    Option (List (Nat × List (Option UInt64))) :=
  (activeLanes s).mapM fun lane =>
    if i.field "OFFEN" == 1 then
      (Dom.conc (readVgpr s (i.field "VADDR") lane)).map fun v => (lane, mubufAddrs i r soff v.toNat n)
    else some (lane, mubufAddrs i r soff 0 n)

def storeAll (s : GWave V M) (ws : List (UInt64 × V)) : GWave V M :=
  { s with mem := ws.foldl (fun m (a, v) => MemDom.store m a v) s.mem }

def writeRegs (s : GWave V M) (ws : List (Nat × Nat × V)) : GWave V M :=
  ws.foldl (fun st (reg, lane, v) => writeVgpr st reg lane v) s

/-- MUBUF loads and stores of 1, 2 or 4 dwords (manual 8.1: address `base + sgpr_offset + offset`
for a linear buffer with no index, `offset = (OFFEN ? VGPR : 0) + inst_offset`; 8.1.7: the two LSBs of
the address are ignored; out-of-range reads return zero and writes are dropped). Swizzled, indexed and
tid-added buffers, LDS returns and TFE are refused, as are addresses the model does not know. -/
def execMubuf (i : Inst) (s : GWave V M) (isStore : Bool) : GWave V M :=
  s.withSome (i.ie.operands.find? (·.field == "VDATA")) s!"{i.name}: no VDATA operand" fun vdata =>
  let n := vdata.size / 32
  s.withSome (readResource s (4 * i.field "SRSRC")) s!"{i.name}: the buffer resource is not known" fun r =>
  if r.swizzle || r.addTid || i.field "IDXEN" == 1 || i.field "LDS" == 1 || i.field "TFE" == 1 then
    s.fail s!"{i.name}: swizzled, indexed, tid-added, LDS or TFE buffer access is not modelled" else
  s.withSome ((scalarSource s (i.field "SOFFSET") none).bind Dom.conc) s!"{i.name}: SOFFSET is not known" fun soff =>
  s.withSome (mubufLaneAddrs i s r soff n) s!"{i.name}: an address is not known" fun las =>
  let vd := i.field "VDATA"
  -- The effects are read from `s` first and applied afterwards, so memory and registers update in place.
  if isStore then
    storeAll s (las.flatMap fun (lane, as) =>
      (as.zipIdx.filterMap fun (a, k) => a.map fun a => (a, readVgpr s (vd + k) lane)))
  else
    s.withSome ((las.flatMap (fun (lane, as) => as.zipIdx.map fun (a, k) => (vd + k, lane, a))).mapM
        (fun (reg, lane, a) => match a with
          | some a => (MemDom.load s.mem a).map fun v => (reg, lane, v)
          | none => some (reg, lane, Dom.lit 0)))
      s!"{i.name}: a load outside the memory" fun ws => writeRegs s ws

def writeSgprs (s : GWave V M) (ws : List (Nat × V)) : GWave V M :=
  ws.foldl (fun st (n, v) => writeSgpr st n v) s

/-- SMEM loads (manual 7.2.1): `ADDR = SGPR[base] + inst_offset + {M0 or SGPR[offset] or zero}`, the two
LSBs ignored, `N` dwords to `SDATA..`; `S_BUFFER_LOAD` reads base and num_records from the V# at
`SBASE` (stride must be zero: the manual's clamp for a non-zero stride is not modelled). Alignment of
SDATA (7.5) is required. -/
def execSmem (i : Inst) (s : GWave V M) : GWave V M :=
  s.withSome (i.ie.operands.find? (·.field == "SDATA")) s!"{i.name}: no SDATA operand" fun sdata =>
  let n := sdata.size / 32
  let sd := i.field "SDATA"
  if (n == 2 && sd % 2 != 0) || (n ≥ 4 && sd % 4 != 0) then s.fail s!"{i.name}: SDATA s{sd} is not aligned for {n} dwords" else
  let soffCode := i.field "SOFFSET"
  let soff? : Option Nat := if soffCode == 125 then some 0 else ((scalarSource s soffCode none).bind Dom.conc).map (·.toNat)
  s.withSome soff? s!"{i.name}: SOFFSET is not known" fun soff =>
  let imm := signed21 (i.field "OFFSET")
  let sbase := 2 * i.field "SBASE"
  if i.name.startsWith "S_BUFFER_LOAD" then
    s.withSome (readResource s sbase) s!"{i.name}: the buffer resource is not known" fun r =>
    if r.stride != 0 then s.fail s!"{i.name}: a strided buffer constant is not modelled" else
    if imm < 0 then s.fail s!"{i.name}: negative offset with a buffer constant" else
    let off := imm.toNat + soff
    s.withSome ((List.range n).mapM (fun k =>
        let o := off + 4 * k
        if o + 4 ≤ r.numRecords then
          (MemDom.load s.mem (((r.base + UInt64.ofNat o) &&& 0xFFFFFFFFFFFFFFFC) >>> 2)).map fun v => (sd + k, v)
        else some (sd + k, Dom.lit 0)))
      s!"{i.name}: load outside the memory" fun ws => writeSgprs s ws
  else
    s.withSome ((Dom.conc (readSgpr s sbase)).bind fun b0 => (Dom.conc (readSgpr s (sbase + 1))).map fun b1 => join64 b0 b1)
      s!"{i.name}: the base address is not known" fun base =>
    let addr0 : UInt64 := if imm < 0 then base - UInt64.ofNat (-imm).toNat + UInt64.ofNat soff else base + UInt64.ofNat imm.toNat + UInt64.ofNat soff
    s.withSome ((List.range n).mapM (fun k =>
        (MemDom.load s.mem (((addr0 + UInt64.ofNat (4 * k)) &&& 0xFFFFFFFFFFFFFFFC) >>> 2)).map fun v => (sd + k, v)))
      s!"{i.name}: load outside the memory" fun ws => writeSgprs s ws

/-- The scalar sources of SOP1/SOP2 (8-bit codes, with the literal). -/
def ssrc (i : Inst) (s : GWave V M) (k : Nat) : Option V :=
  scalarSource s (i.field (if k == 0 then "SSRC0" else "SSRC1")) i.literal

def ssrc64 (i : Inst) (s : GWave V M) (k : Nat) : Option (V × V) :=
  let code := i.field (if k == 0 then "SSRC0" else "SSRC1")
  if code == 255 then none else source64 s code 0

/-- S_AND_B64's write (manual 12.1: `D = S0 & S1; SCC = (D != 0)`), from the two halves of `D`. -/
def andB64 (s : GWave V M) (code : Nat) (d0 d1 : V) : GWave V M :=
  let s' := writeScalarDst64 s code (d0, d1)
  if s'.err.isSome then s' else { s' with scc := Dom.nez64 d0 d1 }

/-- `D = EXEC; EXEC = S0 & EXEC; SCC = EXEC != 0` (manual 12.2, S_AND_SAVEEXEC_B64). -/
def saveexecB64 (s : GWave V M) (code : Nat) (a : V × V) : GWave V M :=
  let old : V × V := (Dom.lit s.exec.toUInt32, Dom.lit (s.exec >>> 32).toUInt32)
  let s1 := writeExec s (Dom.band a.1 old.1) (Dom.band a.2 old.2)
  if s1.err.isSome then s1 else
  let s2 := writeScalarDst64 s1 code old
  if s2.err.isSome then s2 else { s2 with scc := Dom.lit (if s2.exec != 0 then 1 else 0) }

/-- S_MOVK_I32 (manual 12.2): `D.i32 = signext(SIMM16[15:0])`. -/
def movkValue (simm : Nat) : UInt32 := if simm ≥ 32768 then UInt32.ofNat (simm + 0xFFFF0000) else UInt32.ofNat simm

def src0 (src : List V) : V := src.getD 0 (Dom.lit 0)
def src1 (src : List V) : V := src.getD 1 (Dom.lit 0)
def src2 (src : List V) : V := src.getD 2 (Dom.lit 0)

/-- The instructions the model gives a semantics to; everything else is `unknown` and refused. -/
inductive InstOp where
  | s_mov_b32 | s_mov_b64 | s_movk_i32 | s_and_b64 | s_cbranch_execz | s_endpgm | s_waitcnt | s_clause
  | smem | mubuf_load | mubuf_store
  | v_mov_b32 | v_add_nc_u32 | v_and_b32 | v_or_b32 | v_lshlrev_b32 | v_lshl_add_u32 | v_add3_u32 | v_and_or_b32
  | v_mul_lo_u32 | v_mul_hi_u32 | v_cndmask_b32 | v_add_co_u32 | v_sub_co_u32 | v_add_co_ci_u32 | v_sub_co_ci_u32
  | v_lshlrev_b64 | v_lshrrev_b64 | v_cmp_le_u32 | v_cmp_gt_u32 | v_cmpx_gt_u32 | v_cmp_lt_u64 | v_cmp_ne_i64
  | s_or_b64 | s_andn2_b64 | s_nor_b64 | s_and_saveexec_b64 | s_mulk_i32
  | v_cmp_lt_u32 | v_cmp_eq_i32 | v_cmp_ne_i32 | v_max_u32 | v_min_u32 | v_sub_nc_u32 | v_lshrrev_b32
  | v_subrev_co_ci_u32 | v_cmpx_ne_i32 | v_lshl_or_b32 | v_add_lshl_u32 | v_mul_u32_u24
  | v_cmpx_eq_i32 | v_cmpx_le_u32
  | unknown
  deriving DecidableEq, Repr

def instOp (name : String) : InstOp :=
  match name with
  | "S_MOV_B32" => .s_mov_b32 | "S_MOV_B64" => .s_mov_b64 | "S_MOVK_I32" => .s_movk_i32
  | "S_AND_B64" => .s_and_b64 | "S_CBRANCH_EXECZ" => .s_cbranch_execz | "S_ENDPGM" => .s_endpgm
  | "S_WAITCNT" => .s_waitcnt | "S_CLAUSE" => .s_clause
  | "S_LOAD_DWORD" | "S_LOAD_DWORDX2" | "S_LOAD_DWORDX4" | "S_LOAD_DWORDX8" | "S_LOAD_DWORDX16"
  | "S_BUFFER_LOAD_DWORD" | "S_BUFFER_LOAD_DWORDX2" | "S_BUFFER_LOAD_DWORDX4" => .smem
  | "BUFFER_LOAD_DWORD" | "BUFFER_LOAD_DWORDX2" | "BUFFER_LOAD_DWORDX4" => .mubuf_load
  | "BUFFER_STORE_DWORD" | "BUFFER_STORE_DWORDX2" | "BUFFER_STORE_DWORDX4" => .mubuf_store
  | "V_MOV_B32" => .v_mov_b32 | "V_ADD_NC_U32" => .v_add_nc_u32 | "V_AND_B32" => .v_and_b32
  | "V_OR_B32" => .v_or_b32 | "V_LSHLREV_B32" => .v_lshlrev_b32 | "V_LSHL_ADD_U32" => .v_lshl_add_u32
  | "V_ADD3_U32" => .v_add3_u32 | "V_AND_OR_B32" => .v_and_or_b32 | "V_MUL_LO_U32" => .v_mul_lo_u32
  | "V_MUL_HI_U32" => .v_mul_hi_u32 | "V_CNDMASK_B32" => .v_cndmask_b32 | "V_ADD_CO_U32" => .v_add_co_u32
  | "V_SUB_CO_U32" => .v_sub_co_u32 | "V_ADD_CO_CI_U32" => .v_add_co_ci_u32 | "V_SUB_CO_CI_U32" => .v_sub_co_ci_u32
  | "V_LSHLREV_B64" => .v_lshlrev_b64 | "V_LSHRREV_B64" => .v_lshrrev_b64 | "V_CMP_LE_U32" => .v_cmp_le_u32
  | "V_CMP_GT_U32" => .v_cmp_gt_u32 | "V_CMPX_GT_U32" => .v_cmpx_gt_u32 | "V_CMP_LT_U64" => .v_cmp_lt_u64
  | "V_CMP_NE_I64" => .v_cmp_ne_i64
  | "S_OR_B64" => .s_or_b64 | "S_ANDN2_B64" => .s_andn2_b64 | "S_NOR_B64" => .s_nor_b64
  | "S_AND_SAVEEXEC_B64" => .s_and_saveexec_b64 | "S_MULK_I32" => .s_mulk_i32
  | "V_CMP_LT_U32" => .v_cmp_lt_u32 | "V_CMP_EQ_I32" => .v_cmp_eq_i32 | "V_CMP_NE_I32" => .v_cmp_ne_i32
  | "V_MAX_U32" => .v_max_u32 | "V_MIN_U32" => .v_min_u32 | "V_SUB_NC_U32" => .v_sub_nc_u32
  | "V_LSHRREV_B32" => .v_lshrrev_b32 | "V_SUBREV_CO_CI_U32" => .v_subrev_co_ci_u32
  | "V_CMPX_NE_I32" => .v_cmpx_ne_i32 | "V_LSHL_OR_B32" => .v_lshl_or_b32 | "V_ADD_LSHL_U32" => .v_add_lshl_u32
  | "V_MUL_U32_U24" => .v_mul_u32_u24 | "V_CMPX_EQ_I32" => .v_cmpx_eq_i32 | "V_CMPX_LE_U32" => .v_cmpx_le_u32
  | _ => .unknown

/-- One instruction. `s.pc` already points past it (branches add their offset to that, manual 12.5:
`PC = PC + signext(SIMM16 * 4) + 4`). Each case cites the manual and its gem5 twin (see the header). -/
def execInst (i : Inst) (s : GWave V M) : GWave V M :=
  if !modifiersClear i then s.fail s!"{i.name}: VOP3 modifiers on an integer instruction are not modelled" else
  match instOp i.name with
  -- Scalar ALU (manual 12.1 SOP2, 12.2 SOPK, 12.3 SOP1); gem5 twins sop1.cc S_MOV_B32/B64, sopk.cc S_MOVK_I32, sop2.cc S_AND_B64
  | .s_mov_b32 => s.withSome (ssrc i s 0) "S_MOV_B32: source code not modelled" fun v =>
    writeScalarDst s (i.field "SDST") v
  | .s_mov_b64 => s.withSome (ssrc64 i s 0) "S_MOV_B64: source code not modelled" fun v =>
    writeScalarDst64 s (i.field "SDST") v
  | .s_movk_i32 => writeScalarDst s (i.field "SDST") (Dom.lit (movkValue (i.field "SIMM16")))
  -- manual 12.1: D = S0 & S1; SCC = (D != 0)
  | .s_and_b64 => s.withSome ((ssrc64 i s 0).bind fun a => (ssrc64 i s 1).map fun b => (a, b))
      "S_AND_B64: source code not modelled" fun ab =>
    andB64 s (i.field "SDST") (Dom.band ab.1.1 ab.2.1) (Dom.band ab.1.2 ab.2.2)
  -- Program flow (manual 12.5 SOPP); gem5 twins sopp.cc S_CBRANCH_EXECZ, S_ENDPGM, S_WAITCNT
  | .s_cbranch_execz =>
    if s.exec == 0 then { s with pc := (Int.ofNat s.pc + signed16 (i.field "SIMM16")).toNat } else s
  | .s_endpgm => { s with halted := true }
  | .s_waitcnt => s
  | .s_clause => s
  -- Scalar memory (manual 12.6 SMEM); gem5 twins smem.cc S_LOAD_DWORDX4, S_BUFFER_LOAD_DWORDX2 (address only)
  | .smem => execSmem i s
  -- Vector memory (manual 12.14 MUBUF); gem5 twins mubuf.cc BUFFER_LOAD_DWORD/DWORDX2, BUFFER_STORE_DWORDX2
  | .mubuf_load => execMubuf i s false
  | .mubuf_store => execMubuf i s true
  -- Vector ALU, 32-bit (manual 12.7 VOP2, 12.8 VOP1, 12.11 VOP3); gem5 twins vop1.cc/vop2.cc/vop3.cc
  | .v_mov_b32 => valuLanes i s 1 fun src _ => src0 src
  | .v_add_nc_u32 => valuLanes i s 2 fun src _ => Dom.add (src0 src) (src1 src)   -- gem5 twin V_ADD_U32
  | .v_and_b32 => valuLanes i s 2 fun src _ => Dom.band (src0 src) (src1 src)
  | .v_or_b32 => valuLanes i s 2 fun src _ => Dom.bor (src0 src) (src1 src)
  | .v_lshlrev_b32 => valuLanes i s 2 fun src _ => Dom.shl (src1 src) (src0 src)
  | .v_lshl_add_u32 => valuLanes i s 3 fun src _ => Dom.add (Dom.shl (src0 src) (src1 src)) (src2 src)
  | .v_add3_u32 => valuLanes i s 3 fun src _ => Dom.add (Dom.add (src0 src) (src1 src)) (src2 src)
  | .v_and_or_b32 => valuLanes i s 3 fun src _ => Dom.bor (Dom.band (src0 src) (src1 src)) (src2 src)
  | .v_mul_lo_u32 => valuLanes i s 2 fun src _ => Dom.mul (src0 src) (src1 src)
  | .v_mul_hi_u32 => valuLanes i s 2 fun src _ => Dom.mulHi (src0 src) (src1 src)
  | .v_cndmask_b32 => s.withSome (maskSource s (maskSrcCode i)) "V_CNDMASK_B32: mask code not modelled" fun m =>
    valuLanes i s 2 fun src lane => Dom.ite (maskBit m lane) (src1 src) (src0 src)
  | .v_add_co_u32 => valuLanesCarry i s fun a b _ => (Dom.add a b, Dom.carry a b)
  | .v_sub_co_u32 => valuLanesCarry i s fun a b _ => (Dom.sub a b, Dom.borrow a b)
  | .v_add_co_ci_u32 =>      -- gem5 twin V_ADDC_CO_U32
    s.withSome (maskSource s (maskSrcCode i)) "V_ADD_CO_CI_U32: carry-in code not modelled" fun m =>
    valuLanesCarry i s fun a b lane => (Dom.addc a b (maskBit m lane), Dom.carryc a b (maskBit m lane))
  | .v_sub_co_ci_u32 =>      -- gem5 twin V_SUBB_CO_U32
    s.withSome (maskSource s (maskSrcCode i)) "V_SUB_CO_CI_U32: carry-in code not modelled" fun m =>
    valuLanesCarry i s fun a b lane => (Dom.subc a b (maskBit m lane), Dom.borrowc a b (maskBit m lane))
  | .v_lshlrev_b64 => valuShift64 i s Dom.shl64
  | .v_lshrrev_b64 => valuShift64 i s Dom.lshr64
  -- Compares (manual 12.9 VOPC, in VOP3 12.11); gem5 twins vopc.cc / vop3_cmp.cc; V_CMPX writes EXEC only here
  | .v_cmp_le_u32 => valuCompare i s false fun src => Dom.ule (src0 src) (src1 src)
  | .v_cmp_gt_u32 => valuCompare i s false fun src => Dom.ugt (src0 src) (src1 src)
  | .v_cmpx_gt_u32 => valuCompare i s false fun src => Dom.ugt (src0 src) (src1 src)
  | .v_cmp_lt_u64 => valuCompare i s true fun src => Dom.ult64 (src0 src) (src1 src) (src2 src) (src.getD 3 (Dom.lit 0))
  | .v_cmp_ne_i64 => valuCompare i s true fun src => Dom.ne64 (src0 src) (src1 src) (src2 src) (src.getD 3 (Dom.lit 0))
  -- Manual 12.2 SOP1/12.3 SOP2: S_OR_B64 `D = S0 | S1`, S_ANDN2_B64 `D = S0 & ~S1`, S_NOR_B64
  -- `D = ~(S0 | S1)`, each `SCC = D != 0`; ~ and & ~ by the identities andn2_spec and not_spec
  | .s_or_b64 => s.withSome ((ssrc64 i s 0).bind fun a => (ssrc64 i s 1).map fun b => (a, b))
      "S_OR_B64: an operand code is not modelled" fun ab =>
    andB64 s (i.field "SDST") (Dom.bor ab.1.1 ab.2.1) (Dom.bor ab.1.2 ab.2.2)
  | .s_andn2_b64 => s.withSome ((ssrc64 i s 0).bind fun a => (ssrc64 i s 1).map fun b => (a, b))
      "S_ANDN2_B64: an operand code is not modelled" fun ab =>
    andB64 s (i.field "SDST") (Dom.sub ab.1.1 (Dom.band ab.1.1 ab.2.1)) (Dom.sub ab.1.2 (Dom.band ab.1.2 ab.2.2))
  | .s_nor_b64 => s.withSome ((ssrc64 i s 0).bind fun a => (ssrc64 i s 1).map fun b => (a, b))
      "S_NOR_B64: an operand code is not modelled" fun ab =>
    andB64 s (i.field "SDST") (Dom.sub (Dom.lit 0xFFFFFFFF) (Dom.bor ab.1.1 ab.2.1))
      (Dom.sub (Dom.lit 0xFFFFFFFF) (Dom.bor ab.1.2 ab.2.2))
  -- Manual 12.2 SOP1 S_AND_SAVEEXEC_B64: `D = EXEC; EXEC = S0 & EXEC; SCC = EXEC != 0`; a mask the
  -- model does not know is refused by writeExec
  | .s_and_saveexec_b64 => s.withSome (ssrc64 i s 0) "S_AND_SAVEEXEC_B64: an operand code is not modelled" fun a =>
    saveexecB64 s (i.field "SDST") a
  -- Manual 12.4 SOPK S_MULK_I32: `D = D * signext(SIMM16)`, SCC unchanged
  | .s_mulk_i32 =>
    writeScalarDst s (i.field "SDST") (Dom.mul (readSgpr s (i.field "SDST")) (Dom.lit (movkValue (i.field "SIMM16"))))
  -- Manual 12.9 VOPC: V_CMP_LT_U32 `S0 < S1`, V_CMP_EQ_I32 `S0 == S1`, V_CMP_NE_I32 `S0 <> S1`
  | .v_cmp_lt_u32 => valuCompare i s false fun src => Dom.ugt (src1 src) (src0 src)
  | .v_cmp_eq_i32 => valuCompare i s false fun src =>
    Dom.ite (Dom.ne64 (src0 src) (Dom.lit 0) (src1 src) (Dom.lit 0)) (Dom.lit 0) (Dom.lit 1)
  | .v_cmp_ne_i32 => valuCompare i s false fun src => Dom.ne64 (src0 src) (Dom.lit 0) (src1 src) (Dom.lit 0)
  | .v_cmpx_eq_i32 => valuCompare i s false fun src =>
    Dom.ite (Dom.ne64 (src0 src) (Dom.lit 0) (src1 src) (Dom.lit 0)) (Dom.lit 0) (Dom.lit 1)
  | .v_cmpx_le_u32 => valuCompare i s false fun src => Dom.ule (src0 src) (src1 src)
  | .v_cmpx_ne_i32 => valuCompare i s false fun src => Dom.ne64 (src0 src) (Dom.lit 0) (src1 src) (Dom.lit 0)
  -- Manual 12.7 VOP2 V_SUBREV_CO_CI_U32: `D = S1 - S0 - VCC; VCC = borrow` (gem5 twin V_SUBBREV_CO_U32)
  | .v_subrev_co_ci_u32 =>
    s.withSome (maskSource s (maskSrcCode i)) "V_SUBREV_CO_CI_U32: carry-in code not modelled" fun m =>
    valuLanesCarry i s fun a b lane => (Dom.subc b a (maskBit m lane), Dom.borrowc b a (maskBit m lane))
  -- Manual 12.7 VOP2: V_MAX_U32, V_MIN_U32, V_SUB_NC_U32 `D = S0 - S1`, V_LSHRREV_B32 `D = S1 >> S0[4:0]`
  | .v_max_u32 => valuLanes i s 2 fun src _ => Dom.ite (Dom.ugt (src0 src) (src1 src)) (src0 src) (src1 src)
  | .v_min_u32 => valuLanes i s 2 fun src _ => Dom.ite (Dom.ugt (src0 src) (src1 src)) (src1 src) (src0 src)
  | .v_sub_nc_u32 => valuLanes i s 2 fun src _ => Dom.sub (src0 src) (src1 src)
  | .v_lshrrev_b32 => valuLanes i s 2 fun src _ =>      -- the low half of a 64-bit shift of (S1, 0) by S0[4:0]
    (Dom.lshr64 (Dom.band (src0 src) (Dom.lit 31)) (src1 src) (Dom.lit 0)).1
  -- Manual 12.11 VOP3: V_LSHL_OR_B32 `D = (S0 << S1[4:0]) | S2`, V_ADD_LSHL_U32 `D = (S0 + S1) << S2[4:0]`;
  -- 12.7 VOP2 V_MUL_U32_U24 `D = S0[23:0] * S1[23:0]` (the low 32 bits)
  | .v_lshl_or_b32 => valuLanes i s 3 fun src _ => Dom.bor (Dom.shl (src0 src) (src1 src)) (src2 src)
  | .v_add_lshl_u32 => valuLanes i s 3 fun src _ => Dom.shl (Dom.add (src0 src) (src1 src)) (src2 src)
  | .v_mul_u32_u24 => valuLanes i s 2 fun src _ =>
    Dom.mul (Dom.band (src0 src) (Dom.lit 0xFFFFFF)) (Dom.band (src1 src) (Dom.lit 0xFFFFFF))
  | .unknown => s.fail s!"{i.name}: no semantics (refused, not guessed)"

/-- The identities the bitwise complements above are written with, on the concrete domain. -/
theorem andn2_spec (a b : UInt32) : a - (a &&& b) = a &&& ~~~b := by bv_decide
theorem not_spec (a : UInt32) : 0xFFFFFFFF - a = ~~~a := by bv_decide
theorem lshr32_spec (c x : UInt32) : (lshrrev64 (c &&& 31) (join64 x 0)).toUInt32 = x >>> (c &&& 31) := by
  unfold lshrrev64 join64; bv_decide

/-! ## 6. Stepping -/

/-- A decoded program: `prog[d]` is the instruction at dword `d`. -/
abbrev Program := Array (Option Inst)

def step (prog : Program) (s : GWave V M) : GWave V M :=
  if s.halted || s.err.isSome then s else
  match prog[s.pc]? with
  | none => s.fail "pc outside the program"
  | some none => s.fail "pc inside an instruction"
  | some (some i) => execInst i { s with pc := s.pc + i.words.length }

/-- `fuel` steps, or until the wave halts or fails. -/
def run (prog : Program) : Nat → GWave V M → GWave V M
  | 0, s => if s.halted || s.err.isSome then s else s.fail "the wave did not halt within its step budget"
  | n + 1, s => if s.halted || s.err.isSome then s else run prog n (step prog s)

/-- A wave as RADV launches one of our compute dispatches (manual 3.12; `Obend.Hardware.Gpu.Rdna2.Check`
cites the host side): `s2` the descriptor set's low address `setLo`, `s3` the workgroup id, `v0` the
lane, EXEC all ones, everything else zero. -/
def initWave (mem : M) (setLo : UInt32) (g : Nat) : GWave V M :=
  let s := writeSgpr (writeSgpr (GWave.init mem) 2 (Dom.lit setLo)) 3 (Dom.lit (UInt32.ofNat g))
  (List.range lanes).foldl (fun st lane => writeVgpr st 0 lane (Dom.lit (UInt32.ofNat lane))) s

/-- The concrete wave: the model. -/
abbrev WaveState := GWave UInt32 Memory

end Obend.Hardware.Gpu.Rdna2
