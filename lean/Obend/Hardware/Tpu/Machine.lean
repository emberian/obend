module
public import Obend.Crypto.FastRing
public import Obend.Hardware.Gpu.NttSum
public import Obend.Apps.ZkNtt.Goldilocks

public section
namespace Obend.Hardware.Tpu
open Obend.Crypto.Fast

/-! A single TensorCore, with whole 128×128 tiles as the DMA aliasing unit.
A descriptor snapshots its source at issue, writes its destination at retirement,
and leaves a counting-semaphore credit until a wait consumes it. Partial-tile DMA
is deliberately not an instruction of this ISA. All accesses fail closed.

For allocated initial states, `checkDmaSemaphores_async_refines_sync` proves
that every legal retirement schedule of an accepted program is fault-free and
ends in exactly the synchronous state. The simulation tracks pending payloads,
unchanged memory outside their destinations, and conservation of semaphore
credits across arbitrary indexed retirement and partial or complete waits.
-/

abbrev Tile := Sized UInt64 16384
abbrev VReg := Sized UInt64 1024

def zeroTile : Tile := Sized.ofFn fun _ => 0
def zeroVReg : VReg := Sized.ofFn fun _ => 0

def tileAt (t : Tile) (r c : Fin 128) : UInt64 :=
  t.spec ⟨r.val * 128 + c.val, by have := r.isLt; have := c.isLt; omega⟩

inductive MemorySpace where
  | hbm | vmem
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

structure TileAddr where
  space : MemorySpace
  index : Nat
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

inductive TpuTrap where
  | outOfBounds | dmaRace | semaphoreUnderflow
  | nonzeroExitSemaphore | pendingDmaAtExit | invalidDma | invalidRetirement
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

structure DmaDescriptor where
  source : TileAddr
  destination : TileAddr
  semaphore : Nat
  payload : Tile
  deriving DecidableEq

structure TpuCoreState where
  hbm : Array Tile
  vmem : Array Tile
  smem : Array UInt64
  vreg : Array VReg
  dma : List DmaDescriptor := []
  semaphores : Array Nat
  error : Option TpuTrap := none
  deriving DecidableEq

def TpuCoreState.initial (hbmTiles vmemTiles scalarRegs vectorRegs semaphoreCount : Nat) : TpuCoreState :=
  { hbm := Array.replicate hbmTiles zeroTile
    vmem := Array.replicate vmemTiles zeroTile
    smem := Array.replicate scalarRegs 0
    vreg := Array.replicate vectorRegs zeroVReg
    semaphores := Array.replicate semaphoreCount 0 }

def trap (s : TpuCoreState) (e : TpuTrap) : TpuCoreState :=
  if s.error.isSome then s else { s with error := some e }

def readTile (s : TpuCoreState) (a : TileAddr) : Option Tile :=
  match a.space with
  | .hbm => s.hbm[a.index]?
  | .vmem => s.vmem[a.index]?

def writeTile (s : TpuCoreState) (a : TileAddr) (v : Tile) : TpuCoreState :=
  match a.space with
  | .hbm => if a.index < s.hbm.size then { s with hbm := s.hbm.set! a.index v }
            else trap s .outOfBounds
  | .vmem => if a.index < s.vmem.size then { s with vmem := s.vmem.set! a.index v }
             else trap s .outOfBounds

/-- A read conflicts with a pending write; a write conflicts with both reads and writes. -/
def dmaHazard (pending : List DmaDescriptor) (reads writes : Array TileAddr) : Bool :=
  pending.any fun d => reads.contains d.destination ||
    writes.contains d.source || writes.contains d.destination

inductive VpuOp where
  | add32 | add64 | mul32 | mul64 | shl32 | shr32 | shl64 | shr64
  | carry32 | carry64 | mulHigh64 | goldilocksReduce
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

def evalVpu (op : VpuOp) (a b : UInt64) : UInt64 :=
  match op with
  | .add32 => (a.toUInt32 + b.toUInt32).toUInt64
  | .add64 => a + b
  | .mul32 => (a.toUInt32 * b.toUInt32).toUInt64
  | .mul64 => a * b
  | .shl32 => (a.toUInt32 <<< (b.toUInt32 &&& 31)).toUInt64
  | .shr32 => (a.toUInt32 >>> (b.toUInt32 &&& 31)).toUInt64
  | .shl64 => a <<< (b &&& 63)
  | .shr64 => a >>> (b &&& 63)
  | .carry32 => UInt64.ofNat ((a.toUInt32.toNat + b.toUInt32.toNat) / 2^32)
  | .carry64 => UInt64.ofNat ((a.toNat + b.toNat) / 2^64)
  | .mulHigh64 => UInt64.ofNat ((a.toNat*b.toNat) / 2^64)
  | .goldilocksReduce => UInt64.ofNat
      (Obend.Apps.ZkNtt.goldilocksReduce128Spec a.toNat b.toNat)

/-- Signed byte decoding is explicit, independent of the host signed-integer ABI. -/
def signedByte (x : UInt64) : Int :=
  let n := x.toNat % 256
  if n < 128 then n else (n : Int) - 256

inductive MxuMode where
  | unsigned8 | signed8 | bf16
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

/-- Finite IEEE values are represented exactly as mantissa × 2^exponent.
The special cases remain distinct; arithmetic never routes through host Float. -/
inductive BinaryFloat where
  | finite (mantissa : Int) (exponent : Int)
  | zero (negative : Bool)
  | infinity (negative : Bool)
  | nan
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

def decodeBf16 (bits : UInt16) : BinaryFloat :=
  let u := bits.toNat
  let e := u / 128 % 256
  let f := u % 128
  let neg := u / 32768 != 0
  if e == 255 then if f == 0 then .infinity neg else .nan
  else if e == 0 && f == 0 then .zero neg
  else .finite ((if neg then -1 else 1) * (if e == 0 then (f : Int) else 128 + f))
    (if e == 0 then -133 else (e : Int) - 134)

/-- Flush BF16 subnormals (`exponent == 0`, `mantissa != 0`) to signed zero per TPU hardware FTZ contract. -/
def flushBf16Subnormal (bits : UInt16) : UInt16 :=
  if bits.toNat / 128 % 256 == 0 then bits &&& 0x8000 else bits

/-- TPU hardware-accurate BF16 decoder with subnormal flush-to-zero (FTZ). -/
def decodeBf16Ftz (bits : UInt16) : BinaryFloat := decodeBf16 (flushBf16Subnormal bits)

theorem decodeBf16Ftz_eq_decodeBf16_of_normal (bits : UInt16) (hNorm : bits.toNat / 128 % 256 ≠ 0) :
    decodeBf16Ftz bits = decodeBf16 bits := by
  have hFalse : (bits.toNat / 128 % 256 == 0) = false := beq_false_of_ne hNorm
  simp [decodeBf16Ftz, flushBf16Subnormal, hFalse]

/-- Hardware discrimination witness: IEEE subnormal `0x0001` (`2^-133`) flushes to `+0` under TPU FTZ. -/
theorem decodeBf16_ne_decodeBf16Ftz_subnormal :
    decodeBf16 0x0001 = .finite 1 (-133) ∧ decodeBf16Ftz 0x0001 = .zero false ∧
    decodeBf16 0x0001 ≠ decodeBf16Ftz 0x0001 := by decide

/-- Round an integer divided by 2^shift to nearest, ties to even. -/
def roundShiftEven (n shift : Nat) : Nat :=
  let unit := 2^shift
  let q := n / unit
  let r := n % unit
  if 2*r > unit || (2*r == unit && q % 2 == 1) then q+1 else q

/-- IEEE binary32 round-to-nearest-even, including subnormal and overflow cases. -/
def roundFp32 (m e : Int) : BinaryFloat :=
  if m == 0 then .zero false else
  let n := m.natAbs
  let top : Int := (n.log2 : Int) + e
  let quantum := max (-149) (top - 23)
  let shift := (quantum - e).toNat
  let rounded := if e ≤ quantum then roundShiftEven n shift else n * 2^(e-quantum).toNat
  if quantum + (rounded.log2 : Int) > 127 then .infinity (m < 0)
  else if rounded == 0 then .zero (m < 0)
  else .finite (if m < 0 then -(rounded : Int) else rounded) quantum

def fpAdd (a b : BinaryFloat) : BinaryFloat :=
  match a, b with
  | .nan, _ | _, .nan => .nan
  | .infinity x, .infinity y => if x == y then .infinity x else .nan
  | .infinity x, _ | _, .infinity x => .infinity x
  | .zero x, .zero y => .zero (x && y)
  | .zero _, .finite m e | .finite m e, .zero _ => roundFp32 m e
  | .finite m e, .finite n f =>
    let g := min e f
    roundFp32 (m * (2 : Int)^(e-g).toNat + n * (2 : Int)^(f-g).toNat) g

/-- Exact product feeding a fused binary32 accumulation step. -/
def fpMul (a b : BinaryFloat) : BinaryFloat :=
  match a, b with
  | .nan, _ | _, .nan => .nan
  | .infinity x, .infinity y => .infinity (x != y)
  | .infinity _, .zero _ | .zero _, .infinity _ => .nan
  | .zero x, .zero y => .zero (x != y)
  | .zero x, .finite n _ | .finite n _, .zero x => .zero (x != (n < 0))
  | .infinity x, .finite n _ | .finite n _, .infinity x =>
    if n == 0 then .nan else .infinity (x != (n < 0))
  | .finite m e, .finite n f => .finite (m*n) (e+f)

def encodeFp32 : BinaryFloat → UInt32
  | .nan => 0x7fc00000
  | .zero neg => if neg then 0x80000000 else 0
  | .infinity neg => if neg then 0xff800000 else 0x7f800000
  | .finite m e =>
    let n := m.natAbs
    let sign := if m < 0 then 2^31 else 0
    if n == 0 then UInt32.ofNat sign else
    let top : Int := (n.log2 : Int) + e
    if top < -126 then UInt32.ofNat (sign + n * 2^(e+149).toNat)
    else
      let sig := if n.log2 ≤ 23 then n * 2^(23-n.log2) else n / 2^(n.log2-23)
      UInt32.ofNat (sign + (top+127).toNat * 2^23 + sig % 2^23)

/-- Fixed 128-deep dot product; u8 and s8 use a wide mathematical sum before
encoding the int32 accumulator. The bounds in CryptoSystolic justify no wrap. -/
def mxuDot (mode : MxuMode) (a b : Nat → UInt64) : UInt32 :=
  match mode with
  | .unsigned8 => UInt32.ofNat (Obend.Hardware.Gpu.Ntt.Sum.sum 128 (fun k =>
      (a k).toNat % 256 * ((b k).toNat % 256)))
  | .signed8 => (Int32.ofInt (sumInt 128 (fun k => signedByte (a k) * signedByte (b k)))).toUInt32
  | .bf16 => encodeFp32 ((Array.range 128).foldl (fun acc k =>
      fpAdd acc (fpMul (decodeBf16 (a k).toUInt16) (decodeBf16 (b k).toUInt16))) (.zero false))


/-- Unboxed UInt32 accumulator for the executable unsigned dot product. -/
def sumU32 (n : Nat) (f : Nat → UInt32) : UInt32 :=
  (Array.range n).foldl (fun acc k => acc + f k) 0

theorem sumU32_ofNat (n : Nat) (f : Nat → Nat) :
    sumU32 n (fun k => UInt32.ofNat (f k)) = UInt32.ofNat (Obend.Hardware.Gpu.Ntt.Sum.sum n f) := by
  unfold sumU32
  have h : (Array.range n).foldl (fun acc k => acc + UInt32.ofNat (f k)) (0 : UInt32) =
      UInt32.ofNat (Obend.Hardware.Gpu.Ntt.Sum.sum (Array.range n).size f) := by
    apply Array.foldl_induction
      (motive := fun k acc => acc = UInt32.ofNat (Obend.Hardware.Gpu.Ntt.Sum.sum k f)) rfl
    intro i acc hacc
    simp only [hacc, Fin.getElem_fin, Array.getElem_range, Obend.Hardware.Gpu.Ntt.Sum.succ, UInt32.ofNat_add]
  simpa only [Array.size_range] using h

def mxuDotExec (mode : MxuMode) (a b : Nat → UInt64) : UInt32 :=
  match mode with
  | .unsigned8 => sumU32 128 (fun k =>
      UInt32.ofNat ((a k).toNat%256) * UInt32.ofNat ((b k).toNat%256))
  | .signed8 => (Int32.ofInt (sumInt 128 (fun k => signedByte (a k) * signedByte (b k)))).toUInt32
  | .bf16 => encodeFp32 ((Array.range 128).foldl (fun acc k =>
      fpAdd acc (fpMul (decodeBf16 (a k).toUInt16) (decodeBf16 (b k).toUInt16))) (.zero false))

@[csimp] theorem mxuDot_eq_exec : @mxuDot = @mxuDotExec := by
  funext mode a b
  cases mode with
  | unsigned8 =>
    simp only [mxuDot, mxuDotExec, ← UInt32.ofNat_mul, sumU32_ofNat]
  | signed8 => unfold mxuDot mxuDotExec; rfl
  | bf16 => unfold mxuDot mxuDotExec; rfl

def mxuTile (mode : MxuMode) (a b : Tile) : Tile :=
  Sized.ofFn fun ij => (mxuDot mode
    (fun k => a.coeffs[ij.val / 128 * 128 + k]!)
    (fun k => b.coeffs[k * 128 + ij.val % 128]!)).toUInt64

def transposeTile (a : Tile) : Tile :=
  Sized.ofFn fun ij => a.spec ⟨ij.val % 128 * 128 + ij.val / 128, by
    have := ij.isLt
    have := Nat.mod_lt ij.val (by decide : 0 < 128)
    have : ij.val / 128 < 128 := Nat.div_lt_of_lt_mul (by omega)
    omega⟩


theorem tileAt_transpose (t : Tile) (r c : Fin 128) :
    tileAt (transposeTile t) r c = tileAt t c r := by
  have hr := r.isLt
  have hc := c.isLt
  have hd : (r.val*128+c.val)/128 = r.val := by omega
  have hm : (r.val*128+c.val)%128 = c.val := by omega
  simp only [tileAt, transposeTile, Sized.spec_ofFn, hd, hm]

def permuteVReg (a : VReg) (lanes : Fin 128 → Fin 128) : VReg :=
  Sized.ofFn fun ij => a.spec ⟨ij.val / 128 * 128 + (lanes ⟨ij.val % 128, Nat.mod_lt _ (by decide)⟩).val,
    by have := ij.isLt
       have := (lanes ⟨ij.val % 128, Nat.mod_lt _ (by decide)⟩).isLt
       have : ij.val / 128 < 8 := Nat.div_lt_of_lt_mul (by omega)
       omega⟩

inductive TpuInstr where
  | dma (src dst : TileAddr) (sem : Nat)
  | wait (sem count : Nat)
  | signal (sem count : Nat)
  | mxu (mode : MxuMode) (dst lhs rhs : Nat)
  | transpose (dst src : Nat)
  | vpu (op : VpuOp) (dst lhs rhs : Nat)
  | loadVReg (dst tile subTile : Nat)
  | storeVReg (tile subTile src : Nat)
  | permute (dst src : Nat) (lanes : Array Nat)
  | fillVReg (dst : Nat) (value : UInt64)
  | scalar (dst : Nat) (value : UInt64)
  | finish
  deriving DecidableEq

abbrev TpuProg := List TpuInstr

/-- Retirement can select any queue entry, not just the oldest descriptor. -/
def retireDma (s : TpuCoreState) (index : Nat) : TpuCoreState :=
  if s.error.isSome then s else
  match s.dma[index]? with
  | none => trap s .invalidRetirement
  | some d =>
    let s' := writeTile s d.destination d.payload
    { s' with dma := s.dma.eraseIdx index
              semaphores := s.semaphores.modify d.semaphore (· + 1) }

/-- A blocking wait may force progress for its semaphore. Other descriptors
remain in flight. A fuel bound equal to queue length suffices. -/
def retireSemaphore : Nat → TpuCoreState → Nat → Nat → TpuCoreState
  | 0, s, _, _ => s
  | n+1, s, sem, count =>
    if count ≤ s.semaphores[sem]! then s else
    match s.dma.findIdx? (fun d => d.semaphore == sem) with
    | none => s
    | some i => retireSemaphore n (retireDma s i) sem count

def stepBody (s : TpuCoreState) : TpuInstr → TpuCoreState
  | .dma src dst sem =>
    if src.space == dst.space then trap s .invalidDma
    else if sem ≥ s.semaphores.size then trap s .outOfBounds
    else if dmaHazard s.dma #[src] #[dst] then trap s .dmaRace
    else match readTile s src, readTile s dst with
      | some value, some _ => { s with dma := s.dma ++ [⟨src, dst, sem, value⟩] }
      | _, _ => trap s .outOfBounds
  | .wait sem count =>
    if sem ≥ s.semaphores.size then trap s .outOfBounds else
    let t := retireSemaphore s.dma.length s sem count
    if count ≤ t.semaphores[sem]! then
      { t with semaphores := t.semaphores.modify sem (· - count) }
    else trap t .semaphoreUnderflow
  | .signal sem count =>
    if sem < s.semaphores.size then { s with semaphores := s.semaphores.modify sem (· + count) }
    else trap s .outOfBounds
  | .mxu mode dst lhs rhs =>
    if dmaHazard s.dma #[⟨.vmem,lhs⟩, ⟨.vmem,rhs⟩] #[⟨.vmem,dst⟩] then trap s .dmaRace
    else match s.vmem[lhs]?, s.vmem[rhs]? with
      | some a, some b => writeTile s ⟨.vmem,dst⟩ (mxuTile mode a b)
      | _, _ => trap s .outOfBounds
  | .transpose dst src =>
    if dmaHazard s.dma #[⟨.vmem,src⟩] #[⟨.vmem,dst⟩] then trap s .dmaRace
    else match s.vmem[src]? with
      | some a => writeTile s ⟨.vmem,dst⟩ (transposeTile a)
      | none => trap s .outOfBounds
  | .vpu op dst lhs rhs =>
    match s.vreg[lhs]?, s.vreg[rhs]? with
    | some a, some b =>
      if dst < s.vreg.size then
        { s with vreg := s.vreg.set! dst (Sized.ofFn fun i => evalVpu op (a.spec i) (b.spec i)) }
      else trap s .outOfBounds
    | _, _ => trap s .outOfBounds
  | .loadVReg dst tile subTile =>
    if dmaHazard s.dma #[⟨.vmem,tile⟩] #[] then trap s .dmaRace
    else if dst < s.vreg.size && subTile < 16 then
      match s.vmem[tile]? with
      | none => trap s .outOfBounds
      | some a => { s with vreg := s.vreg.set! dst (Sized.ofFn fun i =>
          a.coeffs[subTile * 1024 + i.val]!) }
    else trap s .outOfBounds
  | .storeVReg tile subTile src =>
    if dmaHazard s.dma #[] #[⟨.vmem,tile⟩] then trap s .dmaRace
    else if subTile < 16 then
      match s.vmem[tile]?, s.vreg[src]? with
      | some a, some b => writeTile s ⟨.vmem,tile⟩ (Sized.ofFn fun i =>
          if i.val / 1024 == subTile then b.coeffs[i.val % 1024]! else a.spec i)
      | _, _ => trap s .outOfBounds
    else trap s .outOfBounds
  | .permute dst src lanes =>
    if lanes.size == 128 && lanes.all (· < 128) then
      match s.vreg[src]? with
      | some a => if dst < s.vreg.size then
          { s with vreg := s.vreg.set! dst (Sized.ofFn fun i => a.coeffs[i.val / 128 * 128 + lanes[i.val % 128]!]!) }
        else trap s .outOfBounds
      | none => trap s .outOfBounds
    else trap s .outOfBounds
  | .fillVReg dst value =>
    if dst < s.vreg.size then { s with vreg := s.vreg.set! dst (Sized.ofFn fun _ => value) }
    else trap s .outOfBounds
  | .scalar dst value =>
    if dst < s.smem.size then { s with smem := s.smem.set! dst value } else trap s .outOfBounds
  | .finish =>
    if !s.dma.isEmpty then trap s .pendingDmaAtExit
    else if s.semaphores.any (· != 0) then trap s .nonzeroExitSemaphore
    else s

def stepAsync (s : TpuCoreState) (i : TpuInstr) : TpuCoreState :=
  if s.error.isSome then s else stepBody s i

def stepSync (s : TpuCoreState) (i : TpuInstr) : TpuCoreState :=
  let t := stepAsync s i
  match i with
  | .dma _ _ _ => if t.error.isSome then t else retireDma t (t.dma.length-1)
  | _ => t

def runSync (s : TpuCoreState) (p : TpuProg) : TpuCoreState := p.foldl stepSync s

/-- Schedules explicitly interleave arbitrary indexed retirements and instructions. -/
inductive TpuEvent where
  | instruction (i : TpuInstr)
  | retire (index : Nat)

def eventStep (s : TpuCoreState) : TpuEvent → TpuCoreState
  | .instruction i => stepAsync s i
  | .retire i => retireDma s i

def runEvents (s : TpuCoreState) (trace : List TpuEvent) : TpuCoreState :=
  trace.foldl eventStep s

/-- A trace is legal if retirement indices exist when selected. Instruction
faults are retained, rather than silently filtering erroneous executions. -/
inductive ValidTrace : TpuCoreState → List TpuEvent → Prop where
  | nil (s) : ValidTrace s []
  | instruction (s i rest) : ValidTrace (stepAsync s i) rest →
      ValidTrace s (.instruction i :: rest)
  | retire (s index rest) : index < s.dma.length → s.error = none →
      ValidTrace (retireDma s index) rest → ValidTrace s (.retire index :: rest)

theorem stepAsync_failClosed (s : TpuCoreState) (i : TpuInstr) (h : s.error.isSome = true) :
    stepAsync s i = s := by simp [stepAsync, h]

theorem runEvents_append (s : TpuCoreState) (a b : List TpuEvent) :
    runEvents s (a ++ b) = runEvents (runEvents s a) b := by
  simp [runEvents, List.foldl_append]

/-- Abstract descriptors contain addresses only; no tensor data is evaluated by
this static analysis. Credits count both completed and still-pending transfers. -/
structure DmaFootprint where
  source : TileAddr
  destination : TileAddr
  semaphore : Nat
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

structure DmaAnalysis where
  pending : List DmaFootprint := []
  credits : Array Nat
  deriving DecidableEq

def footprintHazard (pending : List DmaFootprint) (reads writes : Array TileAddr) : Bool :=
  pending.any fun d => reads.contains d.destination ||
    writes.contains d.source || writes.contains d.destination

def analyzeStep (a : DmaAnalysis) : TpuInstr → Option DmaAnalysis
  | .dma src dst sem =>
    if src.space == dst.space || sem ≥ a.credits.size ||
        footprintHazard a.pending #[src] #[dst] then none
    else some { pending := a.pending ++ [⟨src,dst,sem⟩]
                credits := a.credits.modify sem (· + 1) }
  | .wait sem count =>
    if sem < a.credits.size && count ≤ a.credits[sem]! then
      some { pending := if count == a.credits[sem]! then a.pending.filter (fun d => d.semaphore != sem) else a.pending
             credits := a.credits.modify sem (· - count) }
    else none
  | .signal sem count =>
    if sem < a.credits.size then some { a with credits := a.credits.modify sem (· + count) }
    else none
  | .mxu _ dst lhs rhs =>
    if footprintHazard a.pending #[⟨.vmem,lhs⟩,⟨.vmem,rhs⟩] #[⟨.vmem,dst⟩] then none else some a
  | .transpose dst src =>
    if footprintHazard a.pending #[⟨.vmem,src⟩] #[⟨.vmem,dst⟩] then none else some a
  | .loadVReg _ tile block =>
    if block ≥ 16 || footprintHazard a.pending #[⟨.vmem,tile⟩] #[] then none else some a
  | .storeVReg tile block _ =>
    if block ≥ 16 || footprintHazard a.pending #[] #[⟨.vmem,tile⟩] then none else some a
  | .permute _ _ lanes =>
    if lanes.size == 128 && lanes.all (· < 128) then some a else none
  | .finish => if a.pending.isEmpty && a.credits.all (· == 0) then some a else none
  | _ => some a

def analyzeProgram : DmaAnalysis → TpuProg → Option DmaAnalysis
  | a, [] => analyzeStep a .finish
  | a, i::is => (analyzeStep a i).bind (fun b => analyzeProgram b is)

def checkDmaSemaphores (semaphoreCount : Nat) (p : TpuProg) : Bool :=
  (analyzeProgram ⟨[], Array.replicate semaphoreCount 0⟩ p).isSome

/-- The analyzer reports missing waits on reads of an outstanding destination,
independently of the contents of either memory. -/
theorem analyzeStep_read_refuses (a : DmaAnalysis) (dst src : Nat)
    (h : footprintHazard a.pending #[⟨.vmem,src⟩] #[⟨.vmem,dst⟩] = true) :
    analyzeStep a (.transpose dst src) = none := by simp [analyzeStep, h]

theorem analyzeProgram_cons (a : DmaAnalysis) (i : TpuInstr) (p : TpuProg) :
    analyzeProgram a (i::p) = (analyzeStep a i).bind (fun b => analyzeProgram b p) := by rw [analyzeProgram]

theorem analyzeStep_finish_drained (a b : DmaAnalysis)
    (h : analyzeStep a .finish = some b) :
    a.pending.isEmpty = true ∧ a.credits.all (· == 0) = true := by
  simp only [analyzeStep] at h
  split at h
  · rename_i hp; simpa only [Bool.and_eq_true] using hp
  · contradiction



/-- Faults are absorbing across arbitrarily long event traces, including DMA
retirements. No later instruction can clear an earlier refusal. -/
theorem runEvents_failClosed (s : TpuCoreState) (events : List TpuEvent)
    (h : s.error.isSome = true) : runEvents s events = s := by
  induction events with
  | nil => rfl
  | cons e es ih =>
    have he : eventStep s e = s := by
      cases e with
      | instruction i => exact stepAsync_failClosed s i h
      | retire i => simp [eventStep, retireDma, h]
    simpa only [runEvents, List.foldl_cons, he] using ih

/-- Terminal drain is proved for the whole analyzed instruction list. This is
an abstract resource invariant, not the still-required operational simulation. -/
theorem analyzeProgram_terminal_drained (p : TpuProg) (a b : DmaAnalysis)
    (h : analyzeProgram a p = some b) :
    b.pending.isEmpty = true ∧ b.credits.all (· == 0) = true := by
  induction p generalizing a with
  | nil =>
    simp only [analyzeProgram, analyzeStep] at h
    split at h
    · rename_i hd
      have he : a = b := Option.some.inj h
      subst b
      simpa only [Bool.and_eq_true] using hd
    · contradiction
  | cons i p ih =>
    rw [analyzeProgram_cons] at h
    cases he : analyzeStep a i with
    | none => simp [he] at h
    | some next =>
      simp only [he, Option.bind_some] at h
      exact ih next h

/-- Allocation bounds are independent of tensor values and DMA retirement order. -/
def tileBound (s : TpuCoreState) (a : TileAddr) : Prop :=
  match a.space with
  | .hbm => a.index < s.hbm.size
  | .vmem => a.index < s.vmem.size

def InstrBound (s : TpuCoreState) : TpuInstr → Prop
  | .dma src dst sem => tileBound s src ∧ tileBound s dst ∧ sem < s.semaphores.size
  | .wait sem _ | .signal sem _ => sem < s.semaphores.size
  | .mxu _ dst lhs rhs => dst < s.vmem.size ∧ lhs < s.vmem.size ∧ rhs < s.vmem.size
  | .transpose dst src => dst < s.vmem.size ∧ src < s.vmem.size
  | .vpu _ dst lhs rhs => dst < s.vreg.size ∧ lhs < s.vreg.size ∧ rhs < s.vreg.size
  | .loadVReg dst tile block => dst < s.vreg.size ∧ tile < s.vmem.size ∧ block < 16
  | .storeVReg tile block src => tile < s.vmem.size ∧ block < 16 ∧ src < s.vreg.size
  | .permute dst src lanes => dst < s.vreg.size ∧ src < s.vreg.size ∧
      lanes.size = 128 ∧ ∀ x ∈ lanes, x < 128
  | .fillVReg dst _ => dst < s.vreg.size
  | .scalar dst _ => dst < s.smem.size
  | .finish => True

/-- Initial resource discipline and all static allocation bounds. -/
structure WellSized (s : TpuCoreState) (p : TpuProg) : Prop where
  healthy : s.error = none
  empty : s.dma = []
  zero : s.semaphores = Array.replicate s.semaphores.size 0
  bounds : ∀ i ∈ p, InstrBound s i

def DmaDescriptor.footprint (d : DmaDescriptor) : DmaFootprint :=
  ⟨d.source, d.destination, d.semaphore⟩

def credit (a : Array Nat) (k : Nat) : Nat := a[k]?.getD 0

def outstanding (ds : List DmaDescriptor) (k : Nat) : Nat :=
  ds.countP (fun d => d.semaphore == k)

/-- The synchronous state already contains each pending payload. Elsewhere the
memories agree. Credits include both completed and outstanding transfers. -/
structure DmaSim (s t : TpuCoreState) (a : DmaAnalysis) : Prop where
  healthy : s.error = none
  syncHealthy : t.error = none
  syncEmpty : t.dma = []
  hbmSize : s.hbm.size = t.hbm.size
  vmemSize : s.vmem.size = t.vmem.size
  scalar : s.smem = t.smem
  vector : s.vreg = t.vreg
  semSize : s.semaphores.size = a.credits.size
  syncCredits : t.semaphores = a.credits
  credits : ∀ k, credit a.credits k = credit s.semaphores k + outstanding s.dma k
  covered : ∀ d ∈ s.dma, d.footprint ∈ a.pending
  semBound : ∀ d ∈ s.dma, d.semaphore < a.credits.size
  committed : ∀ d ∈ s.dma, readTile t d.destination = some d.payload
  unchanged : ∀ addr, (∀ d ∈ s.dma, addr ≠ d.destination) → readTile s addr = readTile t addr

private theorem credit_modify (xs : Array Nat) (j k : Nat) (f : Nat → Nat)
    (hj : j < xs.size) :
    credit (xs.modify j f) k = if k = j then f (credit xs k) else credit xs k := by
  by_cases hk : k = j
  · subst k; simp [credit, Array.getElem_modify_self, hj]
  · simp [credit, Array.getElem?_modify, hk, Ne.symm hk]

private theorem credit_bang (xs : Array Nat) (k : Nat) : credit xs k = xs[k]! := by
  simp only [credit, getElem!_def]; cases xs[k]? <;> rfl

private theorem readTile_bound (s : TpuCoreState) (addr : TileAddr) (v : Tile)
    (h : readTile s addr = some v) : tileBound s addr := by
  cases addr with | mk space index =>
    cases space <;> simp only [readTile, tileBound] at * <;>
      exact (Array.getElem?_eq_some_iff.mp h).1

private theorem writeTile_fields (s : TpuCoreState) (addr : TileAddr) (v : Tile)
    (h : tileBound s addr) :
    (writeTile s addr v).hbm.size = s.hbm.size ∧
    (writeTile s addr v).vmem.size = s.vmem.size ∧
    (writeTile s addr v).smem = s.smem ∧ (writeTile s addr v).vreg = s.vreg ∧
    (writeTile s addr v).dma = s.dma ∧
    (writeTile s addr v).semaphores = s.semaphores ∧
    (writeTile s addr v).error = s.error := by
  cases addr with | mk space index =>
    cases space <;> simp_all [tileBound, writeTile]

private theorem readTile_writeTile (s : TpuCoreState) (addr query : TileAddr) (v : Tile)
    (h : tileBound s addr) :
    readTile (writeTile s addr v) query = if query = addr then some v else readTile s query := by
  cases addr with | mk space index =>
    cases query with | mk qs qi =>
      cases space <;> cases qs <;> simp_all [tileBound, writeTile, readTile, Array.getElem?_setIfInBounds, TileAddr.mk.injEq] <;>
        split <;> simp_all [eq_comm]

private theorem DmaSim.bound_iff (h : DmaSim s t a) (addr : TileAddr) :
    tileBound s addr ↔ tileBound t addr := by
  cases addr with | mk space index =>
    cases space <;> simp [tileBound, h.hbmSize, h.vmemSize]

private theorem erase_count (ds : List DmaDescriptor) (i : Nat) (d : DmaDescriptor)
    (hi : ds[i]? = some d) (k : Nat) :
    outstanding ds k = outstanding (ds.eraseIdx i) k + if d.semaphore == k then 1 else 0 := by
  induction ds generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hi; subst d
              simp [outstanding, List.countP_cons]
    | succ i =>
      simp only [List.getElem?_cons_succ] at hi
      have hh := ih i hi
      simp only [outstanding, List.eraseIdx_cons_succ, List.countP_cons] at *
      omega

private theorem erase_members (ds : List DmaDescriptor) (i : Nat) (d : DmaDescriptor)
    (hi : ds[i]? = some d) (x : DmaDescriptor) :
    x ∈ ds ↔ x = d ∨ x ∈ ds.eraseIdx i := by
  induction ds generalizing i with
  | nil => simp at hi
  | cons y ys ih =>
    cases i with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hi; subst d; simp
    | succ i =>
      simp only [List.getElem?_cons_succ] at hi
      simp only [List.mem_cons, List.eraseIdx_cons_succ, ih i hi]
      rw [or_left_comm]

/-- Arbitrary legal retirement preserves both the committed memory and credits. -/
theorem DmaSim.retire (h : DmaSim s t a) (idx : Nat) (hi : idx < s.dma.length) :
    DmaSim (retireDma s idx) t a := by
  let d := s.dma[idx]
  have hd : s.dma[idx]? = some d := List.getElem?_eq_getElem hi
  have hm : d ∈ s.dma := List.getElem_mem hi
  have hb : tileBound s d.destination := (h.bound_iff d.destination).mpr
    (readTile_bound t d.destination d.payload (h.committed d hm))
  have fields := writeTile_fields s d.destination d.payload hb
  have hf : retireDma s idx =
      { writeTile s d.destination d.payload with
        dma := s.dma.eraseIdx idx
        semaphores := s.semaphores.modify d.semaphore (· + 1) } := by
    simp [retireDma, h.healthy, hd]
  rw [hf]
  refine ⟨?_, h.syncHealthy, h.syncEmpty, ?_, ?_, ?_, ?_, ?_, h.syncCredits,
    ?_, ?_, ?_, ?_, ?_⟩
  · exact fields.2.2.2.2.2.2.trans h.healthy
  · exact fields.1.trans h.hbmSize
  · exact fields.2.1.trans h.vmemSize
  · exact fields.2.2.1.trans h.scalar
  · exact fields.2.2.2.1.trans h.vector
  · simpa using h.semSize
  · intro k
    have hc := h.credits k
    have he := erase_count s.dma idx d hd k
    have hbsem : d.semaphore < s.semaphores.size := by rw [h.semSize]; exact h.semBound d hm
    dsimp only
    rw [credit_modify _ _ _ _ hbsem]
    by_cases hk : k = d.semaphore
    · subst k; simp at he ⊢; omega
    · have hk' : d.semaphore ≠ k := Ne.symm hk
      simp [hk, hk'] at he ⊢; omega
  · intro x hx; exact h.covered x ((erase_members s.dma idx d hd x).mpr (Or.inr hx))
  · intro x hx; exact h.semBound x ((erase_members s.dma idx d hd x).mpr (Or.inr hx))
  · intro x hx; exact h.committed x ((erase_members s.dma idx d hd x).mpr (Or.inr hx))
  · intro addr hn
    change readTile (writeTile s d.destination d.payload) addr = readTile t addr
    rw [readTile_writeTile _ _ _ _ hb]
    split
    · rename_i he; subst addr; exact (h.committed d hm).symm
    · rename_i he
      exact h.unchanged addr (fun x hx => by
        rcases (erase_members s.dma idx d hd x).mp hx with hx | hx
        · subst x; exact he
        · exact hn x hx)

/-- Enough credits imply enough completed transfers after a blocking wait.
The queue-length fuel bounds every possible sequence of forced retirements. -/
theorem DmaSim.wait_ready (h : DmaSim s t a) (sem count fuel : Nat)
    (hc : count ≤ credit a.credits sem) (hf : s.dma.length ≤ fuel) :
    DmaSim (retireSemaphore fuel s sem count) t a ∧
    count ≤ credit (retireSemaphore fuel s sem count).semaphores sem := by
  induction fuel generalizing s with
  | zero =>
    have hd : s.dma = [] := List.length_eq_zero_iff.mp (by omega)
    have he := h.credits sem
    simp only [hd, outstanding, List.countP_nil, Nat.add_zero] at he
    exact ⟨h, by simpa only [retireSemaphore, he] using hc⟩
  | succ fuel ih =>
    rw [retireSemaphore]
    split
    · rename_i he; exact ⟨h, by simpa only [credit_bang] using he⟩
    · rename_i he
      cases hx : s.dma.findIdx? (fun d => d.semaphore == sem) with
      | none =>
        have hz : outstanding s.dma sem = 0 := by
          apply List.countP_eq_zero.mpr
          simpa only [Bool.not_eq_true] using List.findIdx?_eq_none_iff.mp hx
        have hh := h.credits sem
        simp only [hz, Nat.add_zero, credit_bang] at hh
        rw [credit_bang] at hc
        exact False.elim (he (by omega))
      | some i =>
        have hi := (List.findIdx?_eq_some_iff_getElem.mp hx).choose
        have hs := h.retire i hi
        have hl : (retireDma s i).dma.length < s.dma.length := by
          simp [retireDma, h.healthy, List.length_eraseIdx, hi]
          omega
        exact ih hs (by omega)

private theorem DmaSim.write (h : DmaSim s t a) (addr : TileAddr) (v : Tile)
    (hb : tileBound s addr) (hn : ∀ d ∈ s.dma, addr ≠ d.destination) :
    DmaSim (writeTile s addr v) (writeTile t addr v) a := by
  have hb' := (h.bound_iff addr).mp hb
  rcases writeTile_fields s addr v hb with ⟨sh, sv, ss, sr, sd, sc, se⟩
  rcases writeTile_fields t addr v hb' with ⟨th, tv, ts, tr, td, tc, te⟩
  refine ⟨se.trans h.healthy, te.trans h.syncHealthy, td.trans h.syncEmpty,
    sh.trans (h.hbmSize.trans th.symm), sv.trans (h.vmemSize.trans tv.symm),
    ss.trans (h.scalar.trans ts.symm), sr.trans (h.vector.trans tr.symm),
    ?_, tc.trans h.syncCredits, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [sc] using h.semSize
  · simpa only [sc, sd] using h.credits
  · simpa only [sd] using h.covered
  · simpa only [sd] using h.semBound
  · intro d hd; rw [sd] at hd
    rw [readTile_writeTile _ _ _ _ hb', ite_eq_right (Ne.symm (hn d hd))]
    exact h.committed d hd
  · intro q hq
    rw [sd] at hq
    rw [readTile_writeTile _ _ _ _ hb, readTile_writeTile _ _ _ _ hb']
    split
    · rfl
    · exact h.unchanged q hq

private theorem DmaSim.registers (h : DmaSim s t a) (scalars : Array UInt64) (vectors : Array VReg) :
    DmaSim { s with smem := scalars, vreg := vectors }
      { t with smem := scalars, vreg := vectors } a :=
  { h with scalar := rfl, vector := rfl }

private theorem DmaSim.signal (h : DmaSim s t a) (sem count : Nat) (hb : sem < a.credits.size) :
    DmaSim { s with semaphores := s.semaphores.modify sem (· + count) }
      { t with semaphores := t.semaphores.modify sem (· + count) }
      { a with credits := a.credits.modify sem (· + count) } := by
  refine { h with
    semSize := by simpa using h.semSize
    syncCredits := by simp only [h.syncCredits]
    credits := ?_
    semBound := by simpa using h.semBound }
  intro k
  have hb' : sem < s.semaphores.size := by simpa only [h.semSize] using hb
  dsimp only
  rw [credit_modify _ _ _ _ hb, credit_modify _ _ _ _ hb']
  have hh := h.credits k
  split <;> omega

/-- Consuming all abstract credits removes every matching concrete descriptor;
partial waits conservatively retain the abstract footprints. -/
private theorem DmaSim.consume (h : DmaSim s t a) (sem count : Nat)
    (hb : sem < a.credits.size) (hc : count ≤ credit s.semaphores sem) :
    DmaSim { s with semaphores := s.semaphores.modify sem (· - count) }
      { t with semaphores := t.semaphores.modify sem (· - count) }
      { pending := if count == a.credits[sem]! then a.pending.filter (fun d => d.semaphore != sem) else a.pending
        credits := a.credits.modify sem (· - count) } := by
  refine { h with
    semSize := by simpa using h.semSize
    syncCredits := by simp only [h.syncCredits]
    credits := ?_
    covered := ?_
    semBound := by simpa using h.semBound }
  · intro k
    have hb' : sem < s.semaphores.size := by simpa only [h.semSize] using hb
    dsimp only
    rw [credit_modify _ _ _ _ hb, credit_modify _ _ _ _ hb']
    have hh := h.credits k
    split
    · rename_i hk; subst k; omega
    · exact hh
  · intro d hd
    dsimp only
    split
    · rename_i he
      have hh := h.credits sem
      have hz : outstanding s.dma sem = 0 := by
        have he' : count = credit a.credits sem := by simpa only [beq_iff_eq, credit_bang] using he
        omega
      have hn := List.countP_eq_zero.mp hz d hd
      simp only [List.mem_filter]
      exact ⟨h.covered d hd, by simpa [DmaDescriptor.footprint] using hn⟩
    · exact h.covered d hd

private theorem DmaSim.hazard (h : DmaSim s t a) (reads writes : Array TileAddr)
    (hc : footprintHazard a.pending reads writes = false) : dmaHazard s.dma reads writes = false := by
  simp only [footprintHazard, List.any_eq_false] at hc
  simp only [dmaHazard, List.any_eq_false]
  intro d hd
  exact hc d.footprint (h.covered d hd)

private theorem DmaSim.avoids (h : DmaSim s t a) (reads writes : Array TileAddr)
    (hc : footprintHazard a.pending reads writes = false) (addr : TileAddr)
    (ha : addr ∈ reads ∨ addr ∈ writes) : ∀ d ∈ s.dma, addr ≠ d.destination := by
  have hh := h.hazard reads writes hc
  simp only [dmaHazard, List.any_eq_false] at hh
  intro d hd he
  have hh' := hh d hd
  rcases ha with ha | ha <;> subst addr <;> simp_all

private theorem DmaSim.enqueue (h : DmaSim s t a) (src dst : TileAddr) (sem : Nat) (value : Tile)
    (hb : tileBound s dst) (hs : sem < a.credits.size)
    (hn : ∀ d ∈ s.dma, dst ≠ d.destination) :
    DmaSim { s with dma := s.dma ++ [⟨src,dst,sem,value⟩] }
      { writeTile t dst value with semaphores := t.semaphores.modify sem (· + 1) }
      { pending := a.pending ++ [⟨src,dst,sem⟩], credits := a.credits.modify sem (· + 1) } := by
  have hb' := (h.bound_iff dst).mp hb
  rcases writeTile_fields t dst value hb' with ⟨th, tv, ts, tr, td, tc, te⟩
  refine ⟨h.healthy, te.trans h.syncHealthy, td.trans h.syncEmpty,
    h.hbmSize.trans th.symm, h.vmemSize.trans tv.symm, h.scalar.trans ts.symm,
    h.vector.trans tr.symm, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using h.semSize
  · simp only [h.syncCredits]
  · intro k
    dsimp only
    rw [credit_modify _ _ _ _ hs]
    have hh := h.credits k
    simp only [outstanding, List.countP_append, List.countP_cons, List.countP_nil] at *
    by_cases hk : k = sem
    · subst k; simp; omega
    · have hk' := Ne.symm hk; simp [hk, hk']; exact hh
  · intro d hd
    rcases List.mem_append.mp hd with hd | hd
    · exact List.mem_append_left _ (h.covered d hd)
    · simp only [List.mem_singleton] at hd; subst d; simp [DmaDescriptor.footprint]
  · intro d hd
    rcases List.mem_append.mp hd with hd | hd
    · simpa using h.semBound d hd
    · simp only [List.mem_singleton] at hd; subst d; simpa using hs
  · intro d hd
    change readTile (writeTile t dst value) d.destination = some d.payload
    rw [readTile_writeTile _ _ _ _ hb']
    rcases List.mem_append.mp hd with hd | hd
    · rw [ite_eq_right (Ne.symm (hn d hd))]; exact h.committed d hd
    · simp only [List.mem_singleton] at hd; subst d; simp
  · intro addr ha
    change readTile s addr = readTile (writeTile t dst value) addr
    have hn' : addr ≠ dst := ha ⟨src,dst,sem,value⟩ (by simp)
    rw [readTile_writeTile _ _ _ _ hb', ite_eq_right hn']
    exact h.unchanged addr (fun d hd => ha d (List.mem_append_left _ hd))

private theorem DmaSim.drained (h : DmaSim s t a)
    (hp : a.pending.isEmpty = true) : s = t := by
  have hpn : a.pending = [] := List.isEmpty_iff.mp hp
  have hd : s.dma = [] := List.eq_nil_iff_forall_not_mem.mpr (by
    intro d hm; have := h.covered d hm; simp [hpn] at this)
  have hm : ∀ addr, readTile s addr = readTile t addr := fun addr =>
    h.unchanged addr (by simp [hd])
  have hhbm : s.hbm = t.hbm := Array.ext_getElem? (fun i => hm ⟨.hbm,i⟩)
  have hvmem : s.vmem = t.vmem := Array.ext_getElem? (fun i => hm ⟨.vmem,i⟩)
  have hsem : s.semaphores = t.semaphores := by
    apply Array.ext (h.semSize.trans (congrArg Array.size h.syncCredits).symm)
    intro i hi hj
    have hh := h.credits i
    simp only [hd, outstanding, List.countP_nil, Nat.add_zero, credit] at hh
    have ha : i < a.credits.size := by simpa only [h.semSize] using hi
    simp only [Array.getElem?_eq_getElem hi, Array.getElem?_eq_getElem ha, Option.getD_some] at hh
    simpa only [h.syncCredits] using hh.symm
  have hsc := h.scalar
  have hvr := h.vector
  have hdm := hd.trans h.syncEmpty.symm
  have her := h.healthy.trans h.syncHealthy.symm
  cases s; cases t
  simp only [TpuCoreState.mk.injEq]
  exact ⟨hhbm, hvmem, hsc, hvr, hdm, hsem, her⟩

@[simp] theorem dmaHazard_nil (reads writes : Array TileAddr) :
    dmaHazard [] reads writes = false := by simp [dmaHazard]

private theorem DmaSim.step (h : DmaSim s t a) (i : TpuInstr)
    (hb : InstrBound s i) (ha : analyzeStep a i = some b) :
    DmaSim (stepAsync s i) (stepSync t i) b := by
  cases i with
  | dma src dst sem =>
    rcases hb with ⟨hsrc, hdst, hsem⟩
    simp only [analyzeStep] at ha
    split at ha
    · contradiction
    · rename_i hz
      simp only [Bool.or_eq_true, not_or, beq_iff_eq, decide_eq_true_eq, Nat.not_le,
        Bool.not_eq_true] at hz
      rcases hz with ⟨⟨hspace, hs⟩, hh⟩
      cases ha
      have hn := h.avoids #[src] #[dst] hh dst (Or.inr (by simp))
      have hread := h.unchanged src (h.avoids #[src] #[dst] hh src (Or.inl (by simp)))
      have hdr : ∃ v, readTile s src = some v := by
        cases src with | mk space index =>
          cases space <;> simp only [tileBound, readTile] at * <;>
            exact ⟨_, Array.getElem?_eq_getElem hsrc⟩
      obtain ⟨v,hv⟩ := hdr
      have hv' : readTile t src = some v := hread.symm.trans hv
      have hds : (readTile s dst).isSome = true := by
        cases dst with | mk space index => cases space <;> simp_all [tileBound, readTile]
      have hdt : (readTile t dst).isSome = true := by
        have hh := (h.bound_iff dst).mp hdst
        cases dst with | mk space index => cases space <;> simp_all [tileBound, readTile]
      have hdest := Option.isSome_iff_exists.mp hds
      have hdest' := Option.isSome_iff_exists.mp hdt
      obtain ⟨vds,hvds⟩ := hdest
      obtain ⟨vdt,hvdt⟩ := hdest'
      have hzrun := h.hazard #[src] #[dst] hh
      have henqueue := h.enqueue src dst sem v hdst hs hn
      cases dst with | mk space index =>
        cases space <;> simp only [tileBound] at hdst
        all_goals simpa [stepAsync, stepSync, stepBody, h.healthy, h.syncHealthy, h.syncEmpty,
          hspace, Nat.not_le.mpr hsem, Nat.not_le.mpr hs, h.syncCredits, hzrun, dmaHazard_nil,
          hv, hv', hvds, hvdt, retireDma, writeTile, ← h.hbmSize, ← h.vmemSize, hdst] using
          henqueue

  | wait sem count =>
    change sem < s.semaphores.size at hb
    simp only [analyzeStep] at ha
    split at ha
    · rename_i hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      cases ha
      obtain ⟨hw, hready⟩ := h.wait_ready sem count s.dma.length (by simpa only [credit_bang] using hc.2) (by omega)
      have hcons := hw.consume sem count hc.1 hready
      have hr : count ≤ (retireSemaphore s.dma.length s sem count).semaphores[sem]! := by
        simpa only [credit_bang] using hready
      simpa [stepAsync, stepSync, stepBody, h.healthy, h.syncHealthy, h.syncEmpty,
        h.syncCredits, Nat.not_le.mpr hc.1, hc.2, Nat.not_le.mpr hb, hr, retireSemaphore] using hcons
    · contradiction
  | signal sem count =>
    simp only [analyzeStep] at ha
    split at ha
    · rename_i hs; cases ha
      simpa [stepAsync, stepSync, stepBody, h.healthy, h.syncHealthy, h.syncCredits,
        hs, show sem < s.semaphores.size from hb] using h.signal sem count hs
    · contradiction
  | mxu mode dst lhs rhs =>
    rcases hb with ⟨hd,hl,hr⟩
    simp only [analyzeStep] at ha
    split at ha
    · contradiction
    · rename_i hz; have hz := Bool.eq_false_iff.mpr hz; cases ha
      have hlr := h.unchanged ⟨.vmem,lhs⟩ (h.avoids _ _ hz _ (Or.inl (by simp)))
      have hrr := h.unchanged ⟨.vmem,rhs⟩ (h.avoids _ _ hz _ (Or.inl (by simp)))
      have hn := h.avoids _ _ hz ⟨.vmem,dst⟩ (Or.inr (by simp))
      have hh := h.hazard _ _ hz
      simp only [readTile] at hlr hrr
      simpa [stepAsync, stepSync, stepBody, h.healthy, h.syncHealthy, h.syncEmpty,
        dmaHazard_nil, hh, ← hlr, ← hrr, hl, hr] using
        h.write ⟨.vmem,dst⟩ (mxuTile mode s.vmem[lhs] s.vmem[rhs]) hd hn
  | transpose dst src =>
    rcases hb with ⟨hd,hs⟩
    simp only [analyzeStep] at ha
    split at ha
    · contradiction
    · rename_i hz; have hz := Bool.eq_false_iff.mpr hz; cases ha
      have hsr := h.unchanged ⟨.vmem,src⟩ (h.avoids _ _ hz _ (Or.inl (by simp)))
      have hn := h.avoids _ _ hz ⟨.vmem,dst⟩ (Or.inr (by simp))
      have hh := h.hazard _ _ hz
      simp only [readTile] at hsr
      simpa [stepAsync, stepSync, stepBody, h.healthy, h.syncHealthy, h.syncEmpty,
        dmaHazard_nil, hh, ← hsr, hs] using h.write ⟨.vmem,dst⟩ (transposeTile s.vmem[src]) hd hn
  | vpu op dst lhs rhs =>
    rcases hb with ⟨hd,hl,hr⟩
    simp only [analyzeStep, Option.some.injEq] at ha; subst b
    simpa [stepAsync, stepSync, stepBody, h.healthy, h.syncHealthy, ← h.vector, ← h.scalar,
      hl,hr,hd] using h.registers s.smem
        (s.vreg.set! dst (Sized.ofFn fun j => evalVpu op (s.vreg[lhs].spec j) (s.vreg[rhs].spec j)))
  | loadVReg dst tile block =>
    rcases hb with ⟨hd,ht,hblock⟩
    simp only [analyzeStep] at ha
    split at ha
    · contradiction
    · rename_i hz
      have hz : footprintHazard a.pending #[⟨.vmem,tile⟩] #[] = false := by simpa [hblock] using hz
      cases ha
      have he := h.unchanged ⟨.vmem,tile⟩ (h.avoids _ _ hz _ (Or.inl (by simp)))
      have hh := h.hazard _ _ hz
      simp only [readTile] at he
      simpa [stepAsync, stepSync, stepBody, h.healthy, h.syncHealthy, h.syncEmpty,
        dmaHazard_nil, hh, ← he, ht, hd, hblock, ← h.vector, ← h.scalar] using
        h.registers s.smem (s.vreg.set! dst (Sized.ofFn fun j => s.vmem[tile].coeffs[block*1024+j.val]!))
  | storeVReg tile block src =>
    rcases hb with ⟨ht,hblock,hs⟩
    simp only [analyzeStep] at ha
    split at ha
    · contradiction
    · rename_i hz
      have hz : footprintHazard a.pending #[] #[⟨.vmem,tile⟩] = false := by simpa [hblock] using hz
      cases ha
      have hn := h.avoids _ _ hz ⟨.vmem,tile⟩ (Or.inr (by simp))
      have he := h.unchanged ⟨.vmem,tile⟩ hn
      have hh := h.hazard _ _ hz
      simp only [readTile] at he
      simpa [stepAsync, stepSync, stepBody, h.healthy, h.syncHealthy, h.syncEmpty,
        dmaHazard_nil, hh, ← he, ht, hs, hblock, ← h.vector] using
        h.write ⟨.vmem,tile⟩ (Sized.ofFn fun j =>
          if j.val/1024 == block then s.vreg[src].coeffs[j.val%1024]! else s.vmem[tile].spec j) ht hn
  | permute dst src lanes =>
    rcases hb with ⟨hd,hs,hsize,hall⟩
    have hh : (lanes.size == 128 && lanes.all (· < 128)) = true := by
      simp only [Bool.and_eq_true, beq_iff_eq]
      refine ⟨hsize, Array.all_eq_true.mpr ?_⟩
      intro j hj; simpa using hall lanes[j] (Array.getElem_mem hj)
    simp only [analyzeStep, hh, ite_eq_left, Option.some.injEq] at ha; subst b
    simpa [stepAsync, stepSync, stepBody, h.healthy, h.syncHealthy, hh,
      hd, hs, ← h.vector, ← h.scalar] using
        h.registers s.smem (s.vreg.set! dst (Sized.ofFn fun j =>
          s.vreg[src].coeffs[j.val/128*128+lanes[j.val%128]!]!))
  | fillVReg dst value =>
    simp only [analyzeStep, Option.some.injEq] at ha; subst b
    simpa [stepAsync, stepSync, stepBody, h.healthy, h.syncHealthy,
      show dst < s.vreg.size from hb, ← h.vector, ← h.scalar] using
        h.registers s.smem (s.vreg.set! dst (Sized.ofFn fun _ => value))
  | scalar dst value =>
    simp only [analyzeStep, Option.some.injEq] at ha; subst b
    simpa [stepAsync, stepSync, stepBody, h.healthy, h.syncHealthy,
      show dst < s.smem.size from hb, ← h.vector, ← h.scalar] using
        h.registers (s.smem.set! dst value) s.vreg
  | finish =>
    simp only [analyzeStep] at ha
    split at ha
    · rename_i hc; cases ha
      simp only [Bool.and_eq_true] at hc
      have he := h.drained hc.1
      have he' := he
      have hd : s.dma = [] := he ▸ h.syncEmpty
      have hs : s.semaphores = a.credits := he ▸ h.syncCredits
      have hz : s.semaphores.any (· != 0) = false := by
        simp only [Array.all_eq_true, beq_iff_eq] at hc
        simp only [hs, Array.any_eq_false]
        intro j hj; simp [hc.2 j hj]
      simpa [stepAsync, stepSync, stepBody, h.healthy, h.syncHealthy, ← he', hd, hz] using h
    · contradiction

/-- Allocation sizes are stable even when an instruction traps. -/
def allocation (s : TpuCoreState) : Nat × Nat × Nat × Nat × Nat :=
  (s.hbm.size, s.vmem.size, s.smem.size, s.vreg.size, s.semaphores.size)

private theorem allocation_trap (s : TpuCoreState) (e : TpuTrap) : allocation (trap s e) = allocation s := by
  unfold trap; split <;> rfl

private theorem allocation_write (s : TpuCoreState) (a : TileAddr) (v : Tile) :
    allocation (writeTile s a v) = allocation s := by
  cases a with | mk space index =>
    cases space <;> simp only [writeTile] <;> split
    all_goals first | exact allocation_trap _ _ | simp [allocation]

private theorem allocation_retire (s : TpuCoreState) (i : Nat) :
    allocation (retireDma s i) = allocation s := by
  unfold retireDma
  split
  · rfl
  · split
    · exact allocation_trap _ _
    · rename_i d hd
      have hw := allocation_write s d.destination d.payload
      simp only [allocation, Prod.mk.injEq] at hw ⊢
      exact ⟨hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1, Array.size_modify⟩

private theorem allocation_wait (n : Nat) (s : TpuCoreState) (sem count : Nat) :
    allocation (retireSemaphore n s sem count) = allocation s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    unfold retireSemaphore
    split
    · rfl
    · split
      · rfl
      · exact (ih _).trans (allocation_retire _ _)

private theorem allocation_stepBody (s : TpuCoreState) (i : TpuInstr) :
    allocation (stepBody s i) = allocation s := by
  have hw := allocation_wait s.dma.length s
  cases i <;> simp only [stepBody]
  all_goals repeat' first
    | exact allocation_trap _ _
    | exact allocation_write _ _ _
    | exact hw _ _
    | exact (allocation_trap _ _).trans (hw _ _)
    | rfl
    | split
  all_goals simp [allocation]
  all_goals rename_i sem count hbound hcount
  all_goals simpa only [allocation, Prod.mk.injEq] using hw sem count

private theorem allocation_step (s : TpuCoreState) (i : TpuInstr) :
    allocation (stepAsync s i) = allocation s := by
  unfold stepAsync; split
  · rfl
  · exact allocation_stepBody _ _

private theorem InstrBound.of_allocation (h : allocation s = allocation t)
    (hb : InstrBound s i) : InstrBound t i := by
  simp only [allocation, Prod.mk.injEq] at h
  cases i <;> simp_all [InstrBound, tileBound]

/-- Instruction projection ignores all DMA retirement events. -/
def TpuEvent.instruction? : TpuEvent → Option TpuInstr
  | .instruction i => some i
  | .retire _ => none

private theorem DmaSim.trace (h : DmaSim s t a) (trace : List TpuEvent) (p : TpuProg)
    (legal : ValidTrace s trace) (project : trace.filterMap TpuEvent.instruction? = p)
    (bounds : ∀ i ∈ p, InstrBound s i) (checked : analyzeProgram a p = some b) :
    (runEvents s trace).error = none ∧ runEvents s trace = runSync t p := by
  induction legal generalizing t a p with
  | nil s =>
    simp only [List.filterMap_nil] at project; subst p
    have hp := (analyzeStep_finish_drained a b checked).1
    exact ⟨h.healthy, h.drained hp⟩
  | instruction s i rest legal ih =>
    simp only [List.filterMap_cons, TpuEvent.instruction?] at project
    subst p
    rw [analyzeProgram_cons] at checked
    cases ha : analyzeStep a i with
    | none => simp [ha] at checked
    | some next =>
      simp only [ha, Option.bind_some] at checked
      have hs := h.step i (bounds i (by simp)) ha
      have ht := ih hs (rest.filterMap TpuEvent.instruction?) rfl
        (fun j hj => InstrBound.of_allocation (allocation_step s i).symm (bounds j (by simp [hj]))) checked
      simpa only [runEvents, List.foldl_cons, eventStep, runSync] using ht
  | retire s idx rest hi healthy legal ih =>
    simp only [List.filterMap_cons, TpuEvent.instruction?] at project
    have ht := ih (h.retire idx hi) p project
      (fun j hj => InstrBound.of_allocation (allocation_retire s idx).symm (bounds j hj)) checked
    simpa only [runEvents, List.foldl_cons, eventStep] using ht

/-- Every legal retirement schedule for an accepted, allocated program is
fault-free and terminates in exactly the synchronous state, including DMA and
semaphore resources. The proof covers the entire instruction/event trace. -/
theorem checkDmaSemaphores_async_refines_sync (s₀ : TpuCoreState) (p : TpuProg)
    (trace : List TpuEvent) (sized : WellSized s₀ p)
    (checked : checkDmaSemaphores s₀.semaphores.size p = true)
    (legal : ValidTrace s₀ trace) (project : trace.filterMap TpuEvent.instruction? = p) :
    (runEvents s₀ trace).error = none ∧ runEvents s₀ trace = runSync s₀ p := by
  have initial : DmaSim s₀ s₀ ⟨[], Array.replicate s₀.semaphores.size 0⟩ := by
    refine ⟨sized.healthy, sized.healthy, sized.empty, rfl, rfl, rfl, rfl,
      by simp, sized.zero, ?_, ?_, ?_, ?_, ?_⟩
    · intro k; simp only [← sized.zero, sized.empty, outstanding, List.countP_nil, Nat.add_zero]
    · simp [sized.empty]
    · simp [sized.empty]
    · simp [sized.empty]
    · intro addr _; rfl
  unfold checkDmaSemaphores at checked
  obtain ⟨b,hb⟩ := Option.isSome_iff_exists.mp checked
  exact initial.trace trace p legal project sized.bounds hb

/-! Decidable allocation bounds for `WellSized`, and the VMEM frame of a synchronous run. -/

def checkTileBound (hbmSize vmemSize : Nat) (a : TileAddr) : Bool :=
  match a.space with
  | .hbm => a.index < hbmSize
  | .vmem => a.index < vmemSize

/-- `InstrBound` against explicit resource sizes. -/
def checkInstrBounds (hbmSize vmemSize smemSize vregSize semSize : Nat) : TpuInstr → Bool
  | .dma src dst sem => checkTileBound hbmSize vmemSize src && checkTileBound hbmSize vmemSize dst && sem < semSize
  | .wait sem _ | .signal sem _ => sem < semSize
  | .mxu _ dst lhs rhs => dst < vmemSize && lhs < vmemSize && rhs < vmemSize
  | .transpose dst src => dst < vmemSize && src < vmemSize
  | .vpu _ dst lhs rhs => dst < vregSize && lhs < vregSize && rhs < vregSize
  | .loadVReg dst tile block => dst < vregSize && tile < vmemSize && block < 16
  | .storeVReg tile block src => tile < vmemSize && block < 16 && src < vregSize
  | .permute dst src lanes => dst < vregSize && src < vregSize && lanes.size == 128 && lanes.all (· < 128)
  | .fillVReg dst _ => dst < vregSize
  | .scalar dst _ => dst < smemSize
  | .finish => true

/-- Every instruction of `p` stays inside the given HBM, VMEM, scalar, VREG and semaphore allocations. -/
def checkProgramBounds (hbmSize vmemSize smemSize vregSize semSize : Nat) (p : TpuProg) : Bool :=
  p.all (checkInstrBounds hbmSize vmemSize smemSize vregSize semSize)

example : checkInstrBounds 1 3 0 1 1 (.transpose 2 0) = true := by decide
example : checkProgramBounds 2 3 0 2 2 [.mxu .unsigned8 2 0 1, .loadVReg 1 2 15, .finish] = true := by decide

theorem checkInstrBounds_sound (s : TpuCoreState) (i : TpuInstr)
    (h : checkInstrBounds s.hbm.size s.vmem.size s.smem.size s.vreg.size s.semaphores.size i = true) :
    InstrBound s i := by
  cases i with
  | dma src dst sem =>
    cases src with | mk ss si => cases dst with | mk ds di =>
      cases ss <;> cases ds <;> simp_all [checkInstrBounds, checkTileBound, InstrBound, tileBound]
  | permute dst src lanes =>
    simp_all [checkInstrBounds, InstrBound]
    intro x hx; obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hx; exact h.2 i hi
  | _ => simp_all [checkInstrBounds, InstrBound]

/-- **The decidable bounds check establishes `WellSized`** for a healthy state with no pending DMA, zero
semaphores, and the sizes the check was run against. -/
theorem checkProgramBounds_sound (s₀ : TpuCoreState) (p : TpuProg) (healthy : s₀.error = none) (empty : s₀.dma = [])
    (zero : s₀.semaphores = Array.replicate s₀.semaphores.size 0)
    (h : checkProgramBounds s₀.hbm.size s₀.vmem.size s₀.smem.size s₀.vreg.size s₀.semaphores.size p = true) :
    WellSized s₀ p :=
  ⟨healthy, empty, zero, fun i hi => checkInstrBounds_sound s₀ i (List.all_eq_true.mp h i hi)⟩

theorem checkProgramBounds_initial (hbmTiles vmemTiles scalarRegs vectorRegs semaphoreCount : Nat) (p : TpuProg)
    (h : checkProgramBounds hbmTiles vmemTiles scalarRegs vectorRegs semaphoreCount p = true) :
    WellSized (TpuCoreState.initial hbmTiles vmemTiles scalarRegs vectorRegs semaphoreCount) p :=
  checkProgramBounds_sound _ p rfl rfl (by simp [TpuCoreState.initial]) (by simpa [TpuCoreState.initial] using h)

/-- From a freshly allocated core, a program that passes the bounds check and the DMA/semaphore analysis is
fault-free under every legal retirement schedule and ends in the synchronous state. -/
theorem checkedProgram_async_refines_sync (hbmTiles vmemTiles scalarRegs vectorRegs semaphoreCount : Nat)
    (p : TpuProg) (trace : List TpuEvent)
    (bounds : checkProgramBounds hbmTiles vmemTiles scalarRegs vectorRegs semaphoreCount p = true)
    (checked : checkDmaSemaphores semaphoreCount p = true)
    (legal : ValidTrace (TpuCoreState.initial hbmTiles vmemTiles scalarRegs vectorRegs semaphoreCount) trace)
    (project : trace.filterMap TpuEvent.instruction? = p) :
    (runEvents (TpuCoreState.initial hbmTiles vmemTiles scalarRegs vectorRegs semaphoreCount) trace).error = none ∧
    runEvents (TpuCoreState.initial hbmTiles vmemTiles scalarRegs vectorRegs semaphoreCount) trace =
      runSync (TpuCoreState.initial hbmTiles vmemTiles scalarRegs vectorRegs semaphoreCount) p :=
  checkDmaSemaphores_async_refines_sync _ p trace (checkProgramBounds_initial _ _ _ _ _ p bounds)
    (by simpa [TpuCoreState.initial] using checked) legal project

/-- Whether running `i` synchronously may write VMEM tile `t`. A DMA or a wait may retire a descriptor into any
tile; the MXU, the transposer and a VREG store write their destination. -/
def TpuInstr.mayWriteVmem (t : Nat) : TpuInstr → Bool
  | .dma _ _ _ | .wait _ _ => true
  | .mxu _ dst _ _ | .transpose dst _ | .storeVReg dst _ _ => dst == t
  | _ => false

private theorem trap_vmem (s : TpuCoreState) (e : TpuTrap) : (trap s e).vmem = s.vmem := by
  unfold trap; split <;> rfl

private theorem writeTile_vmem_ne (s : TpuCoreState) (dst t : Nat) (v : Tile) (h : dst ≠ t) :
    (writeTile s ⟨.vmem, dst⟩ v).vmem[t]? = s.vmem[t]? := by
  simp only [writeTile]; split
  · simp [h]
  · rw [trap_vmem]

/-- **VMEM frame of one synchronous step**: a tile the instruction cannot write is unchanged, fault or not. -/
theorem stepSync_vmem_frame (s : TpuCoreState) (i : TpuInstr) (t : Nat) (h : i.mayWriteVmem t = false) :
    (stepSync s i).vmem[t]? = s.vmem[t]? := by
  have hAsync : ∀ j : TpuInstr, j.mayWriteVmem t = false → (stepAsync s j).vmem[t]? = s.vmem[t]? := by
    intro j hj; unfold stepAsync; split
    · rfl
    · cases j with
      | dma _ _ _ => simp [TpuInstr.mayWriteVmem] at hj
      | wait _ _ => simp [TpuInstr.mayWriteVmem] at hj
      | mxu m dst a b =>
        have hne : dst ≠ t := by simpa [TpuInstr.mayWriteVmem] using hj
        simp only [stepBody]; repeat' split
        all_goals first | rw [trap_vmem] | exact writeTile_vmem_ne _ _ _ _ hne
      | transpose dst src =>
        have hne : dst ≠ t := by simpa [TpuInstr.mayWriteVmem] using hj
        simp only [stepBody]; repeat' split
        all_goals first | rw [trap_vmem] | exact writeTile_vmem_ne _ _ _ _ hne
      | storeVReg dst blk src =>
        have hne : dst ≠ t := by simpa [TpuInstr.mayWriteVmem] using hj
        simp only [stepBody]; repeat' split
        all_goals first | rw [trap_vmem] | exact writeTile_vmem_ne _ _ _ _ hne
      | _ =>
        simp only [stepBody]; repeat' split
        all_goals first | rfl | rw [trap_vmem]
  cases i with
  | dma _ _ _ => simp [TpuInstr.mayWriteVmem] at h
  | _ => exact hAsync _ h

/-- **VMEM frame of a synchronous run**: a tile no instruction of the program can write is unchanged. -/
theorem runSync_vmem_frame (s : TpuCoreState) (p : TpuProg) (t : Nat) (h : ∀ i ∈ p, i.mayWriteVmem t = false) :
    (runSync s p).vmem[t]? = s.vmem[t]? := by
  induction p generalizing s with
  | nil => rfl
  | cons i rest ih =>
    simp only [runSync, List.foldl_cons]
    exact (ih (stepSync s i) (fun j hj => h j (List.mem_cons_of_mem _ hj))).trans
      (stepSync_vmem_frame s i t (h i List.mem_cons_self))

end Obend.Hardware.Tpu
