module
public import Obend.Hardware.ArrayKernel
public import Obend.Hardware.Gpu.GoldilocksSource
@[expose] public section

namespace Obend.Hardware.Gpu.Ntt
open Obend.Hardware.OpenHypergraph Obend.Hardware.ArrayHypergraph
open Obend.Hardware.ArrayBuild Obend.Hardware.Gpu.GoldilocksSource

/-! ## The NTT -/

/-- Binary modular exponentiation. The exponent decreases by a factor of two;
the zero case preserves the previous implementation's value even at modulus one. -/
def powMod (b e m : Nat) : Nat :=
  if h : e = 0 then 1 else
    let r := powMod b (e / 2) m
    let square := r * r % m
    if e % 2 = 0 then square else square * b % m
termination_by e
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)

/-- A primitive `2^32`-th root of unity in the Goldilocks field (`7^((p-1)/2^32)`). -/
def rootOfUnity2to32 : Nat := powMod 7 ((goldilocksP - 1) / 2 ^ 32) goldilocksP

/-- A primitive `n`-th root, `n` a power of two dividing `2^32`. -/
def rootOfUnity (n : Nat) : Nat := powMod rootOfUnity2to32 (2 ^ 32 / n) goldilocksP

/-! The NTT source uses the general index-parametric multi-output array language.
Each upload is ec-gpu's Stockham map. A radix-4 (or final radix-2) subnetwork stays in
one invocation's registers; successive subnetworks exchange arrays in workgroup
memory. Input/output layout expressions fuse Stockham's transpose into the loads
and stores. No index tables, global gather intermediates, or NTT shader template.
-/

namespace BlockNtt
open Obend.Hardware.ArrayKernel

def addI (a b : Ix) : Ix := .add a b
def mulI (a : Ix) (b : Nat) : Ix := .mul a (.lit b)

/-- Bit reversal is an index expression, not an index buffer or a dispatch. -/
def reverseBits (bits : Nat) (i : Ix) : Ix :=
  (List.range bits).foldl (fun acc bit =>
    addI acc (mulI (.mod (.div i (2^bit)) 2) (2^(bits-1-bit)))) (.lit 0)

/-- Register position within the whole upload tile, with lane/register
coordinates transposed so a register butterfly follows the global DIF layer. -/
def phaseIndex (radix stride r : Nat) : Ix :=
  addI (addI (mulI (.div .lane stride) (radix*stride)) (.mod .lane stride))
    (.lit (r*stride))

def phaseLoadIndex (n count radix stride : Nat) (first : Bool) (r : Nat) : Ix :=
  if first then addI .group (mulI (phaseIndex radix stride r) (n/count))
  else phaseIndex radix stride r

def phaseSaveIndex (count logCount p radix stride : Nat) (last : Bool) (r : Nat) : Ix :=
  if last then
    let k : Ix := .mod .group p
    addI (addI (mulI (.div .group p) (p*count)) k)
      (mulI (reverseBits logCount (phaseIndex radix stride r)) p)
  else phaseIndex radix stride r

/-- One butterfly uses the same shared field source construction as every
other consumer. A missing twiddle is precisely the source's unit-twiddle case. -/
structure Butterfly where
  sum : Nat
  high : Nat
  read : Option Read

def butterfly (k : GlConsts) (a b : Nat) (twiddle : Option Ix) : BuildM Butterfly := do
  let sum ← glAdd 1 k a b
  let diff ← glSub 1 k a b
  match twiddle with
  | none => pure ⟨sum,diff,none⟩
  | some exponent =>
    let tw ← newWire 1
    let high ← glMul 1 k diff tw
    pure ⟨sum,high,some ⟨tw,4,exponent⟩⟩

/-- The register construction interpreted by `phase`; separating it from the
index-to-write packaging exposes the actual source builder to semantic proofs. -/
def phaseAction (n count p done degree src : Nat) (first : Bool) : BuildM (List Read × List Nat) := do
  let radix := 2^degree
  let stride := count / (2^done * radix)
  let index := phaseIndex radix stride
  let loadIndex := phaseLoadIndex n count radix stride first
  let mut reads : List Read := []
  let mut regs : Array Nat := #[]
  for r in List.range radix do
    let a ← newWire 1
    reads := reads ++ [⟨a, src, loadIndex r⟩]
    regs := regs.push a
  let k ← glConsts 1
  if first && p == 1 then
    for r in List.range radix do
      let canonical ← glCanon 1 k regs[r]!
      regs := regs.set! r canonical
  if first && p > 1 then
    for r in List.range radix do
      let tw ← newWire 1
      let exponent := .mod (.mul (index r) (mulI (.mod .group p) (n/count/p))) n
      reads := reads ++ [⟨tw, 4, exponent⟩]
      let v ← glMul 1 k regs[r]! tw
      regs := regs.set! r v
  for round in List.range degree do
    let bit := radix / 2^(round+1)
    for j in List.range (radix/2) do
      let di := j % bit
      let i0 := 2*j-di
      let i1 := i0+bit
      let a := regs[i0]!
      let b := regs[i1]!
      -- Twiddle depends only on the within-butterfly coordinate; the segment
      -- coordinate has been removed by lane modulo stride.
      let exponent := mulI (addI (.mod .lane stride) (.lit (di*stride)))
        (2^(done+round) * (n/count))
      let result ← butterfly k a b
        (if stride == 1 && di == 0 then none else some exponent)
      match result.read with
      | none => pure ()
      | some read => reads := reads ++ [read]
      regs := (regs.set! i0 result.sum).set! i1 result.high
  return (reads, regs.toList)

/-- One register tile of the DIF network. `done` preceding binary layers have
already run; `degree` layers are fused now. All arithmetic is the shared source
builder above, and both index permutations remain source expressions. -/
def phase (n count logCount p done degree src dst : Nat)
    (first last : Bool) : Phase := Id.run do
  let radix := 2^degree
  let stride := count / (2^done * radix)
  let saveIndex := phaseSaveIndex count logCount p radix stride last
  let ((reads, outputs), st) := (phaseAction n count p done degree src first).run {}
  return { lanes := count/radix, reads, code := registerCode st,
           writes := outputs.zipIdx.map fun (value, r) => ⟨dst, saveIndex r, value⟩ }

/-- Consecutive radix-4 register blocks, with one final radix-2 block when odd. -/
def phaseDegrees (degree : Nat) : List Nat :=
  List.replicate (degree/2) 2 ++ if degree%2 == 0 then [] else [1]

/-- The exact barrier-separated phase list, carrying the completed layer count
and alternating shared source row explicitly. -/
def buildPhases (n logCount p dst : Nat) : Nat → Nat → List Nat → List Phase
  | _, _, [] => []
  | done, input, chunk::rest =>
    let last := done+chunk == logCount
    let output := if last then dst else if input == 2 then 3 else 2
    phase n (2^logCount) logCount p done chunk input output (done == 0) last ::
      buildPhases n logCount p dst (done+chunk) output rest

/-- A Stockham upload groups up to eight binary layers. Radix-4 register blocks
keep 64 lanes active for a 256-element tile; barriers exchange successive pairs of layers. -/
def dispatch (n logP degree src dst : Nat) : Dispatch :=
  { groups := n/(2^degree)
    phases := buildPhases n degree (2^logP) dst 0 src (phaseDegrees degree) }

/-- Substitute source indices while batching independent tiles into a workgroup.
This constructs the indexed source maps; admission checks the resulting accesses. -/
def substitute (group lane : Ix) : Ix → Ix
  | .lit n => .lit n
  | .group => group
  | .lane => lane
  | .add a b => .add (substitute group lane a) (substitute group lane b)
  | .mul a b => .mul (substitute group lane a) (substitute group lane b)
  | .div a n => .div (substitute group lane a) n
  | .mod a n => .mod (substitute group lane a) n
  | .lookup values i => .lookup values (substitute group lane i)

def tileSize (d : Dispatch) : Nat :=
  d.phases.foldl (fun n ph => max n (ph.lanes * ph.writes.length)) 1

def packing (d : Dispatch) : Nat :=
  let lanes := d.phases.foldl (fun n ph => max n ph.lanes) 1
  let k := max 1 (min d.groups (64 / lanes))
  if d.groups % k == 0 then k else 1

/-- A batch is one simultaneous map over independent tile coordinates. Shared
arrays acquire a tile coordinate too; all barriers stay uniform across the batch. -/
def batchTiles (stride : Nat) (d : Dispatch) : Dispatch :=
  let k := packing d
  { groups := d.groups / k
    phases := d.phases.map fun ph =>
      let tile : Ix := .div .lane ph.lanes
      let group : Ix := .add (.mul .group (.lit k)) tile
      let lane : Ix := .mod .lane ph.lanes
      let index (array : Nat) (i : Ix) :=
        let i := substitute group lane i
        if array == 2 || array == 3 then .add i (.mul tile (.lit stride)) else i
      { ph with lanes := ph.lanes*k
                reads := ph.reads.map fun r => { r with index := index r.array r.index }
                writes := ph.writes.map fun w => { w with index := index w.array w.index } } }

end BlockNtt

/-- Balanced upload size: the same policy is used by construction and proofs. -/
def uploadDegree (maximum remaining : Nat) : Nat :=
  let uploads := (remaining + maximum - 1) / maximum
  (remaining + uploads - 1) / uploads

/-- Static upload schedule. Fuel is the remaining number of binary layers,
so construction is total without an unchecked termination assertion. -/
def uploadDegrees (maximum : Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | fuel+1, remaining =>
      if remaining = 0 then [] else
        let degree := uploadDegree maximum remaining
        degree :: uploadDegrees maximum fuel (remaining-degree)

/-- The one construction of upload dispatches. Source registers and shared
phases are supplied by `BlockNtt.dispatch`; the schedule only chooses tile sizes. -/
def buildUploads (n : Nat) : List Nat → Nat → Nat → List Obend.Hardware.ArrayKernel.Dispatch × Nat
  | [], _, input => ([], input)
  | degree :: rest, done, input =>
      let output := 1-input
      let tail := buildUploads n rest (done+degree) output
      (BlockNtt.dispatch n done degree input output :: tail.1, tail.2)

/-- Tail-recursive linear-time twiddle generation. Each entry is computed by one
field multiplication, with no per-entry modular exponentiation. -/
def powersLoop (ω : Nat) : Nat → Array Word → Nat → Array Word
  | 0, xs, _ => xs
  | count+1, xs, v => powersLoop ω count (xs.push (BitVec.ofNat 64 v)) (v*ω%goldilocksP)

def twiddlePowers (n ω : Nat) : Array Word := powersLoop ω n #[] 1

def uploadSchedule (n : Nat) : List Nat :=
  let logN := Nat.log2 n
  uploadDegrees (if n ≤ 1024 then 4 else 8) logN logN

def sourceUploads (n : Nat) : List Obend.Hardware.ArrayKernel.Dispatch × Nat :=
  buildUploads n (uploadSchedule n) 0 0

def sharedWords (n : Nat) : Nat :=
  (sourceUploads n).1.foldl
    (fun size d => max size (BlockNtt.tileSize d * BlockNtt.packing d)) 1

/-- Stockham NTT as a composition of general array maps. `n` is a power of two
with initial words canonicalized in registers. The emitter accepts sizes below 2^26. Three uploads suffice for 2^20; each has multiple register maps
separated by workgroup exchanges. Two device arrays are reused between uploads. -/
def nttBlockProgram (n : Nat) : Obend.Hardware.ArrayKernel.Program :=
  { buffers := [⟨n, .device, []⟩, ⟨n, .device, []⟩,
      ⟨sharedWords n, .shared, []⟩, ⟨sharedWords n, .shared, []⟩,
      ⟨n, .constant, (twiddlePowers n (rootOfUnity n)).toList⟩],
    inputs := [0], outputs := [(sourceUploads n).2],
    dispatches := (sourceUploads n).1.map fun d => BlockNtt.batchTiles (BlockNtt.tileSize d) d }

/-- The recursive radix-2 NTT in `Nat` arithmetic: `y_k = E_k + ω^k O_k`, `y_{k+n/2} = E_k - ω^k O_k`. -/
partial def nttFast (xs : Array Nat) (ω : Nat) : Array Nat :=
  let n := xs.size
  if n ≤ 1 then xs else
  let half := n / 2
  let ω2 := ω * ω % goldilocksP
  let ev := nttFast ((Array.range half).map fun i => xs[2 * i]!) ω2
  let od := nttFast ((Array.range half).map fun i => xs[2 * i + 1]!) ω2
  let pw := (Array.range half).map fun j => powMod ω j goldilocksP
  (Array.range n).map fun j =>
    if j < half then (ev[j]! + pw[j]! * od[j]! % goldilocksP) % goldilocksP
    else
      let j' := j - half
      (ev[j']! + goldilocksP - pw[j']! * od[j']! % goldilocksP) % goldilocksP


end Obend.Hardware.Gpu.Ntt
