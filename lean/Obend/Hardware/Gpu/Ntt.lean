module
public import Obend.Hardware.ArrayKernel
public import Obend.Hardware.Gpu.GoldilocksSource
@[expose] public section

namespace Obend.Hardware.Gpu.Ntt
open Obend.Hardware.OpenHypergraph Obend.Hardware.ArrayHypergraph
open Obend.Hardware.ArrayBuild Obend.Hardware.Gpu.GoldilocksSource

/-! ## The NTT -/

def powMod (b e m : Nat) : Nat := Id.run do
  let mut r := 1
  let mut bb := b % m
  let mut ee := e
  while ee > 0 do
    if ee % 2 == 1 then r := r * bb % m
    bb := bb * bb % m
    ee := ee / 2
  return r

/-- A primitive `2^32`-th root of unity in the Goldilocks field (`7^((p-1)/2^32)`). -/
def rootOfUnity2to32 : Nat := powMod 7 ((goldilocksP - 1) / 2 ^ 32) goldilocksP

/-- A primitive `n`-th root, `n` a power of two dividing `2^32`. -/
def rootOfUnity (n : Nat) : Nat := powMod rootOfUnity2to32 (2 ^ 32 / n) goldilocksP

/-! The NTT source uses the general index-parametric multi-output array language.
Each upload is ec-gpu's Stockham map. A radix-8 (or radix-4) subnetwork stays in
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

/-- One register tile of the DIF network. `done` preceding binary layers have
already run; `degree` layers are fused now. All arithmetic is the shared source
builder above, and both index permutations remain source expressions. -/
def phase (n count logCount p done degree src dst : Nat)
    (first last : Bool) : Phase := Id.run do
  let radix := 2^degree
  let stride := count / (2^done * radix)
  let index (r : Nat) : Ix :=
    addI (addI (mulI (.div .lane stride) (radix*stride)) (.mod .lane stride))
      (.lit (r*stride))
  let loadIndex (r : Nat) : Ix :=
    if first then addI .group (mulI (index r) (n/count)) else index r
  let saveIndex (r : Nat) : Ix :=
    if last then
      let k : Ix := .mod .group p
      addI (addI (mulI (.div .group p) (p*count)) k)
        (mulI (reverseBits logCount (index r)) p)
    else index r
  let action : BuildM (List Read × List Nat) := do
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
        let sum ← glAdd 1 k a b
        let diff ← glSub 1 k a b
        -- Twiddle depends only on the within-butterfly coordinate; the segment
        -- coordinate has been removed by lane modulo stride.
        let exponent := mulI (addI (.mod .lane stride) (.lit (di*stride)))
          (2^(done+round) * (n/count))
        let v ← if stride == 1 && di == 0 then pure diff else do
          let tw ← newWire 1
          reads := reads ++ [⟨tw, 4, exponent⟩]
          glMul 1 k diff tw
        regs := (regs.set! i0 sum).set! i1 v
    return (reads, regs.toList)
  let ((reads, outputs), st) := action.run {}
  return { lanes := count/radix, reads, code := registerCode st,
           writes := outputs.zipIdx.map fun (value, r) => ⟨dst, saveIndex r, value⟩ }

/-- A Stockham upload groups up to eight binary layers. Radix-4 register blocks
keep 64 lanes active for a 256-element tile; barriers exchange successive pairs of layers. -/
def dispatch (n logP degree src dst : Nat) : Dispatch := Id.run do
  let count := 2^degree
  let mut phases := []
  let mut done := 0
  let mut input := src
  for _ in List.range degree do
    if done < degree then
      let chunk := min 2 (degree-done)
      let last := done+chunk == degree
      let output := if last then dst else if input == 2 then 3 else 2
      phases := phases ++ [phase n count degree (2^logP) done chunk input output
        (done == 0) last]
      input := output
      done := done+chunk
  return { groups := n/count, phases }

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

/-- Stockham NTT as a composition of general array maps. `n` is a power of two
with initial words canonicalized in registers. The emitter accepts sizes below 2^26. Three uploads suffice for 2^20; each has multiple register maps
separated by workgroup exchanges. Two device arrays are reused between uploads. -/
def nttBlockProgram (n : Nat) : Obend.Hardware.ArrayKernel.Program := Id.run do
  let logN := Nat.log2 n
  let mut dispatches := []
  let mut done := 0
  let mut input := 0
  for _ in List.range logN do
    if done < logN then
      let remaining := logN-done
      let maximumDegree := if n <= 1024 then 4 else 8
      let uploads := (remaining + maximumDegree - 1) / maximumDegree
      let degree := (remaining + uploads - 1) / uploads
      let output := 1-input
      dispatches := dispatches ++ [BlockNtt.dispatch n done degree input output]
      input := output
      done := done+degree
  let omega := rootOfUnity n
  -- Successive powers are linear-time to generate; exponentiation per entry
  -- would dominate construction of the 2^20 source program.
  let packedTile := dispatches.foldl (fun n d => max n (BlockNtt.tileSize d * BlockNtt.packing d)) 1
  dispatches := dispatches.map fun d => BlockNtt.batchTiles (BlockNtt.tileSize d) d
  let powers : Array Word := Id.run do
    let mut xs := #[]
    let mut v := 1
    for _ in [:n] do
      xs := xs.push (BitVec.ofNat 64 v)
      v := v*omega%goldilocksP
    return xs
  return { buffers := [⟨n, .device, []⟩, ⟨n, .device, []⟩,
      ⟨packedTile, .shared, []⟩, ⟨packedTile, .shared, []⟩, ⟨n, .constant, powers.toList⟩],
           inputs := [0], outputs := [input], dispatches }

/-- The naive DFT over the Goldilocks field, `y_k = Σ_j x_j ω^{jk}`, with a table of the powers of `ω`. -/
def nttReference (xs : List Nat) : List Nat :=
  let n := xs.length
  if n == 0 then [] else
  let ω := rootOfUnity n
  let pw : Array Nat := (Array.range n).map fun i => powMod ω i goldilocksP
  let xa := xs.toArray
  (List.range n).map fun k =>
    (List.range n).foldl (fun acc j => (acc + xa[j]! * pw[(j * k) % n]!) % goldilocksP) 0

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
