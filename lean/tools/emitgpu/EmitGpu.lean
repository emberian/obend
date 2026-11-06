/-
# `obend-emit-gpu` — array hypergraphs lowered to compute shaders (`Obend.Hardware.Gpu`)

    obend-emit-gpu list
    obend-emit-gpu <graph> --out DIR [--plant P]
        DIR/plan.json (the allocated device buffer's size, every wire's base and length, the constant and index
        buffers, the boundary wires, one shader per dispatch), DIR/stage_<k>.wgsl, and
        DIR/expected.tsv, one line per vector: index, the input wires, and the output wires
        `Obend.Hardware.Gpu.runProgram` shows (wires separated by `;`, elements by `,`, signed 64-bit)
    obend-emit-gpu all --out DIR [--plant P]
        every graph, each under DIR/<graph>/

`--plant addAsSub` emits every `+` as `-`; `--plant swapMux` exchanges the arms of every `select`:
rules planted in the shader text only, for `hardware/gpu/verify_gpu.sh`'s tooth. The expected values
are always the unplanted model's.

Expected values are `evalGraphArr`'s, which is `evalGraph` with the wires stored (`evalGraphArr_eq`).
Before writing, the emitter refuses a graph that fails `ArrayGraph.wf` (the hypothesis of
`lowerArrayToGpu_sound`, so the expected values are `evalGraph`'s and the device must show them) and an
NTT graph whose evaluation disagrees with a recursive radix-2 NTT over the Goldilocks field in `Nat`
arithmetic (`nttFast`), which for the smaller sizes is itself checked against the naive DFT
(`nttReference`). These are tests of the fixtures, run on every emission.

NTTs use `ArrayKernel.Program`: indexed multi-output maps, radix-4 register networks, shared-memory
phases, and balanced Stockham uploads derived from ec-gpu's `radix_fft` and Govindaraju et al. SC2008.
The source contains every index and arithmetic operation; the generic emitter contains no NTT shader.
`Program.check` admits bounds, SSA closure, initialization and ownership; `SourceProtocol.checkProgram`
checks the actual physical-lane phase protocol against G4. Expected outputs are the executable source
semantics, independently compared with `nttFast` and (at small sizes) the direct DFT. These comparisons
are gates, not a universal theorem that the chosen NTT construction is the mathematical DFT.
`--artifacts-only` omits expected-value evaluation so planted shader rules reuse the unplanted output
oracle once per external gate run; plan equality is required before that reuse.
-/
import Obend.Hardware.Gpu
import Obend.Hardware.ArrayKernel
import Obend.Hardware.Gpu.BlockEmit
import Obend.Hardware.Gpu.LayoutChecks
import Obend.Hardware.Gpu.DispatchProtocol
import Obend.Hardware.Gpu.GoldilocksSource

open Obend.Hardware.OpenHypergraph
open Obend.Hardware.ArrayHypergraph
open Obend.Hardware.Gpu

open Obend.Hardware.ArrayBuild
open Obend.Hardware.Gpu.GoldilocksSource

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

/-! ## Array graphs besides the NTT -/

/-- Elementwise `a * b + c` over length-`n` wires, then a gather that reverses it: the lowering's map,
constant and gather kernels on one wire of several workgroups. -/
def macReverseGraph (n : Nat) : ArrayGraph :=
  runBuild (fun ins => do
    let a := ins.getD 0 0
    let b := ins.getD 1 0
    let c ← broadcast n 7#64
    let m ← map3 n (.scalar .mac) a b c
    let r ← node n (.gather { source := n, target := n, table := (List.range n).reverse }) [m]
    pure [m, r]) [n, n]

/-- A field multiply alone, elementwise, for the arithmetic tooth on big words. -/
def glMulGraph (n : Nat) : ArrayGraph :=
  runBuild (fun ins => do
    let k ← glConsts n
    let y ← glMul n k (ins.getD 0 0) (ins.getD 1 0)
    pure [y]) [n, n]

/-! ## Scalar graphs, as their one-element instance -/

def treeGraph (n : Nat) : StrictOpenHypergraph :=
  let rec levels (fuel : Nat) (lo cnt nextWire opIdx : Nat) (acc : List HyperEdge) : List HyperEdge × Nat :=
    match fuel with
    | 0 => (acc, lo)
    | fuel + 1 =>
      if cnt ≤ 1 then (acc, lo)
      else
        let half := cnt / 2
        let edges := (List.range half).map fun i =>
          { opIdx := opIdx + i, op := HypergraphOp.add, srcWires := [lo + 2 * i, lo + 2 * i + 1]
          , dstWire := nextWire + i : HyperEdge }
        levels fuel nextWire half (nextWire + half) (opIdx + half) (acc ++ edges)
  let (edges, root) := levels (n + 1) 0 n n 0 []
  let numWires := if n ≤ 1 then n else 2 * n - 1
  mkStrictOpenHypergraph numWires (List.range n) [root] edges

def muxChainGraph : StrictOpenHypergraph :=
  mkStrictOpenHypergraph 8 [0, 1, 2, 3] [4, 7]
    [ { opIdx := 0, op := .mux,     srcWires := [0, 1, 2], dstWire := 4 }
    , { opIdx := 1, op := .mul,     srcWires := [4, 3],    dstWire := 5 }
    , { opIdx := 2, op := .const 5, srcWires := [],        dstWire := 6 }
    , { opIdx := 3, op := .mux,     srcWires := [5, 6, 0], dstWire := 7 } ]

def allOpsGraph : StrictOpenHypergraph :=
  mkStrictOpenHypergraph 11 [0, 1, 2] [8, 9, 10]
    [ { opIdx := 0, op := .scale 3,           srcWires := [0],       dstWire := 3 }
    , { opIdx := 1, op := .mac,               srcWires := [1, 2, 0], dstWire := 4 }
    , { opIdx := 2, op := .const (-7),        srcWires := [],        dstWire := 5 }
    , { opIdx := 3, op := .sub,               srcWires := [3, 4],    dstWire := 6 }
    , { opIdx := 4, op := .mul,               srcWires := [6, 5],    dstWire := 7 }
    , { opIdx := 5, op := .add,               srcWires := [7, 3],    dstWire := 8 }
    , { opIdx := 6, op := .scale (-(2 ^ 40)), srcWires := [4],       dstWire := 9 }
    , { opIdx := 7, op := .mux,               srcWires := [0, 8, 9], dstWire := 10 } ]

/-! ## The graphs and their vectors -/

inductive Kind where
  | plain
  | ntt
  deriving DecidableEq

def graphs : List (String × ArrayGraph × Kind) :=
  [ ("diamond",          ofScalar goldenDiamondHypergraph, .plain)
  , ("optic-mul",        ofScalar (compileOpticToHypergraph .mul), .plain)
  , ("optic-linearmac",  ofScalar (compileOpticToHypergraph (.linearMac 7)), .plain)
  , ("optic-bilinear",   ofScalar (compileOpticToHypergraph (.bilinear (-3))), .plain)
  , ("adjoint-mul-add",  ofScalar (compileGraphAdjoint (compileOpticChain2FwdHypergraph .mul .add)), .plain)
  , ("adjoint-square-bilinear",
      ofScalar (compileGraphAdjoint (compileOpticChain2FwdHypergraph .square (.bilinear 5))), .plain)
  , ("allops",           ofScalar allOpsGraph, .plain)
  , ("muxchain",         ofScalar muxChainGraph, .plain)
  , ("tree512",          ofScalar (treeGraph 512), .plain)
  , ("mac-reverse-1000", macReverseGraph 1000, .plain)
  , ("glmul-256",        glMulGraph 256, .ntt)
 ]

def pool : List Int :=
  [0, 1, -1, 2, 3, -3, 10, 255, -256, 65535, 2 ^ 31, -(2 ^ 31), 2 ^ 32 + 1, 2 ^ 62, -(2 ^ 62),
   2 ^ 63 - 1, -(2 ^ 63), 123456789, -987654321]

def lcg (s : Nat) : Nat := (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

/-- A deterministic pseudo-random 64-bit word for element `i` of input `w` of vector `v`. -/
def draw (v w i : Nat) : Nat :=
  (List.range (i % 7 + 1)).foldl (fun acc _ => lcg acc) (lcg (v * 7919 + w * 104729 + i * 31 + 17))

def signed (s : Nat) : Int := (s : Int) - (if s ≥ 2 ^ 63 then 2 ^ 64 else 0)

/-- Vector `v` for a graph: field elements (`< p`) for the field graphs; otherwise the first vectors walk
the pool and later ones are pseudo-random words. -/
def vectorFor (kind : Kind) (lens : List Nat) (v : Nat) : List (List Int) :=
  lens.zipIdx.map fun (n, w) =>
    (List.range n).map fun i =>
      match kind with
      | .ntt => (draw v w i % goldilocksP : Int)
      | .plain =>
        if v < 6 then pool.getD ((i + w + 3 * v) % pool.length) 0
        else signed (draw v w i)

def vectorCount (g : ArrayGraph) : Nat :=
  let total := sumNatList (g.inputs.map (g.lengths.getD · 0))
  if total ≥ 2 ^ 14 then 2 else if total ≥ 64 then 6 else 12

/-! ## Expected values and the checks -/

def wireText (xs : List Int) : String :=
  if xs.isEmpty then "-" else String.intercalate "," (xs.map toString)

def wiresText (ws : List (List Int)) : String := String.intercalate ";" (ws.map wireText)

def toVec (xs : List Int) : Vec := xs.map (BitVec.ofInt 64)

def writeGraph (name : String) (g : ArrayGraph) (kind : Kind) (dir : System.FilePath) (plant : Plant) (artifactsOnly : Bool := false) : IO Unit := do
  unless g.wf do
    throw <| IO.userError s!"{name}: the graph is not well-formed (ArrayGraph.wf)"
  unless layoutOk g do
    throw <| IO.userError s!"{name}: allocated layout fails live-range separation or dispatch race check"
  let p := lowerArrayToGpu g
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir / "plan.json") (emitPlanJson name p)
  for (s, k) in p.stages.zipIdx do
    IO.FS.writeFile (dir / s!"stage_{k}.wgsl") (emitStageWgsl plant name k p.stages.length s)
  if artifactsOnly then return
  let inLens := g.inputs.map (g.lengths.getD · 0)
  let mut lines : Array String := #[]
  for v in List.range (vectorCount g) do
    let vals := if name == "glmul-256" && v == 0 then
      let corners : List Nat := [0, 1, 4294967295, 4294967296, goldilocksP-1, goldilocksP,
        goldilocksP+1, 18446744073709551615]
      inLens.zipIdx.map fun (n, w) => (List.range n).map fun i =>
        (corners.getD ((i / (if w == 0 then 1 else corners.length)) % corners.length) 0 : Int)
    else vectorFor kind inLens v
    let env := mkEnv g.lengths g.inputs (vals.map toVec)
    let model := evalGraphArr g ((List.range g.lengths.length).map fun w => (env w).toArray).toArray
    if kind == .ntt && name.startsWith "ntt" then
      let input := (vals.getD 0 []).map Int.toNat
      let fast := (nttFast input.toArray (rootOfUnity input.length)).toList
      unless (model.getD 0 []).map (·.toNat) == fast do
        throw <| IO.userError s!"{name} vector {v}: the NTT graph disagrees with the recursive NTT"
      if input.length ≤ 4096 then
        unless nttReference input == fast do
          throw <| IO.userError s!"{name} vector {v}: the recursive NTT disagrees with the naive DFT"
    let signed64 (ws : List Int) : List Int := ws.map fun x => (BitVec.ofInt 64 x).toInt
    lines := lines.push s!"{v}\t{wiresText (vals.map signed64)}\t{wiresText (model.map fun ws => ws.map (·.toInt))}"
  IO.FS.writeFile (dir / "expected.tsv") (String.intercalate "\n" lines.toList ++ "\n")
  IO.println s!"  {name}: {g.lengths.length} wires ({p.words} words), {g.edges.length} edges, \
    {(fuseGraph g).edges.length} after fusion, {p.consts.length} constants, \
    {p.tables.length} indices, {p.stages.length} dispatches \
    ({String.intercalate "," (p.stages.map fun s => toString s.kernels.length)} kernels), \
    {vectorCount g} vectors -> {dir}"

/-- Block programs replace the earlier per-stage NTT graphs. -/
def blockGraphs : List (String × Nat) :=
  [4, 16, 64, 1024, 65536, 1048576].map fun n => (s!"ntt-{n}", n)

def writeBlockGraph (name : String) (n : Nat) (dir : System.FilePath) (plant : Plant) (artifactsOnly : Bool := false) : IO Unit := do
  unless n >= 2 && n == 2^(Nat.log2 n) && n < 2^26 do
    throw <| IO.userError s!"{name}: expected a supported power-of-two size below 2^26"
  let p := nttBlockProgram n
  if let .error reason := p.check then
    throw <| IO.userError s!"{name}: block source rejected: {reason}"
  unless SourceProtocol.checkProgram p workgroupSize do
    throw <| IO.userError s!"{name}: source protocol fails G4 phase geometry or race certificate"
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir / "plan.json") (BlockEmit.emitPlan name p)
  for (d, k) in p.dispatches.zipIdx do
    IO.FS.writeFile (dir / s!"stage_{k}.wgsl") (BlockEmit.emitDispatch plant name p d)
  if artifactsOnly then return
  let mut lines := #[]
  let count := if n > 4096 then 2 else if n >= 64 then 6 else 12
  for v in [:count] do
    let vals := vectorFor .ntt [n] v
    let input := (vals.getD 0 []).map Int.toNat
    let mem := Obend.Hardware.ArrayKernel.initialMemory p (vals.map fun xs => (toVec xs).toArray)
    let result := Obend.Hardware.ArrayKernel.evalProgram p mem
    let model := p.outputs.map fun i => (result.getD i #[]).toList
    let fast := (nttFast input.toArray (rootOfUnity n)).toList
    unless (model.getD 0 []).map (·.toNat) == fast do
      throw <| IO.userError s!"{name} vector {v}: block array source disagrees with recursive NTT"
    if n <= 1024 then
      unless nttReference input == fast do
        throw <| IO.userError s!"{name} vector {v}: recursive NTT disagrees with direct DFT"
    let signed64 (xs : List Int) := xs.map fun x => (BitVec.ofInt 64 x).toInt
    lines := lines.push s!"{v}\t{wiresText (vals.map signed64)}\t{wiresText (model.map fun xs => xs.map (·.toInt))}"
  IO.FS.writeFile (dir / "expected.tsv") (String.intercalate "\n" lines.toList ++ "\n")
  IO.println s!"  {name}: {BlockEmit.spaceSize p .device} device words, {BlockEmit.spaceSize p .shared} shared words, {p.dispatches.length} dispatches -> {dir}"

/-! ## Main -/

def usage : String :=
  "usage: obend-emit-gpu list | <graph> --out DIR [--plant addAsSub|swapMux|mulHighZero] | all --out DIR [--plant P]"

def main (args : List String) : IO UInt32 := do
  match args with
  | ["check-layout"] =>
    for (name, ok) in layoutCheckResults do
      IO.println s!"{if ok then "PASS" else "FAIL"} {name}"
    return if layoutCheckFixtures then 0 else 1
  | ["list"] =>
    for (n, _, _) in graphs do IO.println n
    for (n, _) in blockGraphs do IO.println n
    return 0
  | name :: rest =>
    let mut out : Option String := none
    let mut plant : Plant := .none
    let mut artifactsOnly := false
    let mut r := rest
    while !r.isEmpty do
      match r with
      | "--out" :: d :: r' => out := some d; r := r'
      | "--artifacts-only" :: r' => artifactsOnly := true; r := r'
      | "--plant" :: p :: r' =>
        match Plant.ofString? p with
        | some pl => plant := pl; r := r'
        | none => IO.eprintln s!"unknown plant {p}"; return 2
      | other :: _ => IO.eprintln s!"unexpected argument {other}\n{usage}"; return 2
      | [] => pure ()
    let some dir := out | IO.eprintln usage; return 2
    if name == "all" then
      for (n, g, kind) in graphs do writeGraph n g kind (dir / n) plant artifactsOnly
      for (name, n) in blockGraphs do writeBlockGraph name n (dir / name) plant artifactsOnly
      return 0
    if let some (_, n) := blockGraphs.find? (·.1 == name) then
      writeBlockGraph name n dir plant artifactsOnly
      return 0
    match graphs.find? (·.1 == name) with
    | some (_, g, kind) => writeGraph name g kind dir plant artifactsOnly; return 0
    | none => IO.eprintln s!"unknown graph {name}; `obend-emit-gpu list`"; return 2
  | [] => IO.eprintln usage; return 2
