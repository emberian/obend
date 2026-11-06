/-
# `obend-emit-gpu` — array hypergraphs lowered to compute shaders (`Obend.Hardware.Gpu`)

    obend-emit-gpu list
    obend-emit-gpu <graph> --out DIR [--plant P]
        DIR/plan.json (the flat wire buffer's size, every wire's base and length, the constant and index
        buffers, the boundary wires, one shader per wavefront stage), DIR/stage_<k>.wgsl, and
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

The NTT graphs are Stockham radix-2 (Govindaraju et al. 2008; ec-gpu's `radix_fft` kernel with
`deg = 1`, whose output index is `((j - k) << 1) + k`): every stage reads the two halves of the
previous stage's output, multiplies the upper half by `ω_{2Ns}^{j mod Ns}`, and writes the sum and
difference expanded by the sub-transform size, so an NTT of `n` points is `log₂ n` stages of a few
dozen edges over whole wires, and no bit reversal. The field operations are the limb network of
`Obend.Apps.ZkNtt.glMul`; after fusion each stage's sum and difference are one kernel each.
-/
import Obend.Hardware.Gpu

open Obend.Hardware.OpenHypergraph
open Obend.Hardware.ArrayHypergraph
open Obend.Hardware.Gpu

/-! ## A builder for array graphs -/

structure Build where
  lengths : Array Nat := #[]
  edges   : Array ArrayEdge := #[]

abbrev BuildM := StateM Build

def newWire (n : Nat) : BuildM Nat := do
  let st ← get
  set { st with lengths := st.lengths.push n }
  pure st.lengths.size

def emit (op : ArrayOp) (srcs : List Nat) (dst : Nat) : BuildM Unit :=
  modify fun st => { st with edges := st.edges.push { opIdx := st.edges.size, op := op, srcWires := srcs, dstWire := dst } }

/-- A fresh wire of length `n` written by `op`. -/
def node (n : Nat) (op : ArrayOp) (srcs : List Nat) : BuildM Nat := do
  let w ← newWire n
  emit op srcs w
  pure w

/-- A fresh wire of length `n` holding `op` of `srcs` elementwise: the primitive one-instruction program. -/
def mapN (n : Nat) (op : ElemOp) (srcs : List Nat) : BuildM Nat := do
  let w ← newWire n
  emit (.map n (ElemProg.single op srcs w)) srcs w
  pure w

def constWire (vals : List Word) : BuildM Nat := node vals.length (.const vals) []

/-- `n` copies of one word. -/
def broadcast (n : Nat) (v : Word) : BuildM Nat := constWire (List.replicate n v)

def map2 (n : Nat) (op : ElemOp) (a b : Nat) : BuildM Nat := mapN n op [a, b]
def map3 (n : Nat) (op : ElemOp) (a b c : Nat) : BuildM Nat := mapN n op [a, b, c]

def runBuild (inputs : List Nat → BuildM (List Nat)) (inputLens : List Nat) : ArrayGraph :=
  let ((ins, outs), st) := (do
    let ins ← inputLens.mapM newWire
    let outs ← inputs ins
    pure (ins, outs)).run {}
  { lengths := st.lengths.toList, inputs := ins, outputs := outs, edges := st.edges.toList }

/-! ## The Goldilocks field, elementwise (the network of `Obend.Apps.ZkNtt.glMul`) -/

def goldilocksP : Nat := 18446744069414584321

/-- The field constants a vector of length `n` needs: `p`, the low mask and the shift. -/
structure GlConsts where
  p    : Nat
  mask : Nat
  s32  : Nat

def glConsts (n : Nat) : BuildM GlConsts := do
  let p ← broadcast n (BitVec.ofNat 64 goldilocksP)
  let mask ← broadcast n 0xFFFFFFFF#64
  let s32 ← broadcast n 32#64
  pure ⟨p, mask, s32⟩

/-- `x < p ? x : x - p`. -/
def glCanon (n : Nat) (k : GlConsts) (x : Nat) : BuildM Nat := do
  let lt ← map2 n .ult x k.p
  let sub ← map2 n (.scalar .sub) x k.p
  map3 n (.scalar .mux) lt x sub

/-- `(a + b) mod p` for canonical `a b`, without a 65th bit. -/
def glAdd (n : Nat) (k : GlConsts) (a b : Nat) : BuildM Nat := do
  let remP ← map2 n (.scalar .sub) k.p b
  let lt ← map2 n .ult a remP
  let sum ← map2 n (.scalar .add) a b
  let wrap ← map2 n (.scalar .sub) a remP
  map3 n (.scalar .mux) lt sum wrap

/-- `(a - b) mod p` for canonical `a b`. -/
def glSub (n : Nat) (k : GlConsts) (a b : Nat) : BuildM Nat := do
  let lt ← map2 n .ult a b
  let pb ← map2 n (.scalar .sub) k.p b
  let wrap ← map2 n (.scalar .add) pb a
  let diff ← map2 n (.scalar .sub) a b
  map3 n (.scalar .mux) lt wrap diff

/-- `(a * b) mod p` for any 64-bit `a b`: four 32×32 limb products, the 128-bit product `(lo, hi)`, then
the shift/mask reduction (`goldilocksReduce128Spec`). -/
def glMul (n : Nat) (k : GlConsts) (a b : Nat) : BuildM Nat := do
  let aLo ← map2 n .band a k.mask
  let aHi ← map2 n .shr a k.s32
  let bLo ← map2 n .band b k.mask
  let bHi ← map2 n .shr b k.s32
  let p00 ← map2 n (.scalar .mul) aLo bLo
  let p01 ← map2 n (.scalar .mul) aLo bHi
  let p10 ← map2 n (.scalar .mul) aHi bLo
  let p11 ← map2 n (.scalar .mul) aHi bHi
  let p00Hi ← map2 n .shr p00 k.s32
  let p01Lo ← map2 n .band p01 k.mask
  let p10Lo ← map2 n .band p10 k.mask
  let mid32a ← map2 n (.scalar .add) p00Hi p01Lo
  let mid32 ← map2 n (.scalar .add) mid32a p10Lo
  let p00Lo ← map2 n .band p00 k.mask
  let mid32Lo ← map2 n .band mid32 k.mask
  let mid32LoSh ← map2 n .shl mid32Lo k.s32
  let lo ← map2 n .bor p00Lo mid32LoSh
  let p01Hi ← map2 n .shr p01 k.s32
  let p10Hi ← map2 n .shr p10 k.s32
  let mid32Hi ← map2 n .shr mid32 k.s32
  let hi1 ← map2 n (.scalar .add) p11 p01Hi
  let hi2 ← map2 n (.scalar .add) hi1 p10Hi
  let hi ← map2 n (.scalar .add) hi2 mid32Hi
  let hiLo ← map2 n .band hi k.mask
  let hiHi ← map2 n .shr hi k.s32
  let hiLoSh ← map2 n .shl hiLo k.s32
  let mid ← map2 n (.scalar .sub) hiLoSh hiLo
  let loC ← glCanon n k lo
  let t1 ← glAdd n k loC mid
  glSub n k t1 hiHi

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

/-- The output permutation of a Stockham radix-2 stage with sub-transform size `ns` over `n` points, for
the half of the output starting at `offset`: output `i` is `a[(i / 2ns)·ns + r]` when `r = i mod 2ns < ns`,
else `b[(i / 2ns)·ns + (r - ns)]`, as an index into `a ++ b`. For the last stage it is the identity. -/
def expandTable (n ns offset : Nat) : FiniteFunction :=
  let half := n / 2
  { source := half, target := n, table := (List.range half).map fun j =>
      let i := offset + j
      let group := i / (2 * ns)
      let r := i % (2 * ns)
      if r < ns then group * ns + r else half + group * ns + (r - ns) }

/-- The identity on a half of a length-`n` wire. -/
def halfTable (n offset : Nat) : FiniteFunction :=
  { source := n / 2, target := n, table := (List.range (n / 2)).map (offset + ·) }

/-- Stockham radix-2 NTT of `n = 2^L` points, inputs canonical (`< p`). The halves `lo`, `hi` of the
current array travel as two wires; stage `s` (`ns = 2^s`) computes `t = hi · ω_{2ns}^{j mod ns}`,
`a = lo + t`, `b = lo - t`, and gathers the next halves from `a ++ b` by `expandTable`; the last stage's
`a ++ b` is the output in natural order. The twiddles are gathered from one table of the powers of
`ω_n`, so the constants are `n/2` words and each stage's twiddle is an index table. -/
def nttStockham (x n : Nat) : BuildM Nat := do
  if n ≤ 1 then return x
  let half := n / 2
  let L := Nat.log2 n
  let k ← glConsts half
  let ω := rootOfUnity n
  let powers ← constWire ((List.range half).map fun i => BitVec.ofNat 64 (powMod ω i goldilocksP))
  let mut lo ← node half (.gather (halfTable n 0)) [x]
  let mut hi ← node half (.gather (halfTable n half)) [x]
  let mut out := x
  for s in List.range L do
    let ns := 2 ^ s
    let twTable : FiniteFunction :=
      { source := half, target := half, table := (List.range half).map fun j => (j % ns) * (half / ns) }
    let tw ← node half (.gather twTable) [powers]
    let t ← glMul half k hi tw
    let a ← glAdd half k lo t
    let b ← glSub half k lo t
    let ab ← node n .concat [a, b]
    if s + 1 < L then
      lo ← node half (.gather (expandTable n ns 0)) [ab]
      hi ← node half (.gather (expandTable n ns half)) [ab]
    else
      out := ab
  pure out

def nttGraph (n : Nat) : ArrayGraph :=
  runBuild (fun ins => do
    let y ← nttStockham (ins.getD 0 0) n
    pure [y]) [n]

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
  , ("ntt-4",            nttGraph 4, .ntt)
  , ("ntt-16",           nttGraph 16, .ntt)
  , ("ntt-64",           nttGraph 64, .ntt)
  , ("ntt-1024",         nttGraph 1024, .ntt)
  , ("ntt-65536",        nttGraph 65536, .ntt) ]

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

def writeGraph (name : String) (g : ArrayGraph) (kind : Kind) (dir : System.FilePath) (plant : Plant) : IO Unit := do
  unless g.wf do
    throw <| IO.userError s!"{name}: the graph is not well-formed (ArrayGraph.wf)"
  let p := lowerArrayToGpu g
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir / "plan.json") (emitPlanJson name p)
  for (s, k) in p.stages.zipIdx do
    IO.FS.writeFile (dir / s!"stage_{k}.wgsl") (emitStageWgsl plant name k p.stages.length s)
  let inLens := g.inputs.map (g.lengths.getD · 0)
  let mut lines : Array String := #[]
  for v in List.range (vectorCount g) do
    let vals := vectorFor kind inLens v
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

/-! ## Main -/

def usage : String :=
  "usage: obend-emit-gpu list | <graph> --out DIR [--plant addAsSub|swapMux] | all --out DIR [--plant P]"

def main (args : List String) : IO UInt32 := do
  match args with
  | ["list"] =>
    for (n, _, _) in graphs do IO.println n
    return 0
  | name :: rest =>
    let mut out : Option String := none
    let mut plant : Plant := .none
    let mut r := rest
    while !r.isEmpty do
      match r with
      | "--out" :: d :: r' => out := some d; r := r'
      | "--plant" :: p :: r' =>
        match Plant.ofString? p with
        | some pl => plant := pl; r := r'
        | none => IO.eprintln s!"unknown plant {p}"; return 2
      | other :: _ => IO.eprintln s!"unexpected argument {other}\n{usage}"; return 2
      | [] => pure ()
    let some dir := out | IO.eprintln usage; return 2
    if name == "all" then
      for (n, g, kind) in graphs do writeGraph n g kind (dir / n) plant
      return 0
    match graphs.find? (·.1 == name) with
    | some (_, g, kind) => writeGraph name g kind dir plant; return 0
    | none => IO.eprintln s!"unknown graph {name}; `obend-emit-gpu list`"; return 2
  | [] => IO.eprintln usage; return 2
