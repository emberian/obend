/-
# Obend.Hardware.GpuGraphs — the array graphs the GPU rungs run

The graphs `obend-emit-gpu` lowers to shaders (`hardware/gpu/graphs/`) and `obend-rdna2` certifies against
RADV's machine code (rung G2): a builder for array graphs, the Goldilocks field operations elementwise
(the limb network of `Obend.Apps.ZkNtt.glMul`), Stockham radix-2 NTTs, and the scalar graphs as their
one-element instance. Moved out of the emitter so that the certificate's theorem can name the graph it
is about. The emitter's description of the NTT (Stockham, ec-gpu's `radix_fft` indexing) is in
`lean/tools/emitgpu/EmitGpu.lean`.
-/
module
public import Obend.Hardware.Gpu
@[expose] public section

namespace Obend.Hardware.GpuGraphs
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

end Obend.Hardware.GpuGraphs
