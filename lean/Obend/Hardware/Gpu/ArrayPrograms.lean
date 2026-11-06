module
/- Source programs used by the GPU workload gate. All constructions below produce
lexical array syntax; no construction can supply a graph destination or schedule.
The Core4 member frontend and graph compiler consume the same program values. -/
public import Obend.Hardware.Gpu.ArrayMember
@[expose] public section
namespace Obend.Hardware.Gpu.ArrayPrograms
open Obend.Hardware.OpenHypergraph Obend.Hardware.ArrayHypergraph

/-! ## Source-program construction

The host builder gives stable handles to lexical array values. `sourceBuild` closes
those handles into de Bruijn variables and immutable `letE` syntax. Only the compiler
in `ArraySource` allocates graph wires. The same source program has its own evaluator
and a universal compiler theorem.
-/
namespace AS
export Obend.Hardware.Gpu.ArraySource (Rhs Program wire compile)
end AS

structure Build where
  inputCount : Nat := 0
  bindings : Array AS.Rhs := #[]

abbrev BuildM := StateM Build

/-- Bind one source expression, returning a host-side lexical handle. -/
def bindSource (rhs : AS.Rhs) : BuildM Nat := do
  let st ← get
  set { st with bindings := st.bindings.push rhs }
  pure (st.inputCount + st.bindings.size)

def mapN (n : Nat) (op : ElemOp) (srcs : List Nat) : BuildM Nat :=
  bindSource (.map n op srcs)

def gather (f : FiniteFunction) (a : Nat) : BuildM Nat := bindSource (.gather f a)
def concat (a b : Nat) : BuildM Nat := bindSource (.concat a b)
def constWire (vals : List Word) : BuildM Nat := bindSource (.literal vals)

def broadcast (n : Nat) (v : Word) : BuildM Nat := constWire (List.replicate n v)
def map2 (n : Nat) (op : ElemOp) (a b : Nat) : BuildM Nat := mapN n op [a, b]
def map3 (n : Nat) (op : ElemOp) (a b c : Nat) : BuildM Nat := mapN n op [a, b, c]

/-- Close stable construction handles into lexical variables, most recent first. -/
def closeRhs (next : Nat) : AS.Rhs → AS.Rhs
  | .map n op args => .map n op (args.map (AS.wire next))
  | .gather f a => .gather f (AS.wire next a)
  | .concat a b => .concat (AS.wire next a) (AS.wire next b)
  | .literal vs => .literal vs
  | .fold op shape a => .fold op shape (AS.wire next a)

def sourceBuild (inputs : List Nat → BuildM (List Nat)) (inputLens : List Nat) : AS.Program :=
  let (outs, st) := (inputs (List.range inputLens.length)).run ⟨inputLens.length, #[]⟩
  let result : AS.Program := .ret (outs.map (AS.wire (st.inputCount + st.bindings.size)))
  st.bindings.toList.zipIdx.foldr
    (fun (rhs, index) body => .letE (closeRhs (st.inputCount + index) rhs) body) result

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
  let mut lo ← gather (halfTable n 0) x
  let mut hi ← gather (halfTable n half) x
  let mut out := x
  for s in List.range L do
    let ns := 2 ^ s
    let twTable : FiniteFunction :=
      { source := half, target := half, table := (List.range half).map fun j => (j % ns) * (half / ns) }
    let tw ← gather twTable powers
    let t ← glMul half k hi tw
    let a ← glAdd half k lo t
    let b ← glSub half k lo t
    let ab ← concat a b
    if s + 1 < L then
      lo ← gather (expandTable n ns 0) ab
      hi ← gather (expandTable n ns half) ab
    else
      out := ab
  pure out

def nttSource (n : Nat) : AS.Program :=
  sourceBuild (fun ins => do
    let y ← nttStockham (ins.getD 0 0) n
    pure [y]) [n]

/-- Elementwise `a * b + c` over length-`n` wires, then a gather that reverses it: the lowering's map,
constant and gather kernels on one wire of several workgroups. -/
def macReverseSource (n : Nat) : AS.Program :=
  sourceBuild (fun ins => do
    let a := ins.getD 0 0
    let b := ins.getD 1 0
    let c ← broadcast n 7#64
    let m ← map3 n (.scalar .mac) a b c
    let r ← gather { source := n, target := n, table := (List.range n).reverse } m
    pure [m, r]) [n, n]

/-- A field multiply alone, elementwise, for the arithmetic tooth on big words. -/
def glMulSource (n : Nat) : AS.Program :=
  sourceBuild (fun ins => do
    let k ← glConsts n
    let y ← glMul n k (ins.getD 0 0) (ins.getD 1 0)
    pure [y]) [n, n]


/-- A real closed Core4 method, whose array argument is a product of index functions. -/
def memberComposition (name : String) (inputLengths : List Nat) (program : ArraySource.Program) :
    Obend.Logic.Composition :=
  { top := { name := name, metadata := .record [], fields := [("run", .lam (ArrayMember.body program inputLengths))], flat := true }
    below := [], seed := [] }

/-- The emitter obtains a typed graph only by selecting and checking the actual
Core4 member. Failure is retained; there is no fallback to direct graph compilation. -/
def compileSource (name : String) (inputLengths : List Nat) (program : ArraySource.Program) :
    Except String (ArrayMember.Plan (memberComposition name inputLengths program) "run") :=
  ArrayMember.checkMember (memberComposition name inputLengths program) "run" program inputLengths

end Obend.Hardware.Gpu.ArrayPrograms
