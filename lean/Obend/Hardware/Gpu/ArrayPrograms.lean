module
/- Source programs used by the GPU workload gate. Public constructors produce
lexical array syntax, directly or by checked reification of shared arithmetic.
GPU emission selects the actual Core4 member before compiling that source. -/
public import Obend.Hardware.Gpu.ArrayMember
public import Obend.Hardware.Gpu.ArrayReify
public import Obend.Hardware.Gpu.GoldilocksSource
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

/-! The sole Goldilocks arithmetic construction is `GoldilocksSource`, shared with
indexed kernels. Reification below recovers lexical syntax and checks its exact graph
round trip before the usual Core4 member checker runs. The workgroup NTT in `Gpu.Ntt`
is outside this flat SOAC fragment; no per-layer NTT construction is retained here. -/

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

/-- A field multiply from the shared arithmetic construction, admitted as lexical
source only after a structural round trip. This is not a direct graph entry point. -/
def glMulSource (n : Nat) : Except String AS.Program := do
  let g := ArrayBuild.runBuild (fun ins => do
    let k ← GoldilocksSource.glConsts n
    let y ← GoldilocksSource.glMul n k (ins.getD 0 0) (ins.getD 1 0)
    pure [y]) [n, n]
  return (← ArrayReify.reify [n,n] g).program

/-- Routing and constant source fixture shared by the GPU and RTL square. -/
def arrayRouteSource : AS.Program :=
  sourceBuild (fun ins => do
    let x := ins.getD 0 0
    let constants ← constWire [11#64, BitVec.ofInt 64 (-3), 4294967297#64, 7#64]
    let sum ← map2 4 (.scalar .add) x constants
    let rev ← gather ⟨4,4,[3,2,1,0]⟩ sum
    let result ← concat rev sum
    pure [result]) [4]

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
