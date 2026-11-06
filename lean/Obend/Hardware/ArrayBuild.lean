module
public import Obend.Hardware.ArrayHypergraph

/-! The shared array graph/register-program builder. The GPU emitter uses this
construction directly; `registerCode` specializes the same edges to scalar
register instructions for indexed kernels. -/
@[expose] public section
namespace Obend.Hardware.ArrayBuild
open Obend.Hardware.OpenHypergraph Obend.Hardware.ArrayHypergraph

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

def registerCode (st : Build) : List Instr := st.edges.toList.flatMap fun e =>
  match e.op with
  | .map _ prog => prog.code
  | .const vs => [⟨.scalar (.const ((vs.getD 0 0#64).toInt)), [], e.dstWire⟩]
  | _ => []

/-- Interpret the register code emitted so far, starting with an arbitrary
initial environment. This makes extension theorems compose prior programs. -/
def evalBuild (st : Build) (env : Nat → Word) : Nat → Word :=
  runCode env (registerCode st)

theorem mapN_run (st : Build) (n : Nat) (op : ElemOp) (args : List Nat) :
    (mapN n op args).run st =
      (st.lengths.size,
       { lengths := st.lengths.push n,
         edges := st.edges.push
           { opIdx := st.edges.size, op := .map n (ElemProg.single op args st.lengths.size),
             srcWires := args, dstWire := st.lengths.size } }) := rfl

/-- Appending a map appends exactly its scalar instruction. -/
theorem registerCode_mapN (st : Build) (n : Nat) (op : ElemOp) (args : List Nat) :
    registerCode ((mapN n op args).run st).2 =
      registerCode st ++ [⟨op, args, st.lengths.size⟩] := by
  rw [mapN_run]
  simp [registerCode, ElemProg.single]

theorem mapN_fresh (st : Build) (n : Nat) (op : ElemOp) (args : List Nat) :
    ((mapN n op args).run st).1 = st.lengths.size ∧
    ((mapN n op args).run st).2.lengths.size = st.lengths.size + 1 := by
  rw [mapN_run]
  simp

theorem evalBuild_mapN (st : Build) (n : Nat) (op : ElemOp) (args : List Nat)
    (env : Nat → Word) :
    evalBuild ((mapN n op args).run st).2 env =
      stepInstr (evalBuild st env) ⟨op, args, st.lengths.size⟩ := by
  simp only [evalBuild, registerCode_mapN, runCode, List.foldl_append, List.foldl_cons,
    List.foldl_nil]

end Obend.Hardware.ArrayBuild
