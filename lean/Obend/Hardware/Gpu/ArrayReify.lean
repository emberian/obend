module
/- Checked reification of the shared ArrayBuild output into lexical array source.
The producer is untrusted: admission checks lexical scope and an exact structural
round trip, ignoring only the unused operation label. Arithmetic is neither copied
nor recognized by sampled values. Field, array and indexed-kernel constructions can
therefore share one arithmetic source without bypassing the Core4 member frontend. -/
public import Obend.Hardware.Gpu.ArraySource
@[expose] public section
namespace Obend.Hardware.Gpu.ArrayReify
open Obend.Hardware.ArrayHypergraph Obend.Hardware.Gpu.ArraySource
set_option autoImplicit false

/-- `opIdx` labels diagnostics; source compilation labels an edge with its destination. -/
def normalize (e : ArrayEdge) : ArrayEdge := { e with opIdx := e.dstWire }

def canonical (g : ArrayGraph) : ArrayGraph := { g with edges := g.edges.map normalize }

def sameGraph (a b : ArrayGraph) : Prop :=
  a.lengths = b.lengths ∧ a.inputs = b.inputs ∧ a.outputs = b.outputs ∧ a.edges = b.edges

instance (a b : ArrayGraph) : Decidable (sameGraph a b) := by unfold sameGraph; infer_instance

theorem sameGraph_eq {a b : ArrayGraph} (h : sameGraph a b) : a = b := by
  cases a; cases b
  rcases h with ⟨rfl,rfl,rfl,rfl⟩
  rfl

theorem evalComb_normalize (es : List ArrayEdge) (env : Env) :
    evalComb env (es.map normalize) = evalComb env es := by
  induction es generalizing env with
  | nil => rfl
  | cons e es ih =>
    simp only [List.map_cons, evalComb, List.foldl_cons] at *
    exact ih (stepEdge env e)

theorem canonical_eval (g : ArrayGraph) (env : Env) : evalGraph (canonical g) env = evalGraph g env := by
  simp only [canonical, evalGraph, evalComb_normalize]

/-- A scope-checked source witness with an exact graph round-trip certificate. -/
structure Reified (inputLengths : List Nat) (g : ArrayGraph) where
  program : Program
  scope : program.Scoped inputLengths.length
  roundTrip : compile inputLengths program = canonical g

/-- Every accepted reification has the original shared builder's denotation. -/
theorem Reified.eval_sound {inputLengths : List Nat} {g : ArrayGraph}
    (r : Reified inputLengths g) (source target : Env)
    (h : Represents inputLengths.length source target) :
    r.program.eval source = evalGraph g target := by
  rw [← compile_sound inputLengths r.program source target r.scope h, r.roundTrip, canonical_eval]

def reifyRhs (next : Nat) (e : ArrayEdge) : Except String Rhs := do
  unless e.dstWire == next do throw s!"array source reification: destination {e.dstWire} is not next binding {next}"
  unless e.srcWires.all (· < next) do throw "array source reification: forward or out-of-scope read"
  let args := e.srcWires.map (wire next)
  match e.op with
  | .map n p =>
      unless e.primitive do throw "array source reification: map is not a primitive source operation"
      match p.code with
      | [i] => return .map n i.op args
      | _ => throw "array source reification: map instruction count"
  | .gather f =>
      match args with
      | [a] => return .gather f a
      | _ => throw "array source reification: gather arity"
  | .concat =>
      match args with
      | [a,b] => return .concat a b
      | _ => throw "array source reification: concat arity"
  | .const vs =>
      unless args.isEmpty do throw "array source reification: constant has operands"
      return .literal vs
  | .fold op shape =>
      match args with
      | [a] => return .fold op shape a
      | _ => throw "array source reification: fold arity"

/-- Reify any fresh-wire shared construction, then independently validate the result.
Failure is retained; there is no direct graph fallback. -/
def reify (inputLengths : List Nat) (g : ArrayGraph) : Except String (Reified inputLengths g) := do
  let bindings ← g.edges.zipIdx.mapM fun (e,i) => reifyRhs (inputLengths.length + i) e
  let result := Program.ret (g.outputs.map (wire (inputLengths.length + bindings.length)))
  let p := bindings.foldr Program.letE result
  if hs : p.scopedB inputLengths.length = true then
    if hg : sameGraph (compile inputLengths p) (canonical g) then
      return ⟨p, p.scopedB_sound inputLengths.length hs, sameGraph_eq hg⟩
    else throw "array source reification: structural round trip differs from shared construction"
  else throw "array source reification: output is out of lexical scope"

end Obend.Hardware.Gpu.ArrayReify
end
