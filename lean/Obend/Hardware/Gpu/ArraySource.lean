module
/-
# A lexical source language for regular arrays

This is the ANF array fragment of the Futhark/Accelerate separation: a program binds
immutable array values with `letE`, uses de Bruijn variables, and returns arrays.
It contains no graph wire identifiers, destinations, scheduling or storage layout.
The compiler assigns fresh wires. Its correctness is structural, for every scoped
source program and every array environment, including empty arrays.

Futhark PLDI 2017 §2 supplies the SOAC/let semantics; Accelerate separates scalar and
collective expressions. Dex motivates observing arrays by index. NESL's segmented
operations and Lift's separation of patterns from schedules inform the fold extension.
References: https://elsman.com/pdf/pldi17.pdf;
https://www.acceleratehs.org/documentation/users-guide/language.html;
https://arxiv.org/abs/2104.05372; https://www.cs.cmu.edu/~scandal/nesl.html;
https://eprints.gla.ac.uk/146596/.
-/
public import Obend.Hardware.Gpu
public import Obend.Core.Term
@[expose] public section
namespace Obend.Hardware.Gpu.ArraySource
open Obend.Hardware.ArrayHypergraph Obend.Hardware.OpenHypergraph
set_option autoImplicit false

/-- A source right-hand side. Variables count outwards from the most recent let.
`map` is an n-ary scalar primitive applied pointwise; larger scalar functions are
ordinary let compositions. Gather tables are source index functions. -/
inductive Rhs where
  | map (size : Nat) (op : ElemOp) (args : List Nat)
  | gather (indices : FiniteFunction) (array : Nat)
  | concat (left right : Nat)
  | literal (values : Vec)
  | fold (op : ReduceOp) (shape : FoldShape) (array : Nat)
  deriving Repr

/-- Lexical immutable bindings, not a list of graph assignments. -/
inductive Program where
  | ret (arrays : List Nat)
  | letE (value : Rhs) (body : Program)
  deriving Repr

abbrev Env := Nat → Vec

def push (v : Vec) (env : Env) : Env
  | 0 => v
  | i + 1 => env i

/-- Denotation before graph allocation. Out-of-range array elements are zero, as
in the word-array backend; scoping and shape checks reject invalid variable/index use. -/
def Rhs.eval (env : Env) : Rhs → Vec
  | .map n op args => (List.range n).map fun i =>
      evalElemOp op (args.map fun a => (env a).getD i 0#64)
  | .gather f a => f.table.map fun i => (env a).getD i 0#64
  | .concat a b => env a ++ env b
  | .literal vs => vs
  | .fold op shape a => evalFold op shape (fun i => (env a).getD i 0#64)

def Program.eval (env : Env) : Program → List Vec
  | .ret arrays => arrays.map env
  | .letE value body => body.eval (push (value.eval env) env)

def Rhs.vars : Rhs → List Nat
  | .map _ _ args => args
  | .gather _ a => [a]
  | .concat a b => [a, b]
  | .literal _ => []
  | .fold _ _ a => [a]

def Rhs.Scoped (n : Nat) (r : Rhs) : Prop := ∀ i ∈ r.vars, i < n

def Program.Scoped (n : Nat) : Program → Prop
  | .ret arrays => ∀ i ∈ arrays, i < n
  | .letE value body => value.Scoped n ∧ body.Scoped (n + 1)

/-- Decidable lexical scope check, independent of graph compilation. -/
def Program.scopedB (p : Program) (n : Nat) : Bool :=
  match p with
  | .ret arrays => arrays.all (· < n)
  | .letE value body => value.vars.all (· < n) && body.scopedB (n + 1)

theorem Program.scopedB_sound (p : Program) (n : Nat) (h : p.scopedB n = true) :
    p.Scoped n := by
  induction p generalizing n with
  | ret arrays => simpa [Program.scopedB, Program.Scoped, List.all_eq_true] using h
  | letE value body ih =>
    simp only [Program.scopedB, Bool.and_eq_true] at h
    exact ⟨by simpa [Rhs.Scoped, List.all_eq_true] using h.1, ih (n + 1) h.2⟩

/-- Lexical variable to allocated storage; only used under `i < next`. -/
def wire (next i : Nat) : Nat := next - 1 - i

def Rhs.edge (next : Nat) : Rhs → ArrayEdge
  | .map n op args =>
      let src := args.map (wire next)
      ⟨next, .map n (.single op src next), src, next⟩
  | .gather f a => ⟨next, .gather f, [wire next a], next⟩
  | .concat a b => ⟨next, .concat, [wire next a, wire next b], next⟩
  | .literal vs => ⟨next, .const vs, [], next⟩
  | .fold op shape a => ⟨next, .fold op shape, [wire next a], next⟩

def Rhs.length (lens : Nat → Nat) : Rhs → Nat
  | .map n _ _ => n
  | .gather f _ => f.table.length
  | .concat a b => lens a + lens b
  | .literal vs => vs.length
  | .fold _ shape _ => shape.outLen

def Program.edges (next : Nat) : Program → List ArrayEdge
  | .ret _ => []
  | .letE value body => value.edge next :: body.edges (next + 1)

def Program.outputs (next : Nat) : Program → List Nat
  | .ret arrays => arrays.map (wire next)
  | .letE _ body => body.outputs (next + 1)

def Program.lengths (context : List Nat) : Program → List Nat
  | .ret _ => []
  | .letE value body =>
      let n := value.length (fun i => context.getD i 0)
      n :: body.lengths (n :: context)

/-- Inputs retain their public left-to-right order; lexical variables count back
from the last input, just as they count back from the last let. -/
def compile (inputLengths : List Nat) (p : Program) : ArrayGraph :=
  ⟨inputLengths ++ p.lengths inputLengths.reverse, List.range inputLengths.length,
    p.outputs inputLengths.length, p.edges inputLengths.length⟩

def Represents (next : Nat) (source target : Env) : Prop :=
  ∀ i, i < next → target (wire next i) = source i

@[simp] theorem Rhs.edge_dst (r : Rhs) (next : Nat) : (r.edge next).dstWire = next := by
  cases r <;> rfl

theorem Rhs.edge_sound (r : Rhs) (next : Nat) (source target : Env)
    (hs : r.Scoped next) (hr : Represents next source target) :
    edgeValue target (r.edge next) = r.eval source := by
  cases r with
  | literal vs => rfl
  | fold op shape a =>
    have ha := hr a (hs a (by simp [Rhs.vars]))
    simp [edgeValue, edgeSrcs, Rhs.edge, evalArrayOp, Rhs.eval, ha]
  | gather f a =>
    have ha := hr a (hs a (by simp [Rhs.vars]))
    simpa [edgeValue, edgeSrcs, Rhs.edge, evalArrayOp, Rhs.eval] using
      congrArg (fun xs : Vec => f.table.map fun i => xs.getD i 0#64) ha
  | concat a b =>
    have ha := hr a (hs a (by simp [Rhs.vars]))
    have hb := hr b (hs b (by simp [Rhs.vars]))
    simp [edgeValue, edgeSrcs, Rhs.edge, evalArrayOp, Rhs.eval, ha, hb]
  | map n op args =>
    simp only [edgeValue, edgeSrcs, Rhs.edge, evalArrayOp, evalProg_single, Rhs.eval]
    apply List.map_congr_left
    intro i _
    congr 1
    simp only [List.map_map]
    apply List.map_congr_left
    intro a ha
    have hl := srcLookup_map target (args.map (wire next)) (wire next a) (List.mem_map.mpr ⟨a, ha, rfl⟩)
    simp only [List.map_map] at hl
    simp only [Function.comp_apply, hl]
    rw [hr a (hs a ha)]

theorem Represents.step (r : Rhs) (next : Nat) (source target : Env)
    (hs : r.Scoped next) (hr : Represents next source target) :
    Represents (next + 1) (push (r.eval source) source) (stepEdge target (r.edge next)) := by
  intro i hi
  cases i with
  | zero => simp [wire, stepEdge, r.edge_sound next source target hs hr, push]
  | succ i =>
    have hin : i < next := by omega
    have hw : wire (next + 1) (i + 1) = wire next i := by unfold wire; omega
    have hn : wire next i ≠ next := by unfold wire; omega
    simpa [stepEdge, hw, hn, push] using hr i hin

/-- Compiler correctness for every lexical program; no fixture or semantic
certificate is an input to the compiler or a hypothesis of the theorem. -/
theorem Program.lower_sound (p : Program) (next : Nat) (source target : Env)
    (hs : p.Scoped next) (hr : Represents next source target) :
    (p.outputs next).map (evalComb target (p.edges next)) = p.eval source := by
  induction p generalizing next source target with
  | ret arrays =>
    simp only [Program.outputs, Program.edges, Program.eval, evalComb, List.foldl_nil, List.map_map]
    exact List.map_congr_left fun i hi => hr i (hs i hi)
  | letE value body ih =>
    simp only [Program.outputs, Program.edges, Program.eval, evalComb, List.foldl_cons]
    exact ih (next + 1) (push (value.eval source) source) (stepEdge target (value.edge next))
      hs.2 (Represents.step value next source target hs.1 hr)

/-- The public graph compiler has the source denotation on all boundary arrays. -/
theorem compile_sound (inputLengths : List Nat) (p : Program) (source target : Env)
    (hs : p.Scoped inputLengths.length) (hr : Represents inputLengths.length source target) :
    evalGraph (compile inputLengths p) target = p.eval source :=
  p.lower_sound inputLengths.length source target hs hr

/-- A closed indexed array observation. The finite array is represented by its
length and a mathematical index function; this does not extend Core4's syntax. -/
def observe (vs : Vec) (i : Nat) : Obend.Core.Term.Term :=
  .nat (vs.getD i 0#64).toNat

/-- Extensional observation version of the compiler theorem. This states exactly
which array observation is being preserved; it makes no claim that Core4 has an
array primitive or that encoding already-evaluated values proves source reduction. -/
theorem compile_observe (inputLengths : List Nat) (p : Program) (source target : Env)
    (hs : p.Scoped inputLengths.length) (hr : Represents inputLengths.length source target)
    (output index : Nat) :
    observe ((evalGraph (compile inputLengths p) target).getD output []) index =
      observe ((p.eval source).getD output []) index := by
  rw [compile_sound inputLengths p source target hs hr]

end Obend.Hardware.Gpu.ArraySource
