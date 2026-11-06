module
/-
# A checked flat-map frontend for Core4 members

The scalar/collective separation is the one in Accelerate's language specification
(https://www.acceleratehs.org/documentation/users-guide/language.html), and `map` is the
basic SOAC of Henriksen et al., PLDI 2017 (https://elsman.com/pdf/pldi17.pdf).
This module implements the regular, one-dimensional map fragment, not nested parallelism.

Core4 naturals do not wrap. Consequently the accepted arithmetic syntax explicitly takes
addition and multiplication modulo 2^64. Bitwise operations have Core4's word semantics.
The compiler produces ordinary primitive ArrayGraph edges, so the existing fusion and
GPU lowering apply. Translation validation compares symbolic *syntax*, not sampled results
or a proposition asserting the desired semantics. The validator's soundness is universal.
-/
public import Obend.Hardware.Gpu.SourceElem
@[expose] public section
namespace Obend.Hardware.Gpu.Source
open Obend.Core.Term Obend.Equiv Obend.Leaf
open Obend.Hardware.ArrayHypergraph Obend.Hardware.OpenHypergraph
set_option autoImplicit false

inductive Scalar where
  | arg (index : Nat)
  | lit (v : Word)
  | bin (op : Binary) (left right : Scalar)
  | mux (condition whenTrue whenFalse : Scalar)
  deriving DecidableEq, Repr

def Scalar.eval (x : Nat → Word) : Scalar → Word
  | .arg i => x i
  | .lit v => v
  | .bin b l r => b.eval (l.eval x) (r.eval x)
  | .mux c l r => muxEval (c.eval x) (l.eval x) (r.eval x)

def Scalar.term : Scalar → Term
  | .arg i => .bound i
  | .lit v => .nat v.toNat
  | .bin b l r => b.term l.term r.term
  | .mux c l r => muxTerm c.term l.term r.term

/-- Parser candidates are checked by exact Core4 syntax equality below. -/
def readRaw : Term → Option Scalar
  | .bound i => some (.arg i)
  | .nat n => some (.lit (BitVec.ofNat 64 n))
  | .binary .modulo (.binary .add x y) (.nat _) =>
    return .bin .add (← readRaw x) (← readRaw y)
  | .binary .modulo (.binary .multiply x y) (.nat _) =>
    return .bin .mul (← readRaw x) (← readRaw y)
  | .binary .modulo (.binary .subtract (.binary .add x (.nat _)) y) (.nat _) =>
    return .bin .sub (← readRaw x) (← readRaw y)
  | .ifBool (.binary .less y (.nat 64)) (.binary .shl x _) (.nat 0) =>
    return .bin .shl (← readRaw x) (← readRaw y)
  | .ifBool (.binary .less y (.nat 64)) (.binary .lshr x _) (.nat 0) =>
    return .bin .shr (← readRaw x) (← readRaw y)
  | .ifBool (.binary .less x y) (.nat 1) (.nat 0) =>
    return .bin .ult (← readRaw x) (← readRaw y)
  | .ifBool (.binary .equal c (.nat 0)) y x =>
    return .mux (← readRaw c) (← readRaw x) (← readRaw y)
  | .binary .bitAnd x y => return .bin .band (← readRaw x) (← readRaw y)
  | .binary .bitOr x y => return .bin .bor (← readRaw x) (← readRaw y)
  | _ => none

/-- A proof-producing *syntactic* recognizer. Wrong moduli and oversized literals are refused. -/
def read (t : Term) : Option {s : Scalar // s.term = t} := do
  let s ← readRaw t
  if h : Obend.Law.termEq s.term t = true then some ⟨s, Obend.Law.termEq_sound h⟩ else none

theorem Scalar.substitute_congr (s : Scalar) (σ τ : Nat → Term) (h : ∀ i, σ i = τ i) :
    s.term.substitute σ = s.term.substitute τ := by
  induction s with
  | arg i => simpa [Scalar.term, Term.substitute] using h i
  | lit => simp [Scalar.term, Term.substitute]
  | bin b l r il ir => simp only [Scalar.term, Binary.substitute, il, ir]
  | mux c l r ic il ir => simp only [Scalar.term, mux_substitute, ic, il, ir]

/-- Every recognized scalar expression reduces in Core4 to its word denotation. -/
theorem Scalar.sound (s : Scalar) (x : Nat → Word) (σ : Nat → Term) (h : ∀ i, σ i = .nat (x i).toNat) :
    Steps (s.term.substitute σ) (.nat (s.eval x).toNat) := by
  induction s with
  | arg i => simpa [Scalar.term, Term.substitute, Scalar.eval, h i] using Steps.refl (.nat (x i).toNat)
  | lit v => simpa [Scalar.term, Term.substitute, Scalar.eval] using Steps.refl (.nat v.toNat)
  | bin b l r il ir =>
    simp only [Scalar.term, Binary.substitute, Scalar.eval]
    exact b.sound _ _ il ir
  | mux c l r ic il ir =>
    simp only [Scalar.term, mux_substitute, Scalar.eval]
    exact mux_sound _ _ _ ic il ir

inductive Node where
  | lit (v : Word) (dst : Nat)
  | bin (op : Binary) (left right dst : Nat)
  | mux (condition left right dst : Nat)
  deriving DecidableEq, Repr

def Node.dst : Node → Nat
  | .lit _ d | .bin _ _ _ d | .mux _ _ _ d => d

def Node.rhs (σ : Nat → Scalar) : Node → Scalar
  | .lit v _ => .lit v
  | .bin b l r _ => .bin b (σ l) (σ r)
  | .mux c l r _ => .mux (σ c) (σ l) (σ r)

def Node.symbolic (σ : Nat → Scalar) (d : Node) : Nat → Scalar :=
  fun w => if w == d.dst then d.rhs σ else σ w

def Node.edge (n : Nat) : Node → ArrayEdge
  | .lit v d => ⟨d, .map n (.single (.scalar (.const (Int.ofNat v.toNat))) [] d), [], d⟩
  | .bin b l r d => ⟨d, .map n (.single b.op [l, r] d), [l, r], d⟩
  | .mux c l r d => ⟨d, .map n (.single (.scalar .mux) [c, l, r] d), [c, l, r], d⟩

def denote (n : Nat) (xs : Nat → Vec) (s : Scalar) : Vec :=
  (List.range n).map fun i => s.eval (fun w => (xs w).getD i 0#64)

/-- Executable source reference: flat arrays and constant-time indexing, including the input
arrays. The list-valued `denote` is used only in propositions. -/
def evalMapExec (s : Scalar) (n : Nat) (inputs : Array (Array Word)) : Array Word :=
  (Array.range n).map fun i => s.eval fun w => (inputs.getD w #[]).getD i 0#64

theorem evalMapExec_eq (s : Scalar) (n : Nat) (inputs : Array (Array Word)) :
    (evalMapExec s n inputs).toList = denote n (fun w => (inputs.getD w #[]).toList) s := by
  simp [evalMapExec, denote]

def Represents (n : Nat) (xs : Nat → Vec) (σ : Nat → Scalar) (env : Nat → Vec) : Prop :=
  ∀ w, env w = denote n xs (σ w)

theorem denote_get (n : Nat) (xs : Nat → Vec) (s : Scalar) (i : Nat) (hi : i < n) :
    (denote n xs s).getD i 0#64 = s.eval (fun w => (xs w).getD i 0#64) :=
  getD_range_map n _ _ i hi

theorem Node.value_sound (n : Nat) (xs : Nat → Vec) (σ : Nat → Scalar) (env : Nat → Vec)
    (h : Represents n xs σ env) (d : Node) :
    edgeValue env (d.edge n) = denote n xs (d.rhs σ) := by
  cases d with
  | lit v dst =>
    simp [edgeValue, edgeSrcs, Node.edge, evalArrayOp, evalProg_single, evalElemOp,
      evalHypergraphOpBv, Node.rhs, denote, Scalar.eval]
  | bin b l r dst =>
    simp only [edgeValue, edgeSrcs, Node.edge, evalArrayOp, evalProg_single]
    apply List.map_congr_left
    intro i hi
    have hin : i < n := List.mem_range.mp hi
    have hl := srcLookup_map env [l, r] l (by simp)
    have hr := srcLookup_map env [l, r] r (by simp)
    simp only [List.map_cons, List.map_nil] at hl hr
    simp only [List.map_cons, List.map_nil]
    rw [hl, hr, h l, h r, denote_get n xs _ i hin, denote_get n xs _ i hin]
    cases b <;> rfl
  | mux c l r dst =>
    simp only [edgeValue, edgeSrcs, Node.edge, evalArrayOp, evalProg_single]
    apply List.map_congr_left
    intro i hi
    have hin : i < n := List.mem_range.mp hi
    have hc := srcLookup_map env [c, l, r] c (by simp)
    have hl := srcLookup_map env [c, l, r] l (by simp)
    have hr := srcLookup_map env [c, l, r] r (by simp)
    simp only [List.map_cons, List.map_nil] at hc hl hr
    simp only [List.map_cons, List.map_nil]
    rw [hc, hl, hr, h c, h l, h r, denote_get n xs _ i hin,
      denote_get n xs _ i hin, denote_get n xs _ i hin]
    rfl

theorem Node.step_sound (n : Nat) (xs : Nat → Vec) (σ : Nat → Scalar) (env : Nat → Vec)
    (h : Represents n xs σ env) (d : Node) :
    Represents n xs (d.symbolic σ) (stepEdge env (d.edge n)) := by
  intro w
  have hd : (d.edge n).dstWire = d.dst := by cases d <;> rfl
  simp only [stepEdge, hd, Node.symbolic]
  split
  · exact d.value_sound n xs σ env h
  · exact h w

def runSymbolic (σ : Nat → Scalar) (ds : List Node) : Nat → Scalar :=
  ds.foldl Node.symbolic σ

theorem run_sound (n : Nat) (xs : Nat → Vec) (ds : List Node) (σ : Nat → Scalar) (env : Nat → Vec)
    (h : Represents n xs σ env) :
    Represents n xs (runSymbolic σ ds) (evalComb env (ds.map (Node.edge n))) := by
  induction ds generalizing σ env with
  | nil => exact h
  | cons d ds ih =>
    exact ih (d.symbolic σ) (stepEdge env (d.edge n)) (d.step_sound n xs σ env h)

/-- The producer uses fresh monotonically increasing wire names. Its output is checked below. -/
def lowerScalar : Scalar → Nat → List Node × Nat × Nat
  | .arg i, next => ([], i, next)
  | .lit v, next => ([.lit v next], next, next + 1)
  | .bin b l r, next =>
    let (ls, lw, next) := lowerScalar l next
    let (rs, rw, next) := lowerScalar r next
    (ls ++ rs ++ [.bin b lw rw next], next, next + 1)
  | .mux c l r, next =>
    let (cs, cw, next) := lowerScalar c next
    let (ls, lw, next) := lowerScalar l next
    let (rs, rw, next) := lowerScalar r next
    (cs ++ ls ++ rs ++ [.mux cw lw rw next], next, next + 1)

def inputSymbols (inputs : Nat) : Nat → Scalar :=
  fun w => if w < inputs then .arg w else .lit 0#64

structure MapPlan where
  scalar : Scalar
  size : Nat
  inputs : Nat
  nodes : List Node
  output : Nat
  wires : Nat
  /-- Symbolic translation validation; this compares finite syntax, never runtime answers. -/
  sourceEq : runSymbolic (inputSymbols inputs) nodes output = scalar

def MapPlan.graph (p : MapPlan) : ArrayGraph :=
  ⟨List.replicate p.wires p.size, List.range p.inputs, [p.output], p.nodes.map (Node.edge p.size)⟩

def compileMap (s : Scalar) (n inputs : Nat) : Option MapPlan :=
  let (ds, out, wires) := lowerScalar s inputs
  if h : runSymbolic (inputSymbols inputs) ds out = s then
    some ⟨s, n, inputs, ds, out, wires, h⟩
  else none

/-- Input wires carry the supplied arrays; every scratch wire initially contains zero, as in the
deployed GPU runner. Undeclared argument reads cannot pass symbolic validation. -/
def MapPlan.env (p : MapPlan) (xs : Nat → Vec) : Nat → Vec :=
  fun w => denote p.size xs (inputSymbols p.inputs w)

theorem MapPlan.eval_sound (p : MapPlan) (xs : Nat → Vec) :
    evalGraph p.graph (p.env xs) = [denote p.size xs p.scalar] := by
  have h := run_sound p.size xs p.nodes (inputSymbols p.inputs) (p.env xs) (fun _ => rfl)
  change [evalComb (p.env xs) (p.nodes.map (Node.edge p.size)) p.output] = _
  rw [h p.output, p.sourceEq]

/-- Universal source-to-dispatch equality. Well-formedness is independently decidable; the
frontend's symbolic check does not assume or test this equation. -/
theorem MapPlan.gpu_sound (p : MapPlan) (hwf : p.graph.wf = true) (xs : Nat → Vec)
    (flat : Nat → Word) (hflat : Flat p.graph.lengths (p.env xs) flat) :
    runProgram (lowerArrayToGpu p.graph) flat = [denote p.size xs p.scalar] := by
  rw [lowerArrayToGpu_sound p.graph hwf (p.env xs) flat ?_ hflat, p.eval_sound]
  intro w hw
  simp only [MapPlan.graph, List.length_replicate] at hw
  simp [MapPlan.env, denote, MapPlan.graph, List.getD_eq_getElem?_getD, List.getElem?_replicate_of_lt hw]

/-- Free scalar argument indices, used to check the unary member interface. -/
def Scalar.args : Scalar → List Nat
  | .arg i => [i]
  | .lit _ => []
  | .bin _ l r => l.args ++ r.args
  | .mux c l r => c.args ++ l.args ++ r.args

def Scalar.unary (s : Scalar) : Bool := s.args.all (· == 0)

theorem Scalar.unary_index (s : Scalar) (h : s.unary = true) (i : Nat) (hi : i ∈ s.args) :
    i = 0 := by
  exact beq_iff_eq.mp (List.all_eq_true.mp h i hi)

theorem Scalar.substitute_on (s : Scalar) (σ τ : Nat → Term)
    (h : ∀ i ∈ s.args, σ i = τ i) : s.term.substitute σ = s.term.substitute τ := by
  induction s with
  | arg i => simpa [Scalar.term, Term.substitute] using h i (by simp [Scalar.args])
  | lit v => simp [Scalar.term, Term.substitute]
  | bin b l r il ir =>
    simp only [Scalar.term, Binary.substitute]
    rw [il (fun i hi => h i (by simp [Scalar.args, hi])),
      ir (fun i hi => h i (by simp [Scalar.args, hi]))]
  | mux c l r ic il ir =>
    simp only [Scalar.term, mux_substitute]
    rw [ic (fun i hi => h i (by simp [Scalar.args, hi])),
      il (fun i hi => h i (by simp [Scalar.args, hi])),
      ir (fun i hi => h i (by simp [Scalar.args, hi]))]

theorem Scalar.unary_lam (s : Scalar) (hu : s.unary = true) (self : Term) :
    instantiate (.lam s.term) self = .lam s.term := by
  simp only [instantiate_eq, Term.substitute]
  congr 1
  rw [s.substitute_on (liftSubstitution (single self)) Term.bound (by
    intro i hi
    have := s.unary_index hu i hi
    subst i
    rfl), substitute_bound]

theorem Scalar.unary_apply (s : Scalar) (hu : s.unary = true) (x : Word) :
    Steps (.app (.lam s.term) (.nat x.toNat)) (.nat (s.eval (fun _ => x)).toNat) := by
  refine .next (.beta _ _) ?_
  rw [instantiate_eq, s.substitute_on (single (.nat x.toNat)) (fun _ => .nat x.toNat) (by
    intro i hi
    have := s.unary_index hu i hi
    subst i
    rfl)]
  exact s.sound (fun _ => x) (fun _ => .nat x.toNat) (fun _ => rfl)

/-- Reading a closed scalar method from the flattened vtable has its actual Core4 meaning. -/
theorem flat_member_steps (vt : List (String × Term)) (m : String) (s : Scalar)
    (hu : s.unary = true) (hm : vt.find? (·.1 == m) = some (m, .lam s.term)) (x : Word) :
    Steps (.app (.get (flatObject vt) m) (.nat x.toNat))
      (.nat (s.eval (fun _ => x)).toNat) := by
  obtain ⟨mid, first, rest⟩ := flatObject_unfold vt
  have lookup := find_mapFields (instantiate · (flatObject vt)) hm
  have getsteps : Steps (.get (flatObject vt) m) (.lam s.term) := by
    refine steps_trans (steps_get m (.next first rest)) ?_
    rw [s.unary_lam hu] at lookup
    exact .next (.field _ _ _ lookup) (.refl _)
  exact steps_trans (steps_app _ getsteps) (s.unary_apply hu x)

/-- Both ends of the existing Leaf theorem are used: emitted book lookup and the original open
object's member have the same ground answer as the scalar source expression. -/
theorem composition_member_halts (C : Obend.Logic.Composition) (hc : C.closedB = true)
    (m : String) (s : Scalar) (hu : s.unary = true)
    (hm : C.vtable.find? (·.1 == m) = some (m, .lam s.term)) (x : Word) :
    Halts (.app (.get C.object m) (.nat x.toNat)) (.natural (s.eval (fun _ => x)).toNat) := by
  have hf : Halts (.app (.get (flatObject C.vtable) m) (.nat x.toNat))
      (.natural (s.eval (fun _ => x)).toNat) :=
    ⟨_, ⟨flat_member_steps C.vtable m s hu hm x, .natural _⟩, .natural _⟩
  have hb : Halts (.app (.get (emit C).link m) (.nat x.toNat))
      (.natural (s.eval (fun _ => x)).toNat) :=
    ((sameRuns_of_ahead (.app (.get m (link_ahead C.vtable)) (.refl _))).halts _).mpr hf
  have equiv := book_sound C hc m Term.bound (.app (.bound 0) (.nat x.toNat))
  have eqruns : SameRuns (.app (.get (emit C).link m) (.nat x.toNat))
      (.app (.get C.object m) (.nat x.toNat)) := by
    simpa [instantiate_eq, Term.substitute, substitute_bound, single] using equiv
  exact (eqruns.halts _).mp hb

structure MemberPlan (C : Obend.Logic.Composition) (m : String) where
  plan : MapPlan
  unary : plan.scalar.unary = true
  member : C.vtable.find? (·.1 == m) = some (m, .lam plan.scalar.term)

/-- Parse a selected method of the emitted composition. Diagnostics distinguish missing members,
non-methods, unsupported scalar forms, and free argument/self reads. -/
def compileMember (C : Obend.Logic.Composition) (m : String) (n : Nat) :
    Except String (MemberPlan C m) := do
  match C.vtable.find? (·.1 == m) with
  | none => throw s!"unknown Leaf member {m}"
  | some (_, .lam body) =>
    let s ← match read body with
      | none => throw s!"unsupported Core4 scalar form in {m}: {repr body}"
      | some s => pure s.val
    if hu : s.unary = true then
      match compileMap s n 1 with
      | none => throw "scalar-to-SSA symbolic translation check failed"
      | some p =>
        match hm : C.vtable.find? (·.1 == m) with
        | some (name, body) =>
          if hn : name = m then
            if ht : Obend.Law.termEq body (.lam p.scalar.term) = true then
              if hup : p.scalar.unary = true then
                pure ⟨p, hup, by rw [hm, hn, Obend.Law.termEq_sound ht]⟩
              else throw "compiled member has a free argument"
            else throw "compiled member syntax differs from source"
          else throw "selected member name differs from source"
        | none => throw "selected member disappeared"
    else throw s!"member {m} reads self or an argument outside the unary map fragment"
  | some _ => throw s!"member {m} is not a scalar method"

/-- End to end: executing the shader program yields one result vector, and every element is the
Core4 observation of the original composition's selected member on that input element. -/
theorem MemberPlan.source_to_gpu (C : Obend.Logic.Composition) (m : String)
    (p : MemberPlan C m) (hc : C.closedB = true) (hwf : p.plan.graph.wf = true)
    (xs : Vec) (flat : Nat → Word)
    (hflat : Flat p.plan.graph.lengths (p.plan.env (fun _ => xs)) flat) :
    runProgram (lowerArrayToGpu p.plan.graph) flat = [denote p.plan.size (fun _ => xs) p.plan.scalar] ∧
    ∀ i, i < p.plan.size →
      Halts (.app (.get C.object m) (.nat (xs.getD i 0#64).toNat))
        (.natural ((denote p.plan.size (fun _ => xs) p.plan.scalar).getD i 0#64).toNat) := by
  refine ⟨p.plan.gpu_sound hwf (fun _ => xs) flat hflat, ?_⟩
  intro i hi
  rw [denote_get _ _ _ i hi]
  exact composition_member_halts C hc m p.plan.scalar p.unary p.member _

end Obend.Hardware.Gpu.Source
end
