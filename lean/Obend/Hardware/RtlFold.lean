module
/- Linear-size RTL circuits for the associative array folds. Each consumed input
adds one accumulator wire. Consecutive scan prefixes reuse that wire; only segment
boundaries reset it. This is the same cached-prefix schedule as ArrayFold, expressed
as an SSA circuit rather than duplicating an expression tree for every prefix.
The clean referent is ArrayFold's Futhark/Accelerate fold and scan semantics. -/
public import Obend.Hardware.HDL
public import Obend.Hardware.ArrayFold
@[expose] public section
namespace Obend.Hardware.RtlFold
open Obend.Hardware.HDL Obend.Hardware.ArrayHypergraph
set_option autoImplicit false
abbrev Defs := Array WireAssign

def Agrees (ins regs : Nat → Word) (defs : Defs) (wires : Nat → Word) : Prop :=
  ∀ i, i < defs.size → wires i = evalWireTable ins regs defs.toList i

def Denotes (ins regs : Nat → Word) (defs : Defs) (expr : RtlExpr) (value : Word) : Prop :=
  ∀ wires, Agrees ins regs defs wires → evalRtlExpr ins wires regs expr = value

/-- A circuit extension preserves all previously defined wires, including for any
larger table which agrees on the extension's defined prefix. -/
structure Extends (ins regs : Nat → Word) (before after : Defs) : Prop where
  size : before.size ≤ after.size
  agrees : ∀ wires, Agrees ins regs after wires → Agrees ins regs before wires

theorem Extends.refl (ins regs : Nat → Word) (defs : Defs) : Extends ins regs defs defs :=
  ⟨Nat.le_refl _, fun _ h => h⟩

theorem Extends.trans {ins regs : Nat → Word} {a b c : Defs}
    (h : Extends ins regs a b) (h' : Extends ins regs b c) : Extends ins regs a c :=
  ⟨Nat.le_trans h.size h'.size, fun w hw => h.agrees w (h'.agrees w hw)⟩

theorem Denotes.mono {ins regs : Nat → Word} {a b : Defs} {e : RtlExpr} {v : Word}
    (h : Denotes ins regs a e v) (he : Extends ins regs a b) : Denotes ins regs b e v :=
  fun w hw => h w (he.agrees w hw)

def emit (defs : Defs) (expr : RtlExpr) : Defs :=
  defs.push { wireIdx := defs.size, name := s!"fold_{defs.size}", expr := expr }

@[simp] theorem emit_size (defs : Defs) (expr : RtlExpr) :
    (emit defs expr).size = defs.size + 1 := by simp [emit]

theorem emit_table (ins regs : Nat → Word) (defs : Defs) (expr : RtlExpr) (i : Nat) :
    evalWireTable ins regs (emit defs expr).toList i =
      if i == defs.size then evalRtlExpr ins (evalWireTable ins regs defs.toList) regs expr
      else evalWireTable ins regs defs.toList i := by
  simp [emit, evalWireTable, List.foldl_append]

theorem emit_extends (ins regs : Nat → Word) (defs : Defs) (expr : RtlExpr) :
    Extends ins regs defs (emit defs expr) := by
  refine ⟨by simp, ?_⟩
  intro wires hw i hi
  rw [hw i (by simp; omega), emit_table]
  simp [show i ≠ defs.size by omega]

theorem emit_denotes (ins regs : Nat → Word) (defs : Defs) (expr : RtlExpr) (v : Word)
    (h : Denotes ins regs defs expr v) :
    Denotes ins regs (emit defs expr) (.wireRef defs.size) v := by
  intro wires hw
  simp only [evalRtlExpr]
  rw [hw defs.size (by simp), emit_table]
  simpa using h (evalWireTable ins regs defs.toList) (fun _ _ => rfl)

def combine (op : ReduceOp) (a b : RtlExpr) : RtlExpr :=
  .alu (match op with | .add => .add | .mul => .mul | .band => .bitAnd | .bor => .bitOr) a b

@[simp] theorem combine_eval (op : ReduceOp) (a b : RtlExpr) (ins wires regs : Nat → Word) :
    evalRtlExpr ins wires regs (combine op a b) =
      op.combine (evalRtlExpr ins wires regs a) (evalRtlExpr ins wires regs b) := by
  cases op <;> rfl

/-- Tail-recursive accumulator emission; the Array is owned and each push reuses
its storage. No already-emitted expression is copied into its successor. -/
def range (op : ReduceOp) (read : Nat → RtlExpr) :
    Nat → Nat → RtlExpr → Defs → Defs × RtlExpr
  | _, 0, acc, defs => (defs, acc)
  | start, n + 1, acc, defs =>
      range op read (start + 1) n (.wireRef defs.size)
        (emit defs (combine op acc (read start)))

/-- One wire per consumed input, independent of the size of earlier expressions. -/
theorem range_size (op : ReduceOp) (read : Nat → RtlExpr) (start len : Nat)
    (acc : RtlExpr) (defs : Defs) :
    (range op read start len acc defs).1.size = defs.size + len := by
  induction len generalizing start acc defs with
  | zero => simp [range]
  | succ n ih => simp [range, ih, Nat.add_assoc, Nat.add_comm 1 n]

theorem range_sound (op : ReduceOp) (read : Nat → RtlExpr) (values : Nat → Word)
    (ins regs : Nat → Word) (start len : Nat) (acc : RtlExpr) (value : Word) (defs : Defs)
    (hr : ∀ i, Denotes ins regs defs (read i) (values i))
    (ha : Denotes ins regs defs acc value) :
    Extends ins regs defs (range op read start len acc defs).1 ∧
    Denotes ins regs (range op read start len acc defs).1
      (range op read start len acc defs).2 (foldRange op values start len value) := by
  induction len generalizing start acc value defs with
  | zero => exact ⟨Extends.refl _ _ _, ha⟩
  | succ n ih =>
    let expr := combine op acc (read start)
    have he := emit_extends ins regs defs expr
    have hc : Denotes ins regs defs expr (op.combine value (values start)) := by
      intro wires hw
      simp only [expr, combine_eval, ha wires hw, hr start wires hw]
    have hi := ih (start + 1) (.wireRef defs.size) (op.combine value (values start))
      (emit defs expr) (fun i => (hr i).mono he) (emit_denotes ins regs defs expr _ hc)
    refine ⟨he.trans hi.1, ?_⟩
    simpa [range, foldRange, List.range'_succ] using hi.2

def ExprsDenote (ins regs : Nat → Word) (defs : Defs) (exprs : List RtlExpr) (values : Vec) : Prop :=
  ∀ wires, Agrees ins regs defs wires → exprs.map (evalRtlExpr ins wires regs) = values

theorem ExprsDenote.mono {ins regs : Nat → Word} {a b : Defs} {es : List RtlExpr} {vs : Vec}
    (h : ExprsDenote ins regs a es vs) (he : Extends ins regs a b) : ExprsDenote ins regs b es vs :=
  fun w hw => h w (he.agrees w hw)

/-- Results are accumulated in reverse and reversed once, avoiding a growing
append; only the proof's value lists use append. Prefixes reuse the previous wire. -/
def cached (op : ReduceOp) (read : Nat → RtlExpr) :
    List (Nat × Nat) → Nat → Nat → RtlExpr → Defs → List RtlExpr → Defs × List RtlExpr
  | [], _, _, _, defs, out => (defs, out)
  | (start, len) :: rs, prevStart, prevLen, prev, defs, out =>
      let next := if start == prevStart && prevLen ≤ len then
        range op read (start + prevLen) (len - prevLen) prev defs
        else range op read start len (.const op.identity) defs
      cached op read rs start len next.2 next.1 (next.2 :: out)

theorem cached_sound (op : ReduceOp) (read : Nat → RtlExpr) (values : Nat → Word)
    (ins regs : Nat → Word) (rs : List (Nat × Nat)) (start len : Nat) (prev : RtlExpr)
    (defs : Defs) (out : List RtlExpr) (outValues : Vec)
    (hr : ∀ i, Denotes ins regs defs (read i) (values i))
    (hp : Denotes ins regs defs prev (foldRange op values start len op.identity))
    (ho : ExprsDenote ins regs defs out outValues) :
    Extends ins regs defs (cached op read rs start len prev defs out).1 ∧
    ExprsDenote ins regs (cached op read rs start len prev defs out).1
      (cached op read rs start len prev defs out).2
      ((rs.map (fun r => foldRange op values r.1 r.2 op.identity)).reverse ++ outValues) := by
  induction rs generalizing start len prev defs out outValues with
  | nil => exact ⟨Extends.refl _ _ _, ho⟩
  | cons r rs ih =>
    rcases r with ⟨s,n⟩
    let next := if s == start && len ≤ n then
      range op read (s + len) (n - len) prev defs
      else range op read s n (.const op.identity) defs
    have hn : Extends ins regs defs next.1 ∧
        Denotes ins regs next.1 next.2 (foldRange op values s n op.identity) := by
      dsimp only [next]
      split
      · rename_i h
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
        have hh := range_sound op read values ins regs (s+len) (n-len) prev
          (foldRange op values start len op.identity) defs hr hp
        rw [← h.1, ← foldRange_add, Nat.add_sub_of_le h.2] at hh
        exact hh
      · exact range_sound op read values ins regs s n (.const op.identity) op.identity defs hr
          (fun _ _ => rfl)
    have ht : ExprsDenote ins regs next.1 (next.2 :: out)
        (foldRange op values s n op.identity :: outValues) := by
      intro wires hw
      simp only [List.map_cons, hn.2 wires hw, ho.mono hn.1 wires hw]
    have hi := ih s n next.2 next.1 (next.2 :: out)
      (foldRange op values s n op.identity :: outValues) (fun i => (hr i).mono hn.1) hn.2 ht
    refine ⟨hn.1.trans hi.1, ?_⟩
    simpa only [cached, List.map_cons, List.reverse_cons, List.append_assoc, List.singleton_append] using hi.2

def compile (op : ReduceOp) (shape : FoldShape) (read : Nat → RtlExpr) (defs : Defs) :
    Defs × Array RtlExpr :=
  let result := cached op read shape.ranges 0 0 (.const op.identity) defs []
  (result.1, result.2.reverse.toArray)

theorem map_getD (es : List RtlExpr) (ins wires regs : Nat → Word) (i : Nat) :
    evalRtlExpr ins wires regs (es.getD i (.const 0#64)) =
      (es.map (evalRtlExpr ins wires regs)).getD i 0#64 := by
  induction es generalizing i with
  | nil => simp [evalRtlExpr]
  | cons e es ih => cases i with
    | zero => rfl
    | succ i => exact ih i

/-- The generated circuit preserves the old table and names precisely the fold
outputs, for every read function and every shape, including empty segments. -/
theorem compile_sound (op : ReduceOp) (shape : FoldShape) (read : Nat → RtlExpr) (values : Nat → Word)
    (ins regs : Nat → Word) (defs : Defs)
    (hr : ∀ i, Denotes ins regs defs (read i) (values i)) :
    Extends ins regs defs (compile op shape read defs).1 ∧
    (compile op shape read defs).2.size = shape.outLen ∧
    ∀ i, Denotes ins regs (compile op shape read defs).1
      ((compile op shape read defs).2.getD i (.const 0#64)) ((evalFold op shape values).getD i 0#64) := by
  have h := cached_sound op read values ins regs shape.ranges 0 0 (.const op.identity) defs [] [] hr
    (fun _ _ => rfl) (fun _ _ => rfl)
  let result := cached op read shape.ranges 0 0 (.const op.identity) defs []
  have hv : ExprsDenote ins regs result.1 result.2.reverse (evalFold op shape values) := by
    intro wires hw
    have hh := h.2 wires hw
    have := congrArg List.reverse hh
    simpa [List.map_reverse, evalFold] using this
  refine ⟨h.1, ?_, ?_⟩
  · have hh := congrArg List.length (hv (evalWireTable ins regs result.1.toList) (fun _ _ => rfl))
    simpa [compile, result, evalFold, FoldShape.outLen] using hh
  · intro i wires hw
    change evalRtlExpr ins wires regs (result.2.reverse.toArray.getD i (.const 0#64)) = _
    rw [show result.2.reverse.toArray.getD i (.const 0#64) = result.2.reverse.getD i (.const 0#64) by simp]
    rw [map_getD, hv wires hw]

end Obend.Hardware.RtlFold
end
