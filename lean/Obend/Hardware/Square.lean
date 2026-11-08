module
/-
# Obend.Hardware.Square — one hypergraph through two devices

The same open hypergraph lowered twice: to a combinational `RtlModule` (`compileArrayGraphToRtl`; a scalar
graph is its one-element instance, `compileHypergraphToRtl g = compileArrayGraphToRtl (ofScalar g)`, as
`lowerHypergraphToGpu g = lowerArrayToGpu (ofScalar g)` on the GPU side) and to a GPU program
(`lowerArrayToGpu`, `Obend.Hardware.Gpu`). Each leg is checked against the world outside Lean by
`hardware/gpu/square/verify_square.sh`: the RTL leg by Verilator on the emitted SystemVerilog and by the
LEC of `hardware/lec/lec.sh` (Yosys's reading of the `.sv` against Lean's model of the `RtlModule`); the
GPU leg by the card. The theorems here say the two lowerings denote one evaluation.

The lowering is single assignment: module wire `i` is the `i`-th element definition (the input wires'
elements, then each edge's destination elements in edge order), and an array of slots records, per array
wire, where its current definition starts (`LowerSt`). A reader reads the definition current when it is
lowered, which is what `stepEdge` reads; so the graph's own wire numbering, a wire defined twice and an
edge reading its own destination all lower faithfully, and `ArrayGraph.wf` is the only hypothesis. A map's
`ElemProg` is run symbolically into one expression per element (`progExpr`); a gather is wiring, a
concatenation renaming, a constant constants. The state is arrays; the closure folds below
(`inputEnvOf`, `evalComb`) are specifications and are not run.

* `compileArrayGraphToRtl_sound`: for every well-formed array graph and every input, the module's output
  ports are `evalGraph` from the environment its input ports induce (`inputEnvOf`), flattened.
* `rtl_eq_gpu_array`: the GPU program, run from any buffer holding that environment at its layout
  (`Flat`), shows the same words, flattened.
* `compileHypergraphToRtl_sound`, `rtl_eq_gpu`: the scalar corollaries, against the scalar single pass
  `evalHyperEdgesCombBv`.
* `pipelined_eq_comb`: the pipelined module (`compileHypergraphToRtlPipelined`, one register bank per
  wavefront stage) after one clock edge per stage shows what the combinational module shows
  (`compileHypergraphToRtlPipelined_sound`), a third corner of the same square.
-/
public import Obend.Hardware.Gpu
@[expose] public section

namespace Obend.Hardware.Square
open Obend.Hardware.HDL
open Obend.Hardware.OpenHypergraph
open Obend.Hardware.ArrayHypergraph
open Obend.Hardware.Gpu
set_option autoImplicit false

/-! ## 1. Elementwise operations as expressions -/

/-- One element's operation over operand expressions. The scalar operations go through
`compileHypergraphOpExpr`. A shift by `64` or more is `0`, as `evalElemOp`'s `Nat` shift is, where
the ALU shift takes its amount modulo `64`: the mux makes the lowering exact on every input. -/
def elemOpToRtl (op : ElemOp) (args : List RtlExpr) : RtlExpr :=
  let a (i : Nat) : RtlExpr := args.getD i (.const 0#64)
  match op with
  | .scalar o => compileHypergraphOpExpr o args
  | .ult      => .alu .ult (a 0) (a 1)
  | .band     => .alu .bitAnd (a 0) (a 1)
  | .bor      => .alu .bitOr (a 0) (a 1)
  | .shr      => .mux (.alu .ult (a 1) (.const 64#64)) (.alu .lshr (a 0) (a 1)) (.const 0#64)
  | .shl      => .mux (.alu .ult (a 1) (.const 64#64)) (.alu .shl (a 0) (a 1)) (.const 0#64)

theorem ushiftRight_guard (a b : Word) :
    (if (if BitVec.ult b 64#64 then 1#64 else 0#64) != 0#64 then a >>> (b.toNat % 64) else 0#64) =
      a >>> b.toNat := by
  by_cases h : BitVec.ult b 64#64
  · have hlt : b.toNat < 64 := by simpa [BitVec.ult] using h
    simp [h, Nat.mod_eq_of_lt hlt]
  · have hge : 64 ≤ b.toNat := by simpa [BitVec.ult] using h
    simp [h, BitVec.ushiftRight_eq_zero hge]

theorem shiftLeft_guard (a b : Word) :
    (if (if BitVec.ult b 64#64 then 1#64 else 0#64) != 0#64 then a <<< (b.toNat % 64) else 0#64) =
      a <<< b.toNat := by
  by_cases h : BitVec.ult b 64#64
  · have hlt : b.toNat < 64 := by simpa [BitVec.ult] using h
    simp [h, Nat.mod_eq_of_lt hlt]
  · have hge : 64 ≤ b.toNat := by simpa [BitVec.ult] using h
    simp [h, BitVec.shiftLeft_eq_zero hge]

/-- **`evalRtlExpr_elemOpToRtl`**: for every element operation and operand list, the lowered expression
is `evalElemOp` of the evaluated operands. -/
theorem evalRtlExpr_elemOpToRtl (op : ElemOp) (args : List RtlExpr) (inputs wires regs : Nat → Word) :
    evalRtlExpr inputs wires regs (elemOpToRtl op args) =
      evalElemOp op (args.map (evalRtlExpr inputs wires regs)) := by
  cases op with
  | scalar o => exact evalRtlExpr_compileHypergraphOpExpr o args inputs wires regs
  | ult | band | bor =>
    simp only [elemOpToRtl, evalRtlExpr, evalAluOp, evalElemOp, evalRtlExpr_getD_const]
  | shr =>
    simp only [elemOpToRtl, evalRtlExpr, evalAluOp, evalElemOp, evalRtlExpr_getD_const]
    exact ushiftRight_guard _ _
  | shl =>
    simp only [elemOpToRtl, evalRtlExpr, evalAluOp, evalElemOp, evalRtlExpr_getD_const]
    exact shiftLeft_guard _ _

/-! ## 2. The lowering -/

/-- The lowering's state: the module's wires so far (wire `i` at index `i`) and, per array wire, the
module wire holding element `0` of its current definition. -/
structure LowerSt where
  defs : Array WireAssign
  slot : Array (Option Nat)

/-- Element `e` of array wire `w` as the module reads it now; `0` before any definition. -/
def LowerSt.read (st : LowerSt) (w e : Nat) : RtlExpr :=
  match st.slot.getD w none with
  | some b => .wireRef (b + e)
  | none => .const 0#64

/-- The wire assignment for element `e` of a definition starting at module wire `n0`. -/
def defAssign (n0 : Nat) (nm : String) (x : Nat → RtlExpr) (e : Nat) : WireAssign :=
  { wireIdx := n0 + e, name := s!"{nm}_{e}", expr := x e }

/-- Define array wire `w` as `m` elements, element `e` driven by `x e`. -/
def LowerSt.define (st : LowerSt) (w m : Nat) (x : Nat → RtlExpr) : LowerSt :=
  { defs := (List.range m).foldl (fun a e => a.push (defAssign st.defs.size s!"w{w}" x e)) st.defs
  , slot := st.slot.set! w (some st.defs.size) }

/-- A program's local name `w` at element `e` before any instruction: element `e` of source `w`, or `0`
for a name that is no source (`srcLookup`). -/
def srcElemExpr (st : LowerSt) (srcs : List Nat) (e w : Nat) : RtlExpr :=
  if srcs.contains w then st.read w e else .const 0#64

/-- One instruction run symbolically: its destination name now stands for the operation's expression. -/
def instrStepExpr (loc : Nat → RtlExpr) (i : Instr) : Nat → RtlExpr :=
  let x := elemOpToRtl i.op (i.args.map loc)
  fun w => if w == i.dst then x else loc w

/-- Element `e` of a map's program as one expression. -/
def progExpr (st : LowerSt) (srcs : List Nat) (e : Nat) (p : ElemProg) : RtlExpr :=
  (p.code.foldl instrStepExpr (srcElemExpr st srcs e)) p.out

/-- The expression driving element `e` of the destination of `d`. -/
def edgeElemExpr (st : LowerSt) (ls : List Nat) (d : ArrayEdge) (e : Nat) : RtlExpr :=
  match d.op with
  | .map _ p => progExpr st d.srcWires e p
  | .gather f => st.read (d.srcWires.getD 0 0) (f.table.getD e 0)
  | .concat =>
    let s0 := d.srcWires.getD 0 0
    if e < ls.getD s0 0 then st.read s0 e
    else st.read (d.srcWires.getD 1 0) (e - ls.getD s0 0)
  | .const vs => .const (vs.getD e 0#64)

/-- Input wire `w` at ports `p, p + 1, …`, then the port after it. -/
def defineInput (ls : List Nat) (acc : LowerSt × Nat) (w : Nat) : LowerSt × Nat :=
  (acc.1.define w (ls.getD w 0) (fun e => .inputPort (acc.2 + e)), acc.2 + ls.getD w 0)

def defineEdge (ls : List Nat) (st : LowerSt) (d : ArrayEdge) : LowerSt :=
  st.define d.dstWire (ls.getD d.dstWire 0) (edgeElemExpr st ls d)

/-- The state after every definition: inputs, then edges. -/
def lowerSt (g : ArrayGraph) : LowerSt :=
  let st0 : LowerSt := ⟨#[], Array.replicate g.lengths.length none⟩
  g.edges.foldl (defineEdge g.lengths) (g.inputs.foldl (defineInput g.lengths) (st0, 0)).1

/-- The elements of the boundary wires `ws`, in order: `(w, e)` for each `w` and each `e < length w`. -/
def boundaryElems (ls : List Nat) (ws : List Nat) : List (Nat × Nat) :=
  ws.flatMap fun w => (List.range (ls.getD w 0)).map fun e => (w, e)

/-- An `ArrayGraph` as a combinational `RtlModule`: a port per input element, a wire per element
definition, a port per output element reading its wire's last definition. -/
def compileArrayGraphToRtl (name : String) (g : ArrayGraph) : RtlModule :=
  let st := lowerSt g
  { name       := name
  , inputNames := (boundaryElems g.lengths g.inputs).map fun we => s!"in_w{we.1}_{we.2}"
  , wires      := st.defs.toList
  , regs       := []
  , outputs    := (boundaryElems g.lengths g.outputs).map fun we =>
      { name := s!"out_w{we.1}_{we.2}", expr := st.read we.1 we.2 } }

/-- A scalar graph as the one-element instance. -/
def compileHypergraphToRtl (name : String) (g : StrictOpenHypergraph) : RtlModule :=
  compileArrayGraphToRtl name (ofScalar g)

/-! ## 3. The meaning of the ports -/

/-- The wire environment the input ports induce: input wire `w` holds the ports after those of the
inputs before it (a later listing of `w` wins); every other wire is zeros of its length. -/
def inputEnvOf (g : ArrayGraph) (ins : Nat → Word) : Nat → Vec :=
  (g.inputs.foldl (fun (acc : (Nat → Vec) × Nat) w =>
      (fun u => if u == w then (List.range (g.lengths.getD w 0)).map (fun e => ins (acc.2 + e)) else acc.1 u,
       acc.2 + g.lengths.getD w 0))
    (fun u => List.replicate (g.lengths.getD u 0) 0#64, 0)).1

/-! ## 4. Soundness -/

theorem runCode_expr (inputs W regs : Nat → Word) (code : List Instr) :
    ∀ (locE : Nat → RtlExpr) (loc : Nat → Word), (∀ w, evalRtlExpr inputs W regs (locE w) = loc w) →
      ∀ w, evalRtlExpr inputs W regs ((code.foldl instrStepExpr locE) w) = runCode loc code w := by
  induction code with
  | nil => intro locE loc h w; exact h w
  | cons i rest ih =>
    intro locE loc h
    simp only [List.foldl_cons, runCode] at ih ⊢
    apply ih
    intro u
    simp only [instrStepExpr, stepInstr]
    by_cases hu : u == i.dst
    · simp only [hu, ↓reduceIte, evalRtlExpr_elemOpToRtl, List.map_map]
      congr 1
      apply List.map_congr_left
      intro a _
      exact h a
    · simp only [hu, Bool.false_eq_true, ↓reduceIte]
      exact h u

theorem srcLookup_not_mem (f : Nat → Vec) (ws : List Nat) (u : Nat) (hu : u ∉ ws) :
    srcLookup (ws.map fun w => (w, f w)) u = [] := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [List.map_cons, srcLookup, List.find?_cons]
    have hwu : w ≠ u := fun h => hu (h ▸ List.mem_cons_self)
    have hb : (w == u) = false := beq_eq_false_iff_ne.mpr hwu
    simp only [hb]
    simpa [srcLookup] using ih (fun h => hu (List.mem_cons_of_mem w h))

/-- What an edge's element expression reads: the current definitions of its sources' elements. If they
hold `env` there, the expression is the edge's value at `e`. -/
theorem edgeElemExpr_eval (st : LowerSt) (ls : List Nat) (d : ArrayEdge) (hOk : edgeOk ls d = true)
    (env : Nat → Vec) (hGood : Good ls env) (W ins regs : Nat → Word)
    (hRead : ∀ s ∈ d.srcWires, ∀ i, i < ls.getD s 0 → evalRtlExpr ins W regs (st.read s i) = (env s).getD i 0#64)
    (e : Nat) (he : e < ls.getD d.dstWire 0) :
    evalRtlExpr ins W regs (edgeElemExpr st ls d e) = (edgeValue env d).getD e 0#64 := by
  simp only [edgeOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true] at hOk
  obtain ⟨⟨⟨_, hSrcs⟩, hLen⟩, hOp⟩ := hOk
  cases hop : d.op with
  | map n p =>
    simp only [hop, ArrayOp.outLen, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hLen hOp
    have hSrcLen : ∀ s ∈ d.srcWires, ls.getD s 0 = ls.getD d.dstWire 0 := hOp.1.1
    have hArr : (edgeValue env d).getD e 0#64 =
        evalProg p (fun w => (srcLookup (edgeSrcs env d) w).getD e 0#64) := by
      simp only [edgeValue, hop, evalArrayOp]
      rw [getD_range_map n _ _ e (by rw [hLen]; exact he)]
    rw [hArr]
    simp only [edgeElemExpr, hop, progExpr, evalProg]
    apply runCode_expr
    intro w
    simp only [srcElemExpr, edgeSrcs]
    by_cases hw : w ∈ d.srcWires
    · rw [ite_eq_left (List.contains_iff_mem.mpr hw), srcLookup_map env d.srcWires w hw]
      exact hRead w hw e (by rw [hSrcLen w hw]; exact he)
    · rw [ite_eq_right (fun h => hw (List.contains_iff_mem.mp h)), srcLookup_not_mem env d.srcWires w hw]
      simp [evalRtlExpr]
  | gather f =>
    simp only [hop, ArrayOp.outLen, Bool.and_eq_true, beq_iff_eq] at hLen hOp
    obtain ⟨⟨hfwf, hOne⟩, hTarget⟩ := hOp
    rw [← hLen] at he
    simp only [FiniteFunction.wf, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at hfwf
    obtain ⟨hTabLen, hTabLt⟩ := hfwf
    have heTab : e < f.table.length := by rw [hTabLen]; exact he
    obtain ⟨s, hs⟩ : ∃ s, d.srcWires = [s] := by
      cases h : d.srcWires with
      | nil => simp [h] at hOne
      | cons s rest => cases rest with
        | nil => exact ⟨s, rfl⟩
        | cons _ _ => simp [h] at hOne
    have hsMem : s ∈ d.srcWires := by rw [hs]; exact List.mem_cons_self
    rw [hs] at hTarget
    simp only [List.getD_cons_zero] at hTarget
    have hIdx : f.table.getD e 0 = f.table[e] := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem heTab]
    have hi : f.table.getD e 0 < ls.getD s 0 := by
      rw [← hTarget, hIdx]
      exact hTabLt _ (List.getElem_mem heTab)
    have hav : (edgeValue env d).getD e 0#64 = (env s).getD (f.table.getD e 0) 0#64 := by
      simp only [edgeValue, edgeSrcs, hop, evalArrayOp, hs, List.map_cons, List.map_nil, List.getD_cons_zero]
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem heTab, hIdx]
      rfl
    rw [hav]
    simp only [edgeElemExpr, hop, hs, List.getD_cons_zero]
    exact hRead s hsMem _ hi
  | concat =>
    simp only [hop, ArrayOp.outLen, beq_iff_eq] at hLen hOp
    obtain ⟨s0, s1, hs⟩ : ∃ s0 s1, d.srcWires = [s0, s1] := by
      cases h : d.srcWires with
      | nil => simp [h] at hOp
      | cons s0 rest => cases rest with
        | nil => simp [h] at hOp
        | cons s1 rest2 => cases rest2 with
          | nil => exact ⟨s0, s1, rfl⟩
          | cons _ _ => simp [h] at hOp
    have h0 : s0 ∈ d.srcWires := by rw [hs]; exact List.mem_cons_self
    have h1 : s1 ∈ d.srcWires := by rw [hs]; exact List.mem_cons_of_mem _ List.mem_cons_self
    have he' : e < ls.getD s0 0 + ls.getD s1 0 := by
      rw [← hLen, hs] at he
      simpa using he
    have hLen0 := hGood s0 (hSrcs s0 h0)
    simp only [edgeElemExpr, edgeValue, edgeSrcs, hop, evalArrayOp, hs, List.map_cons, List.map_nil,
      List.getD_cons_zero, List.getD_cons_succ]
    by_cases hlt : e < ls.getD s0 0
    · rw [ite_eq_left hlt]
      rw [hRead s0 h0 e hlt]
      exact (getD_append_of_lt (env s0) (env s1) e 0#64 (by rw [hLen0]; exact hlt)).symm
    · rw [ite_eq_right hlt]
      rw [hRead s1 h1 (e - ls.getD s0 0) (by omega)]
      have h' := getD_append_right (env s0) (env s1) (e - ls.getD s0 0) 0#64
      rw [hLen0, show ls.getD s0 0 + (e - ls.getD s0 0) = e by omega] at h'
      exact h'.symm
  | const vs =>
    simp only [edgeElemExpr, edgeValue, hop, evalRtlExpr, evalArrayOp]

/-- `stepEdge` keeps the declared lengths. -/
theorem stepEdge_good (ls : List Nat) (d : ArrayEdge) (hOk : edgeOk ls d = true)
    (env : Nat → Vec) (hGood : Good ls env) : Good ls (stepEdge env d) := by
  intro u hu
  simp only [stepEdge]
  by_cases hud : u == d.dstWire
  · rw [ite_eq_left hud]
    have hOkd := hOk
    simp only [edgeOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at hOkd
    have hfw : ∀ f, d.op = .gather f → f.wf = true := by
      intro f hf
      have := hOkd.2
      simp only [hf, Bool.and_eq_true] at this
      exact this.1.1
    simp only [edgeValue]
    rw [evalArrayOp_length d.op _ hfw]
    have hLens : ((edgeSrcs env d).map (·.2)).map List.length = d.srcWires.map (ls.getD · 0) := by
      simp only [edgeSrcs, List.map_map]
      exact List.map_congr_left fun s hs => hGood s (hOkd.1.1.2 s hs)
    rw [hLens, hOkd.1.2, beq_iff_eq.mp hud]
  · rw [ite_eq_right (by simpa using hud)]
    exact hGood u hu

/-- `evalWireTable`'s step, named. -/
def wireStep (ins regs : Nat → Word) (W : Nat → Word) (a : WireAssign) : Nat → Word :=
  let v := evalRtlExpr ins W regs a.expr
  fun i => if i == a.wireIdx then v else W i

theorem evalWireTable_eq_foldl (ins regs : Nat → Word) (assigns : List WireAssign) :
    evalWireTable ins regs assigns = assigns.foldl (wireStep ins regs) (fun _ => 0#64) := rfl

theorem define_defs (st : LowerSt) (w m : Nat) (x : Nat → RtlExpr) :
    (st.define w m x).defs.toList =
      st.defs.toList ++ (List.range m).map (defAssign st.defs.size s!"w{w}" x) := by
  simp only [LowerSt.define]
  generalize st.defs.size = n0
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, Array.toList_push, ih,
      List.map_append, List.append_assoc]
    rfl

theorem define_size (st : LowerSt) (w m : Nat) (x : Nat → RtlExpr) :
    (st.define w m x).defs.size = st.defs.size + m := by
  rw [← Array.length_toList, define_defs]
  simp

theorem wireStep_defAssign (ins regs W : Nat → Word) (n0 : Nat) (nm : String) (x : Nat → RtlExpr)
    (e i : Nat) :
    wireStep ins regs W (defAssign n0 nm x e) i =
      if i = n0 + e then evalRtlExpr ins W regs (x e) else W i := by
  by_cases h : i = n0 + e <;> simp [wireStep, defAssign, h]

/-- Folding a definition's assignments from `W`: below `n0` nothing moves, and element `e` holds what its
expression gives on any table that agrees with `W` below `n0`. -/
theorem foldl_defAssign (ins regs : Nat → Word) (n0 : Nat) (nm : String) (x : Nat → RtlExpr)
    (v : Nat → Word) (W : Nat → Word) (M : Nat)
    (hx : ∀ W', (∀ i, i < n0 → W' i = W i) → ∀ e, e < M → evalRtlExpr ins W' regs (x e) = v e)
    (m : Nat) (hm : m ≤ M) :
    (∀ i, i < n0 → ((List.range m).map (defAssign n0 nm x)).foldl (wireStep ins regs) W i = W i) ∧
    (∀ e, e < m → ((List.range m).map (defAssign n0 nm x)).foldl (wireStep ins regs) W (n0 + e) = v e) := by
  induction m with
  | zero => exact ⟨fun _ _ => rfl, fun e he => absurd he (Nat.not_lt_zero e)⟩
  | succ m ih =>
    obtain ⟨ihBelow, ihOn⟩ := ih (by omega)
    simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil, List.foldl_append,
      List.foldl_cons, List.foldl_nil]
    refine ⟨fun i hi => ?_, fun e he => ?_⟩
    · rw [wireStep_defAssign, ite_eq_right (by omega)]
      exact ihBelow i hi
    · rw [wireStep_defAssign]
      by_cases hem : e = m
      · subst hem
        rw [ite_eq_left rfl]
        exact hx _ ihBelow e (by omega)
      · rw [ite_eq_right (by omega)]
        exact ihOn e (by omega)

/-- The lowering's invariant against an environment: the slots fit the array wires, every current
definition lies below the next module wire, and on any table agreeing with the folded one below it every
element reads `env`. -/
def Rep (ls : List Nat) (ins regs : Nat → Word) (st : LowerSt) (env : Nat → Vec) : Prop :=
  st.slot.size = ls.length ∧
  (∀ w b, w < ls.length → st.slot.getD w none = some b → b + ls.getD w 0 ≤ st.defs.size) ∧
  (∀ W', (∀ i, i < st.defs.size → W' i = evalWireTable ins regs st.defs.toList i) →
    ∀ w e, w < ls.length → e < ls.getD w 0 → evalRtlExpr ins W' regs (st.read w e) = (env w).getD e 0#64) ∧
  Good ls env

theorem Rep_define (ls : List Nat) (ins regs : Nat → Word) (st : LowerSt) (env : Nat → Vec)
    (hR : Rep ls ins regs st env) (w : Nat) (hw : w < ls.length) (x : Nat → RtlExpr) (v : Nat → Word)
    (hx : ∀ W', (∀ i, i < st.defs.size → W' i = evalWireTable ins regs st.defs.toList i) →
      ∀ e, e < ls.getD w 0 → evalRtlExpr ins W' regs (x e) = v e) :
    Rep ls ins regs (st.define w (ls.getD w 0) x)
      (fun u => if u == w then (List.range (ls.getD w 0)).map v else env u) := by
  obtain ⟨hSize, hBelow, hVal, hGood⟩ := hR
  have hwS : w < st.slot.size := by rw [hSize]; exact hw
  have hFold := foldl_defAssign ins regs st.defs.size s!"w{w}" x v
    (evalWireTable ins regs st.defs.toList) (ls.getD w 0) hx (ls.getD w 0) (Nat.le_refl _)
  have hTable : evalWireTable ins regs (st.define w (ls.getD w 0) x).defs.toList =
      ((List.range (ls.getD w 0)).map (defAssign st.defs.size s!"w{w}" x)).foldl (wireStep ins regs)
        (evalWireTable ins regs st.defs.toList) := by
    rw [define_defs, evalWireTable_eq_foldl, List.foldl_append]
    rfl
  have hSlot : ∀ u, (st.define w (ls.getD w 0) x).slot.getD u none =
      if u = w then some st.defs.size else st.slot.getD u none := by
    intro u
    exact array_getD_set! st.slot w u _ none hwS
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [LowerSt.define, hSize]
  · intro u b hu hb
    rw [define_size]
    rw [hSlot u] at hb
    by_cases huw : u = w
    · subst huw
      simp at hb
      omega
    · rw [ite_eq_right huw] at hb
      have := hBelow u b hu hb
      omega
  · intro W' hW' u e hu he
    rw [define_size] at hW'
    by_cases huw : u = w
    · subst huw
      simp only [LowerSt.read, hSlot, ite_eq_left rfl, evalRtlExpr, beq_self_eq_true, if_true]
      rw [hW' (st.defs.size + e) (by omega), hTable, hFold.2 e he, getD_range_map _ _ _ e he]
    · have hRead : (st.define w (ls.getD w 0) x).read u e = st.read u e := by
        simp only [LowerSt.read, hSlot, ite_eq_right huw]
      rw [hRead]
      have hne : (u == w) = false := by simpa using huw
      simp only [hne, Bool.false_eq_true, if_false]
      apply hVal W' _ u e hu he
      intro i hi
      rw [hW' i (by omega), hTable]
      exact hFold.1 i hi
  · intro u hu
    by_cases huw : u = w
    · subst huw; simp
    · have hne : (u == w) = false := by simpa using huw
      simp only [hne, Bool.false_eq_true, if_false]
      exact hGood u hu

theorem map_range_getD {α : Type} (l : List α) (z : α) (m : Nat) (h : l.length = m) :
    (List.range m).map (fun e => l.getD e z) = l := by
  subst h
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

/-- One edge: the invariant moves from `env` to `stepEdge env d`. -/
theorem Rep_defineEdge (ls : List Nat) (ins regs : Nat → Word) (st : LowerSt) (env : Nat → Vec)
    (hR : Rep ls ins regs st env) (d : ArrayEdge) (hOk : edgeOk ls d = true) :
    Rep ls ins regs (defineEdge ls st d) (stepEdge env d) := by
  have hOk' := hOk
  simp only [edgeOk, Bool.and_eq_true, decide_eq_true_eq] at hOk'
  have hDst : d.dstWire < ls.length := hOk'.1.1.1
  have hSrcs : ∀ s ∈ d.srcWires, s < ls.length := by
    have := hOk'.1.1.2
    simpa [List.all_eq_true] using this
  have hStep := Rep_define ls ins regs st env hR d.dstWire hDst (edgeElemExpr st ls d)
    (fun e => (edgeValue env d).getD e 0#64) (fun W' hW' e he =>
      edgeElemExpr_eval st ls d hOk env hR.2.2.2 W' ins regs
        (fun s hs i hi => hR.2.2.1 W' hW' s i (hSrcs s hs) hi) e he)
  have hLen : (edgeValue env d).length = ls.getD d.dstWire 0 := by
    have := stepEdge_good ls d hOk env hR.2.2.2 d.dstWire hDst
    simpa [stepEdge] using this
  have hEnv : (fun u => if u == d.dstWire then
        (List.range (ls.getD d.dstWire 0)).map (fun e => (edgeValue env d).getD e 0#64) else env u) =
      stepEdge env d := by
    funext u
    simp only [stepEdge]
    by_cases h : u == d.dstWire
    · simp only [h, if_true]
      exact map_range_getD _ _ _ hLen
    · simp only [h, Bool.false_eq_true, if_false]
  rw [← hEnv]
  exact hStep

theorem Rep_edges (ls : List Nat) (ins regs : Nat → Word) (es : List ArrayEdge)
    (hOk : ∀ d ∈ es, edgeOk ls d = true) :
    ∀ (st : LowerSt) (env : Nat → Vec), Rep ls ins regs st env →
      Rep ls ins regs (es.foldl (defineEdge ls) st) (evalComb env es) := by
  induction es with
  | nil => intro st env h; exact h
  | cons d rest ih =>
    intro st env h
    simp only [List.foldl_cons, evalComb] at ih ⊢
    exact ih (fun d' hd' => hOk d' (List.mem_cons_of_mem d hd')) _ _
      (Rep_defineEdge ls ins regs st env h d (hOk d List.mem_cons_self))

/-- The input step of `inputEnvOf`, named. -/
def inputStep (ls : List Nat) (ins : Nat → Word) (acc : (Nat → Vec) × Nat) (w : Nat) : (Nat → Vec) × Nat :=
  (fun u => if u == w then (List.range (ls.getD w 0)).map (fun e => ins (acc.2 + e)) else acc.1 u,
   acc.2 + ls.getD w 0)

theorem inputEnvOf_eq (g : ArrayGraph) (ins : Nat → Word) :
    inputEnvOf g ins =
      (g.inputs.foldl (inputStep g.lengths ins) (fun u => List.replicate (g.lengths.getD u 0) 0#64, 0)).1 := rfl

theorem Rep_inputs (ls : List Nat) (ins regs : Nat → Word) (xs : List Nat) (hxs : ∀ w ∈ xs, w < ls.length) :
    ∀ (st : LowerSt) (env : Nat → Vec) (p : Nat), Rep ls ins regs st env →
      Rep ls ins regs (xs.foldl (defineInput ls) (st, p)).1 (xs.foldl (inputStep ls ins) (env, p)).1 := by
  induction xs with
  | nil => intro st env p h; exact h
  | cons w rest ih =>
    intro st env p h
    simp only [List.foldl_cons]
    exact ih (fun w' hw' => hxs w' (List.mem_cons_of_mem w hw')) _ _ _
      (Rep_define ls ins regs st env h w (hxs w List.mem_cons_self) (fun e => .inputPort (p + e))
        (fun e => ins (p + e)) (fun _ _ _ _ => rfl))

theorem Rep_init (ls : List Nat) (ins regs : Nat → Word) :
    Rep ls ins regs ⟨#[], Array.replicate ls.length none⟩ (fun u => List.replicate (ls.getD u 0) 0#64) := by
  have hNone : ∀ w, (Array.replicate ls.length (none : Option Nat)).getD w none = none :=
    fun w => array_getD_replicate _ _ _
  refine ⟨by simp, ?_, ?_, ?_⟩
  · intro w b _ hb
    rw [hNone] at hb
    cases hb
  · intro W' _ w e _ he
    have he' : e < ls[w]?.getD 0 := by simpa [List.getD_eq_getElem?_getD] using he
    simp only [LowerSt.read, hNone, evalRtlExpr]
    simp [List.getD_eq_getElem?_getD, List.getElem?_replicate, he']
  · intro w _
    simp

theorem wf_inputs (g : ArrayGraph) (h : g.wf = true) : ∀ w ∈ g.inputs, w < g.lengths.length := by
  simp only [ArrayGraph.wf, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.1.1

/-- The whole lowering against the whole evaluation. -/
theorem lowerSt_rep (g : ArrayGraph) (hwf : g.wf = true) (ins regs : Nat → Word) :
    Rep g.lengths ins regs (lowerSt g) (evalComb (inputEnvOf g ins) g.edges) := by
  rw [inputEnvOf_eq]
  exact Rep_edges g.lengths ins regs g.edges (wf_edgeOk g hwf) _ _
    (Rep_inputs g.lengths ins regs g.inputs (wf_inputs g hwf) _ _ 0 (Rep_init g.lengths ins regs))

theorem inputEnvOf_good (g : ArrayGraph) (hwf : g.wf = true) (ins : Nat → Word) :
    Good g.lengths (inputEnvOf g ins) := by
  rw [inputEnvOf_eq]
  exact (Rep_inputs g.lengths ins ins g.inputs (wf_inputs g hwf) _ _ 0 (Rep_init g.lengths ins ins)).2.2.2

/-- The boundary elements read through `f` are the boundary wires of `env`, flattened. -/
theorem map_boundaryElems (ls : List Nat) (ws : List Nat) (hws : ∀ w ∈ ws, w < ls.length)
    (env : Nat → Vec) (hGood : Good ls env) (f : Nat → Nat → Word)
    (hf : ∀ w e, w < ls.length → e < ls.getD w 0 → f w e = (env w).getD e 0#64) :
    (boundaryElems ls ws).map (fun we => f we.1 we.2) = (ws.map env).flatten := by
  induction ws with
  | nil => rfl
  | cons w rest ih =>
    simp only [boundaryElems] at ih ⊢
    simp only [List.flatMap_cons, List.map_append, List.map_map, List.map_cons, List.flatten_cons]
    rw [ih (fun w' hw' => hws w' (List.mem_cons_of_mem w hw'))]
    congr 1
    have hw := hws w List.mem_cons_self
    apply List.ext_getElem
    · simp [hGood w hw]
    · intro i h1 h2
      simp only [List.getElem_map, List.getElem_range, Function.comp_def]
      have hi : i < ls.getD w 0 := by simpa using h1
      rw [hf w i hw hi]
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

/-- **`compileArrayGraphToRtl_sound`**: for every well-formed array graph and every input, the module's
output ports, in order, are `evalGraph` from the environment the input ports induce, flattened. -/
theorem compileArrayGraphToRtl_sound (name : String) (g : ArrayGraph) (hwf : g.wf = true)
    (ins regs : Nat → Word) :
    (evalModuleOutputs (compileArrayGraphToRtl name g) ins regs).map Prod.snd =
      (evalGraph g (inputEnvOf g ins)).flatten := by
  obtain ⟨_, _, hVal, hGood⟩ := lowerSt_rep g hwf ins regs
  have hOut : (evalModuleOutputs (compileArrayGraphToRtl name g) ins regs).map Prod.snd =
      (boundaryElems g.lengths g.outputs).map (fun we =>
        evalRtlExpr ins (evalWireTable ins regs (lowerSt g).defs.toList) regs ((lowerSt g).read we.1 we.2)) := by
    simp only [evalModuleOutputs, compileArrayGraphToRtl, List.map_map]
    rfl
  rw [hOut, evalGraph]
  exact map_boundaryElems g.lengths g.outputs (wf_outputs g hwf) _ hGood _
    (fun w e hw he => hVal _ (fun _ _ => rfl) w e hw he)

/-- **`rtl_eq_gpu_array`**: the GPU program, run from any buffer holding the input ports' environment at
its layout, shows on its output wires, flattened, the RTL module's output ports. -/
theorem rtl_eq_gpu_array (name : String) (g : ArrayGraph) (hwf : g.wf = true) (ins regs : Nat → Word)
    (flat : Nat → Word) (hFlat : Flat g.lengths (inputEnvOf g ins) flat) :
    (runProgram (lowerArrayToGpu g) flat).flatten =
      (evalModuleOutputs (compileArrayGraphToRtl name g) ins regs).map Prod.snd := by
  rw [compileArrayGraphToRtl_sound name g hwf ins regs,
    lowerArrayToGpu_sound g hwf _ flat (inputEnvOf_good g hwf ins) hFlat]

/-! ## 5. Scalar graphs, the one-element instance -/

theorem evalComb_lift (env : Nat → Word) (edges : List HyperEdge) :
    evalComb (singletonEnv env) (edges.map liftEdge) = singletonEnv (evalHyperEdgesCombBv env edges) := by
  induction edges generalizing env with
  | nil => rfl
  | cons e rest ih =>
    simp only [evalComb, evalHyperEdgesCombBv] at ih ⊢
    simp only [List.map_cons, List.foldl_cons, stepEdge_lift]
    exact ih (stepHyperEdgeSyncBv env env e)

theorem singletonEnv_injective {a b : Nat → Word} (h : singletonEnv a = singletonEnv b) : a = b := by
  funext w
  have := congrFun h w
  simp only [singletonEnv, List.cons.injEq, and_true] at this
  exact this

/-- The scalar layering, evaluated synchronously at 64 bits, is the single combinational pass: the
array layering theorem (`layerGraph_sound`) read on the one-element instance. -/
theorem evalLayeredStagesSyncBv_eq_comb (g : StrictOpenHypergraph) (env : Nat → Word) :
    evalLayeredStagesSyncBv env (layerHypergraph g) = evalHyperEdgesCombBv env (extractHyperEdges g) := by
  apply singletonEnv_injective
  rw [← ofScalar_layered_sound, (layerGraph_sound (ofScalar g) (singletonEnv env)).2.2]
  exact evalComb_lift env _

/-- Two environments that agree on the declared wires evaluate alike there. -/
theorem evalComb_congr (ls : List Nat) (es : List ArrayEdge) (hOk : ∀ d ∈ es, edgeOk ls d = true) :
    ∀ (env1 env2 : Nat → Vec), (∀ u, u < ls.length → env1 u = env2 u) →
      ∀ u, u < ls.length → evalComb env1 es u = evalComb env2 es u := by
  induction es with
  | nil => intro env1 env2 h; exact h
  | cons d rest ih =>
    intro env1 env2 h
    simp only [evalComb, List.foldl_cons] at ih ⊢
    apply ih (fun d' hd' => hOk d' (List.mem_cons_of_mem d hd'))
    intro u hu
    have hOkd := hOk d List.mem_cons_self
    simp only [edgeOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hOkd
    simp only [stepEdge]
    by_cases hud : u == d.dstWire
    · simp only [hud, if_true]
      exact edgeValue_congr env2 env1 d (fun s hs => h s (hOkd.1.1.2 s hs))
    · simp only [hud, Bool.false_eq_true, if_false]
      exact h u hu

/-- A scalar graph's input environment, one word per wire. -/
def scalarInputEnv (g : StrictOpenHypergraph) (ins : Nat → Word) : Nat → Word :=
  fun w => (inputEnvOf (ofScalar g) ins w).getD 0 0#64

theorem eq_singleton_getD {α : Type} (l : List α) (z : α) (h : l.length = 1) : l = [l.getD 0 z] := by
  match l, h with
  | [a], _ => rfl

theorem evalGraph_ofScalar (g : StrictOpenHypergraph) (hwf : (ofScalar g).wf = true) (ins : Nat → Word) :
    evalGraph (ofScalar g) (inputEnvOf (ofScalar g) ins) =
      g.boundaryOut.table.map (fun w => [evalHyperEdgesCombBv (scalarInputEnv g ins) (extractHyperEdges g) w]) := by
  have hGood := inputEnvOf_good (ofScalar g) hwf ins
  have hLen : ∀ u, u < (ofScalar g).lengths.length → (ofScalar g).lengths.getD u 0 = 1 := by
    intro u hu
    simp only [ofScalar, List.length_replicate] at hu ⊢
    simp [List.getD_eq_getElem?_getD, List.getElem?_replicate, hu]
  have hAgree : ∀ u, u < (ofScalar g).lengths.length →
      inputEnvOf (ofScalar g) ins u = singletonEnv (scalarInputEnv g ins) u := by
    intro u hu
    simp only [singletonEnv, scalarInputEnv]
    exact eq_singleton_getD _ _ (by rw [hGood u hu, hLen u hu])
  simp only [evalGraph]
  apply List.map_congr_left
  intro w hw
  have hwlt := wf_outputs (ofScalar g) hwf w hw
  rw [evalComb_congr _ _ (wf_edgeOk _ hwf) _ _ hAgree w hwlt]
  have := congrFun (evalComb_lift (scalarInputEnv g ins) (extractHyperEdges g)) w
  simpa [ofScalar, singletonEnv] using this

theorem flatten_map_singleton {α β : Type} (l : List α) (f : α → β) :
    (l.map fun a => [f a]).flatten = l.map f := by
  induction l with
  | nil => rfl
  | cons a rest ih => simp [ih]

/-- **`compileHypergraphToRtl_sound`**: for every scalar graph whose one-element instance is well-formed
and every input, the module's output ports are the 64-bit single pass from the environment its input
ports induce. -/
theorem compileHypergraphToRtl_sound (name : String) (g : StrictOpenHypergraph)
    (hwf : (ofScalar g).wf = true) (ins regs : Nat → Word) :
    (evalModuleOutputs (compileHypergraphToRtl name g) ins regs).map Prod.snd =
      g.boundaryOut.table.map (evalHyperEdgesCombBv (scalarInputEnv g ins) (extractHyperEdges g)) := by
  rw [compileHypergraphToRtl, compileArrayGraphToRtl_sound name _ hwf, evalGraph_ofScalar g hwf,
    flatten_map_singleton]

/-- **`rtl_eq_gpu`**: the scalar square. The GPU program, run from any buffer holding the input ports'
environment, shows on each output wire, as a singleton, the RTL module's output port. -/
theorem rtl_eq_gpu (name : String) (g : StrictOpenHypergraph) (hwf : (ofScalar g).wf = true)
    (ins regs : Nat → Word) (flat : Nat → Word)
    (hFlat : Flat (ofScalar g).lengths (inputEnvOf (ofScalar g) ins) flat) :
    runProgram (lowerHypergraphToGpu g) flat =
      (evalModuleOutputs (compileHypergraphToRtl name g) ins regs).map (fun o => [o.2]) := by
  rw [lowerHypergraphToGpu, lowerArrayToGpu_sound (ofScalar g) hwf _ flat (inputEnvOf_good _ hwf ins) hFlat,
    evalGraph_ofScalar g hwf]
  rw [show (evalModuleOutputs (compileHypergraphToRtl name g) ins regs).map (fun o => [o.2]) =
        ((evalModuleOutputs (compileHypergraphToRtl name g) ins regs).map Prod.snd).map (fun v => [v]) by
        simp [List.map_map],
    compileHypergraphToRtl_sound name g hwf ins regs, List.map_map]
  rfl

/-! ## 6. The pipelined module, a third corner -/

/-- Every source wire of a well-formed scalar graph is below its wire count. -/
theorem srcWires_lt_of_wf (g : StrictOpenHypergraph) (hwf : (ofScalar g).wf = true) :
    ∀ e ∈ extractHyperEdges g, ∀ u ∈ e.srcWires, u < g.nodeTypes.length := by
  intro e he u hu
  have hOk := wf_edgeOk (ofScalar g) hwf (liftEdge e) (List.mem_map_of_mem he)
  simp only [edgeOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hOk
  have := hOk.1.1.2 u hu
  simpa [ofScalar, liftEdge] using this

/-- **`pipelined_eq_comb`**: on a scalar graph whose one-element instance is well-formed, the pipelined
module, its wire inputs held at the scalar input environment for one clock edge per wavefront stage,
shows on its outputs what the combinational module shows on its ports. -/
theorem pipelined_eq_comb (name name' : String) (g : StrictOpenHypergraph)
    (hwf : (ofScalar g).wf = true) (ins initRegs regs : Nat → Word) :
    (evalModuleOutputs (compileHypergraphToRtlPipelined name g) (scalarInputEnv g ins)
        (runModuleTrace (compileHypergraphToRtlPipelined name g) initRegs
          (List.replicate (layerHypergraph g).length (false, scalarInputEnv g ins)))).map Prod.snd =
      (evalModuleOutputs (compileHypergraphToRtl name' g) ins regs).map Prod.snd := by
  have hOut : ∀ w ∈ g.boundaryOut.table, w < g.nodeTypes.length := by
    intro w hw
    have := wf_outputs (ofScalar g) hwf w hw
    simpa [ofScalar] using this
  rw [compileHypergraphToRtlPipelined_sound name g (srcWires_lt_of_wf g hwf) hOut,
    evalLayeredStagesSyncBv_eq_comb, compileHypergraphToRtl_sound name' g hwf]

end Obend.Hardware.Square
