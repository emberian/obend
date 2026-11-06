module
/-
# Obend.Hardware.Square — one hypergraph through two devices

The same open hypergraph lowered twice: to a combinational `RtlModule` (`compileHypergraphToRtl`,
`Obend.Hardware.OpenHypergraph`; for array graphs `compileArrayGraphToRtl` below) and to a GPU program
(`lowerArrayToGpu`, `Obend.Hardware.Gpu`). Each leg is checked against the world outside Lean by
`hardware/gpu/square/verify_square.sh`: the RTL leg by Verilator on the emitted SystemVerilog, by the
LEC of `hardware/lec/lec.sh` (Yosys's reading of the `.sv` against Lean's model of the `RtlModule`) and
by EQY against Yosys's synthesis where that terminates; the GPU leg by the card. The theorems here are
the fourth side of the square: the two lowerings denote one evaluation.

* `rtl_eq_gpu`: for every scalar graph that passes `ArrayGraph.wf` as its one-element instance and
  defines each wire once (`(wireDefs g).Nodup`), and for every input, the GPU program run from the
  environment the RTL module's input ports induce shows, wire by wire as singletons, exactly the RTL
  module's output ports. Composed from
  `compileHypergraphToRtl_sound` (the RTL side is the single combinational pass at 64 bits) and
  `lowerHypergraphToGpu_sound` (the GPU side is the layered synchronous evaluation), joined by the
  layering theorem read on the one-element instance (`evalLayeredStagesSyncBv_eq_comb`).
* `compileArrayGraphToRtl_sound`: an `ArrayGraph` unrolled into scalar wires, element `e` of wire `w`
  at RTL wire `base ls w + e`, the GPU program's own flat layout. A map is one `RtlExpr` per element, a
  gather is wiring, a concatenation is renaming, a constant is constants. For a well-formed graph none
  of whose edges reads its own destination, the module's output ports are `evalGraph` flattened.
* `rtl_eq_gpu_array`: the square over array graphs, the GPU's output wires flattened against the RTL's
  output ports, on the same flat input.
* `pipelined_eq_comb`: the pipelined module (`compileHypergraphToRtlPipelined`, one register bank per
  wavefront stage), after one clock edge per stage, shows what the combinational module shows
  (`compileHypergraphToRtlPipelined_sound`); so it is a third corner of the same square.

The array theorem needs `ArrayGraph.wf` (lengths consistent, wires exist) and `edgesAcyclic` (a gather
reading its own destination would see elements already rewritten); the emitter checks every
hypothesis before it writes (`SquareGraph.hyp`).
-/
public import Obend.Hardware.Gpu
@[expose] public section

namespace Obend.Hardware.Square
open Obend.Hardware.HDL
open Obend.Hardware.OpenHypergraph
open Obend.Hardware.ArrayHypergraph
open Obend.Hardware.Gpu
set_option autoImplicit false

/-! ## 1. The scalar square -/

theorem stepEdge_lift (env : Nat → Word) (e : HyperEdge) :
    stepEdge (singletonEnv env) (liftEdge e) = singletonEnv (stepHyperEdgeBv env e) := by
  funext w
  simp only [stepEdge, liftEdge, stepHyperEdgeBv, singletonEnv, evalArrayOp_lift]
  split <;> rfl

theorem evalComb_lift (env : Nat → Word) (edges : List HyperEdge) :
    evalComb (singletonEnv env) (edges.map liftEdge) = singletonEnv (evalHyperEdgesCombBv env edges) := by
  induction edges generalizing env with
  | nil => rfl
  | cons e rest ih =>
    simp only [evalComb, evalHyperEdgesCombBv] at ih ⊢
    simp only [List.map_cons, List.foldl_cons, stepEdge_lift]
    exact ih _

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

/-- **`rtl_eq_gpu`**: the RTL module's output ports and the GPU program's output wires agree on every
input, for every scalar graph whose one-element instance is well-formed. -/
theorem rtl_eq_gpu (name : String) (g : StrictOpenHypergraph) (hwf : (ofScalar g).wf = true)
    (hN : (wireDefs g).Nodup) (ins regs : Nat → Word) :
    runProgram (lowerHypergraphToGpu g) (inputEnv g ins) =
      (evalModuleOutputs (compileHypergraphToRtl name g) ins regs).map (fun o => [o.2]) := by
  have hOut : ∀ w ∈ g.boundaryOut.table, w < g.nodeTypes.length := by
    intro w hw
    have := wf_outputs (ofScalar g) hwf w hw
    simpa [ofScalar] using this
  rw [lowerHypergraphToGpu_sound g (wf_edgeOk _ hwf) hOut, evalLayeredStagesSyncBv_eq_comb]
  have h := compileHypergraphToRtl_sound name g hN ins regs
  rw [show (evalModuleOutputs (compileHypergraphToRtl name g) ins regs).map (fun o => [o.2]) =
        ((evalModuleOutputs (compileHypergraphToRtl name g) ins regs).map Prod.snd).map (fun v => [v]) by
        simp [List.map_map]]
  rw [h, evalHypergraphCombBv, List.map_map]
  rfl

/-! ## 2. Array graphs as scalar wires -/

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

/-- Element `e` of array wire `w` is RTL wire `base ls w + e`: the GPU program's flat buffer address
(`Obend.Hardware.Gpu.base`) is the wire index, so the two lowerings share one layout. -/
def elemWire (ls : List Nat) (w e : Nat) : Nat := base ls w + e

def elemRef (ls : List Nat) (w e : Nat) : RtlExpr := .wireRef (elemWire ls w e)

/-- The expression driving element `e` of the destination of `d`. -/
def edgeElemExpr (ls : List Nat) (d : ArrayEdge) (e : Nat) : RtlExpr :=
  match d.op with
  | .map _ op => elemOpToRtl op (d.srcWires.map fun s => elemRef ls s e)
  | .gather f => elemRef ls (d.srcWires.getD 0 0) (f.table.getD e 0)
  | .concat =>
    let s0 := d.srcWires.getD 0 0
    if e < ls.getD s0 0 then elemRef ls s0 e
    else elemRef ls (d.srcWires.getD 1 0) (e - ls.getD s0 0)
  | .const vs => .const (vs.getD e 0#64)

/-- One wire assignment per element of the destination. -/
def edgeWires (ls : List Nat) (d : ArrayEdge) : List WireAssign :=
  (List.range (ls.getD d.dstWire 0)).map fun e =>
    { wireIdx := elemWire ls d.dstWire e, name := s!"w{d.dstWire}_{e}", expr := edgeElemExpr ls d e }

/-- The elements of the boundary wires `ws`, in order: `(w, e)` for each `w` and each `e < length w`. -/
def boundaryElems (ls : List Nat) (ws : List Nat) : List (Nat × Nat) :=
  ws.flatMap fun w => (List.range (ls.getD w 0)).map fun e => (w, e)

/-- Input port `p` drives the `p`-th input element. -/
def inputWires (g : ArrayGraph) : List WireAssign :=
  (boundaryElems g.lengths g.inputs).zipIdx.map fun (we, p) =>
    { wireIdx := elemWire g.lengths we.1 we.2, name := s!"w{we.1}_{we.2}", expr := .inputPort p }

/-- An `ArrayGraph` as a combinational `RtlModule`: a port per input element, a wire per element of
every destination, a port per output element. -/
def compileArrayGraphToRtl (name : String) (g : ArrayGraph) : RtlModule where
  name       := name
  inputNames := (boundaryElems g.lengths g.inputs).map fun we => s!"in_w{we.1}_{we.2}"
  wires      := inputWires g ++ g.edges.flatMap (edgeWires g.lengths)
  regs       := []
  outputs    := (boundaryElems g.lengths g.outputs).map fun we =>
    { name := s!"out_w{we.1}_{we.2}", expr := elemRef g.lengths we.1 we.2 }

/-- No edge reads its own destination (a topological order has this; `ArrayGraph.wf` does not say it). -/
def edgesAcyclic (g : ArrayGraph) : Bool :=
  g.edges.all fun d => !(d.srcWires.contains d.dstWire)

/-- The flat wire environment the input ports induce: port `p` at its element's wire, `0` elsewhere. -/
def inputFlat (g : ArrayGraph) (ins : Nat → Word) : Nat → Word :=
  (boundaryElems g.lengths g.inputs).zipIdx.foldl
    (fun flat (q : (Nat × Nat) × Nat) => fun u => if u == elemWire g.lengths q.1.1 q.1.2 then ins q.2 else flat u)
    (fun _ => 0#64)

/-- A flat buffer read back as wires of the declared lengths. -/
def unflatten (ls : List Nat) (flat : Nat → Word) : Nat → Vec :=
  fun w => (List.range (ls.getD w 0)).map fun e => flat (base ls w + e)

theorem unflatten_good (ls : List Nat) (flat : Nat → Word) : Good ls (unflatten ls flat) := by
  intro w _
  simp [unflatten]

theorem unflatten_flat (ls : List Nat) (flat : Nat → Word) : Flat ls (unflatten ls flat) flat := by
  intro w e _ he
  simp only [unflatten]
  rw [getD_range_map _ _ _ e he]

/-! ### The wire table as a fold -/

/-- `evalWireTable`'s step, named. -/
def wireStep (ins regs : Nat → Word) (W : Nat → Word) (a : WireAssign) : Nat → Word :=
  let v := evalRtlExpr ins W regs a.expr
  fun i => if i == a.wireIdx then v else W i

theorem evalWireTable_eq_foldl (ins regs : Nat → Word) (assigns : List WireAssign) :
    evalWireTable ins regs assigns = assigns.foldl (wireStep ins regs) (fun _ => 0#64) := rfl

theorem foldl_inputWires (g : ArrayGraph) (ins regs : Nat → Word) :
    (inputWires g).foldl (wireStep ins regs) (fun _ => 0#64) = inputFlat g ins := by
  simp only [inputWires, inputFlat, List.foldl_map]
  rfl

/-- What an edge's element expression reads: the elements of its sources. If `W` holds `env` there, the
expression is the edge's value at `e`. -/
theorem edgeElemExpr_eval (ls : List Nat) (d : ArrayEdge) (hOk : edgeOk ls d = true)
    (env : Nat → Vec) (hGood : Good ls env) (W ins regs : Nat → Word)
    (hRead : ∀ s ∈ d.srcWires, ∀ i, i < ls.getD s 0 → W (elemWire ls s i) = (env s).getD i 0#64)
    (e : Nat) (he : e < ls.getD d.dstWire 0) :
    evalRtlExpr ins W regs (edgeElemExpr ls d e) = (evalArrayOp d.op (d.srcWires.map env)).getD e 0#64 := by
  simp only [edgeOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true] at hOk
  obtain ⟨⟨⟨_, hSrcs⟩, hLen⟩, hOp⟩ := hOk
  cases hop : d.op with
  | map n op =>
    simp only [hop, ArrayOp.outLen, List.all_eq_true, beq_iff_eq] at hLen hOp
    have hElem : ∀ s ∈ d.srcWires, W (elemWire ls s e) = (env s).getD e 0#64 :=
      fun s hs => hRead s hs e (by rw [hOp s hs]; exact he)
    have hArr : (evalArrayOp (.map n op) (d.srcWires.map env)).getD e 0#64 =
        evalElemOp op (d.srcWires.map fun s => (env s).getD e 0#64) := by
      simp only [evalArrayOp]
      rw [getD_range_map n _ _ e (by rw [hLen]; exact he)]
      simp [List.map_map, Function.comp_def]
    rw [hArr]
    simp only [edgeElemExpr, hop, evalRtlExpr_elemOpToRtl, List.map_map]
    congr 1
    apply List.map_congr_left
    intro s hs
    simp only [Function.comp_def, elemRef, evalRtlExpr]
    exact hElem s hs
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
    have hav : (evalArrayOp (.gather f) (d.srcWires.map env)).getD e 0#64 =
        (env s).getD (f.table.getD e 0) 0#64 := by
      simp only [evalArrayOp, hs, List.map_cons, List.map_nil, List.getD_cons_zero]
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem heTab, hIdx]
      rfl
    rw [hav]
    simp only [edgeElemExpr, hop, elemRef, evalRtlExpr, hs, List.getD_cons_zero]
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
    simp only [edgeElemExpr, hop, elemRef, evalArrayOp, hs, List.map_cons, List.map_nil,
      List.getD_cons_zero, List.getD_cons_succ]
    by_cases hlt : e < ls.getD s0 0
    · rw [ite_eq_left hlt]
      simp only [evalRtlExpr]
      rw [hRead s0 h0 e hlt]
      exact (getD_append_of_lt (env s0) (env s1) e 0#64 (by rw [hLen0]; exact hlt)).symm
    · rw [ite_eq_right hlt]
      simp only [evalRtlExpr]
      rw [hRead s1 h1 (e - ls.getD s0 0) (by omega)]
      have h' := getD_append_right (env s0) (env s1) (e - ls.getD s0 0) 0#64
      rw [hLen0, show ls.getD s0 0 + (e - ls.getD s0 0) = e by omega] at h'
      exact h'.symm
  | const vs =>
    simp only [edgeElemExpr, hop, evalRtlExpr, evalArrayOp]

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
    rw [evalArrayOp_length d.op _ hfw]
    have hLens : (d.srcWires.map env).map List.length = d.srcWires.map (ls.getD · 0) := by
      rw [List.map_map]
      exact List.map_congr_left fun s hs => hGood s (hOkd.1.1.2 s hs)
    rw [hLens, hOkd.1.2, beq_iff_eq.mp hud]
  · rw [ite_eq_right (by simpa using hud)]
    exact hGood u hu

/-- The fold over the first `k` elements of an edge: untouched off the destination's range, the edge's
value on the elements written so far. -/
theorem foldl_edgeWires_prefix (ls : List Nat) (d : ArrayEdge) (hOk : edgeOk ls d = true)
    (hSelf : (d.srcWires.contains d.dstWire) = false)
    (env : Nat → Vec) (hGood : Good ls env) (W ins regs : Nat → Word) (hFlat : Flat ls env W)
    (k : Nat) (hk : k ≤ ls.getD d.dstWire 0) :
    let Wk := ((List.range k).map fun e =>
      ({ wireIdx := elemWire ls d.dstWire e, name := s!"w{d.dstWire}_{e}", expr := edgeElemExpr ls d e } : WireAssign)).foldl
      (wireStep ins regs) W
    (∀ i, (∀ e, e < ls.getD d.dstWire 0 → i ≠ elemWire ls d.dstWire e) → Wk i = W i) ∧
    (∀ e, e < k → Wk (elemWire ls d.dstWire e) = (evalArrayOp d.op (d.srcWires.map env)).getD e 0#64) := by
  have hOk' := hOk
  simp only [edgeOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true] at hOk'
  obtain ⟨⟨⟨hDst, hSrcs⟩, _⟩, _⟩ := hOk'
  induction k with
  | zero => exact ⟨fun _ _ => rfl, fun e he => absurd he (Nat.not_lt_zero e)⟩
  | succ k ih =>
    obtain ⟨ihOff, ihOn⟩ := ih (Nat.le_of_succ_le hk)
    simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil, List.foldl_append,
      List.foldl_cons, List.foldl_nil]
    -- the sources' elements are off the destination's range, so the prefix fold left them as `W`
    have hRead : ∀ s ∈ d.srcWires, ∀ i, i < ls.getD s 0 →
        (((List.range k).map fun e =>
          ({ wireIdx := elemWire ls d.dstWire e, name := s!"w{d.dstWire}_{e}", expr := edgeElemExpr ls d e } : WireAssign)).foldl
          (wireStep ins regs) W) (elemWire ls s i) = (env s).getD i 0#64 := by
      intro s hs i hi
      have hne : s ≠ d.dstWire := by
        intro h
        rw [h] at hs
        have := List.contains_iff_mem.mpr hs  -- hmm name
        simp_all
      rw [ihOff]
      · exact hFlat s i (hSrcs s hs) hi
      · intro e he
        exact base_disjoint ls s d.dstWire i e (hSrcs s hs) hDst hi he hne
    have hVal := edgeElemExpr_eval ls d hOk env hGood _ ins regs hRead k (Nat.lt_of_succ_le hk)
    refine ⟨?_, ?_⟩
    · intro i hi
      simp only [wireStep]
      rw [ite_eq_right (by simpa using hi k (Nat.lt_of_succ_le hk))]
      exact ihOff i hi
    · intro e he
      simp only [wireStep]
      by_cases hek : e = k
      · subst hek
        rw [ite_eq_left (by simp)]
        exact hVal
      · have hlt : e < k := by omega
        rw [ite_eq_right (by simp [elemWire]; omega)]
        exact ihOn e hlt

/-- One edge's wires, folded, carry `stepEdge`. -/
theorem foldl_edgeWires (ls : List Nat) (d : ArrayEdge) (hOk : edgeOk ls d = true)
    (hSelf : (d.srcWires.contains d.dstWire) = false)
    (env : Nat → Vec) (hGood : Good ls env) (W ins regs : Nat → Word) (hFlat : Flat ls env W) :
    Flat ls (stepEdge env d) ((edgeWires ls d).foldl (wireStep ins regs) W) := by
  have hOk' := hOk
  simp only [edgeOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true] at hOk'
  obtain ⟨⟨⟨hDst, _⟩, _⟩, _⟩ := hOk'
  obtain ⟨hOff, hOn⟩ := foldl_edgeWires_prefix ls d hOk hSelf env hGood W ins regs hFlat
    (ls.getD d.dstWire 0) (Nat.le_refl _)
  intro w e hw he
  simp only [stepEdge, edgeWires]
  by_cases hwd : w = d.dstWire
  · subst hwd
    rw [ite_eq_left (by simp)]
    exact hOn e he
  · rw [ite_eq_right (by simpa using hwd)]
    rw [hOff (base ls w + e) (fun e' he' => base_disjoint ls w d.dstWire e e' hw hDst he he' hwd)]
    exact hFlat w e hw he

/-- All edges' wires, folded, carry `evalComb`. -/
theorem foldl_edges (ls : List Nat) (es : List ArrayEdge)
    (hOk : ∀ d ∈ es, edgeOk ls d = true)
    (hSelf : ∀ d ∈ es, (d.srcWires.contains d.dstWire) = false)
    (env : Nat → Vec) (hGood : Good ls env) (W ins regs : Nat → Word) (hFlat : Flat ls env W) :
    Flat ls (evalComb env es) ((es.flatMap (edgeWires ls)).foldl (wireStep ins regs) W) ∧
    Good ls (evalComb env es) := by
  induction es generalizing env W with
  | nil => exact ⟨hFlat, hGood⟩
  | cons d rest ih =>
    simp only [List.flatMap_cons, List.foldl_append, evalComb, List.foldl_cons] at ih ⊢
    have hOkd := hOk d List.mem_cons_self
    have hGood' := stepEdge_good ls d hOkd env hGood
    have hFlat' := foldl_edgeWires ls d hOkd (hSelf d List.mem_cons_self) env hGood W ins regs hFlat
    exact ih (fun d' hd' => hOk d' (List.mem_cons_of_mem d hd'))
      (fun d' hd' => hSelf d' (List.mem_cons_of_mem d hd')) _ hGood' _ hFlat'

/-- The boundary elements read from a flat buffer holding `env` are `env` on those wires, flattened. -/
theorem map_boundaryElems (ls : List Nat) (ws : List Nat) (hws : ∀ w ∈ ws, w < ls.length)
    (env : Nat → Vec) (hGood : Good ls env) (W : Nat → Word) (hFlat : Flat ls env W) :
    (boundaryElems ls ws).map (fun we => W (elemWire ls we.1 we.2)) = (ws.map env).flatten := by
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
      simp only [List.getElem_map, List.getElem_range, Function.comp_def, elemWire]
      have hi : i < ls.getD w 0 := by simpa using h1
      rw [hFlat w i hw hi]
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

/-- **`compileArrayGraphToRtl_sound`**: for a well-formed array graph none of whose edges reads its own
destination, the module's output ports, in order, are `evalGraph` from the environment the input ports
induce, flattened. -/
theorem compileArrayGraphToRtl_sound (name : String) (g : ArrayGraph)
    (hwf : g.wf = true) (hAcyc : edgesAcyclic g = true) (ins regs : Nat → Word) :
    (evalModuleOutputs (compileArrayGraphToRtl name g) ins regs).map Prod.snd =
      (evalGraph g (unflatten g.lengths (inputFlat g ins))).flatten := by
  have hSelf : ∀ d ∈ g.edges, (d.srcWires.contains d.dstWire) = false := by
    intro d hd
    simp only [edgesAcyclic, List.all_eq_true, Bool.not_eq_true'] at hAcyc
    exact hAcyc d hd
  obtain ⟨hFlat, hGood⟩ := foldl_edges g.lengths g.edges (wf_edgeOk g hwf) hSelf
    (unflatten g.lengths (inputFlat g ins)) (unflatten_good _ _) (inputFlat g ins) ins regs (unflatten_flat _ _)
  simp only [evalModuleOutputs, compileArrayGraphToRtl, evalWireTable_eq_foldl, List.foldl_append,
    foldl_inputWires, List.map_map]
  simp only [evalGraph]
  rw [← map_boundaryElems g.lengths g.outputs (wf_outputs g hwf) _ hGood _ hFlat]
  apply List.map_congr_left
  intro we _
  rfl

/-- **`rtl_eq_gpu_array`**: the GPU program's output wires, flattened, are the RTL module's output ports,
on the same flat input. -/
theorem rtl_eq_gpu_array (name : String) (g : ArrayGraph)
    (hwf : g.wf = true) (hAcyc : edgesAcyclic g = true) (ins regs : Nat → Word) :
    (runProgram (lowerArrayToGpu g) (inputFlat g ins)).flatten =
      (evalModuleOutputs (compileArrayGraphToRtl name g) ins regs).map Prod.snd := by
  rw [compileArrayGraphToRtl_sound name g hwf hAcyc ins regs,
    lowerArrayToGpu_sound g (wf_edgeOk g hwf) (wf_outputs g hwf) _ _ (unflatten_good _ _) (unflatten_flat _ _)]

/-! ## 3. The pipelined module, a third corner -/

/-- Every source wire of a well-formed scalar graph is below its wire count. -/
theorem srcWires_lt_of_wf (g : StrictOpenHypergraph) (hwf : (ofScalar g).wf = true) :
    ∀ e ∈ extractHyperEdges g, ∀ u ∈ e.srcWires, u < g.nodeTypes.length := by
  intro e he u hu
  have hOk := wf_edgeOk (ofScalar g) hwf (liftEdge e) (List.mem_map_of_mem he)
  simp only [edgeOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hOk
  have := hOk.1.1.2 u hu
  simpa [ofScalar, liftEdge] using this

/-- **`pipelined_eq_comb`**: on a well-formed scalar graph that defines each wire once, the pipelined
module, its wire inputs held at the environment the combinational module's ports induce for one edge
per wavefront stage, shows on its outputs what the combinational module shows: the single pass. With
`rtl_eq_gpu`, the pipelined RTL, the combinational RTL and the GPU program are one evaluation. -/
theorem pipelined_eq_comb (name name' : String) (g : StrictOpenHypergraph)
    (hwf : (ofScalar g).wf = true) (hN : (wireDefs g).Nodup) (ins initRegs regs : Nat → Word) :
    (evalModuleOutputs (compileHypergraphToRtlPipelined name g) (inputEnv g ins)
        (runModuleTrace (compileHypergraphToRtlPipelined name g) initRegs
          (List.replicate (layerHypergraph g).length (false, inputEnv g ins)))).map Prod.snd =
      (evalModuleOutputs (compileHypergraphToRtl name' g) ins regs).map Prod.snd := by
  have hOut : ∀ w ∈ g.boundaryOut.table, w < g.nodeTypes.length := by
    intro w hw
    have := wf_outputs (ofScalar g) hwf w hw
    simpa [ofScalar] using this
  rw [compileHypergraphToRtlPipelined_sound name g (srcWires_lt_of_wf g hwf) hOut,
    evalLayeredStagesSyncBv_eq_comb, compileHypergraphToRtl_sound name' g hN]
  rfl

end Obend.Hardware.Square
