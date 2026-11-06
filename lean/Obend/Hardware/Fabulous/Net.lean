module
/-
# Obend.Hardware.Fabulous.Net — what a configured FABulous fabric computes, and when it realizes a module

A configured LUT4AB fabric, read back from its bitstream (`Obend.Hardware.Fabulous.Bitstream`), is a
`Net`: LUT4 gates in topological order, flip-flops, and the output pins, each input of each a `Lit`
(a constant, an input pin, a flip-flop output or an earlier gate). This file gives the `Net` its
cycle semantics (`Net.step`, `Net.outputs`, `Net.run`) and proves `fabric_realizes_module`: a
register-to-flip-flop correspondence that one clock step preserves, with equal outputs, for every
in-width state and input, makes the fabric and the `RtlModule` agree on every trace.

The LUT4 cell is FABulous's `LUT4c_frame_config_dffesr`: `O = INIT[{I3,I2,I1,I0}]`, or, with the `FF`
bit set, the flop, which on a clock edge with `EN` loads `SR ? SET_NORESET : LUT` and otherwise holds.
-/
public import Obend.Hardware.HDL
@[expose] public section

namespace Obend.Hardware.Fabulous

open Obend.Hardware.HDL

/-- An input of a gate, a flop or an output pin. -/
inductive Lit
  | const (b : Bool)
  | pin (k : Nat)
  | ff (k : Nat)
  | gate (k : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- A LUT4: `init` indexed by `i0 + 2·i1 + 4·i2 + 8·i3`. `site` is where it sits (`X2Y9.C`). -/
structure Gate where
  init : BitVec 16
  i0 : Lit
  i1 : Lit
  i2 : Lit
  i3 : Lit
  site : String
  deriving DecidableEq, Repr, Inhabited

/-- A LUT4 cell's flop: `d` is its LUT, `en` and `sr` its enable and set/reset inputs, `rv` its
`SET_NORESET` value. -/
structure Flop where
  d : Lit
  en : Lit
  sr : Lit
  rv : Bool
  site : String
  deriving DecidableEq, Repr, Inhabited

/-- A configured fabric's logic: gates (gate `k` reads only gates below `k`), flops, and the output
pins, each as (pin index, the `Lit` that drives it). -/
structure Net where
  gates : List Gate
  flops : List Flop
  outs : List (Nat × Lit)
  deriving DecidableEq, Repr, Inhabited

/-- A 2:1 multiplexer (`cus_mux21`: `S ? A1 : A0`). -/
def mux2 (s x0 x1 : Bool) : Bool := (s && x1) || (!s && x0)

/-- The LUT4 function, as `cus_mux161` computes it: a tree of 2:1 multiplexers over the truth table,
selected by `I0` first. Bit `k` of `init` is the value at `I0 + 2·I1 + 4·I2 + 8·I3 = k` (`lut4_eq_getLsbD`). -/
def lut4 (init : BitVec 16) (a b c d : Bool) : Bool :=
  let l := init.getLsbD
  mux2 d
    (mux2 c (mux2 b (mux2 a (l 0) (l 1)) (mux2 a (l 2) (l 3))) (mux2 b (mux2 a (l 4) (l 5)) (mux2 a (l 6) (l 7))))
    (mux2 c (mux2 b (mux2 a (l 8) (l 9)) (mux2 a (l 10) (l 11))) (mux2 b (mux2 a (l 12) (l 13)) (mux2 a (l 14) (l 15))))

theorem lut4_eq_getLsbD (init : BitVec 16) (a b c d : Bool) :
    lut4 init a b c d = init.getLsbD (a.toNat + 2 * b.toNat + 4 * c.toNat + 8 * d.toNat) := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp [lut4, mux2]

/-- A literal's value given the pins, the flop state and the gate values so far. -/
def Lit.eval (pins q : Nat → Bool) (vals : Array Bool) : Lit → Bool
  | .const b => b
  | .pin k => pins k
  | .ff k => q k
  | .gate k => vals.getD k false

def Gate.eval (pins q : Nat → Bool) (vals : Array Bool) (g : Gate) : Bool :=
  lut4 g.init (g.i0.eval pins q vals) (g.i1.eval pins q vals) (g.i2.eval pins q vals) (g.i3.eval pins q vals)

/-- Every gate's value, in order. -/
def evalGates (pins q : Nat → Bool) : List Gate → Array Bool → Array Bool
  | [], vals => vals
  | g :: gs, vals => evalGates pins q gs (vals.push (g.eval pins q vals))

def Net.gateVals (N : Net) (pins q : Nat → Bool) : Array Bool := evalGates pins q N.gates #[]

/-- One flop's next value. -/
def Flop.next (pins q : Nat → Bool) (vals : Array Bool) (f : Flop) (cur : Bool) : Bool :=
  mux2 (f.en.eval pins q vals) cur (mux2 (f.sr.eval pins q vals) (f.d.eval pins q vals) f.rv)

/-- The flop state after one clock edge (`false` past the last flop). -/
def Net.step (N : Net) (pins q : Nat → Bool) : Nat → Bool :=
  let vals := N.gateVals pins q
  fun k => match N.flops[k]? with
    | some f => f.next pins q vals (q k)
    | none => false

/-- The output pins' values before the edge. -/
def Net.outputs (N : Net) (pins q : Nat → Bool) : List (Nat × Bool) :=
  let vals := N.gateVals pins q
  N.outs.map fun (p, l) => (p, l.eval pins q vals)

/-- Outputs on every cycle of a trace of pin vectors, and the state after it. -/
def Net.run (N : Net) : (Nat → Bool) → List (Nat → Bool) → List (List (Nat × Bool)) × (Nat → Bool)
  | q, [] => ([], q)
  | q, p :: ps => let r := N.run (N.step p q) ps; (N.outputs p q :: r.1, r.2)

/-! ## Gate values as equations

`Net.gateVals` computes the gates in order. For a topologically ordered net (`Net.topo`), its values
are a solution of the gate equations `gatesHold`, which is how the bit-level obligations of a concrete
net state them: one Boolean per gate and one equation each, so shared logic stays shared. -/

/-- Every gate reads only gates below it. -/
def Lit.below (k : Nat) : Lit → Bool
  | .gate j => j < k
  | _ => true

def gatesTopo : List Gate → Nat → Bool
  | [], _ => true
  | g :: gs, k => g.i0.below k && g.i1.below k && g.i2.below k && g.i3.below k && gatesTopo gs (k + 1)

def Net.topo (N : Net) : Bool := gatesTopo N.gates 0

/-- A literal's value with the gate values given as a function. -/
def Lit.evalF (pins q v : Nat → Bool) : Lit → Bool
  | .const b => b
  | .pin k => pins k
  | .ff k => q k
  | .gate k => v k

/-- `v` solves the equations of gates `gs`, numbered from `k`. -/
def gatesHold (pins q v : Nat → Bool) : List Gate → Nat → Prop
  | [], _ => True
  | g :: gs, k =>
    v k = lut4 g.init (g.i0.evalF pins q v) (g.i1.evalF pins q v) (g.i2.evalF pins q v) (g.i3.evalF pins q v) ∧
      gatesHold pins q v gs (k + 1)

theorem evalGates_size (pins q : Nat → Bool) (gs : List Gate) (arr : Array Bool) :
    (evalGates pins q gs arr).size = arr.size + gs.length := by
  induction gs generalizing arr with
  | nil => simp [evalGates]
  | cons g gs ih => simp only [evalGates, ih, Array.size_push, List.length_cons]; omega

theorem evalGates_prefix (pins q : Nat → Bool) (gs : List Gate) (arr : Array Bool) (i : Nat)
    (hi : i < arr.size) : (evalGates pins q gs arr).getD i false = arr.getD i false := by
  induction gs generalizing arr with
  | nil => rfl
  | cons g gs ih =>
    simp only [evalGates]
    rw [ih _ (by simp only [Array.size_push]; omega)]
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_push, show i ≠ arr.size from by omega, ite_false]

theorem Lit.eval_eq_evalF (pins q : Nat → Bool) (arr : Array Bool) (v : Nat → Bool) (l : Lit)
    (hb : l.below arr.size = true) (hv : ∀ j, j < arr.size → v j = arr.getD j false) :
    l.eval pins q arr = l.evalF pins q v := by
  cases l with
  | gate j => simp only [Lit.below, decide_eq_true_eq] at hb; simp only [Lit.eval, Lit.evalF]; rw [hv j hb]
  | _ => rfl

theorem gatesHold_evalGates (pins q : Nat → Bool) (gs : List Gate) (arr : Array Bool)
    (hT : gatesTopo gs arr.size = true) :
    gatesHold pins q (fun i => (evalGates pins q gs arr).getD i false) gs arr.size := by
  induction gs generalizing arr with
  | nil => trivial
  | cons g gs ih =>
    simp only [gatesTopo, Bool.and_eq_true] at hT
    obtain ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, hT⟩ := hT
    let arr' := arr.push (g.eval pins q arr)
    have hs : arr'.size = arr.size + 1 := Array.size_push ..
    have hT' : gatesTopo gs arr'.size = true := by rw [hs]; exact hT
    have hv : ∀ j, j < arr.size → (evalGates pins q gs arr').getD j false = arr.getD j false := by
      intro j hj
      rw [evalGates_prefix pins q gs arr' j (by omega)]
      simp only [arr', Array.getD_eq_getD_getElem?, Array.getElem?_push, show j ≠ arr.size from by omega, ite_false]
    refine ⟨?_, ?_⟩
    · show (evalGates pins q gs arr').getD arr.size false = _
      rw [evalGates_prefix pins q gs arr' arr.size (by omega)]
      simp only [arr', Array.getD_eq_getD_getElem?, Array.getElem?_push, ite_true, Option.getD_some]
      simp only [Gate.eval]
      rw [Lit.eval_eq_evalF pins q arr _ g.i0 h0 hv, Lit.eval_eq_evalF pins q arr _ g.i1 h1 hv,
        Lit.eval_eq_evalF pins q arr _ g.i2 h2 hv, Lit.eval_eq_evalF pins q arr _ g.i3 h3 hv]
      simp only [evalGates, arr', Array.getD_eq_getD_getElem?]
    · have := ih arr' hT'
      rw [hs] at this
      exact this

/-- The gate values of a topologically ordered net solve its gate equations. -/
theorem Net.gatesHold_gateVals (N : Net) (hT : N.topo = true) (pins q : Nat → Bool) :
    gatesHold pins q (fun i => (N.gateVals pins q).getD i false) N.gates 0 :=
  gatesHold_evalGates pins q N.gates #[] hT

/-! ## The step as a list of flop values -/

/-- The flop state a register file gives, through a correspondence `M` (flop `k` holds bit `M[k].2`
of register `M[k].1`; past `M`'s end, `false`). -/
def projOf (M : List (Nat × Nat)) (regs : Nat → BitVec 64) (k : Nat) : Bool :=
  match M[k]? with
  | some (r, j) => (regs r).getLsbD j
  | none => false

theorem Net.step_eq_projOf (N : Net) (M : List (Nat × Nat)) (pins q : Nat → Bool) (R : Nat → BitVec 64)
    (hLen : N.flops.length = M.length)
    (h : N.flops.zipIdx.map (fun (f, k) => f.next pins q (N.gateVals pins q) (q k)) =
      M.map (fun (r, j) => (R r).getLsbD j)) :
    N.step pins q = projOf M R := by
  funext k
  have hk := congrArg (·[k]?) h
  simp only [List.getElem?_map, List.getElem?_zipIdx] at hk
  simp only [Net.step, projOf]
  cases hf : N.flops[k]? with
  | none =>
    have : M[k]? = none := by
      rw [List.getElem?_eq_none_iff] at hf ⊢; omega
    rw [this]
  | some f =>
    rw [hf] at hk
    cases hm : M[k]? with
    | none => rw [hm] at hk; simp at hk
    | some rj => rw [hm] at hk; simpa using hk

/-! ## The module side, cycle by cycle -/

/-- Outputs on every cycle of a trace (sampled before each edge), and the register file after it. -/
def moduleRun (m : RtlModule) :
    (Nat → BitVec 64) → List (Bool × (Nat → BitVec 64)) → List (List (String × BitVec 64)) × (Nat → BitVec 64)
  | regs, [] => ([], regs)
  | regs, c :: cs =>
    let r := moduleRun m (stepModuleRegs m c.1 c.2 regs) cs
    (evalModuleOutputsW m c.2 regs :: r.1, r.2)

theorem moduleRun_snd (m : RtlModule) (regs : Nat → BitVec 64) (tr : List (Bool × (Nat → BitVec 64))) :
    (moduleRun m regs tr).2 = runModuleTrace m regs tr := by
  induction tr generalizing regs with
  | nil => rfl
  | cons c cs ih => simp only [moduleRun, runModuleTrace, List.foldl_cons]; exact ih _

/-! ## Ports and the correspondence -/

/-- What a pin carries: bit `bit` of input `port`, the reset, or bit `bit` of output `port`. -/
inductive PinRole
  | input (port bit : Nat)
  | reset
  | output (port bit : Nat)
  deriving DecidableEq, Repr

/-- A pin: an IO BEL (`tile`, `bel` ∈ {A, B} of a `W_IO` tile) and its role. Pin `k` is the `k`-th
entry of a pin map. -/
structure Pin where
  tile : String
  bel : String
  role : PinRole
  deriving DecidableEq, Repr

def tileName (x y : Nat) : String := s!"X{x}Y{y}"

/-- Pins in order: pin `k` is IO BEL `A` (even `k`) or `B` (odd) of `W_IO` tile `X0Y(1 + k/2)`. -/
def pinsInOrder (roles : List PinRole) : List Pin :=
  roles.zipIdx.map fun (r, k) => { tile := tileName 0 (1 + k / 2), bel := if k % 2 == 0 then "A" else "B", role := r }

/-- The pin vector of one module cycle: input pins carry their port bit, the reset pin the reset. -/
def pinValues (pm : List Pin) (c : Bool × (Nat → BitVec 64)) : Nat → Bool := fun k =>
  match pm[k]? with
  | some ⟨_, _, .input port bit⟩ => (c.2 port).getLsbD bit
  | some ⟨_, _, .reset⟩ => c.1
  | _ => false

/-- The value an output pin should show, from the module's port values (in `m.outputs` order). -/
def outPinValue (pm : List Pin) (outs : List (String × BitVec 64)) (k : Nat) : Bool :=
  match pm[k]? with
  | some ⟨_, _, .output port bit⟩ => match outs[port]? with
    | some (_, v) => v.getLsbD bit
    | none => false
  | _ => false

/-- A cycle whose inputs are within the module's input widths. -/
def InputsFit (m : RtlModule) (c : Bool × (Nat → BitVec 64)) : Prop :=
  ∀ i, (c.2 i).toNat < 2 ^ inputWidth m i

/-- A register file within the module's register widths. -/
def RegsFit (m : RtlModule) (regs : Nat → BitVec 64) : Prop :=
  ∀ i, (regs i).toNat < 2 ^ regWidthOf m i

/-- The one-step condition: from every in-width register file `regs`, with the flops holding
`proj regs`, every in-width cycle leaves the flops holding `proj` of the module's next registers,
and every output pin `p` of `N.outs` shows the module's port bit. -/
def StepRealizes (N : Net) (m : RtlModule) (pm : List Pin) (proj : (Nat → BitVec 64) → Nat → Bool) : Prop :=
  ∀ regs c, RegsFit m regs → InputsFit m c →
    N.step (pinValues pm c) (proj regs) = proj (stepModuleRegs m c.1 c.2 regs) ∧
    N.outputs (pinValues pm c) (proj regs) =
      N.outs.map fun (p, _) => (p, outPinValue pm (evalModuleOutputsW m c.2 regs) p)

/-- **`fabric_realizes_module`**: if one clock step of the configured fabric `N` preserves the
correspondence `proj` and shows the module's outputs (`StepRealizes`), then from any in-width
register file, on every trace of in-width cycles, the fabric shows the module's outputs on every
cycle and ends holding `proj` of the module's final registers. -/
theorem fabric_realizes_module (N : Net) (m : RtlModule) (pm : List Pin)
    (proj : (Nat → BitVec 64) → Nat → Bool) (hChk : checkWidths m = true)
    (hStep : StepRealizes N m pm proj) :
    ∀ (tr : List (Bool × (Nat → BitVec 64))) (regs : Nat → BitVec 64),
      RegsFit m regs → (∀ c ∈ tr, InputsFit m c) →
      N.run (proj regs) (tr.map (pinValues pm)) =
        ((moduleRun m regs tr).1.map fun outs => N.outs.map fun (p, _) => (p, outPinValue pm outs p),
         proj (runModuleTrace m regs tr)) := by
  intro tr
  induction tr with
  | nil => intro regs _ _; rfl
  | cons c cs ih =>
    intro regs hRegs hIn
    have hc := hIn c List.mem_cons_self
    obtain ⟨hS, hO⟩ := hStep regs c hRegs hc
    have hRegs' : RegsFit m (stepModuleRegs m c.1 c.2 regs) :=
      stepModuleRegs_lt m c.1 c.2 regs hc hRegs hChk
    have ihr := ih _ hRegs' (fun c' h => hIn c' (List.mem_cons_of_mem _ h))
    simp only [List.map_cons, Net.run, moduleRun, runModuleTrace, List.foldl_cons] at ihr ⊢
    rw [hS, ihr, hO]

/-- The reset condition: a reset cycle, from any flop state, leaves the flops holding `proj` of the
module's registers after reset (whatever they were). -/
def ResetRealizes (N : Net) (m : RtlModule) (pm : List Pin) (proj : (Nat → BitVec 64) → Nat → Bool) : Prop :=
  ∀ (q : Nat → Bool) regs (ins : Nat → BitVec 64), InputsFit m (true, ins) →
    N.step (pinValues pm (true, ins)) q = proj (stepModuleRegs m true ins regs)

/-- **`fabric_realizes_module_from_reset`**: with `ResetRealizes` as well, the fabric started in any
flop state (a configured FPGA's flops power up unknown) agrees with the module on every cycle after a
first reset cycle, whatever the module's registers were. -/
theorem fabric_realizes_module_from_reset (N : Net) (m : RtlModule) (pm : List Pin)
    (proj : (Nat → BitVec 64) → Nat → Bool) (hChk : checkWidths m = true)
    (hStep : StepRealizes N m pm proj) (hRst : ResetRealizes N m pm proj)
    (hRstFit : ∀ regs ins, InputsFit m (true, ins) → RegsFit m (stepModuleRegs m true ins regs))
    (q : Nat → Bool) (regs : Nat → BitVec 64) (ins : Nat → BitVec 64)
    (tr : List (Bool × (Nat → BitVec 64))) (hIn0 : InputsFit m (true, ins)) (hIn : ∀ c ∈ tr, InputsFit m c) :
    (N.run q (pinValues pm (true, ins) :: tr.map (pinValues pm))).1.tail =
        (moduleRun m (stepModuleRegs m true ins regs) tr).1.map
          (fun outs => N.outs.map fun (p, _) => (p, outPinValue pm outs p)) := by
  simp only [Net.run, List.tail_cons]
  rw [hRst q regs ins hIn0]
  rw [fabric_realizes_module N m pm proj hChk hStep tr _ (hRstFit regs ins hIn0) hIn]

end Obend.Hardware.Fabulous
