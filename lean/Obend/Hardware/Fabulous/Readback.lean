module
/-
# Obend.Hardware.Fabulous.Readback — the configured fabric, from its tile models, computes the `Net`

The fabric is a grid of tiles. Each tile of a modelled type carries its switch matrix
(`Obend.Hardware.Fabulous.Tile`, read from FABulous's generated Verilog and LEC'd against it) and its
LUT4 cells (`lut4cModule`, likewise LEC'd); between them run the fabric's wires. The grid semantics is a
consistency relation over the value of every wire (`Consistent`): each switch-matrix output is what
`smModule` computes from the tile's wires and configuration bits, each wire carries its source, each
cell's `O` is what `lut4cModule` computes from its inputs, its flop and its configuration bits, and each
input pad carries its pin. No fixpoint is computed; a theorem holds for every consistent assignment.

The extraction (`Obend.Hardware.Fabulous.Bitstream.extractS`) emits a certificate (`Cert`): for every
input of every gate and flop and every output pin, the hops it followed back to a source, each a
switch-matrix hop (`Hop.sm k i`: output `k` of the tile's switch matrix, configured to select input `i`)
or a wire (`Hop.wire`). `Cert.check` is the structural part (kernel-decided for a concrete
certificate); `Cert.required` lists the configuration bits it rests on and `Cert.wiresUsed` the wires.
`readback_sound`: if the certificate checks, the grid has those tile models and wires, and the
configuration has those bits, then in every consistent assignment the output pins carry `Net.outputs`
and every flop's next value is `Net.step`. `fabric_run_eq` lifts that to every cycle of a run.

What the grid takes as given: the tiles' top-level wiring (`LUT4AB.v`'s jump wires and nested wires,
listed as `Grid.wires`), the configuration latches' index-to-frame map (`TileModel.pos`), and the input
pads (`Grid.pads`). The carry chain and `MUX8LUT` are not in the certificate's vocabulary (the
extraction refuses a design that uses them).
-/
public import Obend.Hardware.Fabulous.Cell
@[expose] public section

namespace Obend.Hardware.Fabulous

open Obend.Hardware.HDL

/-- A wire of the fabric: tile column `x`, row `y`, and its name in that tile. -/
structure Node where
  x : Nat
  y : Nat
  w : String
  deriving DecidableEq, Repr, Inhabited

/-- The fabric: the model of each tile, the wires outside the switch matrices `(source, destination)`,
and the input pads `(pin, node)`. -/
structure Grid where
  tile : Nat → Nat → Option TileModel
  wires : List (Node × Node)
  pads : List (Nat × Node)

/-- The configuration: frame bit `p` of tile `(x, y)`. -/
abbrev Bits := Nat → Nat → Nat → Bool

/-- A cell port: `cellNode x y "LA_" "O"` is `LA_O` of tile `(x, y)`. -/
def cellNode (x y : Nat) (pre port : String) : Node := ⟨x, y, pre ++ port⟩

/-- `lut4cModule`'s inputs for the cell with prefix `pre` of a tile, from the wire values. -/
def cellInsAt (tm : TileModel) (b : Nat → Bool) (σ : Node → Bool) (x y : Nat) (pre : String) (co : Nat) :
    Nat → BitVec 64 :=
  cellIns (σ (cellNode x y pre "I0")) (σ (cellNode x y pre "I1")) (σ (cellNode x y pre "I2"))
    (σ (cellNode x y pre "I3")) (σ (cellNode x y pre "Ci")) (σ (cellNode x y pre "SR")) (σ (cellNode x y pre "EN"))
    (tm.cellCfg b co)

/-- **The grid semantics.** `σ` gives every wire a value, `Q` every cell's flop (by `⟨x, y, prefix⟩`). -/
structure Consistent (G : Grid) (b : Bits) (pins : Nat → Bool) (Q σ : Node → Bool) : Prop where
  sm : ∀ x y tm, G.tile x y = some tm → ∀ (k : Nat) (o : String) (p : SmPrim), tm.sm.prims[k]? = some (o, p) →
    (evalModuleOutputsW (smModule tm.sm) (smIns tm.sm (tm.smCfg (b x y)) (fun n => σ ⟨x, y, n⟩)) (fun _ => 0#64))[k]? =
      some (o, boolBV (σ ⟨x, y, o⟩))
  wire : ∀ e ∈ G.wires, σ e.2 = σ e.1
  cell : ∀ x y tm, G.tile x y = some tm → ∀ pre co, (pre, co) ∈ tm.cells →
    (evalModuleOutputsW lut4cModule (cellInsAt tm (b x y) σ x y pre co) (fun _ => boolBV (Q ⟨x, y, pre⟩)))[0]? =
      some ("O", boolBV (σ (cellNode x y pre "O")))
  pad : ∀ e ∈ G.pads, σ e.2 = pins e.1

/-- Each cell's flop after the clock edge, through `lut4cModule`'s register; other state holds. -/
def cellNext (G : Grid) (b : Bits) (Q σ : Node → Bool) (n : Node) : Bool :=
  match G.tile n.x n.y with
  | some tm =>
    match tm.cells.lookup n.w with
    | some co => stepModuleRegs lut4cModule false (cellInsAt tm (b n.x n.y) σ n.x n.y n.w co) (fun _ => boolBV (Q n)) 0 != 0#64
    | none => Q n
  | none => Q n

/-! ## The certificate -/

/-- One hop backwards from a wire to the wire driving it. -/
inductive Hop
  /-- the wire is output `k` of its tile's switch matrix, configured to select input `i` -/
  | sm (k i : Nat)
  /-- the wire is driven by fabric wire `src` -/
  | wire (src : Node)
  deriving DecidableEq, Repr, Inhabited

/-- Where a path ends: a wire, or a constant input of a multiplexer. -/
inductive End
  | node (n : Node)
  | const (b : Bool)
  deriving DecidableEq, Repr, Inhabited

def End.val (σ : Node → Bool) : End → Bool
  | .node n => σ n
  | .const b => b

/-- A configuration bit `(x, y, frame position, value)` a certificate rests on. -/
abbrev BitReq := Nat × Nat × Nat × Bool

/-- A gate's cell and the paths of its four inputs (`none`: the truth table ignores that input). -/
structure GateCert where
  x : Nat
  y : Nat
  pre : String
  isFlop : Bool
  ins : List (Option (List Hop))
  deriving DecidableEq, Repr, Inhabited

/-- A flop's cell, its gate (the same cell's LUT), and the paths of its `EN` and `SR`. -/
structure FlopCert where
  x : Nat
  y : Nat
  pre : String
  gate : Nat
  en : List Hop
  sr : List Hop
  deriving DecidableEq, Repr, Inhabited

structure Cert where
  /-- the tile models used -/
  models : List TileModel
  /-- `((x, y), model index)` for every tile a path or cell is in -/
  tiles : List ((Nat × Nat) × Nat)
  gates : List GateCert
  flops : List FlopCert
  /-- each output pin: its pin index, the node it shows, and that node's path -/
  outs : List (Nat × Node × List Hop)
  /-- the input pads read -/
  pads : List (Nat × Node)
  deriving DecidableEq, Repr, Inhabited

def Cert.tileOf (C : Cert) (x y : Nat) : Option TileModel :=
  match C.tiles.find? (fun e => e.1.1 == x && e.1.2 == y) with
  | some e => C.models[e.2]?
  | none => none

/-- Follow a path from `n`: where it ends, the wires it used, the configuration bits it read. -/
def Cert.walk (C : Cert) : Node → List Hop → Option (End × List (Node × Node) × List BitReq)
  | n, [] => some (.node n, [], [])
  | n, .sm k i :: hs =>
    match C.tileOf n.x n.y with
    | none => none
    | some tm =>
      match tm.sm.prims[k]? with
      | none => none
      | some (o, p) =>
        if o = n.w then
          let req : List BitReq := (List.range p.selBits).map fun c =>
            (n.x, n.y, tm.pos.getD (tm.smOff + (p.base + c)) 0, i.testBit c)
          match p.ins[i]? with
          | some (.port m) =>
            match C.walk ⟨n.x, n.y, m⟩ hs with
            | some (e, W, B) => some (e, W, req ++ B)
            | none => none
          | some (.const c) => if hs = [] then some (.const c, [], req) else none
          | none => none
        else none
  | n, .wire s :: hs =>
    match C.walk s hs with
    | some (e, W, B) => some (e, (s, n) :: W, B)
    | none => none

/-! ## A path carries its source -/

theorem boolBV_inj {a b : Bool} (h : boolBV a = boolBV b) : a = b := by
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

theorem selFrom_testBit (bit : Nat → Bool) (base : Nat) :
    ∀ (k j i : Nat), (∀ c < k, bit (base + j + c) = i.testBit c) → i < 2 ^ k → selFrom bit base j k = i
  | 0, _, i, _, hi => by simp at hi; simp [selFrom]; omega
  | k + 1, j, i, h, hi => by
    simp only [selFrom]
    have h0 := h 0 (by omega)
    rw [show base + j + 0 = base + j by omega, Nat.testBit_zero] at h0
    have ih := selFrom_testBit bit base k (j + 1) (i / 2) (fun c hc => by
      have := h (c + 1) (by omega)
      rwa [show base + j + (c + 1) = base + (j + 1) + c by omega, Nat.testBit_succ] at this)
      (by rw [Nat.pow_succ] at hi; omega)
    rw [ih, h0]
    by_cases hm : i % 2 = 1 <;> simp [hm] <;> omega

theorem SmPrim.ins_length_of_selBits_zero (p : SmPrim) (h : p.selBits = 0) : p.ins.length = 1 := by
  cases p <;> simp_all [SmPrim.selBits, SmPrim.ins]

/-- A switch-matrix output in a consistent assignment is its primitive's `SmPrim.eval` (through
`smModule_eval_eq_SmPrim_eval`). -/
theorem Consistent.sm_eval {G : Grid} {b : Bits} {pins : Nat → Bool} {Q σ : Node → Bool}
    (hσ : Consistent G b pins Q σ) {x y : Nat} {tm : TileModel} (hT : G.tile x y = some tm)
    (hWF : tm.sm.wf = true) {k : Nat} {o : String} {p : SmPrim} (hk : tm.sm.prims[k]? = some (o, p)) :
    σ ⟨x, y, o⟩ = p.eval (tm.smCfg (b x y)) (fun n => σ ⟨x, y, n⟩) := by
  have h := hσ.sm x y tm hT k o p hk
  rw [smModule_eval_eq_SmPrim_eval tm.sm hWF _ _ _ _ (smIns_encodes _ _ _), List.getElem?_map, hk] at h
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, true_and] at h
  exact (boolBV_inj h).symm

theorem Cert.walk_sound (C : Cert) (G : Grid) (b : Bits) (pins : Nat → Bool) (Q σ : Node → Bool)
    (hσ : Consistent G b pins Q σ)
    (hG : ∀ x y tm, C.tileOf x y = some tm → G.tile x y = some tm)
    (hWF : ∀ x y tm, C.tileOf x y = some tm → tm.sm.wf = true) :
    ∀ (hs : List Hop) (n : Node) (e : End) (W : List (Node × Node)) (B : List BitReq),
      C.walk n hs = some (e, W, B) → (∀ w ∈ W, w ∈ G.wires) → (∀ r ∈ B, b r.1 r.2.1 r.2.2.1 = r.2.2.2) →
      σ n = e.val σ
  | [], n, e, W, B, h, _, _ => by
    simp only [Cert.walk, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]; rfl
  | .wire s :: hs, n, e, W, B, h, hW, hB => by
    simp only [Cert.walk] at h
    split at h
    · rename_i e' W' B' hr
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      rw [hσ.wire (s, n) (hW _ (List.mem_cons_self ..)),
        C.walk_sound G b pins Q σ hσ hG hWF hs s e' W' B' hr (fun w hw => hW w (List.mem_cons_of_mem _ hw)) hB]
    · simp at h
  | .sm k i :: hs, n, e, W, B, h, hW, hB => by
    obtain ⟨x, y, w⟩ := n
    simp only [Cert.walk] at h
    split at h
    · simp at h
    rename_i tm htm
    split at h
    · simp at h
    rename_i o p hk
    split at h
    rotate_left
    · simp at h
    rename_i ho
    subst ho
    have hwf := hWF x y tm htm
    have hσo := hσ.sm_eval (hG x y tm htm) hwf hk
    have hpm : (o, p) ∈ tm.sm.prims := List.mem_of_getElem? hk
    have hp := List.all_eq_true.mp hwf (o, p) hpm
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq] at hp
    -- the configured select is `i`
    have hsel : ∀ (B' : List BitReq),
        (∀ r ∈ (List.range p.selBits).map (fun c => ((x, y, tm.pos.getD (tm.smOff + (p.base + c)) 0, i.testBit c) : BitReq)) ++ B',
          b r.1 r.2.1 r.2.2.1 = r.2.2.2) → i < p.ins.length →
        p.sel (tm.smCfg (b x y)) = i := by
      intro B' hB' hi
      rw [SmPrim.sel_eq_selFrom]
      refine selFrom_testBit _ _ _ 0 i (fun c hc => ?_) ?_
      · have := hB' _ (List.mem_append_left _ (List.mem_map.mpr ⟨c, List.mem_range.mpr hc, rfl⟩))
        simpa [TileModel.smCfg, TileModel.bit] using this
      · rcases hp.1.1 with h0 | h1
        · have := SmPrim.ins_length_of_selBits_zero p h0; rw [h0]; omega
        · omega
    split at h
    · rename_i m hm
      split at h
      · rename_i e' W' B' hr
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        have hi : i < p.ins.length := (List.getElem?_eq_some_iff.mp hm).1
        rw [hσo, SmPrim.eval, hsel B' hB hi, hm]
        simp only [Option.map_some, Option.getD_some, SmSrc.eval]
        exact C.walk_sound G b pins Q σ hσ hG hWF hs ⟨x, y, m⟩ e' W' B' hr hW
          (fun r hr => hB r (List.mem_append_right _ hr))
      · simp at h
    · rename_i c hc
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        have hi : i < p.ins.length := (List.getElem?_eq_some_iff.mp hc).1
        rw [hσo, SmPrim.eval, hsel [] (by simpa using hB) hi, hc]
        rfl
      · simp at h
    · simp at h

/-! ## Checking a certificate against a `Net` -/

/-- The `Lit` a path end stands for: a constant, an input pad, a combinational cell's `O`, a flop cell's `O`. -/
def Cert.litEnd (C : Cert) : Lit → End → Bool
  | .const c, .const c' => c == c'
  | .pin k, .node n => C.pads.contains (k, n)
  | .gate k, .node n =>
    match C.gates[k]? with
    | some g => !g.isFlop && n == cellNode g.x g.y g.pre "O"
    | none => false
  | .ff k, .node n =>
    match C.flops[k]? with
    | some f => n == cellNode f.x f.y f.pre "O"
    | none => false
  | _, _ => false

/-- The path from `start` ends where `l` says. -/
def Cert.pathOK (C : Cert) (start : Node) (hs : List Hop) (l : Lit) : Bool :=
  match C.walk start hs with
  | some (e, _, _) => C.litEnd l e
  | none => false

def Cert.pathReqs (C : Cert) (start : Node) (hs : List Hop) : List BitReq :=
  match C.walk start hs with
  | some (_, _, B) => B
  | none => []

def Cert.pathWires (C : Cert) (start : Node) (hs : List Hop) : List (Node × Node) :=
  match C.walk start hs with
  | some (_, W, _) => W
  | none => []

/-- Where a cell's configuration bits start. -/
def Cert.cellOff (C : Cert) (x y : Nat) (pre : String) : Option Nat :=
  match C.tileOf x y with
  | some tm => tm.cells.lookup pre
  | none => none

/-- Input `port` of a gate: followed to `l`, or ignored by the truth table and read as `false`. -/
def Cert.inOK (C : Cert) (gc : GateCert) (init : BitVec 16) (i : Nat) (port : String) (l : Lit) :
    Option (List Hop) → Bool
  | some hs => C.pathOK (cellNode gc.x gc.y gc.pre port) hs l
  | none => l == .const false && ignores init i

def Cert.gateOK (C : Cert) (g : Gate) (gc : GateCert) : Bool :=
  (C.cellOff gc.x gc.y gc.pre).isSome &&
  match gc.ins with
  | [p0, p1, p2, p3] =>
    C.inOK gc g.init 0 "I0" g.i0 p0 && C.inOK gc g.init 1 "I1" g.i1 p1 && C.inOK gc g.init 2 "I2" g.i2 p2 &&
      C.inOK gc g.init 3 "I3" g.i3 p3
  | _ => false

def Cert.flopOK (C : Cert) (nG : Nat) (f : Flop) (fc : FlopCert) : Bool :=
  (C.cellOff fc.x fc.y fc.pre).isSome && f.d == .gate fc.gate && fc.gate < nG &&
  (match C.gates[fc.gate]? with
    | some g => g.isFlop && g.x == fc.x && g.y == fc.y && g.pre == fc.pre
    | none => false) &&
  f.en.below nG && f.sr.below nG &&
  C.pathOK (cellNode fc.x fc.y fc.pre "EN") fc.en f.en && C.pathOK (cellNode fc.x fc.y fc.pre "SR") fc.sr f.sr

/-- **The structural check**, decided by the kernel for a concrete certificate. -/
def Cert.check (C : Cert) (N : Net) : Bool :=
  C.models.all (·.sm.wf) && N.gates.length == C.gates.length && N.flops.length == C.flops.length &&
  N.outs.length == C.outs.length &&
  (List.range N.gates.length).all (fun k =>
    match N.gates[k]?, C.gates[k]? with
    | some g, some gc => C.gateOK g gc
    | _, _ => false) &&
  (List.range N.flops.length).all (fun k =>
    match N.flops[k]?, C.flops[k]? with
    | some f, some fc => C.flopOK N.gates.length f fc
    | _, _ => false) &&
  (List.range N.outs.length).all (fun k =>
    match N.outs[k]?, C.outs[k]? with
    | some (p, l), some (p', n, hs) => p == p' && l.below N.gates.length && C.pathOK n hs l
    | _, _ => false)

/-- A cell's configuration bits: the truth table, `FF`, `I0mux` off, and, for a flop, `SET_NORESET`. -/
def Cert.cellReqs (C : Cert) (x y : Nat) (pre : String) (init : BitVec 16) (ff : Bool) : List BitReq :=
  match C.tileOf x y, C.cellOff x y pre with
  | some tm, some co =>
    (List.range 16).map (fun j => (x, y, tm.pos.getD (co + j) 0, init.getLsbD j)) ++
      [(x, y, tm.pos.getD (co + 16) 0, ff), (x, y, tm.pos.getD (co + 17) 0, false)]
  | _, _ => []

def Cert.rvReq (C : Cert) (x y : Nat) (pre : String) (rv : Bool) : List BitReq :=
  match C.tileOf x y, C.cellOff x y pre with
  | some tm, some co => [(x, y, tm.pos.getD (co + 18) 0, rv)]
  | _, _ => []

def Cert.inReqs (C : Cert) (gc : GateCert) (port : String) : Option (List Hop) → List BitReq
  | some hs => C.pathReqs (cellNode gc.x gc.y gc.pre port) hs
  | none => []

def Cert.inWires (C : Cert) (gc : GateCert) (port : String) : Option (List Hop) → List (Node × Node)
  | some hs => C.pathWires (cellNode gc.x gc.y gc.pre port) hs
  | none => []

def portName : Nat → String
  | 0 => "I0" | 1 => "I1" | 2 => "I2" | _ => "I3"

/-- **The configuration bits the certificate rests on.** `obend fabric check` compares them with the bitstream. -/
def Cert.required (C : Cert) (N : Net) : List BitReq :=
  (List.range N.gates.length).flatMap (fun k =>
    match N.gates[k]?, C.gates[k]? with
    | some g, some gc =>
      C.cellReqs gc.x gc.y gc.pre g.init gc.isFlop ++
        (List.range 4).flatMap fun i => C.inReqs gc (portName i) (gc.ins.getD i none)
    | _, _ => []) ++
  (List.range N.flops.length).flatMap (fun k =>
    match N.flops[k]?, C.flops[k]? with
    | some f, some fc =>
      C.rvReq fc.x fc.y fc.pre f.rv ++ C.pathReqs (cellNode fc.x fc.y fc.pre "EN") fc.en ++
        C.pathReqs (cellNode fc.x fc.y fc.pre "SR") fc.sr
    | _, _ => []) ++
  C.outs.flatMap (fun (_, n, hs) => C.pathReqs n hs)

/-- **The fabric wires the certificate rests on.** -/
def Cert.wiresUsed (C : Cert) : List (Node × Node) :=
  C.gates.flatMap (fun gc => (List.range 4).flatMap fun i => C.inWires gc (portName i) (gc.ins.getD i none)) ++
  C.flops.flatMap (fun fc =>
    C.pathWires (cellNode fc.x fc.y fc.pre "EN") fc.en ++ C.pathWires (cellNode fc.x fc.y fc.pre "SR") fc.sr) ++
  C.outs.flatMap (fun (_, n, hs) => C.pathWires n hs)

/-- Net flop `k`'s cell, and the flop state the `Net` sees. -/
def Cert.flopNode (C : Cert) (k : Nat) : Node :=
  match C.flops[k]? with
  | some f => ⟨f.x, f.y, f.pre⟩
  | none => default

def Cert.q (C : Cert) (Q : Node → Bool) (k : Nat) : Bool := if k < C.flops.length then Q (C.flopNode k) else false

/-- What the output pins show. -/
def Cert.observe (C : Cert) (σ : Node → Bool) : List (Nat × Bool) := C.outs.map fun (p, n, _) => (p, σ n)

/-! ## Soundness -/

theorem lookup_mem {pre : String} {co : Nat} : ∀ {L : List (String × Nat)}, L.lookup pre = some co → (pre, co) ∈ L
  | [], h => by simp at h
  | (a, c) :: L, h => by
    simp only [List.lookup_cons] at h
    split at h
    · rename_i ha
      simp only [beq_iff_eq] at ha
      simp only [Option.some.injEq] at h
      subst ha h; exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (lookup_mem h)

theorem Cert.tileOf_grid (C : Cert) (G : Grid) (hT : ∀ e ∈ C.tiles, G.tile e.1.1 e.1.2 = C.models[e.2]?)
    {x y : Nat} {tm : TileModel} (h : C.tileOf x y = some tm) : G.tile x y = some tm := by
  unfold Cert.tileOf at h
  split at h
  · rename_i e he
    have hp := List.find?_some he
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    rw [← hp.1, ← hp.2, hT e (List.mem_of_find?_eq_some he), h]
  · simp at h

theorem Cert.tileOf_wf (C : Cert) (hW : C.models.all (·.sm.wf) = true) {x y : Nat} {tm : TileModel}
    (h : C.tileOf x y = some tm) : tm.sm.wf = true := by
  unfold Cert.tileOf at h
  split at h
  · exact List.all_eq_true.mp hW tm (List.mem_of_getElem? h)
  · simp at h

theorem Cert.cellOff_some {C : Cert} {x y : Nat} {pre : String} {co : Nat} (h : C.cellOff x y pre = some co) :
    ∃ tm, C.tileOf x y = some tm ∧ tm.cells.lookup pre = some co := by
  unfold Cert.cellOff at h
  split at h
  · exact ⟨_, by assumption, h⟩
  · simp at h

theorem Cert.walk_of_pathOK {C : Cert} {start : Node} {hs : List Hop} {l : Lit} (h : C.pathOK start hs l = true) :
    ∃ e W B, C.walk start hs = some (e, W, B) ∧ C.litEnd l e = true ∧
      C.pathWires start hs = W ∧ C.pathReqs start hs = B := by
  unfold Cert.pathOK at h
  split at h
  · rename_i e W B hw
    exact ⟨e, W, B, hw, h, by simp [Cert.pathWires, hw], by simp [Cert.pathReqs, hw]⟩
  · simp at h

/-- The value of gate `k` in the fabric: its cell's LUT over the cell's input wires. -/
def Cert.lutVal (C : Cert) (N : Net) (σ : Node → Bool) (k : Nat) : Bool :=
  match N.gates[k]?, C.gates[k]? with
  | some g, some gc =>
    lut4 g.init (σ (cellNode gc.x gc.y gc.pre "I0")) (σ (cellNode gc.x gc.y gc.pre "I1"))
      (σ (cellNode gc.x gc.y gc.pre "I2")) (σ (cellNode gc.x gc.y gc.pre "I3"))
  | _, _ => false

theorem Lit.evalF_congr (pins q v v' : Nat → Bool) (n : Nat) (l : Lit) (hb : l.below n = true)
    (h : ∀ j < n, v j = v' j) : l.evalF pins q v = l.evalF pins q v' := by
  cases l with
  | gate j => simp only [Lit.below, decide_eq_true_eq] at hb; simp only [Lit.evalF]; exact h j hb
  | _ => rfl

theorem gatesHold_of (pins q v : Nat → Bool) : ∀ (gs : List Gate) (k0 : Nat),
    (∀ j (h : j < gs.length), v (k0 + j) = lut4 gs[j].init (gs[j].i0.evalF pins q v) (gs[j].i1.evalF pins q v)
      (gs[j].i2.evalF pins q v) (gs[j].i3.evalF pins q v)) → gatesHold pins q v gs k0
  | [], _, _ => trivial
  | g :: gs, k0, h => ⟨by have := h 0 (by simp); rwa [List.getElem_cons_zero, Nat.add_zero] at this,
      gatesHold_of pins q v gs (k0 + 1) (fun j hj => by
        have := h (j + 1) (by simp; omega)
        rwa [show k0 + (j + 1) = k0 + 1 + j by omega, List.getElem_cons_succ] at this)⟩

/-- A topologically ordered net's gate equations have one solution. -/
theorem gatesHold_unique (pins q v v' : Nat → Bool) : ∀ (gs : List Gate) (k0 : Nat),
    gatesTopo gs k0 = true → gatesHold pins q v gs k0 → gatesHold pins q v' gs k0 →
      (∀ j < k0, v j = v' j) → ∀ j < k0 + gs.length, v j = v' j
  | [], _, _, _, _, h, j, hj => h j (by simpa using hj)
  | g :: gs, k0, hT, ⟨h1, h2⟩, ⟨h1', h2'⟩, h, j, hj => by
    simp only [gatesTopo, Bool.and_eq_true] at hT
    obtain ⟨⟨⟨⟨b0, b1⟩, b2⟩, b3⟩, hT⟩ := hT
    have hk : v k0 = v' k0 := by
      rw [h1, h1', Lit.evalF_congr pins q v v' k0 _ b0 h, Lit.evalF_congr pins q v v' k0 _ b1 h,
        Lit.evalF_congr pins q v v' k0 _ b2 h, Lit.evalF_congr pins q v v' k0 _ b3 h]
    exact gatesHold_unique pins q v v' gs (k0 + 1) hT h2 h2'
      (fun i hi => if hik : i < k0 then h i hik else by rw [show i = k0 by omega]; exact hk) j
      (by simp at hj; omega)

theorem lut4_args (init : BitVec 16) (a0 a1 a2 a3 e0 e1 e2 e3 : Bool)
    (h0 : a0 = e0 ∨ (e0 = false ∧ ignores init 0 = true)) (h1 : a1 = e1 ∨ (e1 = false ∧ ignores init 1 = true))
    (h2 : a2 = e2 ∨ (e2 = false ∧ ignores init 2 = true)) (h3 : a3 = e3 ∨ (e3 = false ∧ ignores init 3 = true)) :
    lut4 init a0 a1 a2 a3 = lut4 init e0 e1 e2 e3 := by
  have s0 : lut4 init a0 a1 a2 a3 = lut4 init e0 a1 a2 a3 := by
    rcases h0 with h | ⟨rfl, h⟩
    · rw [h]
    · exact (lut4_ignored init a0 a1 a2 a3).1 h
  have s1 : lut4 init e0 a1 a2 a3 = lut4 init e0 e1 a2 a3 := by
    rcases h1 with h | ⟨rfl, h⟩
    · rw [h]
    · exact (lut4_ignored init e0 a1 a2 a3).2.1 h
  have s2 : lut4 init e0 e1 a2 a3 = lut4 init e0 e1 e2 a3 := by
    rcases h2 with h | ⟨rfl, h⟩
    · rw [h]
    · exact (lut4_ignored init e0 e1 a2 a3).2.2.1 h
  have s3 : lut4 init e0 e1 e2 a3 = lut4 init e0 e1 e2 e3 := by
    rcases h3 with h | ⟨rfl, h⟩
    · rw [h]
    · exact (lut4_ignored init e0 e1 e2 a3).2.2.2 h
  rw [s0, s1, s2, s3]

theorem Cert.check_spec {C : Cert} {N : Net} (h : C.check N = true) :
    C.models.all (·.sm.wf) = true ∧ N.gates.length = C.gates.length ∧ N.flops.length = C.flops.length ∧
    N.outs.length = C.outs.length ∧
    (∀ k < N.gates.length, ∃ g gc, N.gates[k]? = some g ∧ C.gates[k]? = some gc ∧ C.gateOK g gc = true) ∧
    (∀ k < N.flops.length, ∃ f fc, N.flops[k]? = some f ∧ C.flops[k]? = some fc ∧
      C.flopOK N.gates.length f fc = true) ∧
    (∀ k < N.outs.length, ∃ p l n hs, N.outs[k]? = some (p, l) ∧ C.outs[k]? = some (p, n, hs) ∧
      l.below N.gates.length = true ∧ C.pathOK n hs l = true) := by
  simp only [Cert.check, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨hw, hg⟩, hf⟩, ho⟩, hG⟩, hF⟩, hO⟩ := h
  refine ⟨List.all_eq_true.mpr hw, hg, hf, ho, fun k hk => ?_, fun k hk => ?_, fun k hk => ?_⟩
  · have := hG k hk
    split at this
    · exact ⟨_, _, by assumption, by assumption, this⟩
    · simp at this
  · have := hF k hk
    split at this
    · exact ⟨_, _, by assumption, by assumption, this⟩
    · simp at this
  · have := hO k hk
    split at this
    · rename_i p l p' n hs h1 h2
      simp only [Bool.and_eq_true, beq_iff_eq] at this
      obtain ⟨⟨rfl, hb⟩, hp⟩ := this
      exact ⟨p, l, n, hs, h1, h2, hb, hp⟩
    · simp at this

theorem Cert.req_gate {C : Cert} {N : Net} {k : Nat} {g : Gate} {gc : GateCert}
    (hg : N.gates[k]? = some g) (hgc : C.gates[k]? = some gc) :
    (∀ r ∈ C.cellReqs gc.x gc.y gc.pre g.init gc.isFlop, r ∈ C.required N) ∧
    (∀ i < 4, ∀ r ∈ C.inReqs gc (portName i) (gc.ins.getD i none), r ∈ C.required N) := by
  have hk : k < N.gates.length := (List.getElem?_eq_some_iff.mp hg).1
  refine ⟨fun r hr => ?_, fun i hi r hr => ?_⟩ <;>
  · unfold Cert.required
    refine List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.mpr ⟨k, List.mem_range.mpr hk, ?_⟩))
    simp only [hg, hgc]
    first
    | exact List.mem_append_left _ hr
    | exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi, hr⟩)

theorem Cert.req_flop {C : Cert} {N : Net} {k : Nat} {f : Flop} {fc : FlopCert}
    (hf : N.flops[k]? = some f) (hfc : C.flops[k]? = some fc) :
    ∀ r ∈ C.rvReq fc.x fc.y fc.pre f.rv ++ C.pathReqs (cellNode fc.x fc.y fc.pre "EN") fc.en ++
      C.pathReqs (cellNode fc.x fc.y fc.pre "SR") fc.sr, r ∈ C.required N := by
  have hk : k < N.flops.length := (List.getElem?_eq_some_iff.mp hf).1
  intro r hr
  unfold Cert.required
  refine List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨k, List.mem_range.mpr hk, ?_⟩))
  simp only [hf, hfc]
  exact hr

theorem Cert.req_out {C : Cert} {N : Net} {p : Nat} {n : Node} {hs : List Hop} (hm : (p, n, hs) ∈ C.outs) :
    ∀ r ∈ C.pathReqs n hs, r ∈ C.required N := fun _ hr =>
  List.mem_append_right _ (List.mem_flatMap.mpr ⟨(p, n, hs), hm, hr⟩)

theorem Cert.wires_gate {C : Cert} {gc : GateCert} (hm : gc ∈ C.gates) :
    ∀ i < 4, ∀ w ∈ C.inWires gc (portName i) (gc.ins.getD i none), w ∈ C.wiresUsed := fun i hi _ hw =>
  List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.mpr ⟨gc, hm,
    List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi, hw⟩⟩))

theorem Cert.wires_flop {C : Cert} {fc : FlopCert} (hm : fc ∈ C.flops) :
    ∀ w ∈ C.pathWires (cellNode fc.x fc.y fc.pre "EN") fc.en ++ C.pathWires (cellNode fc.x fc.y fc.pre "SR") fc.sr,
      w ∈ C.wiresUsed := fun _ hw =>
  List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨fc, hm, hw⟩))

theorem Cert.wires_out {C : Cert} {p : Nat} {n : Node} {hs : List Hop} (hm : (p, n, hs) ∈ C.outs) :
    ∀ w ∈ C.pathWires n hs, w ∈ C.wiresUsed := fun _ hw =>
  List.mem_append_right _ (List.mem_flatMap.mpr ⟨(p, n, hs), hm, hw⟩)

section Sound

variable (C : Cert) (N : Net) (G : Grid) (b : Bits) (pins : Nat → Bool) (Q σ : Node → Bool)

/-- A cell's `O` in a consistent assignment, from `lut4c_O` and its configuration bits. -/
theorem cell_O_val (hσ : Consistent G b pins Q σ) (hT : ∀ e ∈ C.tiles, G.tile e.1.1 e.1.2 = C.models[e.2]?)
    {x y : Nat} {pre : String} {co : Nat} (hco : C.cellOff x y pre = some co) (init : BitVec 16) (ff : Bool)
    (hReq : ∀ r ∈ C.cellReqs x y pre init ff, b r.1 r.2.1 r.2.2.1 = r.2.2.2) :
    σ (cellNode x y pre "O") =
      if ff then Q ⟨x, y, pre⟩ else
        lut4 init (σ (cellNode x y pre "I0")) (σ (cellNode x y pre "I1")) (σ (cellNode x y pre "I2"))
          (σ (cellNode x y pre "I3")) := by
  obtain ⟨tm, htm, hl⟩ := Cert.cellOff_some hco
  have h := hσ.cell x y tm (C.tileOf_grid G hT htm) pre co (lookup_mem hl)
  simp only [cellInsAt] at h
  rw [lut4c_O] at h
  simp only [Option.some.injEq, Prod.mk.injEq, true_and] at h
  rw [← boolBV_inj h]
  simp only [Cert.cellReqs, htm, hco, List.mem_append, List.mem_map, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false] at hReq
  have h16 : tm.cellCfg (b x y) co 16 = ff := hReq _ (Or.inr (Or.inl rfl))
  have h17 : tm.cellCfg (b x y) co 17 = false := hReq _ (Or.inr (Or.inr rfl))
  have hj : ∀ j < 16, tm.cellCfg (b x y) co j = init.getLsbD j := fun j hj => hReq _ (Or.inl ⟨j, hj, rfl⟩)
  rw [h16]
  cases ff
  · simp only [Bool.false_eq_true, ite_false, cellLut, h17, lut4_eq_lut4F]
    exact lut4F_congr _ _ hj _ _ _ _
  · rfl

/-- A flop cell's next value, from `lut4c_next` and its configuration bits. -/
theorem cell_next_val (hT : ∀ e ∈ C.tiles, G.tile e.1.1 e.1.2 = C.models[e.2]?)
    {x y : Nat} {pre : String} {co : Nat} (hco : C.cellOff x y pre = some co) (init : BitVec 16) (rv : Bool)
    (hReq : ∀ r ∈ C.cellReqs x y pre init true ++ C.rvReq x y pre rv, b r.1 r.2.1 r.2.2.1 = r.2.2.2) :
    cellNext G b Q σ ⟨x, y, pre⟩ =
      mux2 (σ (cellNode x y pre "EN")) (Q ⟨x, y, pre⟩)
        (mux2 (σ (cellNode x y pre "SR"))
          (lut4 init (σ (cellNode x y pre "I0")) (σ (cellNode x y pre "I1")) (σ (cellNode x y pre "I2"))
            (σ (cellNode x y pre "I3"))) rv) := by
  obtain ⟨tm, htm, hl⟩ := Cert.cellOff_some hco
  simp only [cellNext, C.tileOf_grid G hT htm, hl, cellInsAt, lut4c_next, boolBV_ne_zero]
  simp only [Cert.cellReqs, Cert.rvReq, htm, hco, List.mem_append, List.mem_map, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false] at hReq
  have h17 : tm.cellCfg (b x y) co 17 = false := hReq _ (Or.inl (Or.inr (Or.inr rfl)))
  have h18 : tm.cellCfg (b x y) co 18 = rv := hReq _ (Or.inr rfl)
  have hj : ∀ j < 16, tm.cellCfg (b x y) co j = init.getLsbD j := fun j hj => hReq _ (Or.inl (Or.inl ⟨j, hj, rfl⟩))
  simp only [cellLut, h17, h18, Bool.false_eq_true, ite_false, lut4_eq_lut4F]
  rw [lut4F_congr _ _ hj]

/-- **Readback soundness.** A certificate that checks against `N`, on a grid with the certificate's tile
models, wires and pads, under a configuration with the bits it requires: in every consistent assignment
of the wires, the output pins show `N.outputs` and every flop cell of `N` loads `N.step` on the edge. -/
theorem readback_sound (hC : C.check N = true) (hTopo : N.topo = true)
    (hT : ∀ e ∈ C.tiles, G.tile e.1.1 e.1.2 = C.models[e.2]?)
    (hWires : ∀ e ∈ C.wiresUsed, e ∈ G.wires) (hPads : ∀ e ∈ C.pads, e ∈ G.pads)
    (hBits : ∀ r ∈ C.required N, b r.1 r.2.1 r.2.2.1 = r.2.2.2)
    (hσ : Consistent G b pins Q σ) :
    C.observe σ = N.outputs pins (C.q Q) ∧
      ∀ k < N.flops.length, cellNext G b Q σ (C.flopNode k) = N.step pins (C.q Q) k := by
  obtain ⟨hwf, hlg, hlf, hlo, hGs, hFs, hOs⟩ := Cert.check_spec hC
  have hwalk := C.walk_sound G b pins Q σ hσ (fun x y tm h => C.tileOf_grid G hT h)
    (fun x y tm h => C.tileOf_wf hwf h)
  let q := C.q Q
  let v := C.lutVal N σ
  -- a path end is the value of its `Lit`
  have hlit : ∀ l e, C.litEnd l e = true → e.val σ = l.evalF pins q v := by
    intro l e h
    cases l <;> cases e <;> simp only [Cert.litEnd, Bool.false_eq_true] at h
    · simp only [beq_iff_eq] at h; subst h; rfl
    · rename_i k n
      simp only [List.contains_iff_mem] at h
      exact hσ.pad _ (hPads _ h)
    · rename_i k n
      split at h
      · rename_i fc hfc
        simp only [beq_iff_eq] at h
        subst h
        have hkf : k < N.flops.length := by have := (List.getElem?_eq_some_iff.mp hfc).1; omega
        obtain ⟨f, fc', hf, hfc', hok⟩ := hFs k hkf
        rw [hfc] at hfc'; cases hfc'
        simp only [Cert.flopOK, Bool.and_eq_true, decide_eq_true_eq] at hok
        obtain ⟨⟨⟨⟨⟨⟨⟨_, _⟩, hgl⟩, hgc⟩, _⟩, _⟩, _⟩, _⟩ := hok
        split at hgc
        · rename_i gc hgcs
          simp only [Bool.and_eq_true, beq_iff_eq] at hgc
          obtain ⟨⟨⟨hfl, hx⟩, hy⟩, hpre⟩ := hgc
          obtain ⟨g, gc', hg, hgc', hok⟩ := hGs fc.gate hgl
          rw [hgcs] at hgc'; cases hgc'
          simp only [Cert.gateOK, Bool.and_eq_true, Option.isSome_iff_exists] at hok
          obtain ⟨⟨co, hco⟩, _⟩ := hok
          have := cell_O_val C G b pins Q σ hσ hT hco g.init gc.isFlop (Cert.req_gate hg hgcs |>.1 · · |> hBits _)
          simp only [hfl, ite_true] at this
          rw [hx, hy, hpre] at this
          simp only [End.val, this, Lit.evalF, q, Cert.q, Cert.flopNode, hfc,
            show k < C.flops.length by omega, ite_true]
        · simp at hgc
      · simp at h
    · rename_i k n
      split at h
      · rename_i gc hgc
        simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at h
        obtain ⟨hnf, rfl⟩ := h
        obtain ⟨g, gc', hg, hgc', hok⟩ := hGs k (by have := (List.getElem?_eq_some_iff.mp hgc).1; omega)
        rw [hgc] at hgc'; cases hgc'
        simp only [Cert.gateOK, Bool.and_eq_true, Option.isSome_iff_exists] at hok
        obtain ⟨⟨co, hco⟩, _⟩ := hok
        have := cell_O_val C G b pins Q σ hσ hT hco g.init gc.isFlop (Cert.req_gate hg hgc |>.1 · · |> hBits _)
        simp only [hnf, Bool.false_eq_true, ite_false] at this
        simp only [End.val, this, Lit.evalF, v, Cert.lutVal, hg, hgc]
      · simp at h
  -- every input of every gate
  have hgate : ∀ k (hk : k < N.gates.length), v k = lut4 (N.gates[k]).init ((N.gates[k]).i0.evalF pins q v)
      ((N.gates[k]).i1.evalF pins q v) ((N.gates[k]).i2.evalF pins q v) ((N.gates[k]).i3.evalF pins q v) := by
    intro k hk
    obtain ⟨g, gc, hg, hgc, hok⟩ := hGs k hk
    have hgk : N.gates[k] = g := by rw [List.getElem?_eq_some_iff] at hg; exact hg.2
    rw [hgk]
    have hgcm : gc ∈ C.gates := List.mem_of_getElem? hgc
    have hreq := (Cert.req_gate hg hgc).2
    have hwir := Cert.wires_gate hgcm
    simp only [Cert.gateOK, Bool.and_eq_true] at hok
    obtain ⟨_, hins⟩ := hok
    split at hins
    · rename_i p0 p1 p2 p3 hgi
      simp only [Bool.and_eq_true] at hins
      obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := hins
      have hin : ∀ (i : Nat) (port : String) (l : Lit) (pp : Option (List Hop)), i < 4 → port = portName i →
          gc.ins.getD i none = pp → C.inOK gc g.init i port l pp = true →
          σ (cellNode gc.x gc.y gc.pre port) = l.evalF pins q v ∨
            (l.evalF pins q v = false ∧ ignores g.init i = true) := by
        intro i port l pp hi hport hpp hok
        cases pp with
        | none =>
          simp only [Cert.inOK, Bool.and_eq_true, beq_iff_eq] at hok
          obtain ⟨rfl, hig⟩ := hok
          exact Or.inr ⟨rfl, hig⟩
        | some hs =>
          simp only [Cert.inOK] at hok
          obtain ⟨e, W, B, hw, hle, hW, hB⟩ := Cert.walk_of_pathOK hok
          left
          rw [hwalk hs _ e W B hw (fun w hw' => hWires _ (hwir i hi w (by
              rw [hpp, ← hport]; simp only [Cert.inWires]; rw [hW]; exact hw')))
            (fun r hr => hBits _ (hreq i hi r (by rw [hpp, ← hport]; simp only [Cert.inReqs]; rw [hB]; exact hr))),
            hlit l e hle]
      simp only [v, Cert.lutVal, hg, hgc]
      apply lut4_args
      · exact hin 0 "I0" _ p0 (by decide) rfl (by simp [hgi]) h0
      · exact hin 1 "I1" _ p1 (by decide) rfl (by simp [hgi]) h1
      · exact hin 2 "I2" _ p2 (by decide) rfl (by simp [hgi]) h2
      · exact hin 3 "I3" _ p3 (by decide) rfl (by simp [hgi]) h3
    · simp at hins
  have hHold : gatesHold pins q v N.gates 0 :=
    gatesHold_of pins q v N.gates 0 (fun j hj => by rw [Nat.zero_add]; exact hgate j hj)
  have hvals : ∀ j < N.gates.length, v j = (N.gateVals pins q).getD j false := fun j hj =>
    gatesHold_unique pins q v _ N.gates 0 hTopo hHold (N.gatesHold_gateVals hTopo pins q) (fun _ h => absurd h (by omega))
      j (by omega)
  have hsize : (N.gateVals pins q).size = N.gates.length := by
    simp [Net.gateVals, evalGates_size]
  have hlitV : ∀ l : Lit, l.below N.gates.length = true → l.evalF pins q v = l.eval pins q (N.gateVals pins q) := by
    intro l hb
    rw [Lit.eval_eq_evalF pins q _ (fun i => (N.gateVals pins q).getD i false) l (by rwa [hsize]) (fun _ _ => rfl)]
    exact Lit.evalF_congr pins q _ _ _ l hb hvals
  refine ⟨?_, fun k hk => ?_⟩
  · -- the output pins
    apply List.ext_getElem (by simp [Cert.observe, Net.outputs, hlo])
    intro k h1 h2
    have hk : k < N.outs.length := by simpa [Net.outputs] using h2
    obtain ⟨p, l, n, hs, ho, hco, hb, hp⟩ := hOs k hk
    obtain ⟨e, W, B, hw, hle, hW, hB⟩ := Cert.walk_of_pathOK hp
    have hcm : (p, n, hs) ∈ C.outs := List.mem_of_getElem? hco
    have hσn := hwalk hs n e W B hw (fun w hw' => hWires _ (Cert.wires_out hcm w (by rw [hW]; exact hw')))
      (fun r hr => hBits _ (Cert.req_out (N := N) hcm r (by rw [hB]; exact hr)))
    rw [List.getElem?_eq_some_iff] at ho hco
    obtain ⟨_, ho⟩ := ho
    obtain ⟨_, hco⟩ := hco
    simp only [Cert.observe, Net.outputs, List.getElem_map, ho, hco, hσn, hlit l e hle, hlitV l hb]
    rfl
  · -- the flops
    obtain ⟨f, fc, hf, hfc, hok⟩ := hFs k hk
    have hfcm : fc ∈ C.flops := List.mem_of_getElem? hfc
    have hreq := Cert.req_flop hf hfc
    have hwir := Cert.wires_flop hfcm
    simp only [Cert.flopOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hok
    obtain ⟨⟨⟨⟨⟨⟨⟨hcoS, hd⟩, hgl⟩, hgc⟩, hben⟩, hbsr⟩, hpen⟩, hpsr⟩ := hok
    split at hgc
    · rename_i gc hgcs
      simp only [Bool.and_eq_true, beq_iff_eq] at hgc
      obtain ⟨⟨⟨hfl, hx⟩, hy⟩, hpre⟩ := hgc
      obtain ⟨g, gc', hg, hgc', _⟩ := hGs fc.gate hgl
      rw [hgcs] at hgc'; cases hgc'
      obtain ⟨co, hco⟩ := Option.isSome_iff_exists.mp hcoS
      have hcr := (Cert.req_gate hg hgcs).1
      rw [hfl, hx, hy, hpre] at hcr
      obtain ⟨e1, W1, B1, hw1, hle1, hW1, hB1⟩ := Cert.walk_of_pathOK hpen
      obtain ⟨e2, W2, B2, hw2, hle2, hW2, hB2⟩ := Cert.walk_of_pathOK hpsr
      have hen := hwalk fc.en _ e1 W1 B1 hw1
        (fun w hw' => hWires _ (hwir w (List.mem_append_left _ (by rw [hW1]; exact hw'))))
        (fun r hr => hBits _ (hreq r (List.mem_append_left _ (List.mem_append_right _ (by rw [hB1]; exact hr)))))
      have hsr := hwalk fc.sr _ e2 W2 B2 hw2
        (fun w hw' => hWires _ (hwir w (List.mem_append_right _ (by rw [hW2]; exact hw'))))
        (fun r hr => hBits _ (hreq r (List.mem_append_right _ (by rw [hB2]; exact hr))))
      have hnext := cell_next_val C G b Q σ hT hco g.init f.rv (fun r hr => by
        rcases List.mem_append.mp hr with hr | hr
        · exact hBits _ (hcr r hr)
        · exact hBits _ (hreq r (List.mem_append_left _ (List.mem_append_left _ hr))))
      have hnode : C.flopNode k = ⟨fc.x, fc.y, fc.pre⟩ := by simp [Cert.flopNode, hfc]
      have hqk : q k = Q ⟨fc.x, fc.y, fc.pre⟩ := by
        simp [q, Cert.q, show k < C.flops.length by omega, hnode]
      have hdv : f.d.eval pins q (N.gateVals pins q) = v fc.gate := by
        rw [hd, ← hlitV (.gate fc.gate) (by simpa [Lit.below] using hgl)]; rfl
      have hvg : v fc.gate = lut4 g.init (σ (cellNode fc.x fc.y fc.pre "I0")) (σ (cellNode fc.x fc.y fc.pre "I1"))
          (σ (cellNode fc.x fc.y fc.pre "I2")) (σ (cellNode fc.x fc.y fc.pre "I3")) := by
        simp only [v, Cert.lutVal, hg, hgcs, hx, hy, hpre]
      rw [hnode, hnext]
      simp only [Net.step, hf, Flop.next]
      rw [← hlitV f.en hben, ← hlitV f.sr hbsr, ← hlit f.en e1 hle1, ← hlit f.sr e2 hle2, ← hen, ← hsr, hdv, hvg]
      exact congrArg (fun z => mux2 _ z _) hqk.symm
    · simp at hgc

end Sound

/-! ## Every cycle of a run -/

/-- A run of the configured fabric: each cycle's wire values are consistent with that cycle's pins and
flop state, and the next cycle's flop state is every cell's flop after the edge. -/
def FabricRun (G : Grid) (b : Bits) : (Node → Bool) → List ((Nat → Bool) × (Node → Bool)) → Prop
  | _, [] => True
  | Q, (pins, σ) :: rest => Consistent G b pins Q σ ∧ FabricRun G b (cellNext G b Q σ) rest

/-- **The fabric's run is the `Net`'s run.** On every cycle the output pins show what `Net.run` gives
from the flop state the cells hold. -/
theorem fabric_run_eq (C : Cert) (N : Net) (G : Grid) (b : Bits) (hC : C.check N = true) (hTopo : N.topo = true)
    (hT : ∀ e ∈ C.tiles, G.tile e.1.1 e.1.2 = C.models[e.2]?)
    (hWires : ∀ e ∈ C.wiresUsed, e ∈ G.wires) (hPads : ∀ e ∈ C.pads, e ∈ G.pads)
    (hBits : ∀ r ∈ C.required N, b r.1 r.2.1 r.2.2.1 = r.2.2.2) :
    ∀ (cyc : List ((Nat → Bool) × (Node → Bool))) (Q : Node → Bool), FabricRun G b Q cyc →
      cyc.map (fun c => C.observe c.2) = (N.run (C.q Q) (cyc.map (·.1))).1
  | [], _, _ => rfl
  | (pins, σ) :: rest, Q, ⟨hσ, hRest⟩ => by
    obtain ⟨hObs, hStep⟩ := readback_sound C N G b pins Q σ hC hTopo hT hWires hPads hBits hσ
    have hlf := (Cert.check_spec hC).2.2.1
    have hq : C.q (cellNext G b Q σ) = N.step pins (C.q Q) := by
      funext k
      by_cases hk : k < C.flops.length
      · simp only [Cert.q, hk, ite_true]; exact hStep k (by omega)
      · have : N.flops[k]? = none := List.getElem?_eq_none (by omega)
        simp [Cert.q, hk, Net.step, this]
    simp only [List.map_cons, Net.run]
    rw [hObs, ← hq, fabric_run_eq C N G b hC hTopo hT hWires hPads hBits rest _ hRest]

end Obend.Hardware.Fabulous
