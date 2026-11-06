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

The extraction (`Obend.Hardware.Fabulous.Bitstream.extractS`) emits a certificate (`Cert`): a table with one
entry per wire it followed (chunked by tile, no wire twice), the hop that drives it (`Hop.sm k i`: output
`k` of the tile's switch matrix configured to select input `i`; `Hop.wire`) and the entry of the wire it
reads, with a rank that decreases along every hop, so the table is acyclic; gates, flops and output pins
index it. Its equations are the cone's semantics (`ConeConsistent`), implied by the whole grid's
(`Consistent.cone`). `Cert.check` is the structural part, kernel-decided piece by piece (`Cert.check_of`);
`Cert.required` lists the configuration bits it rests on. `cone_sound`: in every cone assignment the output
pins show `Net.outputs` and every flop loads `Net.step`. `consistent_exists_unique`: for every pin input
and flop state the cone has exactly one assignment (`Cert.solve`), so routing loops outside the cone do not
make the theorems vacuous. `cone_run_eq` lifts it to every cycle, and `Cert.runFrom_run` gives the run.

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

/-! ## The certificate: the cone the extraction covers, as a table of drivers

Every wire the extraction followed appears once (`Cert.entries`, strictly sorted by `Node.lt`, so no wire
has two entries) with the hop that drives it and the entry of the wire it reads (`next`), or none when
that is a terminal: a LUT4 cell's `O`, an input pad, or a multiplexer's constant. `rank` strictly
decreases along `next`, so the table is acyclic. Gates, flops and output pins point into the table. -/

structure Entry where
  node : Node
  rank : Nat
  hop : Hop
  next : Option Nat
  deriving DecidableEq, Repr, Inhabited

/-- A gate's cell and the entries of its four inputs (`none`: the truth table ignores that input). -/
structure GateCert where
  x : Nat
  y : Nat
  pre : String
  isFlop : Bool
  ins : List (Option Nat)
  deriving DecidableEq, Repr, Inhabited

/-- A flop's cell, its gate (the same cell's LUT), and the entries of its `EN` and `SR`. -/
structure FlopCert where
  x : Nat
  y : Nat
  pre : String
  gate : Nat
  en : Nat
  sr : Nat
  deriving DecidableEq, Repr, Inhabited

structure Cert where
  /-- the tile models used -/
  models : List TileModel
  /-- `((x, y), model index)` for every tile an entry or cell is in -/
  tiles : List ((Nat × Nat) × Nat)
  /-- the table, one chunk per tile `((x, y), the entries of wires in that tile)`, keys strictly increasing -/
  chunks : List ((Nat × Nat) × List Entry)
  gates : List GateCert
  flops : List FlopCert
  /-- each output pin: its pin index, the node it shows, and that node's entry -/
  outs : List (Nat × Node × Nat)
  /-- the input pads -/
  pads : List (Nat × Node)
  deriving DecidableEq, Repr, Inhabited

def Cert.tileOf (C : Cert) (x y : Nat) : Option TileModel :=
  match C.tiles.find? (fun e => e.1.1 == x && e.1.2 == y) with
  | some e => C.models[e.2]?
  | none => none

/-- Where a cell's configuration bits start. -/
def Cert.cellOff (C : Cert) (x y : Nat) (pre : String) : Option Nat :=
  match C.tileOf x y with
  | some tm => tm.cells.lookup pre
  | none => none

/-- The table: every chunk's entries, in order; `next` indexes into it. -/
def Cert.entries (C : Cert) : List Entry := C.chunks.flatMap (·.2)

/-- Tile keys in strict order (column, then row). -/
def keyLt (a b : Nat × Nat) : Bool := a.1 < b.1 || (a.1 == b.1 && a.2 < b.2)

def chunksSorted : List ((Nat × Nat) × List Entry) → Bool
  | a :: b :: rest => keyLt a.1 b.1 && chunksSorted (b :: rest)
  | _ => true

/-- No two of the listed names are equal. -/
def distinctNames : List String → Bool
  | [] => true
  | n :: ns => !ns.contains n && distinctNames ns

/-- The node or constant an entry's hop reads. -/
def Cert.target (C : Cert) (e : Entry) : Option End :=
  match e.hop with
  | .wire s => some (.node s)
  | .sm k i =>
    match C.tileOf e.node.x e.node.y with
    | none => none
    | some tm =>
      match tm.sm.prims[k]? with
      | none => none
      | some (o, p) =>
        if o = e.node.w then
          match p.ins[i]? with
          | some (.port m) => some (.node ⟨e.node.x, e.node.y, m⟩)
          | some (.const c) => some (.const c)
          | none => none
        else none

/-- The terminals the cone ends at: the gates' cells' `O`, and the input pads. -/
def Cert.knownTerm (C : Cert) (m : Node) : Bool :=
  C.gates.any (fun gc => cellNode gc.x gc.y gc.pre "O" == m) || C.pads.any (·.2 == m)

def Cert.entryOK (C : Cert) (e : Entry) : Bool :=
  !C.knownTerm e.node && e.rank < C.entries.length &&
  match C.target e with
  | some (.const _) => e.next == none
  | some (.node m) =>
    match e.next with
    | some j' =>
      match C.entries[j']? with
      | some e' => e'.node == m && e'.rank < e.rank
      | none => false
    | none => C.knownTerm m
  | none => false

/-- Follow the table from entry `j` to its end. -/
def Cert.follow (C : Cert) : Nat → Nat → Option End
  | 0, _ => none
  | f + 1, j =>
    match C.entries[j]? with
    | none => none
    | some e =>
      match C.target e, e.next with
      | some (.const c), _ => some (.const c)
      | some (.node _), some j' => C.follow f j'
      | some (.node m), none => some (.node m)
      | none, _ => none

def Cert.endOf (C : Cert) (j : Nat) : Option End := C.follow C.entries.length j

/-- The `Lit` a cone end stands for. -/
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

/-- Entry `j` is wire `n`, and the cone from it ends where `l` says. -/
def Cert.startOK (C : Cert) (j : Nat) (n : Node) (l : Lit) : Bool :=
  (C.entries[j]?.map (·.node)) == some n &&
  match C.endOf j with
  | some e => C.litEnd l e
  | none => false

def Cert.inOK (C : Cert) (gc : GateCert) (init : BitVec 16) (i : Nat) (port : String) (l : Lit) :
    Option Nat → Bool
  | some j => C.startOK j (cellNode gc.x gc.y gc.pre port) l
  | none => l == .const false && ignores init i

def Cert.gateOK (C : Cert) (g : Gate) (gc : GateCert) : Bool :=
  (C.cellOff gc.x gc.y gc.pre).isSome &&
  match gc.ins with
  | [p0, p1, p2, p3] =>
    C.inOK gc g.init 0 "I0" g.i0 p0 && C.inOK gc g.init 1 "I1" g.i1 p1 && C.inOK gc g.init 2 "I2" g.i2 p2 &&
      C.inOK gc g.init 3 "I3" g.i3 p3
  | _ => false

def Cert.flopOK (C : Cert) (nG : Nat) (f : Flop) (fc : FlopCert) : Bool :=
  f.d == .gate fc.gate && fc.gate < nG &&
  (match C.gates[fc.gate]? with
    | some g => g.isFlop && g.x == fc.x && g.y == fc.y && g.pre == fc.pre
    | none => false) &&
  f.en.below nG && f.sr.below nG &&
  C.startOK fc.en (cellNode fc.x fc.y fc.pre "EN") f.en && C.startOK fc.sr (cellNode fc.x fc.y fc.pre "SR") f.sr

/-- No two of the listed wires are equal. -/
def distinctNodes : List Node → Bool
  | [] => true
  | n :: ns => !ns.contains n && distinctNodes ns

/-- A chunk: every entry in its tile, no two with the same name, each well formed. -/
def Cert.chunkOK (C : Cert) (ch : (Nat × Nat) × List Entry) : Bool :=
  ch.2.all (fun e => e.node.x == ch.1.1 && e.node.y == ch.1.2) && distinctNames (ch.2.map (·.node.w)) &&
    ch.2.all C.entryOK

def Cert.gateAt (C : Cert) (N : Net) (k : Nat) : Bool :=
  match N.gates[k]?, C.gates[k]? with
  | some g, some gc => C.gateOK g gc
  | _, _ => false

def Cert.flopAt (C : Cert) (N : Net) (k : Nat) : Bool :=
  match N.flops[k]?, C.flops[k]? with
  | some f, some fc => C.flopOK N.gates.length f fc
  | _, _ => false

def Cert.outAt (C : Cert) (N : Net) (k : Nat) : Bool :=
  match N.outs[k]?, C.outs[k]? with
  | some (p, l), some (p', n, j) => p == p' && l.below N.gates.length && C.startOK j n l
  | _, _ => false

/-- **The structural check**, decided by the kernel for a concrete certificate piece by piece
(`Cert.check_of`): one chunk, or one block of gates, flops or outputs, at a time. -/
def Cert.check (C : Cert) (N : Net) : Bool :=
  C.models.all (·.sm.wf) && N.gates.length == C.gates.length && N.flops.length == C.flops.length &&
  N.outs.length == C.outs.length && chunksSorted C.chunks && C.chunks.all C.chunkOK &&
  distinctNodes (C.gates.map (fun gc => cellNode gc.x gc.y gc.pre "O") ++ C.pads.map (·.2)) &&
  (List.range N.gates.length).all (C.gateAt N) && (List.range N.flops.length).all (C.flopAt N) &&
  (List.range N.outs.length).all (C.outAt N)

/-- A cell's configuration bits: the truth table, `FF`, `I0mux` off. -/
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

/-- The select bits a switch-matrix entry reads. -/
def Cert.entryReqs (C : Cert) (e : Entry) : List BitReq :=
  match e.hop with
  | .wire _ => []
  | .sm k i =>
    match C.tileOf e.node.x e.node.y with
    | none => []
    | some tm =>
      match tm.sm.prims[k]? with
      | none => []
      | some (_, p) => (List.range p.selBits).map fun c =>
          (e.node.x, e.node.y, tm.pos.getD (tm.smOff + (p.base + c)) 0, i.testBit c)

/-- **The configuration bits the certificate rests on.** -/
def Cert.required (C : Cert) (N : Net) : List BitReq :=
  C.entries.flatMap C.entryReqs ++
  (List.range N.gates.length).flatMap (fun k =>
    match N.gates[k]?, C.gates[k]? with
    | some g, some gc => C.cellReqs gc.x gc.y gc.pre g.init gc.isFlop
    | _, _ => []) ++
  (List.range N.flops.length).flatMap (fun k =>
    match N.flops[k]?, C.flops[k]? with
    | some f, some fc => C.rvReq fc.x fc.y fc.pre f.rv
    | _, _ => [])

/-- **The fabric wires the certificate rests on.** -/
def Cert.wiresUsed (C : Cert) : List (Node × Node) :=
  C.entries.filterMap fun e => match e.hop with
    | .wire s => some (s, e.node)
    | .sm .. => none

/-- Net flop `k`'s cell, and the flop state the `Net` sees. -/
def Cert.flopNode (C : Cert) (k : Nat) : Node :=
  match C.flops[k]? with
  | some f => ⟨f.x, f.y, f.pre⟩
  | none => default

def Cert.q (C : Cert) (Q : Node → Bool) (k : Nat) : Bool := if k < C.flops.length then Q (C.flopNode k) else false

/-- What the output pins show. -/
def Cert.observe (C : Cert) (σ : Node → Bool) : List (Nat × Bool) := C.outs.map fun (p, n, _) => (p, σ n)

/-- The wires of the cone: every entry, every gate's cell output, every input pad. -/
def Cert.coneNodes (C : Cert) : List Node :=
  C.entries.map (·.node) ++ C.gates.map (fun gc => cellNode gc.x gc.y gc.pre "O") ++ C.pads.map (·.2)

/-! ## The cone semantics -/

/-- **The cone's semantics**: the grid equations of the wires the certificate covers. Every switch-matrix
entry is what `smModule` computes, every wire entry carries its source, every gate's cell's `O` is what
`lut4cModule` computes, every input pad carries its pin. -/
structure ConeConsistent (C : Cert) (b : Bits) (pins : Nat → Bool) (Q σ : Node → Bool) : Prop where
  sm : ∀ e ∈ C.entries, ∀ (k i : Nat), e.hop = .sm k i → ∀ tm, C.tileOf e.node.x e.node.y = some tm →
    ∀ (o : String) (p : SmPrim), tm.sm.prims[k]? = some (o, p) →
    (evalModuleOutputsW (smModule tm.sm) (smIns tm.sm (tm.smCfg (b e.node.x e.node.y))
      (fun n => σ ⟨e.node.x, e.node.y, n⟩)) (fun _ => 0#64))[k]? = some (o, boolBV (σ ⟨e.node.x, e.node.y, o⟩))
  wire : ∀ e ∈ C.entries, ∀ s, e.hop = .wire s → σ e.node = σ s
  cell : ∀ gc ∈ C.gates, ∀ tm co, C.tileOf gc.x gc.y = some tm → tm.cells.lookup gc.pre = some co →
    (evalModuleOutputsW lut4cModule (cellInsAt tm (b gc.x gc.y) σ gc.x gc.y gc.pre co)
      (fun _ => boolBV (Q ⟨gc.x, gc.y, gc.pre⟩)))[0]? = some ("O", boolBV (σ (cellNode gc.x gc.y gc.pre "O")))
  pad : ∀ e ∈ C.pads, σ e.2 = pins e.1

/-- A cone cell's flop after the clock edge, through `lut4cModule`'s register; other state holds. -/
def Cert.cellNext (C : Cert) (b : Bits) (Q σ : Node → Bool) (n : Node) : Bool :=
  match C.tileOf n.x n.y with
  | some tm =>
    match tm.cells.lookup n.w with
    | some co => stepModuleRegs lut4cModule false (cellInsAt tm (b n.x n.y) σ n.x n.y n.w co) (fun _ => boolBV (Q n)) 0 != 0#64
    | none => Q n
  | none => Q n

/-! ## Lemmas -/

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


/-! ## The table: one entry per wire, followed to its end -/

theorem keyLt_trans {a b c : Nat × Nat} (h1 : keyLt a b = true) (h2 : keyLt b c = true) : keyLt a c = true := by
  simp only [keyLt, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq] at h1 h2 ⊢
  omega

theorem chunksSorted_pairwise : ∀ cs : List ((Nat × Nat) × List Entry), chunksSorted cs = true →
    cs.Pairwise (fun a b => keyLt a.1 b.1)
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: rest, h => by
    simp only [chunksSorted, Bool.and_eq_true] at h
    have ih := chunksSorted_pairwise (b :: rest) h.2
    refine List.Pairwise.cons (fun c hc => ?_) ih
    rcases List.mem_cons.mp hc with rfl | hc
    · exact h.1
    · exact keyLt_trans h.1 (List.rel_of_pairwise_cons ih hc)

theorem distinctNames_pairwise : ∀ l : List String, distinctNames l = true → l.Pairwise (· ≠ ·)
  | [], _ => List.Pairwise.nil
  | n :: ns, h => by
    simp only [distinctNames, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_any_beq, List.any_eq_false,
      beq_iff_eq] at h
    exact List.Pairwise.cons (fun m hm heq => h.1 m hm heq) (distinctNames_pairwise ns h.2)

/-- Chunked by tile, with names distinct within a tile, no two entries share a wire. -/
theorem Cert.entries_distinct {C : Cert} (hS : chunksSorted C.chunks = true) (hC : C.chunks.all C.chunkOK = true) :
    C.entries.Pairwise (fun a b => a.node ≠ b.node) := by
  unfold Cert.entries
  have hP := chunksSorted_pairwise _ hS
  have hOK := List.all_eq_true.mp hC
  clear hS hC
  generalize C.chunks = cs at hP hOK ⊢
  induction cs with
  | nil => exact List.Pairwise.nil
  | cons ch rest ih =>
    obtain ⟨hk, hr⟩ := List.pairwise_cons.mp hP
    have hch := hOK ch (List.mem_cons_self ..)
    simp only [Cert.chunkOK, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hch
    obtain ⟨⟨htile, hnames⟩, _⟩ := hch
    simp only [List.flatMap_cons]
    refine List.pairwise_append.mpr ⟨?_, ih hr (fun c hc => hOK c (List.mem_cons_of_mem _ hc)), ?_⟩
    · have := List.pairwise_map.mp (distinctNames_pairwise _ hnames)
      exact this.imp (fun h heq => h (by rw [heq]))
    · intro a ha b hb heq
      obtain ⟨c, hc, hbc⟩ := List.mem_flatMap.mp hb
      have hcc := hOK c (List.mem_cons_of_mem _ hc)
      simp only [Cert.chunkOK, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hcc
      have hb' := hcc.1.1 b hbc
      have ha' := htile a ha
      have hlt := hk c hc
      rw [heq] at ha'
      simp only [keyLt, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq] at hlt
      omega

/-- In a sorted table, an entry's wire finds that entry. -/
theorem Cert.findIdx_entry {C : Cert} (hS : C.entries.Pairwise (fun a b => a.node ≠ b.node)) {j : Nat} {e : Entry}
    (h : C.entries[j]? = some e) : C.entries.findIdx? (·.node == e.node) = some j := by
  have hP := List.pairwise_iff_getElem.mp hS
  obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.mp h
  rw [List.findIdx?_eq_some_iff_getElem]
  refine ⟨hj, by simp, fun i hi heq => ?_⟩
  simp only [beq_iff_eq] at heq
  exact hP i j (by omega) hj hi heq

theorem Cert.entryOK_spec {C : Cert} {e : Entry} (h : C.entryOK e = true) :
    C.knownTerm e.node = false ∧ e.rank < C.entries.length ∧
    ((∃ c, C.target e = some (.const c) ∧ e.next = none) ∨
     (∃ m j' e', C.target e = some (.node m) ∧ e.next = some j' ∧ C.entries[j']? = some e' ∧ e'.node = m ∧
        e'.rank < e.rank) ∨
     (∃ m, C.target e = some (.node m) ∧ e.next = none ∧ C.knownTerm m = true)) := by
  simp only [Cert.entryOK, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h
  obtain ⟨⟨ht, hr⟩, h⟩ := h
  refine ⟨ht, hr, ?_⟩
  split at h
  · rename_i c hc; simp only [beq_iff_eq] at h; exact Or.inl ⟨c, hc, h⟩
  · rename_i m hm
    split at h
    · rename_i j' hn
      split at h
      · rename_i e' he'
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
        exact Or.inr (Or.inl ⟨m, j', e', hm, hn, he', h.1, h.2⟩)
      · simp at h
    · rename_i hn
      exact Or.inr (Or.inr ⟨m, hm, hn, h⟩)
  · simp at h

theorem Cert.follow_mono (C : Cert) : ∀ f j r, C.follow f j = some r → C.follow (f + 1) j = some r
  | 0, _, _, h => by simp [Cert.follow] at h
  | f + 1, j, r, h => by
    unfold Cert.follow at h ⊢
    split at h
    · simp at h
    · rename_i e he
      cases ht : C.target e with
      | none => simp [ht] at h
      | some t =>
        cases t <;> cases hn : e.next <;> simp only [ht, hn] at h ⊢
        all_goals first | exact h | exact C.follow_mono f _ r h

theorem Cert.follow_mono' (C : Cert) {f f' j : Nat} {r : End} (h : C.follow f j = some r) (hf : f ≤ f') :
    C.follow f' j = some r := by
  induction hf with
  | refl => exact h
  | step _ ih => exact C.follow_mono _ _ _ ih

theorem Cert.follow_some (C : Cert) (hOK : C.entries.all C.entryOK = true) :
    ∀ f j e, C.entries[j]? = some e → e.rank < f → ∃ r, C.follow f j = some r
  | 0, _, _, _, h => absurd h (by omega)
  | f + 1, j, e, he, hr => by
    have hok := (Cert.entryOK_spec (List.all_eq_true.mp hOK e (List.mem_of_getElem? he))).2.2
    simp only [Cert.follow, he]
    rcases hok with ⟨c, ht, hn⟩ | ⟨m, j', e', ht, hn, he', _, hlt⟩ | ⟨m, ht, hn, _⟩
    · simp only [ht, hn]; exact ⟨_, rfl⟩
    · simp only [ht, hn]; exact C.follow_some hOK f j' e' he' (by omega)
    · simp only [ht, hn]; exact ⟨_, rfl⟩

/-- Along `next`, the table's end does not change. -/
theorem Cert.endOf_next (C : Cert) (hOK : C.entries.all C.entryOK = true) {j j' : Nat} {e e' : Entry} {m : Node}
    (he : C.entries[j]? = some e) (ht : C.target e = some (.node m)) (hn : e.next = some j')
    (he' : C.entries[j']? = some e') (hlt : e'.rank < e.rank) (hr : e.rank < C.entries.length) :
    C.endOf j = C.endOf j' := by
  obtain ⟨r, hfr⟩ := C.follow_some hOK (C.entries.length - 1) j' e' he' (by omega)
  have h1 : C.endOf j = C.follow (C.entries.length - 1) j' := by
    unfold Cert.endOf
    rw [show C.entries.length = (C.entries.length - 1) + 1 by omega]
    simp only [Cert.follow, he, ht, hn]
    rw [show C.entries.length - 1 + 1 - 1 = C.entries.length - 1 by omega]
  rw [h1, hfr]
  exact (C.follow_mono' hfr (by omega)).symm

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

/-- What an entry's target is, unfolded. -/
theorem Cert.target_cases {C : Cert} {e : Entry} {t : End} (h : C.target e = some t) :
    (∃ s, e.hop = .wire s ∧ t = .node s) ∨
    (∃ k i tm o p src, e.hop = .sm k i ∧ C.tileOf e.node.x e.node.y = some tm ∧ tm.sm.prims[k]? = some (o, p) ∧
      o = e.node.w ∧ p.ins[i]? = some src ∧
      t = (match src with | .port m => .node ⟨e.node.x, e.node.y, m⟩ | .const c => .const c)) := by
  unfold Cert.target at h
  split at h
  · rename_i s hh; simp only [Option.some.injEq] at h; exact Or.inl ⟨s, hh, h.symm⟩
  · rename_i k i hh
    split at h
    · simp at h
    rename_i tm htm
    split at h
    · simp at h
    rename_i o p hk
    split at h
    · rename_i ho
      split at h
      · rename_i m hs; simp only [Option.some.injEq] at h
        exact Or.inr ⟨k, i, tm, o, p, .port m, hh, htm, hk, ho, hs, h.symm⟩
      · rename_i c hs; simp only [Option.some.injEq] at h
        exact Or.inr ⟨k, i, tm, o, p, .const c, hh, htm, hk, ho, hs, h.symm⟩
      · simp at h
    · simp at h

section Cone

variable {C : Cert} {b : Bits} {pins : Nat → Bool} {Q σ : Node → Bool}

/-- An entry's wire carries what its hop reads (through `smModule_eval_eq_SmPrim_eval` for a
switch-matrix entry, with the select its configuration bits set). -/
theorem Cert.target_val (hσ : ConeConsistent C b pins Q σ) (hW : C.models.all (·.sm.wf) = true)
    {e : Entry} (hm : e ∈ C.entries) (hB : ∀ r ∈ C.entryReqs e, b r.1 r.2.1 r.2.2.1 = r.2.2.2)
    {t : End} (ht : C.target e = some t) : σ e.node = t.val σ := by
  rcases Cert.target_cases ht with ⟨s, hh, rfl⟩ | ⟨k, i, tm, o, p, src, hh, htm, hk, ho, hs, rfl⟩
  · exact hσ.wire e hm s hh
  · have hn : e.node = ⟨e.node.x, e.node.y, o⟩ := by rw [ho]
    have hwf := C.tileOf_wf hW htm
    have h := hσ.sm e hm k i hh tm htm o p hk
    rw [smModule_eval_eq_SmPrim_eval tm.sm hwf _ _ _ _ (smIns_encodes _ _ _), List.getElem?_map, hk] at h
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, true_and] at h
    rw [hn, ← boolBV_inj h]
    have hp := List.all_eq_true.mp hwf (o, p) (List.mem_of_getElem? hk)
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq] at hp
    have hi : i < p.ins.length := (List.getElem?_eq_some_iff.mp hs).1
    have hsel : p.sel (tm.smCfg (b e.node.x e.node.y)) = i := by
      rw [SmPrim.sel_eq_selFrom]
      refine selFrom_testBit _ _ _ 0 i (fun c hc => ?_) ?_
      · have := hB (e.node.x, e.node.y, tm.pos.getD (tm.smOff + (p.base + c)) 0, i.testBit c) (by
          simp only [Cert.entryReqs, hh, htm, hk]
          exact List.mem_map.mpr ⟨c, List.mem_range.mpr hc, rfl⟩)
        simpa [TileModel.smCfg, TileModel.bit] using this
      · rcases hp.1.1 with h0 | h1
        · have := SmPrim.ins_length_of_selBits_zero p h0; rw [h0]; omega
        · omega
    rw [SmPrim.eval, hsel, hs]
    cases src <;> rfl

/-- **Following the table.** In any assignment of the cone, an entry's wire carries its end's value. -/
theorem Cert.follow_sound (hσ : ConeConsistent C b pins Q σ) (hW : C.models.all (·.sm.wf) = true)
    (hOK : C.entries.all C.entryOK = true)
    (hB : ∀ e ∈ C.entries, ∀ r ∈ C.entryReqs e, b r.1 r.2.1 r.2.2.1 = r.2.2.2) :
    ∀ f j r e, C.follow f j = some r → C.entries[j]? = some e → σ e.node = r.val σ
  | 0, _, _, _, h, _ => by simp [Cert.follow] at h
  | f + 1, j, r, e, h, he => by
    have hm := List.mem_of_getElem? he
    simp only [Cert.follow, he] at h
    cases ht : C.target e with
    | none => simp [ht] at h
    | some t =>
      rw [C.target_val hσ hW hm (hB e hm) ht]
      cases t with
      | const c => simp only [ht, Option.some.injEq] at h; rw [← h]
      | node m =>
        cases hn : e.next with
        | none => simp only [ht, hn, Option.some.injEq] at h; rw [← h]
        | some j' =>
          simp only [ht, hn] at h
          rcases (Cert.entryOK_spec (List.all_eq_true.mp hOK e hm)).2.2 with
            ⟨c, ht', _⟩ | ⟨m', j'', e', ht', hn', he', hnode, _⟩ | ⟨m', ht', hn', _⟩
          · rw [ht] at ht'; cases ht'
          · rw [hn] at hn'; cases hn'
            rw [ht] at ht'; cases ht'
            rw [← hnode]
            exact Cert.follow_sound hσ hW hOK hB f j' r e' h he'
          · rw [hn] at hn'; cases hn'

end Cone

theorem Cert.check_spec {C : Cert} {N : Net} (h : C.check N = true) :
    C.models.all (·.sm.wf) = true ∧ N.gates.length = C.gates.length ∧ N.flops.length = C.flops.length ∧
    N.outs.length = C.outs.length ∧ C.entries.Pairwise (fun a b => a.node ≠ b.node) ∧
    C.entries.all C.entryOK = true ∧
    distinctNodes (C.gates.map (fun gc => cellNode gc.x gc.y gc.pre "O") ++ C.pads.map (·.2)) = true ∧
    (∀ k < N.gates.length, ∃ g gc, N.gates[k]? = some g ∧ C.gates[k]? = some gc ∧ C.gateOK g gc = true) ∧
    (∀ k < N.flops.length, ∃ f fc, N.flops[k]? = some f ∧ C.flops[k]? = some fc ∧
      C.flopOK N.gates.length f fc = true) ∧
    (∀ k < N.outs.length, ∃ p l n j, N.outs[k]? = some (p, l) ∧ C.outs[k]? = some (p, n, j) ∧
      l.below N.gates.length = true ∧ C.startOK j n l = true) := by
  simp only [Cert.check, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hw, hg⟩, hf⟩, ho⟩, hs⟩, hok⟩, hd⟩, hG⟩, hF⟩, hO⟩ := h
  have hent : C.entries.all C.entryOK = true := by
    refine List.all_eq_true.mpr fun e he => ?_
    obtain ⟨c, hc, hec⟩ := List.mem_flatMap.mp he
    have := List.all_eq_true.mp hok c hc
    simp only [Cert.chunkOK, Bool.and_eq_true] at this
    exact List.all_eq_true.mp this.2 e hec
  have hdist := Cert.entries_distinct hs hok
  simp only [List.all_eq_true, List.mem_range] at hG hF hO
  refine ⟨hw, hg, hf, ho, hdist, hent, hd, fun k hk => ?_, fun k hk => ?_, fun k hk => ?_⟩
  · have := hG k hk
    unfold Cert.gateAt at this
    split at this
    · exact ⟨_, _, by assumption, by assumption, this⟩
    · simp at this
  · have := hF k hk
    unfold Cert.flopAt at this
    split at this
    · exact ⟨_, _, by assumption, by assumption, this⟩
    · simp at this
  · have := hO k hk
    unfold Cert.outAt at this
    split at this
    · rename_i p l p' n j h1 h2
      simp only [Bool.and_eq_true, beq_iff_eq] at this
      obtain ⟨⟨rfl, hb⟩, hp⟩ := this
      exact ⟨p, l, n, j, h1, h2, hb, hp⟩
    · simp at this

theorem Cert.startOK_spec {C : Cert} {j : Nat} {n : Node} {l : Lit} (h : C.startOK j n l = true) :
    ∃ e r, C.entries[j]? = some e ∧ e.node = n ∧ C.endOf j = some r ∧ C.litEnd l r = true := by
  simp only [Cert.startOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨h1, h2⟩ := h
  cases he : C.entries[j]? with
  | none => rw [he] at h1; simp at h1
  | some e =>
    rw [he] at h1; simp only [Option.map_some, Option.some.injEq] at h1
    split at h2
    · rename_i r hr; exact ⟨e, r, rfl, h1, hr, h2⟩
    · simp at h2

theorem Cert.req_entry {C : Cert} {N : Net} {e : Entry} (hm : e ∈ C.entries) :
    ∀ r ∈ C.entryReqs e, r ∈ C.required N := fun _ hr =>
  List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.mpr ⟨e, hm, hr⟩))

theorem Cert.req_gate {C : Cert} {N : Net} {k : Nat} {g : Gate} {gc : GateCert}
    (hg : N.gates[k]? = some g) (hgc : C.gates[k]? = some gc) :
    ∀ r ∈ C.cellReqs gc.x gc.y gc.pre g.init gc.isFlop, r ∈ C.required N := by
  have hk : k < N.gates.length := (List.getElem?_eq_some_iff.mp hg).1
  intro r hr
  refine List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨k, List.mem_range.mpr hk, ?_⟩))
  simp only [hg, hgc]; exact hr

theorem Cert.req_flop {C : Cert} {N : Net} {k : Nat} {f : Flop} {fc : FlopCert}
    (hf : N.flops[k]? = some f) (hfc : C.flops[k]? = some fc) :
    ∀ r ∈ C.rvReq fc.x fc.y fc.pre f.rv, r ∈ C.required N := by
  have hk : k < N.flops.length := (List.getElem?_eq_some_iff.mp hf).1
  intro r hr
  refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨k, List.mem_range.mpr hk, ?_⟩)
  simp only [hf, hfc]; exact hr

/-- The value of gate `k` in an assignment: its cell's LUT over the cell's input wires. -/
def Cert.lutVal (C : Cert) (N : Net) (σ : Node → Bool) (k : Nat) : Bool :=
  match N.gates[k]?, C.gates[k]? with
  | some g, some gc =>
    lut4 g.init (σ (cellNode gc.x gc.y gc.pre "I0")) (σ (cellNode gc.x gc.y gc.pre "I1"))
      (σ (cellNode gc.x gc.y gc.pre "I2")) (σ (cellNode gc.x gc.y gc.pre "I3"))
  | _, _ => false

section Sound

variable (C : Cert) (N : Net) (b : Bits) (pins : Nat → Bool) (Q σ : Node → Bool)

/-- A gate's cell's `O` in a cone assignment, from `lut4c_O` and its configuration bits. -/
theorem cell_O_val (hσ : ConeConsistent C b pins Q σ) {gc : GateCert} (hgm : gc ∈ C.gates) {co : Nat}
    (hco : C.cellOff gc.x gc.y gc.pre = some co) (init : BitVec 16)
    (hReq : ∀ r ∈ C.cellReqs gc.x gc.y gc.pre init gc.isFlop, b r.1 r.2.1 r.2.2.1 = r.2.2.2) :
    σ (cellNode gc.x gc.y gc.pre "O") =
      if gc.isFlop then Q ⟨gc.x, gc.y, gc.pre⟩ else
        lut4 init (σ (cellNode gc.x gc.y gc.pre "I0")) (σ (cellNode gc.x gc.y gc.pre "I1"))
          (σ (cellNode gc.x gc.y gc.pre "I2")) (σ (cellNode gc.x gc.y gc.pre "I3")) := by
  obtain ⟨tm, htm, hl⟩ := Cert.cellOff_some hco
  have h := hσ.cell gc hgm tm co htm hl
  simp only [cellInsAt] at h
  rw [lut4c_O] at h
  simp only [Option.some.injEq, Prod.mk.injEq, true_and] at h
  rw [← boolBV_inj h]
  simp only [Cert.cellReqs, htm, hco, List.mem_append, List.mem_map, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false] at hReq
  have h16 : tm.cellCfg (b gc.x gc.y) co 16 = gc.isFlop := hReq _ (Or.inr (Or.inl rfl))
  have h17 : tm.cellCfg (b gc.x gc.y) co 17 = false := hReq _ (Or.inr (Or.inr rfl))
  have hj : ∀ j < 16, tm.cellCfg (b gc.x gc.y) co j = init.getLsbD j := fun j hj => hReq _ (Or.inl ⟨j, hj, rfl⟩)
  rw [h16]
  cases gc.isFlop
  · simp only [Bool.false_eq_true, ite_false, cellLut, h17, lut4_eq_lut4F]
    exact lut4F_congr _ _ hj _ _ _ _
  · rfl

/-- A flop cell's next value, from `lut4c_next` and its configuration bits. -/
theorem cell_next_val {x y : Nat} {pre : String} {co : Nat} (hco : C.cellOff x y pre = some co)
    (init : BitVec 16) (rv : Bool)
    (hReq : ∀ r ∈ C.cellReqs x y pre init true ++ C.rvReq x y pre rv, b r.1 r.2.1 r.2.2.1 = r.2.2.2) :
    C.cellNext b Q σ ⟨x, y, pre⟩ =
      mux2 (σ (cellNode x y pre "EN")) (Q ⟨x, y, pre⟩)
        (mux2 (σ (cellNode x y pre "SR"))
          (lut4 init (σ (cellNode x y pre "I0")) (σ (cellNode x y pre "I1")) (σ (cellNode x y pre "I2"))
            (σ (cellNode x y pre "I3"))) rv) := by
  obtain ⟨tm, htm, hl⟩ := Cert.cellOff_some hco
  simp only [Cert.cellNext, htm, hl, cellInsAt, lut4c_next, boolBV_ne_zero]
  simp only [Cert.cellReqs, Cert.rvReq, htm, hco, List.mem_append, List.mem_map, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false] at hReq
  have h17 : tm.cellCfg (b x y) co 17 = false := hReq _ (Or.inl (Or.inr (Or.inr rfl)))
  have h18 : tm.cellCfg (b x y) co 18 = rv := hReq _ (Or.inr rfl)
  have hj : ∀ j < 16, tm.cellCfg (b x y) co j = init.getLsbD j := fun j hj => hReq _ (Or.inl (Or.inl ⟨j, hj, rfl⟩))
  simp only [cellLut, h17, h18, Bool.false_eq_true, ite_false, lut4_eq_lut4F]
  rw [lut4F_congr _ _ hj]

end Sound

/-- **The cone computes the `Net`.** A certificate that checks against `N`, under a configuration with
the bits it requires: in every assignment satisfying the cone's equations, every gate's cell shows the
`Net`'s gate value (or the flop), the output pins show `N.outputs`, and every flop cell loads `N.step`. -/
theorem cone_sound (C : Cert) (N : Net) (b : Bits) (pins : Nat → Bool) (Q σ : Node → Bool)
    (hC : C.check N = true) (hTopo : N.topo = true)
    (hBits : ∀ r ∈ C.required N, b r.1 r.2.1 r.2.2.1 = r.2.2.2)
    (hσ : ConeConsistent C b pins Q σ) :
    (∀ (k : Nat) (gc : GateCert), C.gates[k]? = some gc → σ (cellNode gc.x gc.y gc.pre "O") =
      if gc.isFlop then Q ⟨gc.x, gc.y, gc.pre⟩ else (N.gateVals pins (C.q Q)).getD k false) ∧
    C.observe σ = N.outputs pins (C.q Q) ∧
    ∀ k < N.flops.length, C.cellNext b Q σ (C.flopNode k) = N.step pins (C.q Q) k := by
  obtain ⟨hwf, hlg, hlf, hlo, _, hOK, _, hGs, hFs, hOs⟩ := Cert.check_spec hC
  have hB : ∀ e ∈ C.entries, ∀ r ∈ C.entryReqs e, b r.1 r.2.1 r.2.2.1 = r.2.2.2 :=
    fun e hm r hr => hBits r (Cert.req_entry hm r hr)
  -- a start entry's wire carries its end's value
  have hstart : ∀ j n l, C.startOK j n l = true → ∃ r, σ n = r.val σ ∧ C.litEnd l r = true ∧ C.endOf j = some r := by
    intro j n l h
    obtain ⟨e, r, he, hn, hr, hl⟩ := Cert.startOK_spec h
    exact ⟨r, hn ▸ Cert.follow_sound hσ hwf hOK hB _ j r e hr he, hl, hr⟩
  let q := C.q Q
  let v := C.lutVal N σ
  have hcellO : ∀ (k : Nat) (gc : GateCert) (g : Gate), C.gates[k]? = some gc → N.gates[k]? = some g →
      σ (cellNode gc.x gc.y gc.pre "O") = if gc.isFlop then Q ⟨gc.x, gc.y, gc.pre⟩ else v k := by
    intro k gc g hgc hg
    obtain ⟨g', gc', hg', hgc', hok⟩ := hGs k (List.getElem?_eq_some_iff.mp hg).1
    rw [hg] at hg'; cases hg'
    rw [hgc] at hgc'; cases hgc'
    simp only [Cert.gateOK, Bool.and_eq_true, Option.isSome_iff_exists] at hok
    obtain ⟨⟨co, hco⟩, _⟩ := hok
    rw [cell_O_val C b pins Q σ hσ (List.mem_of_getElem? hgc) hco g.init (fun r hr => hBits r (Cert.req_gate hg hgc r hr))]
    simp only [v, Cert.lutVal, hg, hgc]
  have hlit : ∀ l e, C.litEnd l e = true → e.val σ = l.evalF pins q v := by
    intro l e h
    cases l <;> cases e <;> simp only [Cert.litEnd, Bool.false_eq_true] at h
    · simp only [beq_iff_eq] at h; subst h; rfl
    · simp only [List.contains_iff_mem] at h
      exact hσ.pad _ h
    · rename_i k n
      split at h
      · rename_i fc hfc
        simp only [beq_iff_eq] at h
        subst h
        have hkf : k < N.flops.length := by have := (List.getElem?_eq_some_iff.mp hfc).1; omega
        obtain ⟨f, fc', hf, hfc', hok⟩ := hFs k hkf
        rw [hfc] at hfc'; cases hfc'
        simp only [Cert.flopOK, Bool.and_eq_true, decide_eq_true_eq] at hok
        obtain ⟨⟨⟨⟨⟨⟨_, hgl⟩, hgc⟩, _⟩, _⟩, _⟩, _⟩ := hok
        split at hgc
        · rename_i gc hgcs
          simp only [Bool.and_eq_true, beq_iff_eq] at hgc
          obtain ⟨⟨⟨hfl, hx⟩, hy⟩, hpre⟩ := hgc
          obtain ⟨g, gc', hg, hgc', _⟩ := hGs fc.gate hgl
          rw [hgcs] at hgc'; cases hgc'
          have := hcellO fc.gate gc g hgcs hg
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
        obtain ⟨g, gc', hg, hgc', _⟩ := hGs k (by have := (List.getElem?_eq_some_iff.mp hgc).1; omega)
        rw [hgc] at hgc'; cases hgc'
        have := hcellO k gc g hgc hg
        simp only [hnf, Bool.false_eq_true, ite_false] at this
        simp only [End.val, this, Lit.evalF]
      · simp at h
  have hgate : ∀ k (hk : k < N.gates.length), v k = lut4 (N.gates[k]).init ((N.gates[k]).i0.evalF pins q v)
      ((N.gates[k]).i1.evalF pins q v) ((N.gates[k]).i2.evalF pins q v) ((N.gates[k]).i3.evalF pins q v) := by
    intro k hk
    obtain ⟨g, gc, hg, hgc, hok⟩ := hGs k hk
    have hgk : N.gates[k] = g := by rw [List.getElem?_eq_some_iff] at hg; exact hg.2
    rw [hgk]
    simp only [Cert.gateOK, Bool.and_eq_true] at hok
    obtain ⟨_, hins⟩ := hok
    split at hins
    · rename_i p0 p1 p2 p3 _
      simp only [Bool.and_eq_true] at hins
      obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := hins
      have hin : ∀ (i : Nat) (port : String) (l : Lit) (pp : Option Nat), C.inOK gc g.init i port l pp = true →
          σ (cellNode gc.x gc.y gc.pre port) = l.evalF pins q v ∨
            (l.evalF pins q v = false ∧ ignores g.init i = true) := by
        intro i port l pp hok
        cases pp with
        | none =>
          simp only [Cert.inOK, Bool.and_eq_true, beq_iff_eq] at hok
          obtain ⟨rfl, hig⟩ := hok
          exact Or.inr ⟨rfl, hig⟩
        | some j =>
          simp only [Cert.inOK] at hok
          obtain ⟨r, hσr, hl, _⟩ := hstart j _ l hok
          exact Or.inl (hσr.trans (hlit l r hl))
      simp only [v, Cert.lutVal, hg, hgc]
      exact lut4_args _ _ _ _ _ _ _ _ _ (hin 0 "I0" _ p0 h0) (hin 1 "I1" _ p1 h1) (hin 2 "I2" _ p2 h2) (hin 3 "I3" _ p3 h3)
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
  refine ⟨fun k gc hgc => ?_, ?_, fun k hk => ?_⟩
  · -- every gate's cell
    have hk : k < N.gates.length := by have := (List.getElem?_eq_some_iff.mp hgc).1; omega
    obtain ⟨g, hg⟩ : ∃ g, N.gates[k]? = some g := ⟨_, List.getElem?_eq_getElem hk⟩
    rw [hcellO k gc g hgc hg, hvals k hk]
  · -- the output pins
    apply List.ext_getElem (by simp [Cert.observe, Net.outputs, hlo])
    intro k _ h2
    have hk : k < N.outs.length := by simpa [Net.outputs] using h2
    obtain ⟨p, l, n, j, ho, hco, hb, hp⟩ := hOs k hk
    obtain ⟨r, hσr, hl, _⟩ := hstart j n l hp
    rw [List.getElem?_eq_some_iff] at ho hco
    obtain ⟨_, ho⟩ := ho
    obtain ⟨_, hco⟩ := hco
    simp only [Cert.observe, Net.outputs, List.getElem_map, ho, hco, hσr, hlit l r hl, hlitV l hb]
    rfl
  · -- the flops
    obtain ⟨f, fc, hf, hfc, hok⟩ := hFs k hk
    simp only [Cert.flopOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hok
    obtain ⟨⟨⟨⟨⟨⟨hd, hgl⟩, hgc⟩, hben⟩, hbsr⟩, hpen⟩, hpsr⟩ := hok
    split at hgc
    · rename_i gc hgcs
      simp only [Bool.and_eq_true, beq_iff_eq] at hgc
      obtain ⟨⟨⟨hfl, hx⟩, hy⟩, hpre⟩ := hgc
      obtain ⟨g, gc', hg, hgc', hgok⟩ := hGs fc.gate hgl
      rw [hgcs] at hgc'; cases hgc'
      simp only [Cert.gateOK, Bool.and_eq_true, Option.isSome_iff_exists] at hgok
      obtain ⟨⟨co, hco⟩, _⟩ := hgok
      have hcr := Cert.req_gate hg hgcs
      rw [hfl, hx, hy, hpre] at hcr
      rw [hx, hy, hpre] at hco
      obtain ⟨e1, hen, hle1, _⟩ := hstart _ _ _ hpen
      obtain ⟨e2, hsr, hle2, _⟩ := hstart _ _ _ hpsr
      have hnext := cell_next_val C b Q σ hco g.init f.rv (fun r hr => by
        rcases List.mem_append.mp hr with hr | hr
        · exact hBits _ (hcr r hr)
        · exact hBits _ (Cert.req_flop hf hfc r hr))
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

/-! ## The cone has exactly one assignment -/

/-- A cone terminal's value: a gate's cell `O` (its flop, or the `Net`'s gate value), an input pad. -/
def Cert.termVal (C : Cert) (N : Net) (pins : Nat → Bool) (Q : Node → Bool) (m : Node) : Bool :=
  match C.gates.findIdx? (fun gc => cellNode gc.x gc.y gc.pre "O" == m) with
  | some k =>
    match C.gates[k]? with
    | some gc => if gc.isFlop then Q ⟨gc.x, gc.y, gc.pre⟩ else (N.gateVals pins (C.q Q)).getD k false
    | none => false
  | none =>
    match C.pads.find? (·.2 == m) with
    | some (k, _) => pins k
    | none => false

def Cert.endVal (C : Cert) (N : Net) (pins : Nat → Bool) (Q : Node → Bool) : Option End → Bool
  | some (.const c) => c
  | some (.node m) => C.termVal N pins Q m
  | none => false

/-- **The cone's assignment**, from the pins and the flop state: each entry's wire the value at its end. -/
def Cert.solve (C : Cert) (N : Net) (pins : Nat → Bool) (Q : Node → Bool) (n : Node) : Bool :=
  match C.entries.findIdx? (·.node == n) with
  | some j => C.endVal N pins Q (C.endOf j)
  | none => C.termVal N pins Q n

theorem distinctNodes_nodup : ∀ l : List Node, distinctNodes l = true → l.Nodup
  | [], _ => List.nodup_nil
  | n :: ns, h => by
    simp only [distinctNodes, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_any_beq, List.any_eq_false,
      beq_iff_eq] at h
    exact List.nodup_cons.mpr ⟨fun hm => h.1 n hm rfl, distinctNodes_nodup ns h.2⟩

theorem nodup_findIdx {l : List Node} (hl : l.Nodup) {k : Nat} (hk : k < l.length) :
    l.findIdx? (· == l[k]) = some k := by
  rw [List.findIdx?_eq_some_iff_getElem]
  refine ⟨hk, by simp, fun i hi heq => ?_⟩
  simp only [beq_iff_eq] at heq
  have := List.pairwise_iff_getElem.mp hl i k (by omega) hk hi
  exact this heq

theorem nodup_map_inj {α β : Type} [DecidableEq β] (g : α → β) :
    ∀ {l : List α}, (l.map g).Nodup → ∀ {a b}, a ∈ l → b ∈ l → g a = g b → a = b
  | [], _, _, _, ha, _, _ => by simp at ha
  | c :: l, h, a, b, ha, hb, hab => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at h
    rcases List.mem_cons.mp ha with h1 | ha' <;> rcases List.mem_cons.mp hb with h2 | hb'
    · rw [h1, h2]
    · subst h1; exact absurd hab.symm (h.1 b hb')
    · subst h2; exact absurd hab (h.1 a ha')
    · exact nodup_map_inj g h.2 ha' hb' hab

section Exists

variable (C : Cert) (N : Net) (pins : Nat → Bool) (Q : Node → Bool)

theorem Cert.solve_entry (hS : C.entries.Pairwise (fun a b => a.node ≠ b.node)) {j : Nat} {e : Entry} (he : C.entries[j]? = some e) :
    C.solve N pins Q e.node = C.endVal N pins Q (C.endOf j) := by
  simp only [Cert.solve, Cert.findIdx_entry hS he]

theorem Cert.solve_term (hOK : C.entries.all C.entryOK = true) {m : Node} (hm : C.knownTerm m = true) :
    C.solve N pins Q m = C.termVal N pins Q m := by
  have : C.entries.findIdx? (·.node == m) = none := by
    rw [List.findIdx?_eq_none_iff]
    intro x hx
    simp only [beq_eq_false_iff_ne, ne_eq]
    intro heq
    have := (Cert.entryOK_spec (List.all_eq_true.mp hOK x hx)).1
    rw [heq, hm] at this; cases this
  simp only [Cert.solve, this]

theorem Cert.termVal_cell (hD : distinctNodes (C.gates.map (fun gc => cellNode gc.x gc.y gc.pre "O") ++ C.pads.map (·.2)) = true)
    {k : Nat} {gc : GateCert} (hgc : C.gates[k]? = some gc) :
    C.termVal N pins Q (cellNode gc.x gc.y gc.pre "O") =
      if gc.isFlop then Q ⟨gc.x, gc.y, gc.pre⟩ else (N.gateVals pins (C.q Q)).getD k false := by
  have hnd := (List.nodup_append.mp (distinctNodes_nodup _ hD)).1
  have hk : k < C.gates.length := (List.getElem?_eq_some_iff.mp hgc).1
  have hget : C.gates[k] = gc := (List.getElem?_eq_some_iff.mp hgc).2
  have := nodup_findIdx hnd (k := k) (by simpa using hk)
  rw [List.findIdx?_map] at this
  simp only [List.getElem_map, hget] at this
  simp only [Cert.termVal]
  rw [show (fun gc' : GateCert => cellNode gc'.x gc'.y gc'.pre "O" == cellNode gc.x gc.y gc.pre "O") =
      ((· == cellNode gc.x gc.y gc.pre "O") ∘ fun gc' : GateCert => cellNode gc'.x gc'.y gc'.pre "O") from rfl, this]
  simp only [hgc]

theorem Cert.termVal_pad (hD : distinctNodes (C.gates.map (fun gc => cellNode gc.x gc.y gc.pre "O") ++ C.pads.map (·.2)) = true)
    {k : Nat} {m : Node} (hp : (k, m) ∈ C.pads) : C.termVal N pins Q m = pins k := by
  have hnd := List.nodup_append.mp (distinctNodes_nodup _ hD)
  have hg : C.gates.findIdx? (fun gc => cellNode gc.x gc.y gc.pre "O" == m) = none := by
    rw [List.findIdx?_eq_none_iff]
    intro gc hgc
    simp only [beq_eq_false_iff_ne, ne_eq]
    intro heq
    exact hnd.2.2 _ (List.mem_map.mpr ⟨gc, hgc, rfl⟩) _ (List.mem_map.mpr ⟨(k, m), hp, rfl⟩) (by simpa using heq)
  cases hf : C.pads.find? (·.2 == m) with
  | none =>
    have := List.find?_eq_none.mp hf (k, m) hp
    simp at this
  | some e =>
    have h1 := List.find?_some hf
    simp only [beq_iff_eq] at h1
    have := nodup_map_inj (·.2) hnd.2.1 (List.mem_of_find?_eq_some hf) hp h1
    simp only [Cert.termVal, hg, hf, this]

end Exists

theorem Cert.sel_of_reqs (C : Cert) (b : Bits) (hW : C.models.all (·.sm.wf) = true) {e : Entry} {k i : Nat}
    (hh : e.hop = .sm k i) {tm : TileModel} (htm : C.tileOf e.node.x e.node.y = some tm) {o : String} {p : SmPrim}
    (hk : tm.sm.prims[k]? = some (o, p)) (hB : ∀ r ∈ C.entryReqs e, b r.1 r.2.1 r.2.2.1 = r.2.2.2)
    (hi : i < p.ins.length) : p.sel (tm.smCfg (b e.node.x e.node.y)) = i := by
  have hwf := C.tileOf_wf hW htm
  have hp := List.all_eq_true.mp hwf (o, p) (List.mem_of_getElem? hk)
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq] at hp
  rw [SmPrim.sel_eq_selFrom]
  refine selFrom_testBit _ _ _ 0 i (fun c hc => ?_) ?_
  · have := hB (e.node.x, e.node.y, tm.pos.getD (tm.smOff + (p.base + c)) 0, i.testBit c) (by
      simp only [Cert.entryReqs, hh, htm, hk]
      exact List.mem_map.mpr ⟨c, List.mem_range.mpr hc, rfl⟩)
    simpa [TileModel.smCfg, TileModel.bit] using this
  · rcases hp.1.1 with h0 | h1
    · have := SmPrim.ins_length_of_selBits_zero p h0; rw [h0]; omega
    · omega

theorem Cert.follow_end (C : Cert) (hOK : C.entries.all C.entryOK = true) :
    ∀ f j m, C.follow f j = some (.node m) → C.knownTerm m = true
  | 0, _, _, h => by simp [Cert.follow] at h
  | f + 1, j, m, h => by
    simp only [Cert.follow] at h
    split at h
    · simp at h
    rename_i e he
    rcases (Cert.entryOK_spec (List.all_eq_true.mp hOK e (List.mem_of_getElem? he))).2.2 with
      ⟨c, ht, hn⟩ | ⟨m', j', e', ht, hn, _, _, _⟩ | ⟨m', ht, hn, hK⟩
    · simp [ht] at h
    · simp only [ht, hn] at h; exact C.follow_end hOK f j' m h
    · simp only [ht, hn, Option.some.injEq, End.node.injEq] at h; subst h; exact hK

/-- The end of entry `j`, one step unfolded. -/
theorem Cert.endOf_step (C : Cert) (hOK : C.entries.all C.entryOK = true) {j : Nat} {e : Entry}
    (he : C.entries[j]? = some e) :
    C.endOf j = match C.target e, e.next with
      | some (.const c), _ => some (.const c)
      | some (.node _), some j' => C.follow (C.entries.length - 1) j'
      | some (.node m), none => some (.node m)
      | none, _ => none := by
  have hr := (Cert.entryOK_spec (List.all_eq_true.mp hOK e (List.mem_of_getElem? he))).2.1
  unfold Cert.endOf
  rw [show C.entries.length = (C.entries.length - 1) + 1 by omega]
  simp only [Cert.follow, he]
  rw [show C.entries.length - 1 + 1 - 1 = C.entries.length - 1 by omega]

/-- An entry's wire, in the cone's assignment, carries what its hop reads. -/
theorem Cert.solve_target (C : Cert) (N : Net) (pins : Nat → Bool) (Q : Node → Bool)
    (hS : C.entries.Pairwise (fun a b => a.node ≠ b.node)) (hOK : C.entries.all C.entryOK = true) {j : Nat} {e : Entry}
    (he : C.entries[j]? = some e) {t : End} (ht : C.target e = some t) :
    C.solve N pins Q e.node = t.val (C.solve N pins Q) := by
  rw [C.solve_entry N pins Q hS he, C.endOf_step hOK he, ht]
  have hok := Cert.entryOK_spec (List.all_eq_true.mp hOK e (List.mem_of_getElem? he))
  rcases hok.2.2 with ⟨c, ht', hn⟩ | ⟨m, j', e', ht', hn, he', hnode, hlt⟩ | ⟨m, ht', hn, hT⟩
  · rw [ht] at ht'; cases ht'; rfl
  · rw [ht] at ht'; cases ht'
    simp only [hn]
    obtain ⟨r, hfr⟩ := C.follow_some hOK (C.entries.length - 1) j' e' he' (by omega)
    rw [hfr, End.val, ← hnode, C.solve_entry N pins Q hS he', Cert.endOf, C.follow_mono' hfr (by omega)]
  · rw [ht] at ht'; cases ht'
    simp only [hn, End.val, Cert.endVal]
    rw [C.solve_term N pins Q hOK hT]

/-- **The cone's equations have exactly one solution.** For a certificate that checks against a
topologically ordered `N` and a configuration with its bits, for every pin input and flop state:
`C.solve` satisfies the cone's equations, and every assignment that does agrees with it on every wire
of the cone. The cone is acyclic by construction (`rank` decreases along every hop), so routing loops
outside it, through multiplexer inputs nothing in it selects, do not enter. -/
theorem consistent_exists_unique (C : Cert) (N : Net) (b : Bits) (hC : C.check N = true) (hTopo : N.topo = true)
    (hBits : ∀ r ∈ C.required N, b r.1 r.2.1 r.2.2.1 = r.2.2.2) (pins : Nat → Bool) (Q : Node → Bool) :
    ConeConsistent C b pins Q (C.solve N pins Q) ∧
      ∀ σ, ConeConsistent C b pins Q σ → ∀ n ∈ C.coneNodes, σ n = C.solve N pins Q n := by
  obtain ⟨hwf, hlg, hlf, _, hS, hOK, hD, hGs, hFs, _⟩ := Cert.check_spec hC
  have hB : ∀ e ∈ C.entries, ∀ r ∈ C.entryReqs e, b r.1 r.2.1 r.2.2.1 = r.2.2.2 :=
    fun e hm r hr => hBits r (Cert.req_entry hm r hr)
  let q := C.q Q
  let vals := N.gateVals pins q
  let vF : Nat → Bool := fun i => vals.getD i false
  have hpadT : ∀ e ∈ C.pads, C.knownTerm e.2 = true := fun e he => by
    simp only [Cert.knownTerm, Bool.or_eq_true, List.any_eq_true, beq_iff_eq]; exact Or.inr ⟨e, he, rfl⟩
  have hcellT : ∀ gc ∈ C.gates, C.knownTerm (cellNode gc.x gc.y gc.pre "O") = true := fun gc hgc => by
    simp only [Cert.knownTerm, Bool.or_eq_true, List.any_eq_true, beq_iff_eq]; exact Or.inl ⟨gc, hgc, rfl⟩
  -- a cone end, in the cone's assignment, is the value of its `Lit` in the `Net`
  have hend : ∀ l r, C.litEnd l r = true → C.endVal N pins Q (some r) = l.evalF pins q vF := by
    intro l r h
    cases l <;> cases r <;> simp only [Cert.litEnd, Bool.false_eq_true] at h
    · simp only [beq_iff_eq] at h; subst h; rfl
    · simp only [List.contains_iff_mem] at h
      exact C.termVal_pad N pins Q hD h
    · rename_i k n
      split at h
      · rename_i fc hfc
        simp only [beq_iff_eq] at h
        subst h
        have hkf : k < N.flops.length := by have := (List.getElem?_eq_some_iff.mp hfc).1; omega
        obtain ⟨f, fc', hf, hfc', hok⟩ := hFs k hkf
        rw [hfc] at hfc'; cases hfc'
        simp only [Cert.flopOK, Bool.and_eq_true, decide_eq_true_eq] at hok
        obtain ⟨⟨⟨⟨⟨⟨_, _⟩, hgc⟩, _⟩, _⟩, _⟩, _⟩ := hok
        split at hgc
        · rename_i gc hgcs
          simp only [Bool.and_eq_true, beq_iff_eq] at hgc
          obtain ⟨⟨⟨hfl, hx⟩, hy⟩, hpre⟩ := hgc
          have := C.termVal_cell N pins Q hD hgcs
          rw [hfl, hx, hy, hpre] at this
          simp only [Cert.endVal, this, ite_true, Lit.evalF, q, Cert.q, Cert.flopNode, hfc,
            show k < C.flops.length by omega]
        · simp at hgc
      · simp at h
    · rename_i k n
      split at h
      · rename_i gc hgc
        simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at h
        obtain ⟨hnf, rfl⟩ := h
        simp only [Cert.endVal, C.termVal_cell N pins Q hD hgc, hnf, Bool.false_eq_true, ite_false, Lit.evalF, vF, vals, q]
      · simp at h
  have hstart : ∀ j n l, C.startOK j n l = true → C.solve N pins Q n = l.evalF pins q vF := by
    intro j n l h
    obtain ⟨e, r, he, hn, hr, hl⟩ := Cert.startOK_spec h
    rw [← hn, C.solve_entry N pins Q hS he, hr, hend l r hl]
  have hcellTerm : ∀ (k : Nat) (gc : GateCert), C.gates[k]? = some gc → C.solve N pins Q (cellNode gc.x gc.y gc.pre "O") =
      if gc.isFlop then Q ⟨gc.x, gc.y, gc.pre⟩ else vF k := by
    intro k gc hgc
    rw [C.solve_term N pins Q hOK (hcellT gc (List.mem_of_getElem? hgc)), C.termVal_cell N pins Q hD hgc]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · -- switch-matrix entries
    intro e hm k i hh tm htm o p hk
    obtain ⟨j, hj, hej⟩ := List.getElem_of_mem hm
    have he : C.entries[j]? = some e := by rw [List.getElem?_eq_getElem hj, hej]
    rw [smModule_eval_eq_SmPrim_eval tm.sm (C.tileOf_wf hwf htm) _ _ _ _ (smIns_encodes _ _ _), List.getElem?_map, hk]
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, true_and]
    congr 1
    -- the entry's target exists
    obtain ⟨t, ht⟩ : ∃ t, C.target e = some t := by
      rcases (Cert.entryOK_spec (List.all_eq_true.mp hOK e hm)).2.2 with ⟨c, h, _⟩ | ⟨m, _, _, h, _⟩ | ⟨m, h, _⟩ <;>
        exact ⟨_, h⟩
    rcases Cert.target_cases ht with ⟨s, hh', _⟩ | ⟨k', i', tm', o', p', src, hh', htm', hk', ho, hs, rfl⟩
    · rw [hh] at hh'; cases hh'
    · rw [hh] at hh'; cases hh'
      rw [htm] at htm'; cases htm'
      rw [hk] at hk'; cases hk'
      have hn : e.node = ⟨e.node.x, e.node.y, o⟩ := by rw [ho]
      have hsel := C.sel_of_reqs b hwf hh htm hk (hB e hm) (List.getElem?_eq_some_iff.mp hs).1
      rw [SmPrim.eval, hsel, hs, ← hn, C.solve_target N pins Q hS hOK he ht]
      cases src <;> rfl
  · -- wire entries
    intro e hm s hh
    obtain ⟨j, hj, hej⟩ := List.getElem_of_mem hm
    have he : C.entries[j]? = some e := by rw [List.getElem?_eq_getElem hj, hej]
    exact C.solve_target N pins Q hS hOK he (t := .node s) (by simp [Cert.target, hh])
  · -- gate cells
    intro gc hgm tm co htm hl
    obtain ⟨k, hk, hkg⟩ := List.getElem_of_mem hgm
    have hgc : C.gates[k]? = some gc := by rw [List.getElem?_eq_getElem hk, hkg]
    obtain ⟨g, gc', hg, hgc', hok⟩ := hGs k (by omega)
    rw [hgc] at hgc'; cases hgc'
    have hco : C.cellOff gc.x gc.y gc.pre = some co := by simp [Cert.cellOff, htm, hl]
    simp only [cellInsAt]
    rw [lut4c_O]
    simp only [Option.some.injEq, Prod.mk.injEq, true_and]
    congr 1
    have hReq := fun r hr => hBits r (Cert.req_gate hg hgc r hr)
    simp only [Cert.cellReqs, htm, hco, List.mem_append, List.mem_map, List.mem_range, List.mem_cons,
      List.not_mem_nil, or_false] at hReq
    have h16 : tm.cellCfg (b gc.x gc.y) co 16 = gc.isFlop := hReq _ (Or.inr (Or.inl rfl))
    have h17 : tm.cellCfg (b gc.x gc.y) co 17 = false := hReq _ (Or.inr (Or.inr rfl))
    have hj : ∀ j < 16, tm.cellCfg (b gc.x gc.y) co j = g.init.getLsbD j := fun j hj => hReq _ (Or.inl ⟨j, hj, rfl⟩)
    rw [hcellTerm k gc hgc, h16]
    cases hfl : gc.isFlop
    · simp only [Bool.false_eq_true, ite_false, cellLut, h17]
      rw [lut4F_congr _ _ hj, ← lut4_eq_lut4F]
      -- the `Net`'s gate value is the LUT over its inputs' values
      have hG := N.gatesHold_gateVals hTopo pins q
      have hgk : k < N.gates.length := (List.getElem?_eq_some_iff.mp hg).1
      have hval : vF k = lut4 g.init (g.i0.evalF pins q vF) (g.i1.evalF pins q vF) (g.i2.evalF pins q vF)
          (g.i3.evalF pins q vF) := by
        have key : ∀ (gs : List Gate) (k0 : Nat), gatesHold pins q vF gs k0 → ∀ j (hj : j < gs.length),
            vF (k0 + j) = lut4 gs[j].init (gs[j].i0.evalF pins q vF) (gs[j].i1.evalF pins q vF)
              (gs[j].i2.evalF pins q vF) (gs[j].i3.evalF pins q vF) := by
          intro gs
          induction gs with
          | nil => intro _ _ j hj; simp at hj
          | cons g' gs ih =>
            intro k0 h j hj
            obtain ⟨h1, h2⟩ := h
            cases j with
            | zero => simpa using h1
            | succ j =>
              have := ih (k0 + 1) h2 j (by simpa using hj)
              rw [show k0 + (j + 1) = k0 + 1 + j by omega]; simpa using this
        have := key N.gates 0 hG k hgk
        rw [Nat.zero_add, (List.getElem?_eq_some_iff.mp hg).2] at this
        exact this
      rw [hval]
      simp only [Cert.gateOK, Bool.and_eq_true] at hok
      obtain ⟨_, hins⟩ := hok
      split at hins
      · rename_i p0 p1 p2 p3 _
        simp only [Bool.and_eq_true] at hins
        obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := hins
        have hin : ∀ (i : Nat) (port : String) (l : Lit) (pp : Option Nat), C.inOK gc g.init i port l pp = true →
            l.evalF pins q vF = C.solve N pins Q (cellNode gc.x gc.y gc.pre port) ∨
              (C.solve N pins Q (cellNode gc.x gc.y gc.pre port) = false ∧ ignores g.init i = true) ∨
              (l.evalF pins q vF = false ∧ ignores g.init i = true) := by
          intro i port l pp hok
          cases pp with
          | none =>
            simp only [Cert.inOK, Bool.and_eq_true, beq_iff_eq] at hok
            obtain ⟨rfl, hig⟩ := hok
            exact Or.inr (Or.inr ⟨rfl, hig⟩)
          | some j =>
            simp only [Cert.inOK] at hok
            exact Or.inl (hstart j _ l hok).symm
        have conv : ∀ (i : Nat) (a e : Bool), (a = e ∨ (e = false ∧ ignores g.init i = true) ∨
            (a = false ∧ ignores g.init i = true)) → ∃ z, (a = z ∨ (z = false ∧ ignores g.init i = true)) ∧
            (e = z ∨ (z = false ∧ ignores g.init i = true)) := by
          intro i a e h
          rcases h with h | h | h
          · exact ⟨e, Or.inl h, Or.inl rfl⟩
          · exact ⟨false, Or.inr ⟨rfl, h.2⟩, Or.inl h.1⟩
          · exact ⟨false, Or.inl h.1, Or.inr ⟨rfl, h.2⟩⟩
        obtain ⟨z0, a0, e0⟩ := conv 0 _ _ (hin 0 "I0" _ p0 h0)
        obtain ⟨z1, a1, e1⟩ := conv 1 _ _ (hin 1 "I1" _ p1 h1)
        obtain ⟨z2, a2, e2⟩ := conv 2 _ _ (hin 2 "I2" _ p2 h2)
        obtain ⟨z3, a3, e3⟩ := conv 3 _ _ (hin 3 "I3" _ p3 h3)
        rw [lut4_args _ _ _ _ _ z0 z1 z2 z3 a0 a1 a2 a3, lut4_args _ _ _ _ _ z0 z1 z2 z3 e0 e1 e2 e3]
      · simp at hins
    · rfl
  · -- pads
    intro e he
    rw [C.solve_term N pins Q hOK (hpadT e he)]
    exact C.termVal_pad N pins Q hD (k := e.1) (m := e.2) he
  · -- uniqueness
    intro σ hσ n hn
    obtain ⟨hcells, _, _⟩ := cone_sound C N b pins Q σ hC hTopo hBits hσ
    have hterm : ∀ m, C.knownTerm m = true → σ m = C.solve N pins Q m := by
      intro m hk
      rw [C.solve_term N pins Q hOK hk]
      simp only [Cert.knownTerm, Bool.or_eq_true, List.any_eq_true, beq_iff_eq] at hk
      rcases hk with ⟨gc, hgm, rfl⟩ | ⟨e, he, rfl⟩
      · obtain ⟨k, hk, hkg⟩ := List.getElem_of_mem hgm
        have hgc : C.gates[k]? = some gc := by rw [List.getElem?_eq_getElem hk, hkg]
        rw [hcells k gc hgc, C.termVal_cell N pins Q hD hgc]
      · rw [hσ.pad e he, C.termVal_pad N pins Q hD (k := e.1) (m := e.2) he]
    simp only [Cert.coneNodes, List.mem_append, List.mem_map] at hn
    rcases hn with (⟨e, hm, rfl⟩ | ⟨gc, hgm, rfl⟩) | ⟨e, he, rfl⟩
    · obtain ⟨j, hj, hej⟩ := List.getElem_of_mem hm
      have he : C.entries[j]? = some e := by rw [List.getElem?_eq_getElem hj, hej]
      have hr := (Cert.entryOK_spec (List.all_eq_true.mp hOK e hm)).2.1
      obtain ⟨r, hfr⟩ := C.follow_some hOK C.entries.length j e he hr
      rw [Cert.follow_sound hσ hwf hOK hB _ j r e hfr he, C.solve_entry N pins Q hS he, Cert.endOf, hfr]
      cases r with
      | const c => rfl
      | node m =>
        have hK := C.follow_end hOK _ j m hfr
        rw [End.val, hterm m hK, C.solve_term N pins Q hOK hK]
        rfl
    · exact hterm _ (hcellT gc hgm)
    · exact hterm _ (hpadT e he)

/-! ## The whole grid's semantics implies the cone's -/

theorem Cert.tileOf_grid (C : Cert) (G : Grid) (hT : ∀ e ∈ C.tiles, G.tile e.1.1 e.1.2 = C.models[e.2]?)
    {x y : Nat} {tm : TileModel} (h : C.tileOf x y = some tm) : G.tile x y = some tm := by
  unfold Cert.tileOf at h
  split at h
  · rename_i e he
    have hp := List.find?_some he
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    rw [← hp.1, ← hp.2, hT e (List.mem_of_find?_eq_some he), h]
  · simp at h

/-- On a grid with the certificate's tile models, wires and pads, an assignment consistent with the
whole grid is consistent with the cone. -/
theorem Consistent.cone {C : Cert} {G : Grid} {b : Bits} {pins : Nat → Bool} {Q σ : Node → Bool}
    (hT : ∀ e ∈ C.tiles, G.tile e.1.1 e.1.2 = C.models[e.2]?)
    (hWires : ∀ e ∈ C.wiresUsed, e ∈ G.wires) (hPads : ∀ e ∈ C.pads, e ∈ G.pads)
    (hσ : Consistent G b pins Q σ) : ConeConsistent C b pins Q σ where
  sm e _ k _ _ tm htm o p hk := hσ.sm _ _ tm (C.tileOf_grid G hT htm) k o p hk
  wire e hm s hh := hσ.wire (s, e.node) (hWires _ (List.mem_filterMap.mpr ⟨e, hm, by simp [hh]⟩))
  cell gc _ tm co htm hl := hσ.cell _ _ tm (C.tileOf_grid G hT htm) gc.pre co (lookup_mem hl)
  pad e he := hσ.pad e (hPads e he)

/-! ## Every cycle of a run -/

/-- A run of the cone: each cycle's assignment satisfies the cone's equations for that cycle's pins and
flop state, and the next cycle's flop state is every cone cell's flop after the edge. -/
def ConeRun (C : Cert) (b : Bits) : (Node → Bool) → List ((Nat → Bool) × (Node → Bool)) → Prop
  | _, [] => True
  | Q, (pins, σ) :: rest => ConeConsistent C b pins Q σ ∧ ConeRun C b (C.cellNext b Q σ) rest

/-- The cone's run on a trace of pin vectors, each cycle's assignment `Cert.solve`. -/
def Cert.runFrom (C : Cert) (N : Net) (b : Bits) : (Node → Bool) → List (Nat → Bool) → List ((Nat → Bool) × (Node → Bool))
  | _, [] => []
  | Q, p :: ps => (p, C.solve N p Q) :: C.runFrom N b (C.cellNext b Q (C.solve N p Q)) ps

/-- **A run exists** for every trace of pin vectors and every flop state. -/
theorem Cert.runFrom_run (C : Cert) (N : Net) (b : Bits) (hC : C.check N = true) (hTopo : N.topo = true)
    (hBits : ∀ r ∈ C.required N, b r.1 r.2.1 r.2.2.1 = r.2.2.2) :
    ∀ (ps : List (Nat → Bool)) (Q : Node → Bool), ConeRun C b Q (C.runFrom N b Q ps) ∧ (C.runFrom N b Q ps).map (·.1) = ps
  | [], _ => ⟨trivial, rfl⟩
  | p :: ps, Q => by
    have ih := C.runFrom_run N b hC hTopo hBits ps (C.cellNext b Q (C.solve N p Q))
    exact ⟨⟨(consistent_exists_unique C N b hC hTopo hBits p Q).1, ih.1⟩, by simp [Cert.runFrom, ih.2]⟩

/-- **The cone's run is the `Net`'s run.** On every cycle of every run the output pins show what
`Net.run` gives from the flop state the cells hold. -/
theorem cone_run_eq (C : Cert) (N : Net) (b : Bits) (hC : C.check N = true) (hTopo : N.topo = true)
    (hBits : ∀ r ∈ C.required N, b r.1 r.2.1 r.2.2.1 = r.2.2.2) :
    ∀ (cyc : List ((Nat → Bool) × (Node → Bool))) (Q : Node → Bool), ConeRun C b Q cyc →
      cyc.map (fun c => C.observe c.2) = (N.run (C.q Q) (cyc.map (·.1))).1
  | [], _, _ => rfl
  | (pins, σ) :: rest, Q, ⟨hσ, hRest⟩ => by
    obtain ⟨_, hObs, hStep⟩ := cone_sound C N b pins Q σ hC hTopo hBits hσ
    have hlf := (Cert.check_spec hC).2.2.1
    have hq : C.q (C.cellNext b Q σ) = N.step pins (C.q Q) := by
      funext k
      by_cases hk : k < C.flops.length
      · simp only [Cert.q, hk, ite_true]; exact hStep k (by omega)
      · have : N.flops[k]? = none := List.getElem?_eq_none (by omega)
        simp [Cert.q, hk, Net.step, this]
    simp only [List.map_cons, Net.run]
    rw [hObs, ← hq, cone_run_eq C N b hC hTopo hBits rest _ hRest]

/-! ## Assembling a check from pieces -/

/-- Blocks `(start, length)` that cover `0..n-1`. -/
def coversRange (blocks : List (Nat × Nat)) (n : Nat) : Bool :=
  (List.range n).all fun k => blocks.any fun b => b.1 ≤ k && k < b.1 + b.2

theorem all_of_blocks {P : Nat → Bool} {blocks : List (Nat × Nat)} {n : Nat} (hc : coversRange blocks n = true)
    (hb : ∀ b ∈ blocks, (List.range' b.1 b.2).all P = true) : (List.range n).all P = true := by
  refine List.all_eq_true.mpr fun k hk => ?_
  have := List.all_eq_true.mp hc k hk
  simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at this
  obtain ⟨b, hbm, h1, h2⟩ := this
  exact List.all_eq_true.mp (hb b hbm) k (List.mem_range'_1.mpr ⟨h1, h2⟩)

/-- **The check, from its pieces.** -/
theorem Cert.check_of (C : Cert) (N : Net) (hw : C.models.all (·.sm.wf) = true)
    (hl : N.gates.length == C.gates.length && N.flops.length == C.flops.length && N.outs.length == C.outs.length)
    (hs : chunksSorted C.chunks = true) (hch : ∀ ch ∈ C.chunks, C.chunkOK ch = true)
    (hd : distinctNodes (C.gates.map (fun gc => cellNode gc.x gc.y gc.pre "O") ++ C.pads.map (·.2)) = true)
    (hg : (List.range N.gates.length).all (C.gateAt N) = true) (hf : (List.range N.flops.length).all (C.flopAt N) = true)
    (ho : (List.range N.outs.length).all (C.outAt N) = true) : C.check N = true := by
  simp only [Bool.and_eq_true] at hl
  simp only [Cert.check, Bool.and_eq_true, hw, hl, hs, List.all_eq_true.mpr hch, hd, hg, hf, ho, and_self]

/-- The required bits, from per-chunk and per-block pieces. -/
theorem Cert.required_of (C : Cert) (N : Net) (b : Bits)
    (hE : ∀ ch ∈ C.chunks, (ch.2.flatMap C.entryReqs).all (fun r => b r.1 r.2.1 r.2.2.1 == r.2.2.2) = true)
    (hG : (List.range N.gates.length).all (fun k => (match N.gates[k]?, C.gates[k]? with
      | some g, some gc => C.cellReqs gc.x gc.y gc.pre g.init gc.isFlop
      | _, _ => []).all (fun r => b r.1 r.2.1 r.2.2.1 == r.2.2.2)) = true)
    (hF : (List.range N.flops.length).all (fun k => (match N.flops[k]?, C.flops[k]? with
      | some f, some fc => C.rvReq fc.x fc.y fc.pre f.rv
      | _, _ => []).all (fun r => b r.1 r.2.1 r.2.2.1 == r.2.2.2)) = true) :
    ∀ r ∈ C.required N, b r.1 r.2.1 r.2.2.1 = r.2.2.2 := by
  intro r hr
  simp only [Cert.required, Cert.entries, List.mem_append, List.mem_flatMap, List.mem_range] at hr
  rcases hr with (⟨e, ⟨ch, hch, he⟩, hr⟩ | ⟨k, hk, hr⟩) | ⟨k, hk, hr⟩
  · have := List.all_eq_true.mp (hE ch hch) r (List.mem_flatMap.mpr ⟨e, he, hr⟩)
    simpa using this
  · have := List.all_eq_true.mp (List.all_eq_true.mp hG k (List.mem_range.mpr hk)) r hr
    simpa using this
  · have := List.all_eq_true.mp (List.all_eq_true.mp hF k (List.mem_range.mpr hk)) r hr
    simpa using this

end Obend.Hardware.Fabulous
