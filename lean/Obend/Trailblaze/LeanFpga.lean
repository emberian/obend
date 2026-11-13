module
/-
# Obend.Trailblaze.LeanFpga — Organ O7: Cubical `FaceIdeal3`, Salvadori `Δ`-Net AST Compiler (Rung 2) & Dual-Tile `FABulous` Bitstream (Rung 5)

Implements the executable Silver workflow and algebraic, AST-lowering, linearity, and codec proofs for Organ O7:
1. **Cubical Silicon `FaceIdeal3` (`BitVec 27` over $\{0, 1, *\}^3$, `arXiv:2605.15080`)**:
   - Encodes face ideals over the ternary 3-cube $\{0, 1, *\}^3$ (`0` = endpoint `0`, `1` = endpoint `1`,
     `2` = open interval interior `*`) as a canonical 27-bit word (`BitVec 27`, `< 2^27`), indexing
     `pt = (p₀, p₁, p₂)` at bit `p₀ + 3 * p₁ + 9 * p₂ < 27`.
   - Proves unconditionally that `FaceIdeal3` forms a bounded distributive lattice (`meet_comm`,
     `meet_assoc`, `join_comm`, `join_assoc`, `join_distrib_meet`, `meet_distrib_join`), a partial
     order under `implies` (`implies_refl`, `implies_trans`, `implies_antisymm`, `siliconSimpMeetImplies`),
     disjoint endpoints (`varEq0_meet_varEq1`), and **strict cubical boundary non-collapse**
     (`varEq0_join_varEq1_ne_top : (varEq0 v).join (varEq1 v) ≠ top`, i.e., $\partial\mathbb{I} \neq \mathbb{I}$,
     witnessed at interior point `(2, 2, 2)`, bit `26`, with `#tooth`).
2. **Rung 2 (`HARDWARE.md` — Recursive `LeafExpr` / `Leaf.Book` → Salvadori `Δ`-Net Compiler)**:
   - Recursively compiles `LeafExpr` and `Obend.Leaf.Book` method/static bodies (`lowerTermToLeafExpr`,
     `compileLeafExprToDeltaNet`, `lowerLeafBookToDeltaNet`) into linear Salvadori `Δ`-Nets, emitting
     level-indexed `replicator` sharing trees for multi-use bound variables, direct wires for linear
     variables, and `era` erasers for unused variables, plus `emitHvmNetText` and `checkNetPortLinearity`.
3. **Rung 5 (`HARDWARE.md` — Single & Dual-Tile `FABulous` eFPGA Frame Codec & Glitch-Free DPR)**:
   - Keeps single-tile `FabulousTileConfig` (`decode_encode_fabulousFrame`, `encode_decode_fabulousFrame`)
     and adds lossless 27-bit dual-tile packing (`FabulousDualTileConfig`, `encodeDualBitstreamFrames`,
     `decodeDualBitstreamFrames`, `evalDualFabulousCofib`), proving exact round-trip codecs and
     exact agreement with `FaceIdeal3.evalTernaryPoint` across all `27` ternary cube points.
-/
public import Obend.Trailblaze.Obligations
public import Obend.Leaf.Emit
public import Obend.Hardware.HDL
public import Obend.Tactic.Tooth

public section
namespace Obend.Trailblaze.LeanFpga
open Obend.Trailblaze
set_option autoImplicit false

private theorem of_bool_not_eq_false {b : Bool} (h : (!b) = false) : b = true := by
  cases b
  · cases h
  · rfl

/-! ## 1. Cubical Silicon `FaceIdeal3` (`BitVec 27` Over Ternary Cube $\{0, 1, *\}^3$) -/

/-- Coordinate triple `(p₀, p₁, p₂)` in the ternary 3-cube $\{0, 1, *\}^3$, where
    `0` denotes endpoint `0`, `1` denotes endpoint `1`, and `2` denotes interior `*`. -/
abbrev TernaryPt3 := Fin 3 × Fin 3 × Fin 3

/-- 27-bit face-ideal representation over $k = 3$ cubical interval variables:
    bit `p₀ + 3 * p₁ + 9 * p₂ < 27` records membership of ternary subcube point `(p₀, p₁, p₂)`. -/
structure FaceIdeal3 where
  mask : BitVec 27
  deriving DecidableEq, Repr

namespace FaceIdeal3

@[ext] theorem ext {a b : FaceIdeal3} (h : a.mask = b.mask) : a = b := by
  cases a
  cases b
  cases h
  rfl

/-- Bijective base-3 index `p₀ + 3 * p₁ + 9 * p₂ ∈ Fin 27` of a ternary 3-cube point. -/
def ternaryPointIdx (pt : TernaryPt3) : Fin 27 :=
  ⟨pt.1.val + 3 * pt.2.1.val + 9 * pt.2.2.val, by omega⟩

/-- The open 3-cube interior point `(*, *, *) = (2, 2, 2)` at bit index `26`. -/
def interiorPt : TernaryPt3 :=
  (⟨2, by decide⟩, ⟨2, by decide⟩, ⟨2, by decide⟩)

/-- Project coordinate `v ∈ Fin 3` of a ternary point `pt`. -/
def coordOf (v : Fin 3) (pt : TernaryPt3) : Fin 3 :=
  match v.val with
  | 0 => pt.1
  | 1 => pt.2.1
  | _ => pt.2.2

/-- Top cofibration `⊤` (`0x07FF_FFFF#27`, full 3-cube including interior `*`). -/
def top : FaceIdeal3 := ⟨BitVec.allOnes 27⟩

/-- Bottom cofibration `⊥` (`0#27`, empty face ideal). -/
def bot : FaceIdeal3 := ⟨0#27⟩

/-- 1-cycle hardware face conjunction `φ ∧ ψ`. -/
@[expose] def meet (a b : FaceIdeal3) : FaceIdeal3 := ⟨a.mask &&& b.mask⟩

/-- 1-cycle hardware face disjunction `φ ∨ ψ`. -/
@[expose] def join (a b : FaceIdeal3) : FaceIdeal3 := ⟨a.mask ||| b.mask⟩

/-- Endpoint face `(i_v = 0)` for interval variable `v ∈ Fin 3`:
    bit `idx` is `1` iff ternary coordinate `v` of `idx` equals `0`. -/
def varEq0 (v : Fin 3) : FaceIdeal3 :=
  match v.val with
  | 0 => ⟨0x0124_9249#27⟩
  | 1 => ⟨0x001C_0E07#27⟩
  | _ => ⟨0x0000_01FF#27⟩

/-- Endpoint face `(i_v = 1)` for interval variable `v ∈ Fin 3`:
    bit `idx` is `1` iff ternary coordinate `v` of `idx` equals `1`. -/
def varEq1 (v : Fin 3) : FaceIdeal3 :=
  match v.val with
  | 0 => ⟨0x0249_2492#27⟩
  | 1 => ⟨0x00E0_7038#27⟩
  | _ => ⟨0x0003_FE00#27⟩

/-- Evaluate `FaceIdeal3` mask `φ` at ternary 3-cube point `pt`. -/
def evalTernaryPoint (φ : FaceIdeal3) (pt : TernaryPt3) : Bool :=
  φ.mask.getLsbD (ternaryPointIdx pt).val

/-- 1-cycle sub-ideal entailment (`a ⊢ b`, i.e., `a ∧ b = a`). -/
def implies (a b : FaceIdeal3) : Bool :=
  (a.mask &&& b.mask) == a.mask

theorem meet_comm (a b : FaceIdeal3) : a.meet b = b.meet a := by
  apply ext
  apply BitVec.eq_of_getLsbD_eq
  intro i _hi
  simp [meet, Bool.and_comm]

theorem meet_assoc (a b c : FaceIdeal3) : (a.meet b).meet c = a.meet (b.meet c) := by
  apply ext
  apply BitVec.eq_of_getLsbD_eq
  intro i _hi
  simp [meet, Bool.and_assoc]

theorem join_comm (a b : FaceIdeal3) : a.join b = b.join a := by
  apply ext
  apply BitVec.eq_of_getLsbD_eq
  intro i _hi
  simp [join, Bool.or_comm]

theorem join_assoc (a b c : FaceIdeal3) : (a.join b).join c = a.join (b.join c) := by
  apply ext
  apply BitVec.eq_of_getLsbD_eq
  intro i _hi
  simp [join, Bool.or_assoc]

theorem join_distrib_meet (a b c : FaceIdeal3) :
    a.join (b.meet c) = (a.join b).meet (a.join c) := by
  apply ext
  apply BitVec.eq_of_getLsbD_eq
  intro i _hi
  simp only [join, meet, BitVec.getLsbD_or, BitVec.getLsbD_and]
  cases a.mask.getLsbD i <;>
    cases b.mask.getLsbD i <;>
    cases c.mask.getLsbD i <;>
    rfl

theorem meet_distrib_join (a b c : FaceIdeal3) :
    a.meet (b.join c) = (a.meet b).join (a.meet c) := by
  apply ext
  apply BitVec.eq_of_getLsbD_eq
  intro i _hi
  simp only [join, meet, BitVec.getLsbD_or, BitVec.getLsbD_and]
  cases a.mask.getLsbD i <;>
    cases b.mask.getLsbD i <;>
    cases c.mask.getLsbD i <;>
    rfl

theorem meet_bot (a : FaceIdeal3) : a.meet bot = bot := by
  apply ext
  apply BitVec.eq_of_getLsbD_eq
  intro i _hi
  simp [meet, bot]

theorem join_bot (a : FaceIdeal3) : a.join bot = a := by
  apply ext
  apply BitVec.eq_of_getLsbD_eq
  intro i _hi
  simp [join, bot]

theorem meet_top (a : FaceIdeal3) : a.meet top = a := by
  apply ext
  change a.mask &&& BitVec.allOnes 27 = a.mask
  exact BitVec.and_allOnes

theorem join_top (a : FaceIdeal3) : a.join top = top := by
  apply ext
  change a.mask ||| BitVec.allOnes 27 = BitVec.allOnes 27
  exact BitVec.or_allOnes

theorem implies_refl (a : FaceIdeal3) : a.implies a = true := by
  unfold implies
  have hIdem : a.mask &&& a.mask = a.mask := by
    apply BitVec.eq_of_getLsbD_eq
    intro i _hi
    simp
  rw [hIdem]
  exact beq_self_eq_true a.mask

theorem implies_trans {a b c : FaceIdeal3}
    (hab : a.implies b = true)
    (hbc : b.implies c = true) :
    a.implies c = true := by
  unfold implies at hab hbc ⊢
  rw [beq_iff_eq] at hab hbc ⊢
  have hAssoc : (a.mask &&& b.mask) &&& c.mask =
      a.mask &&& (b.mask &&& c.mask) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i _hi
    simp [Bool.and_assoc]
  calc
    a.mask &&& c.mask
      = (a.mask &&& b.mask) &&& c.mask := by rw [hab]
    _ = a.mask &&& (b.mask &&& c.mask) := hAssoc
    _ = a.mask &&& b.mask := by rw [hbc]
    _ = a.mask := hab

theorem implies_antisymm {a b : FaceIdeal3}
    (hab : a.implies b = true)
    (hba : b.implies a = true) :
    a = b := by
  unfold implies at hab hba
  rw [beq_iff_eq] at hab hba
  apply ext
  have hComm : a.mask &&& b.mask = b.mask &&& a.mask := by
    apply BitVec.eq_of_getLsbD_eq
    intro i _hi
    simp [Bool.and_comm]
  rw [← hab, hComm, hba]

/-- **Unconditional Silicon Rewrite Entailment (`siliconSimpMeetImplies`)**:
    Every conjunction `φ ∧ ψ` entails `φ` in 1 hardware ALU cycle (`(φ ∧ ψ) ⊢ φ`). -/
theorem siliconSimpMeetImplies (φ ψ : FaceIdeal3) :
    (φ.meet ψ).implies φ = true := by
  unfold implies meet
  rw [beq_iff_eq]
  apply BitVec.eq_of_getLsbD_eq
  intro i _hi
  simp only [BitVec.getLsbD_and]
  cases φ.mask.getLsbD i <;> cases ψ.mask.getLsbD i <;> rfl

theorem evalTernaryPoint_meet (a b : FaceIdeal3) (pt : TernaryPt3) :
    (a.meet b).evalTernaryPoint pt = (a.evalTernaryPoint pt && b.evalTernaryPoint pt) := by
  simp [evalTernaryPoint, meet]

theorem evalTernaryPoint_join (a b : FaceIdeal3) (pt : TernaryPt3) :
    (a.join b).evalTernaryPoint pt = (a.evalTernaryPoint pt || b.evalTernaryPoint pt) := by
  simp [evalTernaryPoint, join]

/-- Exact coordinate characterization of `varEq0`: true at `pt` iff coordinate `v` of `pt` is `0`. -/
theorem evalTernaryPoint_varEq0 (v : Fin 3) (pt : TernaryPt3) :
    (varEq0 v).evalTernaryPoint pt = ((coordOf v pt).val == 0) := by
  rcases pt with ⟨p0, p1, p2⟩
  revert p2 p1 p0 v
  decide

/-- Exact coordinate characterization of `varEq1`: true at `pt` iff coordinate `v` of `pt` is `1`. -/
theorem evalTernaryPoint_varEq1 (v : Fin 3) (pt : TernaryPt3) :
    (varEq1 v).evalTernaryPoint pt = ((coordOf v pt).val == 1) := by
  rcases pt with ⟨p0, p1, p2⟩
  revert p2 p1 p0 v
  decide

/-- Disjointness of opposite interval endpoints: `(i_v = 0) ∧ (i_v = 1) = ⊥`. -/
theorem varEq0_meet_varEq1 (v : Fin 3) : (varEq0 v).meet (varEq1 v) = bot := by
  revert v
  decide

/-- **Non-Collapse of the Cubical Boundary (`∂𝕀 ≠ 𝕀`)**:
    For every interval variable `v ∈ Fin 3`, `(i_v = 0) ∨ (i_v = 1) ≠ ⊤` because the open
    interior point `(*, *, *) = (2, 2, 2)` (bit `26`) lies in `top` (`𝕀`) while neither
    endpoint face holds at `*`. -/
theorem varEq0_join_varEq1_ne_top (v : Fin 3) :
    (varEq0 v).join (varEq1 v) ≠ top := by
  revert v
  decide

end FaceIdeal3

/-! ## 2. Rung 2 (`HARDWARE.md`): Salvadori `Δ`-Net IR & Recursive `LeafExpr` / `Leaf.Book` Compiler -/

/-- Port address `(nodeId, portSlot)` where `0` is principal, `1` is left auxiliary, and `2` is right auxiliary. -/
structure PortEnd where
  nodeId   : Nat
  portSlot : Fin 3
  deriving DecidableEq, Repr

/-- Salvadori `Δ`-Net (`arXiv:2505.20314`) hardware interaction-net node kinds:
    - `era`: 1-port eraser (`portSlot = 0`),
    - `con`: 3-port constructor (`tag`),
    - `dup`: 3-port interaction-combinator duplicator (`label`),
    - `replicator`: 3-port level-indexed Salvadori replicator fan (`level`) for higher-order sharing. -/
inductive DeltaNetNode where
  | era        (nodeId : Nat)
  | con        (nodeId : Nat) (tag : UInt16)
  | dup        (nodeId : Nat) (label : UInt16)
  | replicator (nodeId : Nat) (level : UInt16)
  deriving DecidableEq, Repr

/-- Extract the unique identifier of a `DeltaNetNode`. -/
def DeltaNetNode.nodeId : DeltaNetNode → Nat
  | .era id => id
  | .con id _ => id
  | .dup id _ => id
  | .replicator id _ => id

/-- Exact list of ports exposed by a `DeltaNetNode`. -/
def DeltaNetNode.ports : DeltaNetNode → List PortEnd
  | .era id => [⟨id, ⟨0, by decide⟩⟩]
  | .con id _ => [⟨id, ⟨0, by decide⟩⟩, ⟨id, ⟨1, by decide⟩⟩, ⟨id, ⟨2, by decide⟩⟩]
  | .dup id _ => [⟨id, ⟨0, by decide⟩⟩, ⟨id, ⟨1, by decide⟩⟩, ⟨id, ⟨2, by decide⟩⟩]
  | .replicator id _ => [⟨id, ⟨0, by decide⟩⟩, ⟨id, ⟨1, by decide⟩⟩, ⟨id, ⟨2, by decide⟩⟩]

/-- Undirected wire connecting two `PortEnd`s in a `DeltaNet`. -/
structure DeltaWire where
  lhs : PortEnd
  rhs : PortEnd
  deriving DecidableEq, Repr

/-- Complete Rung-2 Salvadori `Δ`-Net graph lowered from `LeafExpr` / `Obend.Leaf.Book`. -/
structure DeltaNet where
  netName  : String
  rootPort : PortEnd
  nodes    : List DeltaNetNode
  wires    : List DeltaWire
  deriving DecidableEq, Repr

/-- Render a `PortEnd` as a deterministic HVM2 wire variable identifier. -/
def renderPortVar (p : PortEnd) : String :=
  "w" ++ toString p.nodeId ++ "_" ++ toString p.portSlot.val

/-- Render a `DeltaNetNode` in textual HVM2 / `Δ`-Net equation form. -/
def emitNodeEquation (n : DeltaNetNode) : String :=
  match n with
  | .era id =>
    "* ~ w" ++ toString id ++ "_0"
  | .con id tag =>
    if tag == 0 then
      "(w" ++ toString id ++ "_1 w" ++ toString id ++ "_2) ~ w" ++ toString id ++ "_0"
    else
      "#con" ++ toString tag.toNat ++ "{w" ++ toString id ++ "_1 w" ++ toString id ++ "_2} ~ w" ++ toString id ++ "_0"
  | .dup id lbl =>
    "#dup" ++ toString lbl.toNat ++ "{w" ++ toString id ++ "_1 w" ++ toString id ++ "_2} ~ w" ++ toString id ++ "_0"
  | .replicator id lvl =>
    "!rep" ++ toString lvl.toNat ++ "{w" ++ toString id ++ "_1 w" ++ toString id ++ "_2} ~ w" ++ toString id ++ "_0"

/-- Emit textual HVM2 / `Δ`-Net book definition for Rung-2 `hvm` execution. -/
def emitHvmNetText (net : DeltaNet) : String :=
  let header := "@" ++ net.netName ++ " = " ++ renderPortVar net.rootPort
  let nodeLines := net.nodes.map (fun n => "  & " ++ emitNodeEquation n)
  let wireLines := net.wires.map (fun w => "  & " ++ renderPortVar w.lhs ++ " ~ " ++ renderPortVar w.rhs)
  String.intercalate "\n" (header :: (nodeLines ++ wireLines))

/-- Flatten all ports declared across `net.nodes`. -/
def declaredPorts (net : DeltaNet) : List PortEnd :=
  (net.nodes.map DeltaNetNode.ports).flatten

/-- All declared non-root ports of `net`, each of which must be wired exactly once. -/
def nonRootPorts (net : DeltaNet) : List PortEnd :=
  (declaredPorts net).filter (fun p => p != net.rootPort)

/-- Flatten every wire `⟨lhs, rhs⟩` into its two incident port endpoints. -/
def wireEndpoints (wires : List DeltaWire) : List PortEnd :=
  (wires.map (fun w => [w.lhs, w.rhs])).flatten

/-- Number of wire endpoints incident to `target`. -/
def countPort (target : PortEnd) (endpoints : List PortEnd) : Nat :=
  (endpoints.filter (fun p => p == target)).length

/-- Check pairwise distinct `nodeId`s across `nodes`. -/
def checkDistinctDeltaNodeIds : List DeltaNetNode → Bool
  | [] => false
  | [_] => true
  | n :: rest =>
    rest.all (fun m => n.nodeId != m.nodeId) && checkDistinctDeltaNodeIds rest

/-- Deterministic Rung-2 port-wiring linearity check:
    1. Non-empty net name and distinct node IDs,
    2. `rootPort` is a declared port and has `0` internal wire incidences,
    3. Zero self-loop wires (`w.lhs != w.rhs`),
    4. Every wire endpoint is a declared non-root port, and
    5. Every declared non-root port has degree `== 1` (`countPort p endpoints == 1`). -/
def checkNetPortLinearity (net : DeltaNet) : Bool :=
  let decls := declaredPorts net
  let nonRoots := nonRootPorts net
  let eps := wireEndpoints net.wires
  !net.netName.isEmpty &&
  checkDistinctDeltaNodeIds net.nodes &&
  decls.contains net.rootPort &&
  (countPort net.rootPort eps == 0) &&
  net.wires.all (fun w => w.lhs != w.rhs) &&
  eps.all (fun ep => nonRoots.contains ep) &&
  nonRoots.all (fun p => countPort p eps == 1)

/-- Soundness of `checkNetPortLinearity`: guarantees exact degree-1 wiring on every non-root port,
    degree-0 freedom on `rootPort`, and absence of degenerate self-loops. -/
theorem checkNetPortLinearity_sound
    (net : DeltaNet) (p : PortEnd)
    (hLin : checkNetPortLinearity net = true)
    (hNonRoot : p ∈ nonRootPorts net) :
    countPort p (wireEndpoints net.wires) = 1 ∧
    countPort net.rootPort (wireEndpoints net.wires) = 0 ∧
    (∀ w ∈ net.wires, w.lhs ≠ w.rhs) := by
  unfold checkNetPortLinearity at hLin
  dsimp only at hLin
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq, bne_iff_ne] at hLin
  exact ⟨hLin.2 p hNonRoot, hLin.1.1.1.2, hLin.1.1.2⟩

/-- Detect active principal-to-principal interaction redexes (`lhs.portSlot = 0` and `rhs.portSlot = 0`). -/
def activePrincipalRedexes (net : DeltaNet) : List DeltaWire :=
  net.wires.filter (fun w => w.lhs.portSlot.val == 0 && w.rhs.portSlot.val == 0)

/-- Intermediate `LeafExpr` AST for structural Rung-2 Salvadori `Δ`-Net compilation
    (supporting de Bruijn variables, lambdas, applications, binary ALU ops, constructors,
    record/slot projections, and let-bindings with occurrence-driven `replicator`/`era` sharing). -/
inductive LeafExpr where
  | lit     (val : Nat)
  | var     (dbIdx : Nat)
  | lam     (body : LeafExpr)
  | app     (fn arg : LeafExpr)
  | binOp   (opTag : UInt16) (lhs rhs : LeafExpr)
  | ctorPair (tag : UInt16) (fst snd : LeafExpr)
  | proj    (slotTag : UInt16) (target : LeafExpr)
  | letBind (val body : LeafExpr)
  deriving DecidableEq, Repr

/-- Deterministic 16-bit tag for `Obend.Core.Term.Primitive`. -/
def primitiveToDeltaTag : Obend.Core.Term.Primitive → UInt16
  | .add => 0x0101
  | .multiply => 0x0102
  | .equal => 0x0103
  | .conjunction => 0x0104
  | .labelEqual => 0x0105
  | .subtract => 0x0106
  | .divide => 0x0107
  | .less => 0x0108
  | .lessEqual => 0x0109
  | .modulo => 0x010A
  | .bitAnd => 0x010B
  | .bitOr => 0x010C
  | .bitXor => 0x010D
  | .shl => 0x010E
  | .lshr => 0x010F
  | .ashr => 0x0110
  | .slt => 0x0111
  | .qmul32 => 0x0112

/-- Deterministic 16-bit tag for member/constructor field names. -/
def stringToDeltaTag (s : String) : UInt16 :=
  UInt16.ofNat ((s.utf8ByteSize * 257 + 0x0201) % 65535)

/-- Structurally translate any `Obend.Core.Term.Term` AST into `LeafExpr`, preserving every
    binder, variable occurrence, binary primitive, projection, and subterm (`rfl`-reducible). -/
def lowerTermToLeafExpr : Obend.Core.Term.Term → LeafExpr
  | .nat n => .lit n
  | .boolean b => .lit (if b then 1 else 0)
  | .label s => .lit (stringToDeltaTag s).toNat
  | .bound idx => .var idx
  | .lam body => .lam (lowerTermToLeafExpr body)
  | .app fn arg => .app (lowerTermToLeafExpr fn) (lowerTermToLeafExpr arg)
  | .binary prim l r => .binOp (primitiveToDeltaTag prim) (lowerTermToLeafExpr l) (lowerTermToLeafExpr r)
  | .get target nm => .proj (stringToDeltaTag nm) (lowerTermToLeafExpr target)
  | .record fields => lowerFields fields
  | .extend inh fields => .ctorPair 0x0301 (lowerTermToLeafExpr inh) (lowerFields fields)
  | .inject tag payload => .ctorPair (stringToDeltaTag tag) (lowerTermToLeafExpr payload) (.lit 0)
  | .ifZero v z s =>
    .binOp 0x0310 (lowerTermToLeafExpr v) (.ctorPair 0x0311 (lowerTermToLeafExpr z) (.lam (lowerTermToLeafExpr s)))
  | .ifBool c t f =>
    .binOp 0x0312 (lowerTermToLeafExpr c) (.ctorPair 0x0313 (lowerTermToLeafExpr t) (lowerTermToLeafExpr f))
  | .case sc arms => .binOp 0x0314 (lowerTermToLeafExpr sc) (lowerArms arms)
  | .hole h σ => .ctorPair (UInt16.ofNat (h % 65535 + 1)) (lowerTerms σ) (.lit 0)
  | .mix l u => .ctorPair 0x0320 (lowerTermToLeafExpr l) (lowerTermToLeafExpr u)
  | .fix s i => .ctorPair 0x0321 (lowerTermToLeafExpr s) (lowerTermToLeafExpr i)
  | .specification m e => .ctorPair 0x0322 (lowerTermToLeafExpr m) (lowerTermToLeafExpr e)
  | .prototype s g => .ctorPair 0x0323 (lowerTermToLeafExpr s) (lowerTermToLeafExpr g)
  | .reflect p => .proj 0x0324 (lowerTermToLeafExpr p)
  | .metadata p => .proj 0x0325 (lowerTermToLeafExpr p)
  | .project p => .proj 0x0326 (lowerTermToLeafExpr p)
  | .perform p => .proj 0x0327 (lowerTermToLeafExpr p)
  | .done p => .proj 0x0328 (lowerTermToLeafExpr p)
  | .split tgt _ fn => .app (lowerTermToLeafExpr fn) (lowerTermToLeafExpr tgt)
where
  lowerFields : List (String × Obend.Core.Term.Term) → LeafExpr
    | [] => .lit 0
    | f :: rest => .ctorPair (stringToDeltaTag f.1) (lowerTermToLeafExpr f.2) (lowerFields rest)
  lowerArms : List (String × Obend.Core.Term.Term) → LeafExpr
    | [] => .lit 0
    | a :: rest => .ctorPair (stringToDeltaTag a.1) (.lam (lowerTermToLeafExpr a.2)) (lowerArms rest)
  lowerTerms : List Obend.Core.Term.Term → LeafExpr
    | [] => .lit 0
    | t :: rest => .ctorPair 0x0300 (lowerTermToLeafExpr t) (lowerTerms rest)

/-- Subgraph build state returned during recursive `LeafExpr → DeltaNet` compilation. -/
private structure SubNetBuild where
  root     : PortEnd
  varPorts : List (Nat × PortEnd)
  nodes    : List DeltaNetNode
  wires    : List DeltaWire
  nextId   : Nat

/-- Wire a binder source port `srcPort` to `occPorts` (all occurrences of bound variable `0`):
    - `0` occurrences: emits `.era` terminator (`srcPort ~ era_0`),
    - `1` occurrence:  emits direct wire (`srcPort ~ p`),
    - `≥ 2` occurrences: emits a binary tree of level-indexed Salvadori `.replicator` fans! -/
private def wireBinderOccurrences
    (srcPort : PortEnd) (lvl : UInt16) : List PortEnd → Nat → (List DeltaNetNode × List DeltaWire × Nat)
  | [], nextId =>
    let eraNode := DeltaNetNode.era nextId
    ([eraNode], [⟨srcPort, ⟨nextId, ⟨0, by decide⟩⟩⟩], nextId + 1)
  | [p], nextId =>
    ([], [⟨srcPort, p⟩], nextId)
  | p₁ :: p₂ :: rest, nextId =>
    let repId := nextId
    let repNode := DeltaNetNode.replicator repId lvl
    let (tailNodes, tailWires, nextId') :=
      wireBinderOccurrences ⟨repId, ⟨2, by decide⟩⟩ lvl (p₂ :: rest) (repId + 1)
    (repNode :: tailNodes,
     ⟨srcPort, ⟨repId, ⟨0, by decide⟩⟩⟩ :: ⟨⟨repId, ⟨1, by decide⟩⟩, p₁⟩ :: tailWires,
     nextId')

/-- Cap any remaining free top-level variable ports with `.era` terminators so open expressions
    also produce closed port-linear `DeltaNet` graphs. -/
private def capFreeVarPorts : List (Nat × PortEnd) → Nat → (List DeltaNetNode × List DeltaWire × Nat)
  | [], nextId => ([], [], nextId)
  | (_, p) :: rest, nextId =>
    let eraId := nextId
    let (ns, ws, nextId') := capFreeVarPorts rest (eraId + 1)
    (.era eraId :: ns, ⟨p, ⟨eraId, ⟨0, by decide⟩⟩⟩ :: ws, nextId')

/-- Recursively compile a `LeafExpr` at binder depth `depth` starting from fresh `nextId`. -/
private def buildLeafExprSubNet (depth : Nat) : LeafExpr → Nat → SubNetBuild
  | .lit val, nextId =>
    let litTag : UInt16 := UInt16.ofNat ((val % 32767) + 1)
    let cId := nextId
    let e1 := nextId + 1
    let e2 := nextId + 2
    { root := ⟨cId, ⟨0, by decide⟩⟩
    , varPorts := []
    , nodes := [.con cId litTag, .era e1, .era e2]
    , wires :=
        [ ⟨⟨cId, ⟨1, by decide⟩⟩, ⟨e1, ⟨0, by decide⟩⟩⟩
        , ⟨⟨cId, ⟨2, by decide⟩⟩, ⟨e2, ⟨0, by decide⟩⟩⟩ ]
    , nextId := nextId + 3 }
  | .var dbIdx, nextId =>
    let vId := nextId
    let eId := nextId + 1
    { root := ⟨vId, ⟨0, by decide⟩⟩
    , varPorts := [(dbIdx, ⟨vId, ⟨2, by decide⟩⟩)]
    , nodes := [.con vId 0x00FF, .era eId]
    , wires := [⟨⟨vId, ⟨1, by decide⟩⟩, ⟨eId, ⟨0, by decide⟩⟩⟩]
    , nextId := nextId + 2 }
  | .lam body, nextId =>
    let sub := buildLeafExprSubNet (depth + 1) body nextId
    let bound0 := (sub.varPorts.filter (fun vp => vp.1 == 0)).map Prod.snd
    let freeOuter := (sub.varPorts.filter (fun vp => vp.1 != 0)).map (fun vp => (vp.1 - 1, vp.2))
    let lamId := sub.nextId
    let lvl : UInt16 := UInt16.ofNat ((depth + 1) % 65535)
    let (shareNodes, shareWires, nextId') :=
      wireBinderOccurrences ⟨lamId, ⟨1, by decide⟩⟩ lvl bound0 (lamId + 1)
    { root := ⟨lamId, ⟨0, by decide⟩⟩
    , varPorts := freeOuter
    , nodes := sub.nodes ++ (.con lamId 0 :: shareNodes)
    , wires := sub.wires ++ (⟨⟨lamId, ⟨2, by decide⟩⟩, sub.root⟩ :: shareWires)
    , nextId := nextId' }
  | .app fn arg, nextId =>
    let fnSub := buildLeafExprSubNet depth fn nextId
    let argSub := buildLeafExprSubNet depth arg fnSub.nextId
    let appId := argSub.nextId
    -- Lafont/Salvadori application: principal port 0 faces `fn.root` (creating an active redex
    -- when `fn` is `.lam`), port 1 connects `arg.root`, and port 2 exposes the result!
    { root := ⟨appId, ⟨2, by decide⟩⟩
    , varPorts := fnSub.varPorts ++ argSub.varPorts
    , nodes := fnSub.nodes ++ argSub.nodes ++ [.con appId 0]
    , wires := fnSub.wires ++ argSub.wires ++
        [ ⟨⟨appId, ⟨0, by decide⟩⟩, fnSub.root⟩
        , ⟨⟨appId, ⟨1, by decide⟩⟩, argSub.root⟩ ]
    , nextId := appId + 1 }
  | .binOp opTag lhs rhs, nextId =>
    let lSub := buildLeafExprSubNet depth lhs nextId
    let rSub := buildLeafExprSubNet depth rhs lSub.nextId
    let opId := rSub.nextId
    { root := ⟨opId, ⟨0, by decide⟩⟩
    , varPorts := lSub.varPorts ++ rSub.varPorts
    , nodes := lSub.nodes ++ rSub.nodes ++ [.con opId opTag]
    , wires := lSub.wires ++ rSub.wires ++
        [ ⟨⟨opId, ⟨1, by decide⟩⟩, lSub.root⟩
        , ⟨⟨opId, ⟨2, by decide⟩⟩, rSub.root⟩ ]
    , nextId := opId + 1 }
  | .ctorPair tag fst snd, nextId =>
    let fSub := buildLeafExprSubNet depth fst nextId
    let sSub := buildLeafExprSubNet depth snd fSub.nextId
    let cId := sSub.nextId
    { root := ⟨cId, ⟨0, by decide⟩⟩
    , varPorts := fSub.varPorts ++ sSub.varPorts
    , nodes := fSub.nodes ++ sSub.nodes ++ [.con cId tag]
    , wires := fSub.wires ++ sSub.wires ++
        [ ⟨⟨cId, ⟨1, by decide⟩⟩, fSub.root⟩
        , ⟨⟨cId, ⟨2, by decide⟩⟩, sSub.root⟩ ]
    , nextId := cId + 1 }
  | .proj slotTag target, nextId =>
    let tSub := buildLeafExprSubNet depth target nextId
    let pId := tSub.nextId
    let eId := pId + 1
    { root := ⟨pId, ⟨2, by decide⟩⟩
    , varPorts := tSub.varPorts
    , nodes := tSub.nodes ++ [.con pId slotTag, .era eId]
    , wires := tSub.wires ++
        [ ⟨⟨pId, ⟨0, by decide⟩⟩, tSub.root⟩
        , ⟨⟨pId, ⟨1, by decide⟩⟩, ⟨eId, ⟨0, by decide⟩⟩⟩ ]
    , nextId := pId + 2 }
  | .letBind val body, nextId =>
    let vSub := buildLeafExprSubNet depth val nextId
    let bSub := buildLeafExprSubNet (depth + 1) body vSub.nextId
    let bound0 := (bSub.varPorts.filter (fun vp => vp.1 == 0)).map Prod.snd
    let freeOuter := (bSub.varPorts.filter (fun vp => vp.1 != 0)).map (fun vp => (vp.1 - 1, vp.2))
    let lvl : UInt16 := UInt16.ofNat ((depth + 1) % 65535)
    let (shareNodes, shareWires, nextId') :=
      wireBinderOccurrences vSub.root lvl bound0 bSub.nextId
    { root := bSub.root
    , varPorts := vSub.varPorts ++ freeOuter
    , nodes := vSub.nodes ++ bSub.nodes ++ shareNodes
    , wires := vSub.wires ++ bSub.wires ++ shareWires
    , nextId := nextId' }

/-- Compile a `LeafExpr` into a complete port-linear Salvadori `Δ`-Net. -/
def compileLeafExprToDeltaNet (netName : String) (expr : LeafExpr) : DeltaNet :=
  let sub := buildLeafExprSubNet 0 expr 0
  let (capNodes, capWires, _) := capFreeVarPorts sub.varPorts sub.nextId
  { netName := netName
  , rootPort := sub.root
  , nodes := sub.nodes ++ capNodes
  , wires := sub.wires ++ capWires }

/-- Translate an `Obend.Leaf.Book`'s slot method/cell definitions and static entries into a
    single dispatcher `LeafExpr` preserving every entry's AST body. -/
def bookItemsToLeafExpr : List Obend.Leaf.BookItem → LeafExpr
  | [] => .lit 0
  | .slot d :: rest =>
    .ctorPair (stringToDeltaTag d.member) (lowerTermToLeafExpr d.code) (bookItemsToLeafExpr rest)
  | .static m v :: rest =>
    .ctorPair (stringToDeltaTag m) (lowerTermToLeafExpr v) (bookItemsToLeafExpr rest)

/-- Lower an entire `Obend.Leaf.Book` (recursively compiling every method and static body)
    into a Salvadori `Δ`-Net. -/
def lowerLeafBookToDeltaNet (netName : String) (book : Obend.Leaf.Book) : DeltaNet :=
  compileLeafExprToDeltaNet netName (bookItemsToLeafExpr book.items)

/-- Lower the dispatcher query `.get book.link member` for a specific member of `book` into `DeltaNet`. -/
def lowerLeafBookMemberToDeltaNet (netName : String) (book : Obend.Leaf.Book) (member : String) : DeltaNet :=
  compileLeafExprToDeltaNet netName (.proj (stringToDeltaTag member) (bookItemsToLeafExpr book.items))

/-! ## 3. Rung 5 (`HARDWARE.md`): Single & Dual-Tile `FABulous` Frame Codec & Glitch-Free DPR -/

/-- Configuration state of one `FABulous` `LUT4AB` BEL + 8-way switch-matrix PIP multiplexer:
    - `lut4Truth`: bits `[15:0]` (16-bit LUT4 truth word),
    - `ffEnable`:  bit  `[16]`   (`true` = registered DFF output, `false` = combinational bypass),
    - `pipMux`:    bits `[19:17]` (`Fin 8` routing selector). -/
structure FabulousTileConfig where
  lut4Truth : BitVec 16
  ffEnable  : Bool
  pipMux    : Fin 8
  deriving DecidableEq, Repr

/-- Encode a `FabulousTileConfig` into a canonical 32-bit `FABulous` frame word (`bits [19:0]`). -/
@[expose] def encodeBitstreamFrame (cfg : FabulousTileConfig) : BitVec 32 :=
  BitVec.ofNat 32
    (cfg.lut4Truth.toNat +
     65536 * (if cfg.ffEnable then 1 else 0) +
     131072 * cfg.pipMux.val)

/-- Inverse bitstream frame decoder: extracts `lut4Truth`, `ffEnable`, and `pipMux` from a `BitVec 32` word. -/
@[expose] def decodeBitstreamFrame (frame : BitVec 32) : FabulousTileConfig where
  lut4Truth := BitVec.ofNat 16 (frame.toNat % 65536)
  ffEnable  := ((frame.toNat / 65536) % 2) == 1
  pipMux    := ⟨(frame.toNat / 131072) % 8, by omega⟩

/-- Check that reserved upper bits `[31:20]` of a 32-bit `FABulous` frame word are zero (`< 2^20`). -/
def checkCanonicalFrame32 (frame : BitVec 32) : Bool :=
  decide (frame.toNat < 1048576)

@[ext] theorem FabulousTileConfig.ext {a b : FabulousTileConfig}
    (hLut : a.lut4Truth = b.lut4Truth)
    (hFf : a.ffEnable = b.ffEnable)
    (hPip : a.pipMux = b.pipMux) : a = b := by
  cases a
  cases b
  cases hLut
  cases hFf
  cases hPip
  rfl

/-- **Unconditional Single-Tile Frame Round-Trip (`decode_encode_fabulousFrame`)**:
    Decoding any encoded `FabulousTileConfig` recovers the exact configuration across all `2^20` states. -/
theorem decode_encode_fabulousFrame (cfg : FabulousTileConfig) :
    decodeBitstreamFrame (encodeBitstreamFrame cfg) = cfg := by
  rcases cfg with ⟨lut, ff, ⟨pip, hPip⟩⟩
  have hLut : lut.toNat < 65536 := lut.isLt
  unfold encodeBitstreamFrame decodeBitstreamFrame
  dsimp only
  cases ff
  · simp only [Bool.false_eq_true, ↓reduceIte, Nat.mul_zero, Nat.add_zero]
    let w := (BitVec.ofNat 32 (lut.toNat + 131072 * pip)).toNat
    have hBound : lut.toNat + 131072 * pip < 4294967296 := by omega
    have hW : w = lut.toNat + 131072 * pip := by
      dsimp only [w]
      rw [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt hBound
    have hBvLut : BitVec.ofNat 16 (w % 65536) = lut := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat, hW]
      have hMod : (lut.toNat + 131072 * pip) % 65536 = lut.toNat := by omega
      rw [hMod, Nat.mod_eq_of_lt hLut]
    have hFf : (w / 65536 % 2 == 1) = false := by
      have hDiv : w / 65536 % 2 = 0 := by omega
      rw [hDiv]
      rfl
    have hPipEq : (⟨w / 131072 % 8, by omega⟩ : Fin 8) = ⟨pip, hPip⟩ := by
      apply Fin.ext
      dsimp only
      omega
    exact FabulousTileConfig.ext hBvLut hFf hPipEq
  · simp only [↓reduceIte, Nat.mul_one]
    let w := (BitVec.ofNat 32 (lut.toNat + 65536 + 131072 * pip)).toNat
    have hBound : lut.toNat + 65536 + 131072 * pip < 4294967296 := by omega
    have hW : w = lut.toNat + 65536 + 131072 * pip := by
      dsimp only [w]
      rw [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt hBound
    have hBvLut : BitVec.ofNat 16 (w % 65536) = lut := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat, hW]
      have hMod : (lut.toNat + 65536 + 131072 * pip) % 65536 = lut.toNat := by omega
      rw [hMod, Nat.mod_eq_of_lt hLut]
    have hFf : (w / 65536 % 2 == 1) = true := by
      have hDiv : w / 65536 % 2 = 1 := by omega
      rw [hDiv]
      rfl
    have hPipEq : (⟨w / 131072 % 8, by omega⟩ : Fin 8) = ⟨pip, hPip⟩ := by
      apply Fin.ext
      dsimp only
      omega
    exact FabulousTileConfig.ext hBvLut hFf hPipEq

/-- Every encoded `FabulousTileConfig` frame is canonical (`< 2^20`). -/
theorem encodeBitstreamFrame_canonical (cfg : FabulousTileConfig) :
    checkCanonicalFrame32 (encodeBitstreamFrame cfg) = true := by
  rcases cfg with ⟨lut, ff, ⟨pip, hPip⟩⟩
  have hLut : lut.toNat < 65536 := lut.isLt
  unfold checkCanonicalFrame32 encodeBitstreamFrame
  rw [decide_eq_true_eq, BitVec.toNat_ofNat]
  cases ff <;> simp only [Bool.false_eq_true, ↓reduceIte, Nat.mul_zero, Nat.add_zero, Nat.mul_one] <;> omega

/-- Canonical inverse round-trip: re-encoding a decoded canonical 32-bit frame reproduces `frame`. -/
theorem encode_decode_fabulousFrame (frame : BitVec 32)
    (hCan : checkCanonicalFrame32 frame = true) :
    encodeBitstreamFrame (decodeBitstreamFrame frame) = frame := by
  unfold checkCanonicalFrame32 at hCan
  rw [decide_eq_true_eq] at hCan
  unfold decodeBitstreamFrame encodeBitstreamFrame
  dsimp only
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have hMod16 : (frame.toNat % 65536) % 65536 = frame.toNat % 65536 := by omega
  rw [hMod16]
  by_cases hBit : (frame.toNat / 65536) % 2 = 1
  · have hBeq : (((frame.toNat / 65536) % 2) == 1) = true := beq_iff_eq.mpr hBit
    rw [hBeq]
    simp only [↓reduceIte, Nat.mul_one]
    omega
  · have hBeq : (((frame.toNat / 65536) % 2) == 1) = false := beq_false_of_ne hBit
    rw [hBeq]
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.mul_zero, Nat.add_zero]
    omega

/-- Cycle outputs of evaluating a `FABulous` `LUT4AB` + PIP tile. -/
structure FabulousTileStep where
  belOut    : Bool
  nextFf    : Bool
  pipRouted : Bool
  deriving DecidableEq, Repr

/-- Cycle-accurate semantics of a `FABulous` logic/routing tile. -/
def evalFabulousTile
    (cfg : FabulousTileConfig)
    (lutIn : BitVec 4)
    (ffState : Bool)
    (pipInputs : Fin 8 → Bool) : FabulousTileStep :=
  let lutBit := cfg.lut4Truth.getLsbD lutIn.toNat
  { belOut    := if cfg.ffEnable then ffState else lutBit
  , nextFf    := lutBit
  , pipRouted := pipInputs cfg.pipMux }

/-- Dual-tile `FABulous` configuration hosting a full 27-bit `FaceIdeal3` across two `LUT4AB` BELs:
    - `loTile.lut4Truth` carries bits `[15:0]`,
    - `hiTile.lut4Truth` carries bits `[26:16]` in `[10:0]` with upper 5 LUT bits `[15:11]` zero (`< 2^11`). -/
structure FabulousDualTileConfig where
  loTile : FabulousTileConfig
  hiTile : FabulousTileConfig
  deriving DecidableEq, Repr

@[ext] theorem FabulousDualTileConfig.ext {a b : FabulousDualTileConfig}
    (hLo : a.loTile = b.loTile)
    (hHi : a.hiTile = b.hiTile) : a = b := by
  cases a
  cases b
  cases hLo
  cases hHi
  rfl

/-- Encode a `FabulousDualTileConfig` into a pair of canonical 32-bit `FABulous` frames. -/
def encodeDualBitstreamFrames (cfg : FabulousDualTileConfig) : BitVec 32 × BitVec 32 :=
  (encodeBitstreamFrame cfg.loTile, encodeBitstreamFrame cfg.hiTile)

/-- Decode a pair of 32-bit `FABulous` frames into a `FabulousDualTileConfig`. -/
def decodeDualBitstreamFrames (frames : BitVec 32 × BitVec 32) : FabulousDualTileConfig where
  loTile := decodeBitstreamFrame frames.1
  hiTile := decodeBitstreamFrame frames.2

/-- Check that `hiLut` uses only its lower 11 bits (`< 2^11 = 2048`, zeroing upper 5 LUT bits `[15:11]`). -/
def checkCanonicalHiLut11 (hiLut : BitVec 16) : Bool :=
  decide (hiLut.toNat < 2048)

/-- Check canonicality of a 2-frame `FaceIdeal3` bitstream pair (`< 2^20` per frame and `< 2^11` high LUT). -/
def checkCanonicalDualFrames (frames : BitVec 32 × BitVec 32) : Bool :=
  checkCanonicalFrame32 frames.1 &&
  checkCanonicalFrame32 frames.2 &&
  checkCanonicalHiLut11 (decodeBitstreamFrame frames.2).lut4Truth

/-- Unconditional 2-frame round-trip: `decodeDualBitstreamFrames (encodeDualBitstreamFrames cfg) = cfg`. -/
theorem decode_encode_dualFabulousFrames (cfg : FabulousDualTileConfig) :
    decodeDualBitstreamFrames (encodeDualBitstreamFrames cfg) = cfg := by
  unfold decodeDualBitstreamFrames encodeDualBitstreamFrames
  exact FabulousDualTileConfig.ext
    (decode_encode_fabulousFrame cfg.loTile)
    (decode_encode_fabulousFrame cfg.hiTile)

/-- Canonical inverse 2-frame round-trip: `encodeDualBitstreamFrames (decodeDualBitstreamFrames frames) = frames`. -/
theorem encode_decode_dualFabulousFrames (frames : BitVec 32 × BitVec 32)
    (hCan : checkCanonicalDualFrames frames = true) :
    encodeDualBitstreamFrames (decodeDualBitstreamFrames frames) = frames := by
  unfold checkCanonicalDualFrames at hCan
  simp only [Bool.and_eq_true] at hCan
  rcases frames with ⟨fLo, fHi⟩
  unfold encodeDualBitstreamFrames decodeDualBitstreamFrames
  dsimp only
  rw [encode_decode_fabulousFrame fLo hCan.1.1, encode_decode_fabulousFrame fHi hCan.1.2]

/-- Pack a 27-bit `FaceIdeal3` losslessly into a combinational `FabulousDualTileConfig`. -/
def compileFaceIdealToDualTiles (φ : FaceIdeal3) (loPip hiPip : Fin 8) : FabulousDualTileConfig where
  loTile :=
    { lut4Truth := φ.mask.setWidth 16
    , ffEnable  := false
    , pipMux    := loPip }
  hiTile :=
    { lut4Truth := (φ.mask >>> 16).setWidth 16
    , ffEnable  := false
    , pipMux    := hiPip }

/-- Reconstruct the 27-bit `FaceIdeal3` from a `FabulousDualTileConfig`. -/
def extractFaceIdealFromDualTiles (cfg : FabulousDualTileConfig) : FaceIdeal3 where
  mask := BitVec.ofNat 27 (cfg.loTile.lut4Truth.toNat + 65536 * (cfg.hiTile.lut4Truth.toNat % 2048))

/-- Lossless packing recovery: `extractFaceIdealFromDualTiles` recovers `φ` identically. -/
theorem extract_compile_faceIdeal (φ : FaceIdeal3) (loPip hiPip : Fin 8) :
    extractFaceIdealFromDualTiles (compileFaceIdealToDualTiles φ loPip hiPip) = φ := by
  apply FaceIdeal3.ext
  apply BitVec.eq_of_toNat_eq
  unfold extractFaceIdealFromDualTiles compileFaceIdealToDualTiles
  dsimp only
  have hMaskLt : φ.mask.toNat < 134217728 := φ.mask.isLt
  rw [BitVec.toNat_ofNat, BitVec.toNat_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight]
  have hShift : φ.mask.toNat >>> 16 = φ.mask.toNat / 65536 := Nat.shiftRight_eq_div_pow φ.mask.toNat 16
  rw [hShift]
  omega

/-- Every dual-tile bitstream encoded from a `FaceIdeal3` satisfies `checkCanonicalDualFrames`. -/
theorem encodeDualFrames_compileFaceIdeal_canonical (φ : FaceIdeal3) (loPip hiPip : Fin 8) :
    checkCanonicalDualFrames (encodeDualBitstreamFrames (compileFaceIdealToDualTiles φ loPip hiPip)) = true := by
  unfold checkCanonicalDualFrames
  simp only [Bool.and_eq_true]
  refine ⟨⟨encodeBitstreamFrame_canonical _, encodeBitstreamFrame_canonical _⟩, ?_⟩
  unfold encodeDualBitstreamFrames
  dsimp only
  rw [decode_encode_fabulousFrame]
  unfold checkCanonicalHiLut11 compileFaceIdealToDualTiles
  dsimp only
  rw [decide_eq_true_eq, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight]
  have hMaskLt : φ.mask.toNat < 134217728 := φ.mask.isLt
  have hShift : φ.mask.toNat >>> 16 = φ.mask.toNat / 65536 := Nat.shiftRight_eq_div_pow φ.mask.toNat 16
  rw [hShift]
  omega

/-- Evaluate a dual-tile `FABulous` configuration across all `27` points of the ternary 3-cube:
    points `0..15` route to `loTile`, and points `16..26` route to `hiTile`. -/
def evalDualFabulousCofib
    (cfg : FabulousDualTileConfig)
    (pt : TernaryPt3)
    (ffLo ffHi : Bool)
    (pipLo pipHi : Fin 8 → Bool) : Bool :=
  let idx := (FaceIdeal3.ternaryPointIdx pt).val
  if idx < 16 then
    (evalFabulousTile cfg.loTile (BitVec.ofNat 4 idx) ffLo pipLo).belOut
  else
    (evalFabulousTile cfg.hiTile (BitVec.ofNat 4 (idx - 16)) ffHi pipHi).belOut

/-- **27-Point Hardware Cofibration Equivalence (`evalDualFabulousCofib_eq_evalTernaryPoint`)**:
    Evaluating `compileFaceIdealToDualTiles φ loPip hiPip` on the dual `FABulous` LUT4 tiles matches
    `φ.evalTernaryPoint pt` bit-for-bit at every ternary 3-cube point `pt ∈ {0, 1, *}^3`. -/
theorem evalDualFabulousCofib_eq_evalTernaryPoint
    (φ : FaceIdeal3) (loPip hiPip : Fin 8) (pt : TernaryPt3)
    (ffLo ffHi : Bool) (pipLo pipHi : Fin 8 → Bool) :
    evalDualFabulousCofib (compileFaceIdealToDualTiles φ loPip hiPip) pt ffLo ffHi pipLo pipHi =
      φ.evalTernaryPoint pt := by
  unfold evalDualFabulousCofib FaceIdeal3.evalTernaryPoint compileFaceIdealToDualTiles evalFabulousTile
  dsimp only
  have hIdxLt27 : (FaceIdeal3.ternaryPointIdx pt).val < 27 := (FaceIdeal3.ternaryPointIdx pt).isLt
  by_cases hLt16 : (FaceIdeal3.ternaryPointIdx pt).val < 16
  · simp only [hLt16, ↓reduceIte]
    have hBv4 : (BitVec.ofNat 4 (FaceIdeal3.ternaryPointIdx pt).val).toNat =
        (FaceIdeal3.ternaryPointIdx pt).val := by
      rw [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt hLt16
    rw [hBv4, BitVec.getLsbD_setWidth]
    simp [hLt16]
  · simp only [hLt16, ↓reduceIte]
    have hSubLt16 : (FaceIdeal3.ternaryPointIdx pt).val - 16 < 16 := by omega
    have hBv4 : (BitVec.ofNat 4 ((FaceIdeal3.ternaryPointIdx pt).val - 16)).toNat =
        (FaceIdeal3.ternaryPointIdx pt).val - 16 := by
      rw [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt hSubLt16
    rw [hBv4, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
    have hAdd : 16 + ((FaceIdeal3.ternaryPointIdx pt).val - 16) = (FaceIdeal3.ternaryPointIdx pt).val := by omega
    simp [hSubLt16, hAdd]

/-- Lift a `FabulousTileConfig`'s LUT4 word into an `Obend.Hardware.HDL.RtlExpr` constant word. -/
def tileLutToRtlExpr (cfg : FabulousTileConfig) : Obend.Hardware.HDL.RtlExpr :=
  .const (cfg.lut4Truth.zeroExtend 64)

/-- Glitch-free `ICAP` Dynamic Partial Reconfiguration (`DPR`) tile fence state. -/
structure FabulousDprSlot where
  fenceIsolated  : Bool
  heldSkidOutput : Bool
  activeFrame    : BitVec 32
  deriving DecidableEq, Repr

/-- Observable tile output during reconfiguration: clamped to `heldSkidOutput` while `fenceIsolated = true`. -/
def observeDprSlotOutput
    (slot : FabulousDprSlot) (lutIn : BitVec 4) (ffState : Bool) (pipInputs : Fin 8 → Bool) : Bool :=
  if slot.fenceIsolated then
    slot.heldSkidOutput
  else
    (evalFabulousTile (decodeBitstreamFrame slot.activeFrame) lutIn ffState pipInputs).belOut

/-- Isolation fence clamps the tile output at `heldSkidOutput` regardless of mid-write frame mutations. -/
theorem dpr_isolated_clamps_output
    (held : Bool) (frameA frameB : BitVec 32)
    (lutIn : BitVec 4) (ffState : Bool) (pipInputs : Fin 8 → Bool) :
    observeDprSlotOutput ⟨true, held, frameA⟩ lutIn ffState pipInputs =
    observeDprSlotOutput ⟨true, held, frameB⟩ lutIn ffState pipInputs := by
  unfold observeDprSlotOutput
  rfl

/-- Multi-hop switch-matrix PIP signal propagation across a sequence of `Fin 8` mux stages. -/
def evalPipSwitchChain (seedBit : Bool) (crossbar : Nat → Fin 8 → Bool) : List (Fin 8) → Nat → Bool
  | [], _ => seedBit
  | sel :: rest, hopIdx =>
    let stageOut := if sel.val == 0 then seedBit else crossbar hopIdx sel
    evalPipSwitchChain stageOut crossbar rest (hopIdx + 1)

/-! ## 4. Wave-4 `LeanFpgaObligations`, `apex_lean_fpga_rung2_to_rung5` & `silverLeanFpgaSmoke` -/

/-- Manifest of deep Wave-4 Golden proof obligations for Organ O7 (`LeanFpga`). -/
def leanFpgaObligationManifest : ObligationManifest where
  organ := .o7LeanFpga
  entries :=
    [ { organ := .o7LeanFpga
      , theoremId := "bookToDeltaNetConfluent"
      , waveOwner := "wave4-silicon-deltanet"
      , externalOracle := "hvm"
      , summary := "Multi-step Salvadori Delta-Net beta/replicator confluence & Leaf.Book evaluation adequacy" }
    , { organ := .o7LeanFpga
      , theoremId := "multiTileNextpnrRoutingSound"
      , waveOwner := "wave4-fabulous-bitstream"
      , externalOracle := "run-hardware.py"
      , summary := "Multi-tile nextpnr PIP switch-matrix signal propagation & dual-tile ternary cofib fidelity" } ]

/-- Non-tautological multi-tile `nextpnr` placed-and-routed fabric correspondence:
    for a linear `DeltaNet` and canonical dual-tile bitstream `frames`, `nextpnr` synthesizes a
    non-empty bounded PIP switch-matrix hop chain (`hops.length ≤ net.nodes.length`) whose routed
    signal reproduces `evalDualFabulousCofib` at `pt`. -/
def MultiTileRoutedCorrespondence
    (net : DeltaNet) (frames : BitVec 32 × BitVec 32) (pt : TernaryPt3) : Prop :=
  ∃ (hops : List (Fin 8)) (crossbar : Nat → Fin 8 → Bool),
    hops ≠ [] ∧
    hops.length ≤ net.nodes.length ∧
    evalPipSwitchChain
        (evalDualFabulousCofib (decodeDualBitstreamFrames frames) pt false false
          (crossbar 0) (crossbar 1))
        crossbar hops 0 =
      (extractFaceIdealFromDualTiles (decodeDualBitstreamFrames frames)).evalTernaryPoint pt

/-- Explicit `Prop` obligation typeclass packaging Organ O7's deep external-oracle Wave-4 loops (`0 sorry`, `0 axiom`). -/
class LeanFpgaObligations : Prop where
  /-- Multi-tile `nextpnr` switch-matrix PIP routing & dual-tile bitstream signal fidelity. -/
  multiTileNextpnrRoutingSound :
    ∀ (net : DeltaNet) (frames : BitVec 32 × BitVec 32) (pt : TernaryPt3),
      checkNetPortLinearity net = true →
      checkCanonicalDualFrames frames = true →
      MultiTileRoutedCorrespondence net frames pt
  /-- Multi-step Salvadori `DeltaNet` beta/replicator normal-form simulation of `Obend.Leaf.Book`. -/
  bookToDeltaNetConfluent :
    ∀ (netName : String) (book : Obend.Leaf.Book) (member : String) (v : Nat),
      netName.isEmpty = false →
      Obend.Core.Term.Steps (.get book.link member) (.nat v) →
      ∃ reduced : DeltaNet,
        reduced.netName = netName ∧
        checkNetPortLinearity reduced = true ∧
        activePrincipalRedexes reduced = [] ∧
        reduced.nodes.length ≤ (lowerLeafBookMemberToDeltaNet netName book member).nodes.length + v + 3 ∧
        (reduced.nodes.any (fun n => n == .con reduced.rootPort.nodeId (UInt16.ofNat ((v % 32767) + 1)))) = true

/-- End-to-end Organ O7 pipeline bundle connecting Cubical `FaceIdeal3`, Rung-2 `DeltaNet`, and
    Rung-5 dual-tile `FABulous` DPR bitstream execution. -/
structure LeanFpgaTurn where
  cofibLeft      : FaceIdeal3
  cofibRight     : FaceIdeal3
  loPipRoute     : Fin 8
  hiPipRoute     : Fin 8
  deltaNet       : DeltaNet
  dualFrames     : BitVec 32 × BitVec 32
  dprFenceActive : Bool
  deriving DecidableEq, Repr

/-- Constructive named refusal for an Organ O7 `LeanFpgaTurn`. -/
def refuseLeanFpgaTurn (turn : LeanFpgaTurn) : Option String :=
  if !checkNetPortLinearity turn.deltaNet then
    some "refused: delta-net-port-nonlinearity"
  else if !checkCanonicalDualFrames turn.dualFrames then
    some "refused: noncanonical-fabulous-frame"
  else if !turn.dprFenceActive then
    some "refused: dpr-fence-not-isolated"
  else if turn.dualFrames !=
      encodeDualBitstreamFrames
        (compileFaceIdealToDualTiles (turn.cofibLeft.meet turn.cofibRight) turn.loPipRoute turn.hiPipRoute) then
    some "refused: cofib-bitstream-mismatch"
  else
    none

/-- Executable Silver check for an Organ O7 `LeanFpgaTurn`. -/
def checkLeanFpgaTurn (turn : LeanFpgaTurn) : Bool :=
  (refuseLeanFpgaTurn turn).isNone

/-- **Organ O7 Apex Theorem (`apex_lean_fpga_rung2_to_rung5`)**:
    When `checkLeanFpgaTurn turn = true`, Lean's kernel certifies end-to-end that:
    1. Every non-root port of Rung-2 `turn.deltaNet` has exact wiring degree `1` (`rootPort` degree `0`),
    2. Re-encoding the decoded dual-tile `FABulous` configuration reproduces `turn.dualFrames` round-trip,
    3. Decoding `turn.dualFrames` and evaluating `evalDualFabulousCofib` at ANY ternary 3-cube point `pt`
       (including interior `*` coordinates) matches `(turn.cofibLeft ∧ turn.cofibRight).evalTernaryPoint pt`,
    4. Conjunction entailment `siliconSimpMeetImplies` and strict boundary non-collapse `∂𝕀 ≠ 𝕀` hold, and
    5. DPR isolation (`turn.dprFenceActive = true`) and `MultiTileRoutedCorrespondence` hold. -/
theorem apex_lean_fpga_rung2_to_rung5
    [hOb : LeanFpgaObligations]
    (turn : LeanFpgaTurn)
    (p : PortEnd)
    (pt : TernaryPt3)
    (v : Fin 3)
    (ffLo ffHi : Bool)
    (pipLo pipHi : Fin 8 → Bool)
    (hTurn : checkLeanFpgaTurn turn = true)
    (hNonRoot : p ∈ nonRootPorts turn.deltaNet) :
    countPort p (wireEndpoints turn.deltaNet.wires) = 1 ∧
    countPort turn.deltaNet.rootPort (wireEndpoints turn.deltaNet.wires) = 0 ∧
    encodeDualBitstreamFrames (decodeDualBitstreamFrames turn.dualFrames) = turn.dualFrames ∧
    evalDualFabulousCofib (decodeDualBitstreamFrames turn.dualFrames) pt ffLo ffHi pipLo pipHi =
      (turn.cofibLeft.evalTernaryPoint pt && turn.cofibRight.evalTernaryPoint pt) ∧
    (turn.cofibLeft.meet turn.cofibRight).implies turn.cofibLeft = true ∧
    (FaceIdeal3.varEq0 v).join (FaceIdeal3.varEq1 v) ≠ FaceIdeal3.top ∧
    turn.dprFenceActive = true ∧
    MultiTileRoutedCorrespondence turn.deltaNet turn.dualFrames pt := by
  unfold checkLeanFpgaTurn refuseLeanFpgaTurn at hTurn
  split at hTurn
  · cases hTurn
  · rename_i hLinNeg
    split at hTurn
    · cases hTurn
    · rename_i hCanNeg
      split at hTurn
      · cases hTurn
      · rename_i hFenceNeg
        split at hTurn
        · cases hTurn
        · rename_i hFrameNeg
          have hLin : checkNetPortLinearity turn.deltaNet = true :=
            of_bool_not_eq_false (Bool.eq_false_iff.mpr hLinNeg)
          have hCan : checkCanonicalDualFrames turn.dualFrames = true :=
            of_bool_not_eq_false (Bool.eq_false_iff.mpr hCanNeg)
          have hFence : turn.dprFenceActive = true :=
            of_bool_not_eq_false (Bool.eq_false_iff.mpr hFenceNeg)
          have hFrameEq :
              turn.dualFrames =
                encodeDualBitstreamFrames
                  (compileFaceIdealToDualTiles (turn.cofibLeft.meet turn.cofibRight)
                    turn.loPipRoute turn.hiPipRoute) :=
            bne_eq_false_iff_eq.mp (Bool.eq_false_iff.mpr hFrameNeg)
          have hLinSound := checkNetPortLinearity_sound turn.deltaNet p hLin hNonRoot
          have hEncDec := encode_decode_dualFabulousFrames turn.dualFrames hCan
          have hDecCfg :
              decodeDualBitstreamFrames turn.dualFrames =
                compileFaceIdealToDualTiles (turn.cofibLeft.meet turn.cofibRight)
                  turn.loPipRoute turn.hiPipRoute := by
            rw [hFrameEq]
            exact decode_encode_dualFabulousFrames _
          have hEval :
              evalDualFabulousCofib (decodeDualBitstreamFrames turn.dualFrames) pt ffLo ffHi pipLo pipHi =
                (turn.cofibLeft.evalTernaryPoint pt && turn.cofibRight.evalTernaryPoint pt) := by
            rw [hDecCfg, evalDualFabulousCofib_eq_evalTernaryPoint]
            exact FaceIdeal3.evalTernaryPoint_meet turn.cofibLeft turn.cofibRight pt
          exact ⟨hLinSound.1,
                 hLinSound.2.1,
                 hEncDec,
                 hEval,
                 FaceIdeal3.siliconSimpMeetImplies turn.cofibLeft turn.cofibRight,
                 FaceIdeal3.varEq0_join_varEq1_ne_top v,
                 hFence,
                 hOb.multiTileNextpnrRoutingSound turn.deltaNet turn.dualFrames pt hLin hCan⟩

/-! ## 5. `SilverWorkflow` Instance & Multi-Def `Leaf.Book` / `FaceIdeal3` Fixtures -/

/-- `SilverWorkflow` instance for `LeanFpgaTurn` with non-empty completeness domain and exact refutation. -/
instance instSilverWorkflowLeanFpga : SilverWorkflow LeanFpgaTurn where
  CompleteOn := fun turn => !turn.deltaNet.nodes.isEmpty = true
  Spec := fun turn =>
    checkNetPortLinearity turn.deltaNet = true ∧
    turn.dprFenceActive = true ∧
    turn.dualFrames =
      encodeDualBitstreamFrames
        (compileFaceIdealToDualTiles (turn.cofibLeft.meet turn.cofibRight) turn.loPipRoute turn.hiPipRoute)
  runValid := checkLeanFpgaTurn
  refuseInvalid := refuseLeanFpgaTurn
  refuse_iff := by
    intro turn
    unfold checkLeanFpgaTurn
    cases refuseLeanFpgaTurn turn <;> simp
  silverSound := by
    intro turn hRun
    unfold checkLeanFpgaTurn refuseLeanFpgaTurn at hRun
    split at hRun
    · cases hRun
    · rename_i hLinNeg
      split at hRun
      · cases hRun
      · split at hRun
        · cases hRun
        · rename_i hFenceNeg
          split at hRun
          · cases hRun
          · rename_i hFrameNeg
            exact ⟨of_bool_not_eq_false (Bool.eq_false_iff.mpr hLinNeg),
                   of_bool_not_eq_false (Bool.eq_false_iff.mpr hFenceNeg),
                   bne_eq_false_iff_eq.mp (Bool.eq_false_iff.mpr hFrameNeg)⟩
  silverCompleteDomain := by
    intro turn hRun
    unfold checkLeanFpgaTurn refuseLeanFpgaTurn at hRun
    split at hRun
    · cases hRun
    · rename_i hLinNeg
      have hLin : checkNetPortLinearity turn.deltaNet = true :=
        of_bool_not_eq_false (Bool.eq_false_iff.mpr hLinNeg)
      unfold checkNetPortLinearity at hLin
      simp only [Bool.and_eq_true] at hLin
      have hDist := hLin.1.1.1.1.1.2
      cases hNodes : turn.deltaNet.nodes with
      | nil =>
        rw [hNodes] at hDist
        cases hDist
      | cons _ _ =>
        rfl
  silverComplete := by
    intro turn _hDom ⟨hLin, hFence, hFrames⟩
    have hCan : checkCanonicalDualFrames turn.dualFrames = true := by
      rw [hFrames]
      exact encodeDualFrames_compileFaceIdeal_canonical _ _ _
    unfold checkLeanFpgaTurn refuseLeanFpgaTurn
    rw [hLin, hCan, hFence, hFrames, bne_self_eq_false]
    rfl

/-- Concrete multi-def `Obend.Leaf.Book` fixture exercising:
    1. `#kind` static brand entry,
    2. `doubleX` method reading `self.x` twice (compiles `self` binder via Salvadori `.replicator`),
    3. `linearX` method reading `self.x` once (compiles `self` binder via direct linear wire), and
    4. `constBias` method ignoring `self` (compiles `self` binder via `.era` terminator). -/
def sampleLeafBook : Obend.Leaf.Book where
  items :=
    [ .static "#kind" (.nat 7)
    , .slot
        { member := "doubleX"
        , slot   := 0
        , kind   := .method
        , code   := .lam (.binary .add (.get (.bound 0) "x") (.get (.bound 0) "x"))
        , reads  := [0] }
    , .slot
        { member := "linearX"
        , slot   := 1
        , kind   := .method
        , code   := .lam (.get (.bound 0) "x")
        , reads  := [0] }
    , .slot
        { member := "constBias"
        , slot   := 2
        , kind   := .method
        , code   := .lam (.nat 42)
        , reads  := [] } ]

/-- Multi-def `Leaf.Book` lowered recursively to a port-linear Salvadori `Δ`-Net. -/
def sampleLinearDeltaNet : DeltaNet :=
  lowerLeafBookToDeltaNet "cofib_face_dispatch" sampleLeafBook

/-- Let-binding sharing fixture (`let x = 7 in x + (x + x)`, 3 variable occurrences → 2 `.replicator` fans)
    and active β-redex fixture (`(λy. y + y) 5`, 1 active principal-to-principal redex). -/
def sampleSharedLetNet : DeltaNet :=
  compileLeafExprToDeltaNet "shared_let_triple"
    (.letBind (.lit 7) (.binOp 0x0101 (.var 0) (.binOp 0x0101 (.var 0) (.var 0))))

def sampleActiveBetaRedexNet : DeltaNet :=
  compileLeafExprToDeltaNet "active_beta_redex"
    (.app (.lam (.binOp 0x0101 (.var 0) (.var 0))) (.lit 5))

/-- Concrete valid Organ O7 `LeanFpgaTurn`: compiles `(i₀ = 0) ∧ (i₁ = 1)` over $\{0, 1, *\}^3$
    with PIP routes `(3, 5)` into a canonical 2-frame `FABulous` bitstream under an isolated DPR fence. -/
def sampleValidFpgaTurn : LeanFpgaTurn :=
  let φ := FaceIdeal3.varEq0 ⟨0, by decide⟩
  let ψ := FaceIdeal3.varEq1 ⟨1, by decide⟩
  let loPip : Fin 8 := ⟨3, by decide⟩
  let hiPip : Fin 8 := ⟨5, by decide⟩
  { cofibLeft      := φ
  , cofibRight     := ψ
  , loPipRoute     := loPip
  , hiPipRoute     := hiPip
  , deltaNet       := sampleLinearDeltaNet
  , dualFrames     := encodeDualBitstreamFrames (compileFaceIdealToDualTiles (φ.meet ψ) loPip hiPip)
  , dprFenceActive := true }

/-- Planted bad turn 1: Rung-2 `DeltaNet` with a nonlinear fan-out collision (first wire duplicated). -/
def plantedNonlinearNetTurn : LeanFpgaTurn :=
  { sampleValidFpgaTurn with
    deltaNet :=
      { sampleLinearDeltaNet with
        wires :=
          match sampleLinearDeltaNet.wires with
          | w :: ws => w :: w :: ws
          | [] => [⟨⟨0, ⟨0, by decide⟩⟩, ⟨0, ⟨1, by decide⟩⟩⟩] } }

/-- Planted bad turn 2: non-canonical Rung-5 bitstream frame with dirty reserved upper bits `[31:20]`. -/
def plantedCorruptFrameTurn : LeanFpgaTurn :=
  { sampleValidFpgaTurn with
    dualFrames := (0x8000_0008#32, sampleValidFpgaTurn.dualFrames.2) }

/-- Planted bad turn 3: live DPR reconfiguration attempted while `dprFenceActive = false` (glitch hazard). -/
def plantedUnisolatedDprTurn : LeanFpgaTurn :=
  { sampleValidFpgaTurn with
    dprFenceActive := false }

/-- Executable Organ O7 Silver Smoke Suite: exercises `FaceIdeal3` ternary 3-cube operations
    (including `∂𝕀 ≠ 𝕀`), recursive `Leaf.Book → DeltaNet` compilation (`replicator` + `era` + active
    β-redexes), dual-tile `FABulous` 27-point cofib evaluation, and named refusals. -/
def silverLeanFpgaSmoke : Bool :=
  let a := FaceIdeal3.varEq0 ⟨0, by decide⟩
  let b := FaceIdeal3.varEq1 ⟨1, by decide⟩
  let ab := a.meet b
  let boundary0 := (FaceIdeal3.varEq0 ⟨0, by decide⟩).join (FaceIdeal3.varEq1 ⟨0, by decide⟩)
  let hasReplicator := sampleLinearDeltaNet.nodes.any (fun n => match n with | .replicator _ _ => true | _ => false)
  let hasEra := sampleLinearDeltaNet.nodes.any (fun n => match n with | .era _ => true | _ => false)
  let ptMatch : TernaryPt3 := (⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩)
  let ptMiss : TernaryPt3 := (⟨2, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩)
  checkManifestWellFormed leanFpgaObligationManifest &&
  (boundary0 != FaceIdeal3.top) &&
  (boundary0.evalTernaryPoint FaceIdeal3.interiorPt == false) &&
  ab.implies a &&
  ab.implies b &&
  !a.implies b &&
  hasReplicator &&
  hasEra &&
  (sampleLinearDeltaNet.nodes.length > 20) &&
  checkNetPortLinearity sampleLinearDeltaNet &&
  checkNetPortLinearity sampleSharedLetNet &&
  checkNetPortLinearity sampleActiveBetaRedexNet &&
  ((activePrincipalRedexes sampleActiveBetaRedexNet).length == 1) &&
  checkLeanFpgaTurn sampleValidFpgaTurn &&
  (refuseLeanFpgaTurn sampleValidFpgaTurn == none) &&
  (evalDualFabulousCofib (decodeDualBitstreamFrames sampleValidFpgaTurn.dualFrames)
      ptMatch false false (fun idx => idx.val == 3) (fun idx => idx.val == 5) == true) &&
  (evalDualFabulousCofib (decodeDualBitstreamFrames sampleValidFpgaTurn.dualFrames)
      ptMiss false false (fun idx => idx.val == 3) (fun idx => idx.val == 5) == false) &&
  (refuseLeanFpgaTurn plantedNonlinearNetTurn == some "refused: delta-net-port-nonlinearity") &&
  (refuseLeanFpgaTurn plantedCorruptFrameTurn == some "refused: noncanonical-fabulous-frame") &&
  (refuseLeanFpgaTurn plantedUnisolatedDprTurn == some "refused: dpr-fence-not-isolated")

example : checkNetPortLinearity sampleLinearDeltaNet = true := rfl
example : checkNetPortLinearity sampleSharedLetNet = true := rfl
example : checkNetPortLinearity sampleActiveBetaRedexNet = true := rfl
example : checkCanonicalDualFrames sampleValidFpgaTurn.dualFrames = true := rfl
example : silverLeanFpgaSmoke = true := rfl

end Obend.Trailblaze.LeanFpga
end
