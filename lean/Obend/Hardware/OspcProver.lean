module
/-
# Obend.Hardware.OspcProver — 4-Tile Hypercube ($Q_2$) Verified Symbolic Proof-Carrying Hardware Prover
Synthesizable 4-tile hardware prover architecture in `Obend.Hardware.HDL` (`RtlMemModule` +
`SyncRamSpec`) combining symbolic theorem-proving engines with lockstep 2-hop hypercube ($Q_2$)
Sumcheck & canonical Merkle folding and 256-bit 4-limb verifiable receipts:
1. Ternary 4-cube `FaceIdeal4` (`{0, 1, *}^4`, 81 bits = `BitVec 64 × BitVec 17`, `∂𝕀⁴ ≠ 𝕀⁴`).
2. 4 synthesizable `HDL.RtlMemModule` tiles (`ExprCAM+FaceIdeal4`, `DiscrTreeLUT`, `DeltaNet`,
   `StreamLRAT`) passing `checkRtlMemModuleW`, with Tile 0 RTL simulation and Tile 3 LRAT soundness.
3. 2-stage $Q_2$ XOR-butterfly NoC (`t ^^^ 1` then `t ^^^ 2`) for lockstep Sumcheck AllReduce,
   cross-tile MLE folding (`Multilinear.foldFirstVar`/`mleEval`), and depth-2 Merkle root folding
   (`Obend.Receipt.Merkle.root` + constructive `0 Classical` collision binding).
4. 256-bit 4-limb receipt packing, multi-cycle trace soundness (`ospc_four_tile_prover_multi_cycle_sound`),
   fault-rejection completeness, and inhabited non-tautological `ospcProverJudge`.
-/
public import Obend.Hardware.HDL
public import Obend.Crypto.Multilinear
public import Obend.Crypto.Transcript
public import Obend.Crypto.Sumcheck
public import Obend.Judge.Lrat
public import Obend.Receipt.Merkle
public import Obend.Judge.Class
import all Obend.Hardware.HDL
import all Obend.Crypto.Multilinear
import all Obend.Crypto.Transcript
import all Obend.Crypto.Sumcheck
import all Obend.Receipt.Merkle

public section
namespace Obend.Hardware.OspcProver
open Obend.Hardware.HDL Obend.Crypto Obend.Digest.Cshake256
open Obend.Core.Digest (digestWith admissible_of_lt binds_or_collides deployed preimage)
open Obend.Digest.HashBytes (Hash CollisionAmong be ofBE be_injective length_be)
open Obend.Judge.Lrat (Clause litTrue Sat)
set_option autoImplicit false

/-! ## 1. Ternary 4-Cube `FaceIdeal4` (`{0, 1, *}^4`, 81 bits = `BitVec 64 × BitVec 17`) -/
abbrev TernaryPt4 := Fin 3 × Fin 3 × Fin 3 × Fin 3
def ternaryPt4Idx (p : TernaryPt4) : Fin 81 :=
  ⟨p.1.val + 3 * p.2.1.val + 9 * p.2.2.1.val + 27 * p.2.2.2.val, by omega⟩
def idxToTernaryPt4 (i : Fin 81) : TernaryPt4 :=
  (⟨i.val % 3, by omega⟩, ⟨(i.val / 3) % 3, by omega⟩, ⟨(i.val / 9) % 3, by omega⟩, ⟨(i.val / 27) % 3, by omega⟩)
/-- Open 4-cube interior `(*, *, *, *) = (2, 2, 2, 2)` at index `80` (bit 16 of `hi17`). -/
def interiorPt4 : TernaryPt4 := (⟨2, by omega⟩, ⟨2, by omega⟩, ⟨2, by omega⟩, ⟨2, by omega⟩)
def ptCoord : Fin 4 → TernaryPt4 → Fin 3
  | ⟨0, _⟩, p => p.1 | ⟨1, _⟩, p => p.2.1 | ⟨2, _⟩, p => p.2.2.1 | ⟨3, _⟩, p => p.2.2.2
theorem idxToTernaryPt4_ternaryPt4Idx (p : TernaryPt4) : idxToTernaryPt4 (ternaryPt4Idx p) = p := by
  rcases p with ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩, ⟨d, hd⟩⟩
  simp only [idxToTernaryPt4, ternaryPt4Idx, Prod.mk.injEq, Fin.mk.injEq]; omega
theorem ternaryPt4Idx_idxToTernaryPt4 (i : Fin 81) : ternaryPt4Idx (idxToTernaryPt4 i) = i := by
  rcases i with ⟨v, hv⟩; simp only [ternaryPt4Idx, idxToTernaryPt4, Fin.mk.injEq]; omega
private def natOfBits (P : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => 2 * natOfBits (fun k => P (k + 1)) n + (if P 0 then 1 else 0)
private theorem natOfBits_testBit :
    ∀ (n i : Nat) (P : Nat → Bool), (natOfBits P n).testBit i = (decide (i < n) && P i)
  | 0, i, P => by simp [natOfBits]
  | n + 1, 0, P => by
    simp only [natOfBits, Nat.testBit_zero, show (0 < n + 1) by omega, decide_true, Bool.true_and]
    cases P 0 <;> simp <;> omega
  | n + 1, i + 1, P => by
    have hdiv : (2 * natOfBits (fun k => P (k + 1)) n + (if P 0 then 1 else 0)) / 2 =
        natOfBits (fun k => P (k + 1)) n := by cases P 0 <;> simp <;> omega
    simp only [natOfBits, Nat.testBit_succ, hdiv, natOfBits_testBit n i (fun k => P (k + 1)), Nat.add_lt_add_iff_right]
private def bvOfPred (w : Nat) (P : Nat → Bool) : BitVec w := BitVec.ofNat w (natOfBits P w)
private theorem getLsbD_bvOfPred (w i : Nat) (P : Nat → Bool) :
    (bvOfPred w P).getLsbD i = (decide (i < w) && P i) := by
  unfold bvOfPred; rw [BitVec.getLsbD_ofNat, natOfBits_testBit]; cases decide (i < w) <;> simp
/-- Strictly fixed-width 81-bit cubical face-ideal register pair (`lo64 : BitVec 64`, `hi17 : BitVec 17`). -/
structure FaceIdeal4 where
  lo64 : BitVec 64
  hi17 : BitVec 17
  deriving DecidableEq, Repr

namespace FaceIdeal4
def bot : FaceIdeal4 := ⟨0#64, 0#17⟩
def top : FaceIdeal4 := ⟨BitVec.allOnes 64, BitVec.allOnes 17⟩
def meet (a b : FaceIdeal4) : FaceIdeal4 := ⟨a.lo64 &&& b.lo64, a.hi17 &&& b.hi17⟩
def join (a b : FaceIdeal4) : FaceIdeal4 := ⟨a.lo64 ||| b.lo64, a.hi17 ||| b.hi17⟩
def implies (a b : FaceIdeal4) : Bool := ((a.lo64 &&& ~~~b.lo64) == 0#64) && ((a.hi17 &&& ~~~b.hi17) == 0#17)
def getBit (f : FaceIdeal4) (i : Fin 81) : Bool := if i.val < 64 then f.lo64.getLsbD i.val else f.hi17.getLsbD (i.val - 64)
def containsPt (f : FaceIdeal4) (p : TernaryPt4) : Bool := f.getBit (ternaryPt4Idx p)
def ofPred (P : TernaryPt4 → Bool) : FaceIdeal4 :=
  ⟨bvOfPred 64 (fun k => if h : k < 81 then P (idxToTernaryPt4 ⟨k, h⟩) else false),
   bvOfPred 17 (fun k => if h : 64 + k < 81 then P (idxToTernaryPt4 ⟨64 + k, h⟩) else false)⟩
def varEq0 (v : Fin 4) : FaceIdeal4 := ofPred (fun p => ptCoord v p == ⟨0, by omega⟩)
def varEq1 (v : Fin 4) : FaceIdeal4 := ofPred (fun p => ptCoord v p == ⟨1, by omega⟩)

theorem ext {a b : FaceIdeal4} (hlo : a.lo64 = b.lo64) (hhi : a.hi17 = b.hi17) : a = b := by
  cases a; cases b; simp only at hlo hhi; subst hlo hhi; rfl
theorem containsPt_ofPred (P : TernaryPt4 → Bool) (p : TernaryPt4) : (ofPred P).containsPt p = P p := by
  unfold containsPt getBit ofPred; split
  · rename_i hlt; rw [getLsbD_bvOfPred]; have h81 := (ternaryPt4Idx p).isLt
    simp only [hlt, h81, decide_true, Bool.true_and, ↓reduceDIte]
    have hidx : (⟨(ternaryPt4Idx p).val, h81⟩ : Fin 81) = ternaryPt4Idx p := Fin.ext rfl
    rw [hidx, idxToTernaryPt4_ternaryPt4Idx]
  · rename_i hge; have h81 := (ternaryPt4Idx p).isLt
    have h17 : (ternaryPt4Idx p).val - 64 < 17 := by omega
    have hsum : 64 + ((ternaryPt4Idx p).val - 64) < 81 := by omega
    rw [getLsbD_bvOfPred]; simp only [h17, hsum, decide_true, Bool.true_and, ↓reduceDIte]
    have hidx : (⟨64 + ((ternaryPt4Idx p).val - 64), hsum⟩ : Fin 81) = ternaryPt4Idx p := by apply Fin.ext; dsimp; omega
    rw [hidx, idxToTernaryPt4_ternaryPt4Idx]

theorem containsPt_join (a b : FaceIdeal4) (p : TernaryPt4) :
    (a.join b).containsPt p = (a.containsPt p || b.containsPt p) := by unfold containsPt getBit join; split <;> simp [BitVec.getLsbD_or]
theorem containsPt_meet (a b : FaceIdeal4) (p : TernaryPt4) :
    (a.meet b).containsPt p = (a.containsPt p && b.containsPt p) := by unfold containsPt getBit meet; split <;> simp [BitVec.getLsbD_and]
theorem containsPt_top (p : TernaryPt4) : top.containsPt p = true := by
  unfold containsPt getBit top; split
  · rename_i hlt; rw [BitVec.getLsbD_allOnes]; simp [hlt]
  · rename_i hge; have hlt : (ternaryPt4Idx p).val - 64 < 17 := by have := (ternaryPt4Idx p).isLt; omega
    rw [BitVec.getLsbD_allOnes]; simp [hlt]

theorem meet_comm (a b : FaceIdeal4) : a.meet b = b.meet a := by apply ext <;> exact BitVec.and_comm _ _
theorem meet_assoc (a b c : FaceIdeal4) : (a.meet b).meet c = a.meet (b.meet c) := by apply ext <;> exact BitVec.and_assoc _ _ _
theorem join_comm (a b : FaceIdeal4) : a.join b = b.join a := by apply ext <;> exact BitVec.or_comm _ _
theorem join_assoc (a b c : FaceIdeal4) : (a.join b).join c = a.join (b.join c) := by apply ext <;> exact BitVec.or_assoc _ _ _
theorem meet_top (a : FaceIdeal4) : a.meet top = a := by apply ext <;> exact BitVec.and_allOnes
theorem join_bot (a : FaceIdeal4) : a.join bot = a := by apply ext <;> exact BitVec.or_zero
theorem meet_join_distrib (a b c : FaceIdeal4) : a.meet (b.join c) = (a.meet b).join (a.meet c) := by
  unfold meet join; apply ext <;> (apply BitVec.eq_of_getLsbD_eq; intro i _; simp [BitVec.getLsbD_and, BitVec.getLsbD_or, Bool.and_or_distrib_left])
theorem join_meet_distrib (a b c : FaceIdeal4) : a.join (b.meet c) = (a.join b).meet (a.join c) := by
  unfold meet join; apply ext <;> (apply BitVec.eq_of_getLsbD_eq; intro i _; simp [BitVec.getLsbD_and, BitVec.getLsbD_or, Bool.or_and_distrib_left])
private theorem bv_and_not_eq_zero_iff {w : Nat} (a b : BitVec w) : a &&& ~~~b = 0#w ↔ a &&& b = a := by
  constructor <;> (intro h; apply BitVec.eq_of_getLsbD_eq; intro i hi; have h' := congrArg (fun v => v.getLsbD i) h; simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_zero, hi, decide_true, Bool.true_and] at h' ⊢; cases ha : a.getLsbD i <;> cases hb : b.getLsbD i <;> simp_all)

theorem implies_iff_meet_eq (a b : FaceIdeal4) : a.implies b = true ↔ a.meet b = a := by
  unfold implies meet; simp only [Bool.and_eq_true, beq_iff_eq, bv_and_not_eq_zero_iff]
  exact ⟨fun ⟨h1, h2⟩ => ext h1 h2, fun h => ⟨congrArg FaceIdeal4.lo64 h, congrArg FaceIdeal4.hi17 h⟩⟩
end FaceIdeal4
/-- **Cubical Non-Collapse (`∂𝕀⁴ ≠ 𝕀⁴`)**: `(x_v = 0) ∨ (x_v = 1)` excludes interior `(*,*,*,*)`. -/
theorem faceIdeal4_boundary_ne_top :
    ∀ v : Fin 4, (FaceIdeal4.varEq0 v).join (FaceIdeal4.varEq1 v) ≠ FaceIdeal4.top := by
  intro v heq; have h := congrArg (fun f => f.containsPt interiorPt4) heq
  rw [FaceIdeal4.containsPt_join, FaceIdeal4.containsPt_top] at h
  unfold FaceIdeal4.varEq0 FaceIdeal4.varEq1 at h
  rw [FaceIdeal4.containsPt_ofPred, FaceIdeal4.containsPt_ofPred] at h
  match v with | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩ => simp [ptCoord, interiorPt4] at h

/-! ## 2. Fixed-Width Hardware Structs & 4 Synthesizable `HDL.RtlMemModule` Prover Tiles -/

structure CamSlotWord64 where
  tag8 : BitVec 8
  arity8 : BitVec 8
  lhs16 : BitVec 16
  rhs16 : BitVec 16
  payload16 : BitVec 16
  deriving DecidableEq, Repr
def CamSlotWord64.pack (w : CamSlotWord64) : BitVec 64 := (w.payload16 ++ w.rhs16) ++ (w.lhs16 ++ (w.arity8 ++ w.tag8))

structure DiscrLutEntry64 where
  nextState16 : BitVec 16
  symTag16 : BitVec 16
  hitCount32 : BitVec 32
  deriving DecidableEq, Repr
def DiscrLutEntry64.pack (e : DiscrLutEntry64) : BitVec 64 := e.hitCount32 ++ (e.symTag16 ++ e.nextState16)

structure DeltaPortWord64 where
  nodeId16 : BitVec 16
  portKind2 : BitVec 2
  targetNode16 : BitVec 16
  targetPort2 : BitVec 2
  linearFlag1 : BitVec 1
  reserved27 : BitVec 27
  deriving DecidableEq, Repr
def DeltaPortWord64.pack (p : DeltaPortWord64) : BitVec 64 :=
  p.reserved27 ++ (p.linearFlag1 ++ (p.targetPort2 ++ (p.targetNode16 ++ (p.portKind2 ++ p.nodeId16))))
def DeltaPortWord64.isValidRedexPair (a b : DeltaPortWord64) : Bool :=
  (a.targetNode16 == b.nodeId16) && (b.targetNode16 == a.nodeId16) &&
  (a.portKind2 == 0#2) && (b.portKind2 == 0#2) && (a.linearFlag1 == 1#1) && (b.linearFlag1 == 1#1)

structure LratStreamReg64 where
  posMask32 : BitVec 32
  negMask32 : BitVec 32
  deriving DecidableEq, Repr
def LratStreamReg64.pack (r : LratStreamReg64) : BitVec 64 := r.negMask32 ++ r.posMask32
def LratStreamReg64.unpack (x : BitVec 64) : LratStreamReg64 := ⟨x.extractLsb' 0 32, x.extractLsb' 32 32⟩

structure OspcNocFlit where
  srcTile : Fin 4
  dstTile : Fin 4
  stage : Fin 2
  opcode4 : BitVec 4
  payload64 : BitVec 64
  deriving DecidableEq, Repr
/-- **Tile 0 (`tile0_exprcam_face4`)**: `ExprCAM` BRAM + dual-register `FaceIdeal4` datapath. -/
def tile0_exprcam_face4 : RtlMemModule :=
  { core :=
    { name := "ospc_tile0_exprcam_face4"
    , inputNames := ["op_sel", "in_lo64", "in_hi17", "cam_we", "cam_addr", "cam_wdata", "cam_qtag"]
    , inputWidths := [2, 64, 17, 1, 8, 64, 64]
    , wires :=
      [ ⟨0, "is_meet", .alu .eq (.inputPort 0) (.const 1#64), 1⟩, ⟨1, "is_join", .alu .eq (.inputPort 0) (.const 2#64), 1⟩
      , ⟨2, "is_load", .alu .eq (.inputPort 0) (.const 3#64), 1⟩
      , ⟨3, "next_lo", .mux (.wireRef 0) (.alu .bitAnd (.regRead 0) (.inputPort 1))
          (.mux (.wireRef 1) (.alu .bitOr (.regRead 0) (.inputPort 1)) (.mux (.wireRef 2) (.inputPort 1) (.regRead 0))), 64⟩
      , ⟨4, "next_hi", .mux (.wireRef 0) (.alu .bitAnd (.regRead 1) (.inputPort 2))
          (.mux (.wireRef 1) (.alu .bitOr (.regRead 1) (.inputPort 2)) (.mux (.wireRef 2) (.inputPort 2) (.regRead 1))), 17⟩
      , ⟨5, "entails_lo", .alu .eq (.alu .bitAnd (.regRead 0) (.bitNot (.inputPort 1))) (.const 0#64), 1⟩
      , ⟨6, "entails_hi", .alu .eq (.alu .bitAnd (.regRead 1) (.resize (.trunc 17) (.alu .bitXor (.inputPort 2) (.const 0x1FFFF#64)))) (.const 0#64), 1⟩
      , ⟨7, "cam_hit", .alu .eq (.regRead 2) (.inputPort 6), 1⟩ ]
    , regs := [⟨0, "face_lo64", .coreClk, .syncReset 0#64, false, .wireRef 3, 64⟩, ⟨1, "face_hi17", .coreClk, .syncReset 0#64, false, .wireRef 4, 17⟩]
    , outputs := [⟨"out_face_lo64", .regRead 0, 64⟩, ⟨"out_face_hi17", .regRead 1, 17⟩, ⟨"out_entails", .alu .bitAnd (.wireRef 5) (.wireRef 6), 1⟩, ⟨"out_cam_hit", .wireRef 7, 1⟩, ⟨"out_cam_word", .regRead 2, 64⟩] }
  , rams := [⟨0, "cam_bank", "cam_q", .coreClk, .bram, .writeFirst, 8, 64, .inputPort 4, .inputPort 3, .inputPort 4, .inputPort 5⟩] }
/-- **Tile 1 (`tile1_discrtree_lut`)**: 12-bit `(trieState, symTag)` BRAM + LogUp hit accumulator. -/
def tile1_discrtree_lut : RtlMemModule :=
  { core :=
    { name := "ospc_tile1_discrtree_lut"
    , inputNames := ["step_en", "sym_tag", "lut_we", "lut_waddr", "lut_wdata"], inputWidths := [1, 6, 1, 12, 64]
    , wires :=
      [ ⟨0, "raddr_idx", RtlExpr.concat (.regRead 0) (.inputPort 1) 6, 12⟩, ⟨1, "next_state_6", .resize (.trunc 6) (.regRead 2), 6⟩
      , ⟨2, "entry_valid", .alu .ult (.const 0#64) (.regRead 2), 1⟩, ⟨3, "hit_inc_en", .alu .bitAnd (.inputPort 0) (.wireRef 2), 1⟩
      , ⟨4, "next_hits", .resize (.trunc 32) (.alu .add (.regRead 1) (.wireRef 3)), 32⟩ ]
    , regs := [⟨0, "trie_state", .coreClk, .syncReset 0#64, false, .mux (.inputPort 0) (.wireRef 1) (.regRead 0), 6⟩, ⟨1, "logup_hits", .coreClk, .syncReset 0#64, false, .wireRef 4, 32⟩]
    , outputs := [⟨"out_trie_state", .regRead 0, 6⟩, ⟨"out_logup_hits", .regRead 1, 32⟩, ⟨"out_lut_entry", .regRead 2, 64⟩, ⟨"out_hit_valid", .wireRef 3, 1⟩] }
  , rams := [⟨0, "trie_lut", "trie_q", .coreClk, .bram, .readFirst, 12, 64, .wireRef 0, .inputPort 2, .inputPort 3, .inputPort 4⟩] }
/-- **Tile 2 (`tile2_deltanet_redex`)**: `DeltaNet` port bank + principal-port redex & linearity guard. -/
def tile2_deltanet_redex : RtlMemModule :=
  { core :=
    { name := "ospc_tile2_deltanet_redex"
    , inputNames := ["redex_en", "peer_word", "port_we", "port_addr", "port_wdata"], inputWidths := [1, 64, 1, 8, 64]
    , wires :=
      [ ⟨0, "a_node", .resize (.slice 15 0) (.regRead 2), 16⟩, ⟨1, "a_pkind", .resize (.slice 17 16) (.regRead 2), 2⟩
      , ⟨2, "a_tnode", .resize (.slice 33 18) (.regRead 2), 16⟩, ⟨3, "a_lin", .resize (.slice 36 36) (.regRead 2), 1⟩
      , ⟨4, "b_node", .resize (.slice 15 0) (.inputPort 1), 16⟩, ⟨5, "b_pkind", .resize (.slice 17 16) (.inputPort 1), 2⟩
      , ⟨6, "b_tnode", .resize (.slice 33 18) (.inputPort 1), 16⟩, ⟨7, "b_lin", .resize (.slice 36 36) (.inputPort 1), 1⟩
      , ⟨8, "sym_ok", .alu .bitAnd (.alu .eq (.wireRef 2) (.wireRef 4)) (.alu .eq (.wireRef 6) (.wireRef 0)), 1⟩
      , ⟨9, "princ_ok", .alu .bitAnd (.alu .eq (.wireRef 1) (.const 0#64)) (.alu .eq (.wireRef 5) (.const 0#64)), 1⟩
      , ⟨10, "lin_pair", .alu .bitAnd (.wireRef 3) (.wireRef 7), 1⟩
      , ⟨11, "redex_valid", .alu .bitAnd (.inputPort 0) (.alu .bitAnd (.wireRef 8) (.alu .bitAnd (.wireRef 9) (.wireRef 10))), 1⟩
      , ⟨12, "next_redex_cnt", .resize (.trunc 32) (.alu .add (.regRead 0) (.wireRef 11)), 32⟩
      , ⟨13, "next_lin_ok", .alu .bitAnd (.regRead 1) (.mux (.inputPort 0) (.wireRef 10) (.const 1#64)), 1⟩ ]
    , regs := [⟨0, "redex_count", .coreClk, .syncReset 0#64, false, .wireRef 12, 32⟩, ⟨1, "linear_ok", .coreClk, .syncReset 1#64, false, .wireRef 13, 1⟩]
    , outputs := [⟨"out_redex_valid", .wireRef 11, 1⟩, ⟨"out_redex_count", .regRead 0, 32⟩, ⟨"out_linear_ok", .regRead 1, 1⟩] }
  , rams := [⟨0, "port_bank", "port_q", .coreClk, .bram, .writeFirst, 8, 64, .inputPort 3, .inputPort 2, .inputPort 3, .inputPort 4⟩] }
/-- **Tile 3 (`tile3_stream_lrat`)**: `StreamLRAT` 32-var bitmask RUP propagation & conflict engine. -/
def tile3_stream_lrat : RtlMemModule :=
  { core :=
    { name := "ospc_tile3_stream_lrat"
    , inputNames := ["step_en", "clause_we", "clause_addr", "clause_wdata"], inputWidths := [1, 1, 8, 64]
    , wires :=
      [ ⟨0, "c_pos", .resize (.slice 31 0) (.regRead 3), 32⟩, ⟨1, "c_neg", .resize (.slice 63 32) (.regRead 3), 32⟩
      , ⟨2, "rem_pos", .alu .bitAnd (.wireRef 0) (.resize (.trunc 32) (.alu .bitXor (.regRead 1) (.const 0xFFFFFFFF#64))), 32⟩
      , ⟨3, "rem_neg", .alu .bitAnd (.wireRef 1) (.resize (.trunc 32) (.alu .bitXor (.regRead 0) (.const 0xFFFFFFFF#64))), 32⟩
      , ⟨4, "pos_zero", .alu .eq (.wireRef 2) (.const 0#64), 1⟩, ⟨5, "neg_zero", .alu .eq (.wireRef 3) (.const 0#64), 1⟩
      , ⟨6, "is_conflict", .alu .bitAnd (.wireRef 4) (.wireRef 5), 1⟩
      , ⟨7, "pos_pow2", .alu .bitAnd (.alu .ult (.const 0#64) (.wireRef 2)) (.alu .eq (.alu .bitAnd (.wireRef 2) (.resize (.trunc 32) (.alu .sub (.wireRef 2) (.const 1#64)))) (.const 0#64)), 1⟩
      , ⟨8, "neg_pow2", .alu .bitAnd (.alu .ult (.const 0#64) (.wireRef 3)) (.alu .eq (.alu .bitAnd (.wireRef 3) (.resize (.trunc 32) (.alu .sub (.wireRef 3) (.const 1#64)))) (.const 0#64)), 1⟩
      , ⟨9, "is_unit_pos", .alu .bitAnd (.wireRef 5) (.wireRef 7), 1⟩, ⟨10, "is_unit_neg", .alu .bitAnd (.wireRef 4) (.wireRef 8), 1⟩
      , ⟨11, "next_pos", .mux (.alu .bitAnd (.inputPort 0) (.wireRef 9)) (.alu .bitOr (.regRead 0) (.wireRef 2)) (.regRead 0), 32⟩
      , ⟨12, "next_neg", .mux (.alu .bitAnd (.inputPort 0) (.wireRef 10)) (.alu .bitOr (.regRead 1) (.wireRef 3)) (.regRead 1), 32⟩
      , ⟨13, "next_conflict", .alu .bitOr (.regRead 2) (.alu .bitAnd (.inputPort 0) (.wireRef 6)), 1⟩ ]
    , regs :=
      [ ⟨0, "assign_pos", .coreClk, .syncReset 0#64, false, .wireRef 11, 32⟩
      , ⟨1, "assign_neg", .coreClk, .syncReset 0#64, false, .wireRef 12, 32⟩
      , ⟨2, "conflict_latched", .coreClk, .syncReset 0#64, false, .wireRef 13, 1⟩ ]
    , outputs := [⟨"out_conflict", .regRead 2, 1⟩, ⟨"out_unit_pos", .wireRef 9, 1⟩, ⟨"out_unit_neg", .wireRef 10, 1⟩, ⟨"out_assign_pos", .regRead 0, 32⟩, ⟨"out_assign_neg", .regRead 1, 32⟩] }
  , rams := [⟨0, "clause_bank", "clause_q", .coreClk, .bram, .writeFirst, 8, 64, .inputPort 2, .inputPort 1, .inputPort 2, .inputPort 3⟩] }
def ospcTileRtl : Fin 4 → RtlMemModule
  | ⟨0, _⟩ => tile0_exprcam_face4 | ⟨1, _⟩ => tile1_discrtree_lut
  | ⟨2, _⟩ => tile2_deltanet_redex | ⟨3, _⟩ => tile3_stream_lrat

theorem ospcTileRtl_checkRtlMemModuleW : ∀ t : Fin 4, checkRtlMemModuleW (ospcTileRtl t) = true := by decide +kernel

/-! ### Synthesizable Pure-Register/Port Datapath Extraction (`ospcTileDatapathRtl`) & Refinement -/

/-- Synthesizable `RtlModule` datapath/register extraction of `ospcTileRtl t` (`t : Fin 4`),
exposing each synchronous `SyncRamSpec`'s registered readout latch `ram.rdataName` at register
slot `core.regs.length + ram.ramIdx` (fed by input `{ram.rdataName}_in`) and driving the BRAM
interface ports `{ram.name}_{raddr,we,waddr,wdata}` at their exact checked widths. -/
def ospcTileDatapathRtl (t : Fin 4) : RtlModule :=
  let m := ospcTileRtl t
  let nIn := m.core.inputNames.length
  let nCore := m.core.regs.length
  { name        := s!"obend_ospc_tile{t.val}"
  , inputNames  := m.core.inputNames ++ m.rams.map (fun ram => s!"{ram.rdataName}_in")
  , inputWidths := m.core.inputWidths ++ m.rams.map (·.dataWidth)
  , wires       := m.core.wires
  , regs        := m.core.regs ++ m.rams.map (fun ram =>
      { regIdx         := nCore + ram.ramIdx
      , name           := ram.rdataName
      , domain         := ram.domain
      , resetKind      := .resetFree
      , isSynchronizer := false
      , nextExpr       := .inputPort (nIn + ram.ramIdx)
      , width          := ram.dataWidth })
  , outputs     := m.core.outputs ++ m.rams.flatMap (fun ram =>
      [ { name := s!"{ram.name}_raddr", expr := .resize (.trunc ram.addrWidth) ram.readAddrExpr, width := ram.addrWidth }
      , { name := s!"{ram.name}_we",    expr := .resize (.trunc 1) ram.writeEnExpr,             width := 1 }
      , { name := s!"{ram.name}_waddr", expr := .resize (.trunc ram.addrWidth) ram.writeAddrExpr, width := ram.addrWidth }
      , { name := s!"{ram.name}_wdata", expr := .resize (.trunc ram.dataWidth) ram.writeDataExpr, width := ram.dataWidth } ]) }

/-- Lift `ospcTileRtl t` port `inputs` and `MemState` `st` to the port environment of `ospcTileDatapathRtl t`,
binding input `nIn + ram.ramIdx` to `evalSyncRamReadNext` of `ram`. -/
def ospcTileDatapathInputs (t : Fin 4) (inputs : Nat → BitVec 64) (st : MemState) : Nat → BitVec 64 :=
  let m := ospcTileRtl t
  let nIn := m.core.inputNames.length
  let wireEnv := evalWireTable inputs st.regs m.core.wires
  fun idx =>
    if idx < nIn then inputs idx
    else match m.rams.find? (fun ram => nIn + ram.ramIdx == idx) with
      | some ram => evalSyncRamReadNext inputs wireEnv st.regs (st.mems ram.ramIdx) ram
      | none => 0#64

private theorem ospcTileDatapathRtl_checks :
    ∀ t : Fin 4,
      checkRtlModule (ospcTileDatapathRtl t) = true ∧
      checkRtlModuleW (ospcTileDatapathRtl t) = true ∧
      checkWidths (ospcTileDatapathRtl t) = true := by decide +kernel

private theorem ospcTile_core_dag :
    ∀ t : Fin 4,
      let m := ospcTileRtl t
      let nIn := m.core.inputNames.length
      let nTotal := m.core.regs.length + m.rams.length
      let nWires := m.core.wires.length
      checkWireTableDAG nIn nTotal m.core.wires = true ∧
      m.core.regs.all (fun r => checkExprDAG nIn nTotal nWires r.nextExpr) = true ∧
      m.core.outputs.all (fun o => checkExprDAG nIn nTotal nWires o.expr) = true := by decide +kernel

private theorem ospcTile_single_ram (t : Fin 4) :
    ∃ ram0 : SyncRamSpec, (ospcTileRtl t).rams = [ram0] ∧ ram0.ramIdx = 0 := by
  rcases t with ⟨_ | _ | _ | _ | n, hlt⟩
  · exact ⟨_, rfl, rfl⟩
  · exact ⟨_, rfl, rfl⟩
  · exact ⟨_, rfl, rfl⟩
  · exact ⟨_, rfl, rfl⟩
  · omega

/-- All 4 `ospcTileDatapathRtl` modules pass `checkRtlModule`, `checkRtlModuleW`, and `checkWidths`
(which directly discharges `YosysLec.moduleFaithful` via `YosysLec.moduleFaithful_of_checkWidths`). -/
theorem ospcTileDatapathRtl_wellFormed (t : Fin 4) :
    checkRtlModule (ospcTileDatapathRtl t) = true ∧
    checkRtlModuleW (ospcTileDatapathRtl t) = true ∧
    checkWidths (ospcTileDatapathRtl t) = true :=
  ospcTileDatapathRtl_checks t

private theorem evalRtlExpr_inputs_locality (nIn : Nat) (ins1 ins2 wires regs : Nat → BitVec 64)
    (hAgree : ∀ i, i < nIn → ins1 i = ins2 i) :
    ∀ (nReg wB : Nat) (e : RtlExpr), checkExprDAG nIn nReg wB e = true →
      evalRtlExpr ins1 wires regs e = evalRtlExpr ins2 wires regs e := by
  intro nReg wB e; induction e with
  | const _ | wireRef _ | regRead _ => intro _; rfl
  | inputPort idx => intro h; simp only [checkExprDAG, decide_eq_true_eq] at h; exact hAgree idx h
  | alu _ _ _ iha ihb =>
    intro h; simp only [checkExprDAG, Bool.and_eq_true] at h; simp only [evalRtlExpr, iha h.1, ihb h.2]
  | mux _ _ _ ihc iht ihf =>
    intro h; simp only [checkExprDAG, Bool.and_eq_true] at h; simp only [evalRtlExpr, ihc h.1.1, iht h.1.2, ihf h.2]
  | bitNot _ iha | resize _ _ iha =>
    intro h; simp only [checkExprDAG] at h; simp only [evalRtlExpr, iha h]

private theorem evalWireTable_inputs_locality (nIn nReg : Nat) (ins1 ins2 regs : Nat → BitVec 64)
    (assigns : List WireAssign) (hDag : checkWireTableDAG nIn nReg assigns = true)
    (hAgree : ∀ i, i < nIn → ins1 i = ins2 i) :
    evalWireTable ins1 regs assigns = evalWireTable ins2 regs assigns := by
  unfold evalWireTable; unfold checkWireTableDAG at hDag
  suffices ∀ (ws : List WireAssign) (k : Nat) (env : Nat → BitVec 64),
      checkWireTableDAG.go nIn nReg k ws = true →
      ws.foldl (fun e a => let v := evalRtlExpr ins1 e regs a.expr; fun i => if i == a.wireIdx then v else e i) env =
        ws.foldl (fun e a => let v := evalRtlExpr ins2 e regs a.expr; fun i => if i == a.wireIdx then v else e i) env from
    this assigns 0 (fun _ => 0#64) hDag
  intro ws; induction ws with
  | nil => intro _ _ _; rfl
  | cons a rest ih =>
    intro k env hGo
    simp only [checkWireTableDAG.go, Bool.and_eq_true] at hGo
    simp only [List.foldl_cons, evalRtlExpr_inputs_locality nIn ins1 ins2 env regs hAgree nReg k a.expr hGo.1.2]
    exact ih (k + 1) _ hGo.2

private theorem foldRegs_inputs_locality (nIn nReg nWires : Nat) (rst : Bool)
    (ins1 ins2 wireEnv regs : Nat → BitVec 64) (hAgree : ∀ i, i < nIn → ins1 i = ins2 i) :
    ∀ (rs : List RegSpec) (acc : Nat → BitVec 64),
      rs.all (fun r => checkExprDAG nIn nReg nWires r.nextExpr) = true →
      rs.foldl (fun nextSt r => fun i => if i == r.regIdx then regNextValue rst ins1 wireEnv regs r else nextSt i) acc =
        rs.foldl (fun nextSt r => fun i => if i == r.regIdx then regNextValue rst ins2 wireEnv regs r else nextSt i) acc
  | [], _, _ => rfl
  | r :: rest, acc, hAll => by
    simp only [List.all_cons, Bool.and_eq_true] at hAll
    have hVal : regNextValue rst ins1 wireEnv regs r = regNextValue rst ins2 wireEnv regs r := by
      unfold regNextValue
      rw [evalRtlExpr_inputs_locality nIn ins1 ins2 wireEnv regs hAgree nReg nWires r.nextExpr hAll.1]
    simp only [List.foldl_cons, hVal]
    exact foldRegs_inputs_locality nIn nReg nWires rst ins1 ins2 wireEnv regs hAgree rest _ hAll.2

/-- **Single-Step Datapath Refinement (`ospcTileRtl_refines_ospcTileDatapathRtl`)**:
For every tile `t : Fin 4`, `rst : Bool`, `inputs`, and `st : MemState`:
1. Stepping `ospcTileDatapathRtl t` under `ospcTileDatapathInputs t inputs st` produces the **exact**
   `Nat → BitVec 64` register function `(stepMemModule (ospcTileRtl t) rst inputs st).regs` (across both
   core flip-flops `0 .. nCore - 1` and the registered BRAM readout latch `nCore + ram.ramIdx`), and
2. The core output prefix of `evalModuleOutputs (ospcTileDatapathRtl t)` agrees identically with
   `evalMemModuleOutputs (ospcTileRtl t) inputs st`. -/
theorem ospcTileRtl_refines_ospcTileDatapathRtl
    (t : Fin 4) (rst : Bool) (inputs : Nat → BitVec 64) (st : MemState) :
    let dpIns := ospcTileDatapathInputs t inputs st
    stepModuleRegs (ospcTileDatapathRtl t) rst dpIns st.regs =
      (stepMemModule (ospcTileRtl t) rst inputs st).regs ∧
    (evalModuleOutputs (ospcTileDatapathRtl t) dpIns st.regs).take (ospcTileRtl t).core.outputs.length =
      evalMemModuleOutputs (ospcTileRtl t) inputs st := by
  intro dpIns
  have hAgree : ∀ i, i < (ospcTileRtl t).core.inputNames.length → dpIns i = inputs i := fun i hi => by
    dsimp only [dpIns, ospcTileDatapathInputs]; simp [hi]
  obtain ⟨hWireDag, hRegDag, hOutDagAll⟩ := ospcTile_core_dag t
  have hWires : evalWireTable dpIns st.regs (ospcTileRtl t).core.wires =
      evalWireTable inputs st.regs (ospcTileRtl t).core.wires :=
    evalWireTable_inputs_locality _ _ dpIns inputs st.regs (ospcTileRtl t).core.wires hWireDag hAgree
  refine ⟨?_, ?_⟩
  · obtain ⟨ram0, hRams, hIdx0⟩ := ospcTile_single_ram t
    have hDpRam : dpIns (ospcTileRtl t).core.inputNames.length =
        evalSyncRamReadNext inputs (evalWireTable inputs st.regs (ospcTileRtl t).core.wires)
          st.regs (st.mems 0) ram0 := by
      dsimp only [dpIns, ospcTileDatapathInputs]
      simp [Nat.lt_irrefl, hRams, hIdx0]
    rw [stepModuleRegs_eq_foldl_next]
    dsimp only [ospcTileDatapathRtl, stepMemModule]
    rw [hWires, List.foldl_append,
        foldRegs_inputs_locality _ _ _ rst dpIns inputs _ st.regs hAgree
          (ospcTileRtl t).core.regs st.regs hRegDag,
        ← stepModuleRegs_eq_foldl_next, hRams]
    simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil,
      regNextValue, evalRtlExpr, hIdx0, Nat.add_zero, hDpRam]
  · dsimp only [evalMemModuleOutputs, evalModuleOutputs, ospcTileDatapathRtl]
    rw [hWires, List.map_append, List.take_left' (by simp)]
    apply List.map_congr_left; intro o ho
    exact Prod.ext rfl (evalRtlExpr_inputs_locality _ dpIns inputs _ st.regs hAgree _ _ o.expr
      (List.all_eq_true.mp hOutDagAll o ho))

/-- Lift a multi-cycle `(rst, inputs)` trace of `ospcTileRtl t` starting at `st` to `ospcTileDatapathRtl t`. -/
def liftOspcTileDatapathTrace (t : Fin 4) :
    MemState → List (Bool × (Nat → BitVec 64)) → List (Bool × (Nat → BitVec 64))
  | _, [] => []
  | st, (rst, ins) :: rest =>
    (rst, ospcTileDatapathInputs t ins st) ::
      liftOspcTileDatapathTrace t (stepMemModule (ospcTileRtl t) rst ins st) rest

/-- **Multi-Cycle Datapath Trace Refinement (`ospcTileRtl_trace_refines_datapath`)**:
Across arbitrary multi-cycle traces `trace`, running `ospcTileDatapathRtl t` via `HDL.runModuleTrace`
produces the exact final register state `(runMemModuleTrace (ospcTileRtl t) st trace).regs`. -/
theorem ospcTileRtl_trace_refines_datapath
    (t : Fin 4) (st : MemState) (trace : List (Bool × (Nat → BitVec 64))) :
    runModuleTrace (ospcTileDatapathRtl t) st.regs (liftOspcTileDatapathTrace t st trace) =
      (runMemModuleTrace (ospcTileRtl t) st trace).regs := by
  induction trace generalizing st with
  | nil => rfl
  | cons cyc rest ih =>
    rcases cyc with ⟨rst, ins⟩
    dsimp only [liftOspcTileDatapathTrace, runModuleTrace, runMemModuleTrace, List.foldl_cons]
    rw [(ospcTileRtl_refines_ospcTileDatapathRtl t rst ins st).1]
    exact ih (stepMemModule (ospcTileRtl t) rst ins st)

/-! ### Tile 0 RTL-to-Spec Simulation (`stepTile0_simulates_faceIdeal4`) -/
private theorem setWidth64_and17 (a b : BitVec 17) : a.setWidth 64 &&& b.setWidth 64 = (a &&& b).setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi]
private theorem setWidth64_or17 (a b : BitVec 17) : a.setWidth 64 ||| b.setWidth 64 = (a ||| b).setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi]
private theorem setWidth64_implies17 (a b : BitVec 17) :
    (a.setWidth 64 &&& truncToWidth 17 (b.setWidth 64 ^^^ 0x1FFFF#64) == 0#64) = ((a &&& ~~~b) == 0#17) := by
  have hOnes17 : (0x1FFFF#64 : BitVec 64) = BitVec.allOnes 64 >>> (64 - 17) := by decide
  apply Bool.eq_iff_iff.mpr; simp only [beq_iff_eq]; constructor
  · intro h; apply BitVec.eq_of_getLsbD_eq; intro i hi17
    have hi := congrArg (fun v => v.getLsbD i) h; have hi64 : i < 64 := by omega
    have hmask : (BitVec.allOnes 64 >>> (64 - 17)).getLsbD i = true := by
      rw [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_allOnes]; simp; omega
    simp only [truncToWidth, hOnes17, BitVec.getLsbD_and, BitVec.getLsbD_xor, BitVec.getLsbD_not, BitVec.getLsbD_setWidth,
      BitVec.getLsbD_zero, hi17, hi64, decide_true, Bool.true_and, hmask, Bool.xor_true, Bool.and_true] at hi ⊢; exact hi
  · intro h; apply BitVec.eq_of_getLsbD_eq; intro i hi64
    by_cases hi17 : i < 17
    · have hi := congrArg (fun v => v.getLsbD i) h
      have hmask : (BitVec.allOnes 64 >>> (64 - 17)).getLsbD i = true := by
        rw [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_allOnes]; simp; omega
      simp only [truncToWidth, hOnes17, BitVec.getLsbD_and, BitVec.getLsbD_xor, BitVec.getLsbD_not, BitVec.getLsbD_setWidth,
        BitVec.getLsbD_zero, hi17, hi64, decide_true, Bool.true_and, hmask, Bool.xor_true] at hi ⊢
      have : (a.getLsbD i && !b.getLsbD i) = false := hi; rw [← Bool.and_assoc, this, Bool.false_and]
    · simp only [truncToWidth, BitVec.getLsbD_and, BitVec.getLsbD_setWidth, BitVec.getLsbD_zero, hi64, decide_true, Bool.true_and]
      have ha0 : a.getLsbD i = false := by
        have hpow : 2 ^ 17 ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega)
        have hlt : a.toNat < 2 ^ i := Nat.lt_of_lt_of_le a.isLt hpow
        simp only [BitVec.getLsbD, Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hlt]; rfl
      simp [ha0]

theorem stepTile0_simulates_faceIdeal4
    (cur arg : FaceIdeal4) (st : MemState) (inputs : Nat → BitVec 64)
    (hLo : st.regs 0 = cur.lo64) (hHi : st.regs 1 = cur.hi17.setWidth 64)
    (hInLo : inputs 1 = arg.lo64) (hInHi : inputs 2 = arg.hi17.setWidth 64) :
    (inputs 0 = 1#64 → let st' := stepMemModule tile0_exprcam_face4 false inputs st
      st'.regs 0 = (cur.meet arg).lo64 ∧ st'.regs 1 = (cur.meet arg).hi17.setWidth 64) ∧
    (inputs 0 = 2#64 → let st' := stepMemModule tile0_exprcam_face4 false inputs st
      st'.regs 0 = (cur.join arg).lo64 ∧ st'.regs 1 = (cur.join arg).hi17.setWidth 64) ∧
    (evalMemModuleOutputs tile0_exprcam_face4 inputs st).lookup "out_entails" =
      some (if cur.implies arg then 1#64 else 0#64) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hOp; simp only [tile0_exprcam_face4, stepModuleRegs, evalWireTable, evalRtlExpr, evalAluOp,
      List.foldl_cons, List.foldl_nil, hLo, hHi, hInLo, hInHi, hOp, FaceIdeal4.meet, setWidth64_and17]; simp
  · intro hOp; simp only [tile0_exprcam_face4, stepModuleRegs, evalWireTable, evalRtlExpr, evalAluOp,
      List.foldl_cons, List.foldl_nil, hLo, hHi, hInLo, hInHi, hOp, FaceIdeal4.join, setWidth64_or17]; simp
  · simp only [evalMemModuleOutputs, evalModuleOutputs, tile0_exprcam_face4, evalWireTable, evalRtlExpr,
      evalAluOp, evalWidthOp, List.foldl_cons, List.foldl_nil, List.map_cons, List.map_nil, List.lookup,
      hLo, hHi, hInLo, hInHi, FaceIdeal4.implies, setWidth64_implies17, beq_self_eq_true, ↓reduceIte,
      show ("out_entails" == "out_face_lo64") = false by decide, show ("out_entails" == "out_face_hi17") = false by decide]
    have hEq : (if cur.lo64 &&& ~~~arg.lo64 == 0#64 then 1#64 else 0#64) &&&
        (if cur.hi17 &&& ~~~arg.hi17 == 0#17 then 1#64 else 0#64) =
        if (cur.lo64 &&& ~~~arg.lo64 == 0#64) && (cur.hi17 &&& ~~~arg.hi17 == 0#17) then 1#64 else 0#64 := by
      cases (cur.lo64 &&& ~~~arg.lo64 == 0#64) <;> cases (cur.hi17 &&& ~~~arg.hi17 == 0#17) <;> rfl
    exact congrArg some hEq

/-! ### Tile 3 `StreamLRAT` Soundness wrt `Obend.Judge.Lrat` (`0 Classical`) -/
def decodeClause32 (w : LratStreamReg64) : Clause :=
  (List.range 32).flatMap fun i =>
    (if w.posMask32.getLsbD i then [(i + 1 : Int)] else []) ++ (if w.negMask32.getLsbD i then [(-(i + 1 : Int))] else [])
def ModelsAssign32 (σ : Nat → Bool) (ap an : BitVec 32) : Prop :=
  (∀ i : Nat, i < 32 → ap.getLsbD i = true → litTrue σ (i + 1 : Int) = true) ∧
  (∀ i : Nat, i < 32 → an.getLsbD i = true → litTrue σ (-(i + 1 : Int)) = true)

theorem modelsAssign32_inhabited (v : Fin 32) :
    ∃ (σ : Nat → Bool) (ap an : BitVec 32), ap.getLsbD v.val = true ∧ ModelsAssign32 σ ap an := by
  refine ⟨fun _ => true, BitVec.allOnes 32, 0#32, by rw [BitVec.getLsbD_allOnes]; simp [v.isLt],
    fun i _ _ => by simp [litTrue, show (0 : Int) < (i + 1 : Int) by omega],
    fun i _ h => by rw [BitVec.getLsbD_zero] at h; cases h⟩
def lratRemPos (an : BitVec 32) (w : LratStreamReg64) : BitVec 32 := w.posMask32 &&& ~~~an
def lratRemNeg (ap : BitVec 32) (w : LratStreamReg64) : BitVec 32 := w.negMask32 &&& ~~~ap
def isPow2Mask32 (x : BitVec 32) : Bool := (x != 0#32) && ((x &&& (x - 1#32)) == 0#32)
def lratBitmaskConflict (ap an : BitVec 32) (w : LratStreamReg64) : Bool := (lratRemPos an w == 0#32) && (lratRemNeg ap w == 0#32)
def lratBitmaskUnitPos (ap an : BitVec 32) (w : LratStreamReg64) : Bool := (lratRemNeg ap w == 0#32) && isPow2Mask32 (lratRemPos an w)
def lratBitmaskUnitNeg (ap an : BitVec 32) (w : LratStreamReg64) : Bool := (lratRemPos an w == 0#32) && isPow2Mask32 (lratRemNeg ap w)
private theorem nat_testBit_sub_one_eq_of_lt {x i j : Nat} (hij : i < j) (hi : x.testBit i = true) :
    (x - 1).testBit j = x.testBit j := by
  have hmodPos : 0 < x % 2 ^ j := by
    if hz : x % 2 ^ j = 0 then
      exfalso
      have hpow : 2 ^ j = 2 ^ i * 2 ^ (j - i) := by rw [← Nat.pow_add, Nat.add_sub_cancel' (Nat.le_of_lt hij)]
      have h2dvd : 2 ∣ 2 ^ (j - i) := ⟨2 ^ (j - i - 1), by rw [Nat.mul_comm, ← Nat.pow_succ]; exact congrArg (2 ^ ·) (by omega)⟩
      obtain ⟨q, hq⟩ := Nat.dvd_of_mod_eq_zero hz; rw [hpow, Nat.mul_assoc] at hq
      have hdiv : x / 2 ^ i = 2 ^ (j - i) * q := by rw [hq, Nat.mul_div_right _ (Nat.two_pow_pos i)]
      obtain ⟨m, hm⟩ := h2dvd; rw [Nat.testBit, Nat.shiftRight_eq_div_pow, hdiv, hm, Nat.mul_assoc] at hi
      have hmod2 : (2 * (m * q)) % 2 = 0 := by omega
      simp [hmod2] at hi
    else omega
  have hdivEq : (x - 1) / 2 ^ j = x / 2 ^ j := by
    have hdm := Nat.div_add_mod x (2 ^ j); have hlt := Nat.mod_lt x (Nat.two_pow_pos j)
    have h1 : x - 1 = 2 ^ j * (x / 2 ^ j) + (x % 2 ^ j - 1) := by omega
    rw [h1, Nat.mul_add_div (Nat.two_pow_pos j), Nat.div_eq_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hlt), Nat.add_zero]
  simp only [Nat.testBit, Nat.shiftRight_eq_div_pow, hdivEq]
private theorem pow2Mask32_unique_bit {x : BitVec 32} {i j : Nat}
    (hpow : isPow2Mask32 x = true) (hi : x.getLsbD i = true) (hj : x.getLsbD j = true) : i = j := by
  unfold isPow2Mask32 at hpow; simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hpow
  obtain ⟨hne, hand0⟩ := hpow
  have hxPos : 0 < x.toNat := by if hz : x.toNat = 0 then exact absurd (BitVec.eq_of_toNat_eq hz) hne else omega
  have hsubNat : (x - 1#32).toNat = x.toNat - 1 := by rw [BitVec.toNat_sub]; simp; omega
  if heqij : i = j then exact heqij
  else
    exfalso; rcases Nat.lt_or_gt_of_ne heqij with hij | hji
    · have hbit := congrArg (fun v => v.getLsbD j) hand0
      simp only [BitVec.getLsbD_and, BitVec.getLsbD_zero, hj, Bool.true_and] at hbit
      rw [show (x - 1#32).getLsbD j = (x.toNat - 1).testBit j by rw [BitVec.getLsbD, hsubNat],
          nat_testBit_sub_one_eq_of_lt hij (show x.toNat.testBit i = true from hi), show x.toNat.testBit j = true from hj] at hbit; cases hbit
    · have hbit := congrArg (fun v => v.getLsbD i) hand0
      simp only [BitVec.getLsbD_and, BitVec.getLsbD_zero, hi, Bool.true_and] at hbit
      rw [show (x - 1#32).getLsbD i = (x.toNat - 1).testBit i by rw [BitVec.getLsbD, hsubNat],
          nat_testBit_sub_one_eq_of_lt hji (show x.toNat.testBit j = true from hj), show x.toNat.testBit i = true from hi] at hbit; cases hbit
private theorem sat_decodeClause32_exists_rem {σ : Nat → Bool} {ap an : BitVec 32} {w : LratStreamReg64}
    (hMod : ModelsAssign32 σ ap an) (hSat : Sat σ (decodeClause32 w)) :
    (∃ i < 32, (lratRemPos an w).getLsbD i = true ∧ litTrue σ (i + 1 : Int) = true) ∨
    (∃ i < 32, (lratRemNeg ap w).getLsbD i = true ∧ litTrue σ (-(i + 1 : Int)) = true) := by
  obtain ⟨l, hlMem, hlTrue⟩ := hSat
  simp only [decodeClause32, List.mem_flatMap, List.mem_range, List.mem_append] at hlMem
  obtain ⟨i, hi32, hpos | hneg⟩ := hlMem
  · split at hpos
    · rename_i hbit; simp only [List.mem_singleton] at hpos; subst hpos
      left; refine ⟨i, hi32, ?_, hlTrue⟩
      simp only [lratRemPos, BitVec.getLsbD_and, BitVec.getLsbD_not, hi32, decide_true, Bool.true_and, hbit]
      cases han : an.getLsbD i
      · rfl
      · exfalso; have hf := hMod.2 i hi32 han; rw [Obend.Judge.Lrat.litTrue_neg σ (by omega), hlTrue] at hf; cases hf
    · cases hpos
  · split at hneg
    · rename_i hbit; simp only [List.mem_singleton] at hneg; subst hneg
      right; refine ⟨i, hi32, ?_, hlTrue⟩
      simp only [lratRemNeg, BitVec.getLsbD_and, BitVec.getLsbD_not, hi32, decide_true, Bool.true_and, hbit]
      cases hap : ap.getLsbD i
      · rfl
      · exfalso; have hf := hMod.1 i hi32 hap; rw [Obend.Judge.Lrat.litTrue_neg σ (by omega), hf] at hlTrue; cases hlTrue
    · cases hneg

theorem tile3_lrat_conflict_sound (σ : Nat → Bool) (ap an : BitVec 32) (w : LratStreamReg64)
    (hMod : ModelsAssign32 σ ap an) (hSat : Sat σ (decodeClause32 w)) : lratBitmaskConflict ap an w = false := by
  cases h : lratBitmaskConflict ap an w
  · rfl
  · exfalso; unfold lratBitmaskConflict at h; simp only [Bool.and_eq_true, beq_iff_eq] at h
    rcases sat_decodeClause32_exists_rem hMod hSat with ⟨i, _, hb, _⟩ | ⟨i, _, hb, _⟩
    · rw [h.1, BitVec.getLsbD_zero] at hb; cases hb
    · rw [h.2, BitVec.getLsbD_zero] at hb; cases hb

theorem tile3_lrat_unit_step_sound (σ : Nat → Bool) (ap an : BitVec 32) (w : LratStreamReg64)
    (hMod : ModelsAssign32 σ ap an) (hSat : Sat σ (decodeClause32 w)) :
    (lratBitmaskUnitPos ap an w = true → ModelsAssign32 σ (ap ||| lratRemPos an w) an) ∧
    (lratBitmaskUnitNeg ap an w = true → ModelsAssign32 σ ap (an ||| lratRemNeg ap w)) := by
  constructor
  · intro hU; unfold lratBitmaskUnitPos at hU; simp only [Bool.and_eq_true, beq_iff_eq] at hU
    refine ⟨fun j hj32 hj => ?_, hMod.2⟩; simp only [BitVec.getLsbD_or, Bool.or_eq_true] at hj
    rcases hj with hap | hrem
    · exact hMod.1 j hj32 hap
    · rcases sat_decodeClause32_exists_rem hMod hSat with ⟨i, _, hiRem, hiTrue⟩ | ⟨i, _, hiRem, _⟩
      · cases pow2Mask32_unique_bit hU.2 hiRem hrem; exact hiTrue
      · rw [hU.1, BitVec.getLsbD_zero] at hiRem; cases hiRem
  · intro hU; unfold lratBitmaskUnitNeg at hU; simp only [Bool.and_eq_true, beq_iff_eq] at hU
    refine ⟨hMod.1, fun j hj32 hj => ?_⟩; simp only [BitVec.getLsbD_or, Bool.or_eq_true] at hj
    rcases hj with han | hrem
    · exact hMod.2 j hj32 han
    · rcases sat_decodeClause32_exists_rem hMod hSat with ⟨i, _, hiRem, _⟩ | ⟨i, _, hiRem, hiTrue⟩
      · rw [hU.1, BitVec.getLsbD_zero] at hiRem; cases hiRem
      · cases pow2Mask32_unique_bit hU.2 hiRem hrem; exact hiTrue
def runStreamLratRup : BitVec 32 → BitVec 32 → List LratStreamReg64 → Bool
  | _, _, [] => false
  | ap, an, w :: rest =>
    if lratBitmaskConflict ap an w then true
    else if lratBitmaskUnitPos ap an w then runStreamLratRup (ap ||| lratRemPos an w) an rest
    else if lratBitmaskUnitNeg ap an w then runStreamLratRup ap (an ||| lratRemNeg ap w) rest
    else false

theorem tile3_lrat_rup_trace_sound (σ : Nat → Bool) :
    ∀ (hints : List LratStreamReg64) (ap an : BitVec 32),
      (∀ w ∈ hints, Sat σ (decodeClause32 w)) → ModelsAssign32 σ ap an → runStreamLratRup ap an hints = false
  | [], _, _, _, _ => rfl
  | w :: rest, ap, an, hAll, hMod => by
    have hw := hAll w List.mem_cons_self
    have hRest : ∀ u ∈ rest, Sat σ (decodeClause32 u) := fun u hu => hAll u (List.mem_cons_of_mem _ hu)
    simp only [runStreamLratRup, tile3_lrat_conflict_sound σ ap an w hMod hw, Bool.false_eq_true, ↓reduceIte]
    cases hp : lratBitmaskUnitPos ap an w
    · cases hn : lratBitmaskUnitNeg ap an w
      · rfl
      · exact tile3_lrat_rup_trace_sound σ rest ap (an ||| lratRemNeg ap w) hRest ((tile3_lrat_unit_step_sound σ ap an w hMod hw).2 hn)
    · exact tile3_lrat_rup_trace_sound σ rest (ap ||| lratRemPos an w) an hRest ((tile3_lrat_unit_step_sound σ ap an w hMod hw).1 hp)

/-! ## 3. 2-Stage 2D Hypercube XOR-Butterfly ($Q_2$) Inter-Tile NoC -/
def q2Partner : Fin 2 → Fin 4 → Fin 4
  | ⟨0, _⟩, ⟨0, _⟩ => ⟨1, by omega⟩ | ⟨0, _⟩, ⟨1, _⟩ => ⟨0, by omega⟩
  | ⟨0, _⟩, ⟨2, _⟩ => ⟨3, by omega⟩ | ⟨0, _⟩, ⟨3, _⟩ => ⟨2, by omega⟩
  | ⟨1, _⟩, ⟨0, _⟩ => ⟨2, by omega⟩ | ⟨1, _⟩, ⟨1, _⟩ => ⟨3, by omega⟩
  | ⟨1, _⟩, ⟨2, _⟩ => ⟨0, by omega⟩ | ⟨1, _⟩, ⟨3, _⟩ => ⟨1, by omega⟩
theorem q2Partner_val_eq (stage : Fin 2) (t : Fin 4) :
    (q2Partner stage t).val = if stage.val = 0 then t.val ^^^ 1 else t.val ^^^ 2 := by revert stage t; decide
def q2OrderedLo : Fin 2 → Fin 4 → Fin 4
  | ⟨0, _⟩, ⟨0, _⟩ | ⟨0, _⟩, ⟨1, _⟩ => ⟨0, by omega⟩ | ⟨0, _⟩, ⟨2, _⟩ | ⟨0, _⟩, ⟨3, _⟩ => ⟨2, by omega⟩
  | ⟨1, _⟩, ⟨0, _⟩ | ⟨1, _⟩, ⟨2, _⟩ => ⟨0, by omega⟩ | ⟨1, _⟩, ⟨1, _⟩ | ⟨1, _⟩, ⟨3, _⟩ => ⟨1, by omega⟩
def q2OrderedHi : Fin 2 → Fin 4 → Fin 4
  | ⟨0, _⟩, ⟨0, _⟩ | ⟨0, _⟩, ⟨1, _⟩ => ⟨1, by omega⟩ | ⟨0, _⟩, ⟨2, _⟩ | ⟨0, _⟩, ⟨3, _⟩ => ⟨3, by omega⟩
  | ⟨1, _⟩, ⟨0, _⟩ | ⟨1, _⟩, ⟨2, _⟩ => ⟨2, by omega⟩ | ⟨1, _⟩, ⟨1, _⟩ | ⟨1, _⟩, ⟨3, _⟩ => ⟨3, by omega⟩
theorem q2Ordered_spec (stage : Fin 2) (t : Fin 4) :
    let p := q2Partner stage t
    q2OrderedLo stage t = (if t.val ≤ p.val then t else p) ∧ q2OrderedHi stage t = (if t.val ≤ p.val then p else t) := by
  revert stage t; decide
theorem q2Partner_involutive (stage : Fin 2) (t : Fin 4) : q2Partner stage (q2Partner stage t) = t := by revert stage t; decide
theorem q2_two_hop_all_pairs (src dst : Fin 4) :
    ∃ b0 b1 : Bool, let mid := if b0 then q2Partner ⟨0, by omega⟩ src else src
      (if b1 then q2Partner ⟨1, by omega⟩ mid else mid) = dst := by revert src dst; decide
def ospcPolyAddCoeffs {R : Type} [CommRingOps R] : List R → List R → List R
  | [], qs => qs
  | ps, [] => ps
  | c :: cs, d :: ds => CommRingOps.add c d :: ospcPolyAddCoeffs cs ds

def ospcPolyAdd {R : Type} [CommRingOps R] (p q : RoundPoly R) : RoundPoly R :=
  ⟨ospcPolyAddCoeffs p.coeffs q.coeffs⟩

private theorem evalCoeffs_ospcPolyAdd {R : Type} [LawfulCommRing R] :
    ∀ (ps qs : List R) (x : R),
      RoundPoly.evalCoeffs (ospcPolyAddCoeffs ps qs) x =
        CommRingOps.add (RoundPoly.evalCoeffs ps x) (RoundPoly.evalCoeffs qs x)
  | [], _, _ => by simp [ospcPolyAddCoeffs, RoundPoly.evalCoeffs, LawfulCommRing.zero_add]
  | _ :: _, [], _ => by simp [ospcPolyAddCoeffs, RoundPoly.evalCoeffs, LawfulCommRing.add_zero]
  | _ :: cs, _ :: ds, x => by
    simp only [ospcPolyAddCoeffs, RoundPoly.evalCoeffs, evalCoeffs_ospcPolyAdd cs ds x,
      LawfulCommRing.left_distrib, LawfulCommRing.add_add_add_comm]

theorem eval_ospcPolyAdd {R : Type} [LawfulCommRing R] (p q : RoundPoly R) (x : R) :
    (ospcPolyAdd p q).eval x = CommRingOps.add (p.eval x) (q.eval x) :=
  evalCoeffs_ospcPolyAdd p.coeffs q.coeffs x

def stepButterflySumcheck2Hop {R : Type} [CommRingOps R] (s : Fin 4 → RoundPoly R) : Fin 4 → RoundPoly R :=
  let p0 : Fin 4 → RoundPoly R := fun t => ospcPolyAdd (s (q2OrderedLo ⟨0, by omega⟩ t)) (s (q2OrderedHi ⟨0, by omega⟩ t))
  fun t => ospcPolyAdd (p0 (q2OrderedLo ⟨1, by omega⟩ t)) (p0 (q2OrderedHi ⟨1, by omega⟩ t))
def stepButterflySumcheckUnordered {R : Type} [CommRingOps R] (s : Fin 4 → RoundPoly R) : Fin 4 → RoundPoly R :=
  let p0 : Fin 4 → RoundPoly R := fun t => ospcPolyAdd (s t) (s (q2Partner ⟨0, by omega⟩ t))
  fun t => ospcPolyAdd (p0 t) (p0 (q2Partner ⟨1, by omega⟩ t))

theorem q2Butterfly_sumcheck_canonical_eq {R : Type} [CommRingOps R] (s : Fin 4 → RoundPoly R) (t : Fin 4) :
    stepButterflySumcheck2Hop s t = ospcPolyAdd (ospcPolyAdd (s ⟨0, by omega⟩) (s ⟨1, by omega⟩)) (ospcPolyAdd (s ⟨2, by omega⟩) (s ⟨3, by omega⟩)) := by
  match t with | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩ => rfl

theorem q2Butterfly_sumcheck_lockstep_exact {R : Type} [LawfulCommRing R] (s : Fin 4 → RoundPoly R) (t : Fin 4) (x : R) :
    (stepButterflySumcheck2Hop s t).eval x =
      CommRingOps.add (CommRingOps.add ((s ⟨0, by omega⟩).eval x) ((s ⟨1, by omega⟩).eval x))
                      (CommRingOps.add ((s ⟨2, by omega⟩).eval x) ((s ⟨3, by omega⟩).eval x)) := by
  rw [q2Butterfly_sumcheck_canonical_eq, eval_ospcPolyAdd, eval_ospcPolyAdd, eval_ospcPolyAdd]

theorem q2Butterfly_sumcheck_unordered_exact {R : Type} [LawfulCommRing R] (s : Fin 4 → RoundPoly R) (t : Fin 4) (x : R) :
    (stepButterflySumcheckUnordered s t).eval x =
      CommRingOps.add (CommRingOps.add ((s ⟨0, by omega⟩).eval x) ((s ⟨1, by omega⟩).eval x))
                      (CommRingOps.add ((s ⟨2, by omega⟩).eval x) ((s ⟨3, by omega⟩).eval x)) := by
  match t with
  | ⟨0, _⟩ => simp only [stepButterflySumcheckUnordered, q2Partner, eval_ospcPolyAdd]
  | ⟨1, _⟩ => simp only [stepButterflySumcheckUnordered, q2Partner, eval_ospcPolyAdd]; rw [LawfulCommRing.add_comm ((s ⟨1, by omega⟩).eval x), LawfulCommRing.add_comm ((s ⟨3, by omega⟩).eval x)]
  | ⟨2, _⟩ => simp only [stepButterflySumcheckUnordered, q2Partner, eval_ospcPolyAdd]; rw [LawfulCommRing.add_comm]
  | ⟨3, _⟩ => simp only [stepButterflySumcheckUnordered, q2Partner, eval_ospcPolyAdd]; rw [LawfulCommRing.add_comm ((s ⟨3, by omega⟩).eval x), LawfulCommRing.add_comm ((s ⟨1, by omega⟩).eval x), LawfulCommRing.add_comm]

theorem q2Butterfly_transcript_lockstep {R : Type} [CommRingOps R] [TranscriptChallenge R]
    {phase : TranscriptPhase} [CanSqueezeTranscript phase] (s : Fin 4 → RoundPoly R) (tr : Transcript phase) (t₁ t₂ : Fin 4) :
    absorbAndSqueezeRound (stepButterflySumcheck2Hop s t₁) tr = absorbAndSqueezeRound (stepButterflySumcheck2Hop s t₂) tr := by
  rw [q2Butterfly_sumcheck_canonical_eq s t₁, q2Butterfly_sumcheck_canonical_eq s t₂]
def q2MleFoldStep {R : Type} [CommRingOps R] (lo hi r : R) : R := CommRingOps.add lo (CommRingOps.mul r (CommRingOps.sub hi lo))
def stepButterflyMleFold2Hop {R : Type} [CommRingOps R] (v : Fin 4 → R) (r0 r1 : R) : Fin 4 → R :=
  let f0 : Fin 4 → R := fun t => q2MleFoldStep (v (q2OrderedLo ⟨0, by omega⟩ t)) (v (q2OrderedHi ⟨0, by omega⟩ t)) r0
  fun t => q2MleFoldStep (f0 (q2OrderedLo ⟨1, by omega⟩ t)) (f0 (q2OrderedHi ⟨1, by omega⟩ t)) r1

theorem q2Butterfly_mleFold_eq_mleEval {R : Type} [LawfulCommRing R] (v : Fin 4 → R) (r0 r1 : R) (t : Fin 4) :
    let tbl := [v ⟨0, by omega⟩, v ⟨1, by omega⟩, v ⟨2, by omega⟩, v ⟨3, by omega⟩]
    stepButterflyMleFold2Hop v r0 r1 t = mleEval tbl [r0, r1] ∧ [stepButterflyMleFold2Hop v r0 r1 t] = foldFirstVar (foldFirstVar tbl r0) r1 := by
  have hcanon : stepButterflyMleFold2Hop v r0 r1 t =
      q2MleFoldStep (q2MleFoldStep (v ⟨0, by omega⟩) (v ⟨1, by omega⟩) r0) (q2MleFoldStep (v ⟨2, by omega⟩) (v ⟨3, by omega⟩) r0) r1 := by
    match t with | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩ => rfl
  have hfold : foldFirstVar (foldFirstVar [v ⟨0, by omega⟩, v ⟨1, by omega⟩, v ⟨2, by omega⟩, v ⟨3, by omega⟩] r0) r1 =
      [q2MleFoldStep (q2MleFoldStep (v ⟨0, by omega⟩) (v ⟨1, by omega⟩) r0) (q2MleFoldStep (v ⟨2, by omega⟩) (v ⟨3, by omega⟩) r0) r1] := rfl
  refine ⟨?_, by rw [hcanon, hfold]⟩
  rw [← mleEval_foldFirstVar, ← mleEval_foldFirstVar, hfold, hcanon]
  simp only [mleEval, List.length_nil, hypercube, List.map_cons, List.map_nil, eqPoly, innerProd, LawfulCommRing.mul_one, LawfulCommRing.add_zero]
def stepButterflyMerkle2Hop (H : Hash) (leaf : Fin 4 → Nat) : Fin 4 → Nat :=
  let m0 : Fin 4 → Nat := fun t => digestWith H (leaf (q2OrderedLo ⟨0, by omega⟩ t)) (leaf (q2OrderedHi ⟨0, by omega⟩ t))
  fun t => digestWith H (m0 (q2OrderedLo ⟨1, by omega⟩ t)) (m0 (q2OrderedHi ⟨1, by omega⟩ t))

theorem q2Butterfly_merkle_canonical_eq (H : Hash) (leaf : Fin 4 → Nat) (t : Fin 4) :
    stepButterflyMerkle2Hop H leaf t =
      digestWith H (digestWith H (leaf ⟨0, by omega⟩) (leaf ⟨1, by omega⟩)) (digestWith H (leaf ⟨2, by omega⟩) (leaf ⟨3, by omega⟩)) := by
  match t with | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩ => rfl
private theorem merkle_root_singleton (H : Hash) (x : Nat) : Obend.Receipt.Merkle.root H [x] = x := by rw [Obend.Receipt.Merkle.root]; simp
private theorem merkle_root_pair (H : Hash) (x y : Nat) : Obend.Receipt.Merkle.root H [x, y] = digestWith H x y := by
  rw [Obend.Receipt.Merkle.root]; simp [merkle_root_singleton]

theorem q2Butterfly_merkle_eq_canonical_root (H : Hash) (L0 L1 L2 L3 : Nat) (t : Fin 4) :
    stepButterflyMerkle2Hop H (fun i => [L0, L1, L2, L3][i]) t = Obend.Receipt.Merkle.root H [L0, L1, L2, L3] := by
  rw [q2Butterfly_merkle_canonical_eq]; conv => rhs; rw [Obend.Receipt.Merkle.root]
  simp [merkle_root_pair]; rfl

def q2ButterflyMerklePreimages (H : Hash) (leaf : Fin 4 → Nat) : List (List UInt8) :=
  let l0 := leaf ⟨0, by omega⟩; let l1 := leaf ⟨1, by omega⟩
  let l2 := leaf ⟨2, by omega⟩; let l3 := leaf ⟨3, by omega⟩
  [preimage (digestWith H l0 l1) (digestWith H l2 l3), preimage l0 l1, preimage l2 l3]

theorem q2Butterfly_merkle_binding (H : Hash) (hb : Obend.Receipt.Merkle.Bounded H)
    (a b : Fin 4 → Nat) (ha : ∀ i : Fin 4, a i < 2 ^ 256) (hb' : ∀ i : Fin 4, b i < 2 ^ 256)
    (t₁ t₂ : Fin 4) (hEq : stepButterflyMerkle2Hop H a t₁ = stepButterflyMerkle2Hop H b t₂) :
    (∀ i : Fin 4, a i = b i) ∨
      CollisionAmong H (fun m => m ∈ q2ButterflyMerklePreimages H a ++ q2ButterflyMerklePreimages H b) := by
  rw [q2Butterfly_merkle_canonical_eq H a t₁, q2Butterfly_merkle_canonical_eq H b t₂] at hEq
  rcases binds_or_collides H (admissible_of_lt (hb _ _)) (admissible_of_lt (hb _ _)) hEq with ⟨hL, hR⟩ | hC
  · rcases binds_or_collides H (admissible_of_lt (ha ⟨0, by omega⟩)) (admissible_of_lt (hb' ⟨0, by omega⟩)) hL with ⟨h0, h1⟩ | hCL
    · rcases binds_or_collides H (admissible_of_lt (ha ⟨2, by omega⟩)) (admissible_of_lt (hb' ⟨2, by omega⟩)) hR with ⟨h2, h3⟩ | hCR
      · left; intro i; match i with | ⟨0, _⟩ => exact h0 | ⟨1, _⟩ => exact h1 | ⟨2, _⟩ => exact h2 | ⟨3, _⟩ => exact h3
      · exact .inr (hCR.mono fun p hp => by rcases hp with rfl | rfl <;> simp [q2ButterflyMerklePreimages])
    · exact .inr (hCL.mono fun p hp => by rcases hp with rfl | rfl <;> simp [q2ButterflyMerklePreimages])
  · exact .inr (hC.mono fun p hp => by rcases hp with rfl | rfl <;> simp [q2ButterflyMerklePreimages])

/-! ## 4. 256-Bit Receipt Packing, Multi-Cycle Trace Soundness & `ospcProverJudge` -/
def packReceiptLimbs256 (l0 l1 l2 l3 : BitVec 64) : BitVec 256 := (l0 ++ l1) ++ (l2 ++ l3)
def unpackReceiptLimbs256 (r : BitVec 256) : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 :=
  (r.extractLsb' 192 64, r.extractLsb' 128 64, r.extractLsb' 64 64, r.extractLsb' 0 64)
theorem unpack_pack_receiptLimbs256 (l0 l1 l2 l3 : BitVec 64) :
    unpackReceiptLimbs256 (packReceiptLimbs256 l0 l1 l2 l3) = (l0, l1, l2, l3) := by
  unfold unpackReceiptLimbs256 packReceiptLimbs256; simp only [Prod.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply BitVec.eq_of_getLsbD_eq; intro i hi; simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi, decide_true, Bool.true_and, show ¬(192 + i < 128) by omega, show ¬(192 + i - 128 < 64) by omega, show 192 + i - 128 - 64 = i by omega, ↓reduceIte]
  · apply BitVec.eq_of_getLsbD_eq; intro i hi; simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi, decide_true, Bool.true_and, show ¬(128 + i < 128) by omega, show 128 + i - 128 = i by omega, ↓reduceIte]
  · apply BitVec.eq_of_getLsbD_eq; intro i hi; simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi, decide_true, Bool.true_and, show 64 + i < 128 by omega, show ¬(64 + i < 64) by omega, show 64 + i - 64 = i by omega, ↓reduceIte]
  · apply BitVec.eq_of_getLsbD_eq; intro i hi; simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi, decide_true, Bool.true_and, Nat.zero_add, show i < 128 by omega, ↓reduceIte]
theorem pack_unpack_receiptLimbs256 (r : BitVec 256) :
    let (l0, l1, l2, l3) := unpackReceiptLimbs256 r; packReceiptLimbs256 l0 l1 l2 l3 = r := by
  unfold unpackReceiptLimbs256 packReceiptLimbs256; apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  by_cases h1 : i < 64
  · simp [h1, show i < 128 by omega]
  · by_cases h2 : i < 128
    · simp [h1, h2, show i - 64 < 64 by omega, show 64 + (i - 64) = i by omega]
    · by_cases h3 : i < 192
      · simp [h2, show i - 128 < 64 by omega, show 128 + (i - 128) = i by omega]
      · simp [h2, show ¬(i - 128 < 64) by omega, show i - 128 - 64 < 64 by omega, show 192 + (i - 128 - 64) = i by omega]
def encodeOspcReceipt256 (r : BitVec 256) : ByteArray := Native.bytesOfList (be 32 r.toNat)
theorem encodeOspcReceipt256_size (r : BitVec 256) : (encodeOspcReceipt256 r).size = 32 := by
  unfold encodeOspcReceipt256; rw [Fast.size_eq_length, Native.bytesOfList_toList, length_be]
theorem encodeOspcReceipt256_injective {r₁ r₂ : BitVec 256} (h : encodeOspcReceipt256 r₁ = encodeOspcReceipt256 r₂) : r₁ = r₂ := by
  have hl := congrArg (fun b => b.data.toList) h; simp only [encodeOspcReceipt256, Native.bytesOfList_toList] at hl
  have h256 : (2 : Nat) ^ 256 = 256 ^ 32 := by decide
  exact BitVec.eq_of_toNat_eq (be_injective (h256 ▸ r₁.isLt) (h256 ▸ r₂.isLt) hl)

/-! ### Fixed-Width Per-Tile Inputs, Public Instance & Multi-Cycle Execution -/

structure Tile0Input where
  opSel : BitVec 2
  inLo64 : BitVec 64
  inHi17 : BitVec 17
  camWe : BitVec 1
  camAddr : BitVec 8
  camWdata : BitVec 64
  camQtag : BitVec 64
  deriving DecidableEq, Repr
def Tile0Input.toPortEnv (x : Tile0Input) : Nat → BitVec 64
  | 0 => x.opSel.setWidth 64 | 1 => x.inLo64 | 2 => x.inHi17.setWidth 64 | 3 => x.camWe.setWidth 64
  | 4 => x.camAddr.setWidth 64 | 5 => x.camWdata | 6 => x.camQtag | _ => 0#64

structure Tile1Input where
  stepEn : BitVec 1
  symTag : BitVec 6
  lutWe : BitVec 1
  lutWaddr : BitVec 12
  lutWdata : BitVec 64
  deriving DecidableEq, Repr
def Tile1Input.toPortEnv (x : Tile1Input) : Nat → BitVec 64
  | 0 => x.stepEn.setWidth 64 | 1 => x.symTag.setWidth 64 | 2 => x.lutWe.setWidth 64 | 3 => x.lutWaddr.setWidth 64 | 4 => x.lutWdata | _ => 0#64

structure Tile2Input where
  redexEn : BitVec 1
  peerWord : DeltaPortWord64
  portWe : BitVec 1
  portAddr : BitVec 8
  portWdata : DeltaPortWord64
  deriving DecidableEq, Repr
def Tile2Input.toPortEnv (x : Tile2Input) : Nat → BitVec 64
  | 0 => x.redexEn.setWidth 64 | 1 => x.peerWord.pack | 2 => x.portWe.setWidth 64 | 3 => x.portAddr.setWidth 64 | 4 => x.portWdata.pack | _ => 0#64

structure Tile3Input where
  stepEn : BitVec 1
  clauseWe : BitVec 1
  clauseAddr : BitVec 8
  clauseWdata : LratStreamReg64
  deriving DecidableEq, Repr
def Tile3Input.toPortEnv (x : Tile3Input) : Nat → BitVec 64
  | 0 => x.stepEn.setWidth 64 | 1 => x.clauseWe.setWidth 64 | 2 => x.clauseAddr.setWidth 64 | 3 => x.clauseWdata.pack | _ => 0#64

structure OspcPublicInstance where
  protocolId : Nat
  numCycles : Nat
  claimedSum : Goldilocks
  seedLimb0 : BitVec 64
  seedLimb1 : BitVec 64
  seedLimb2 : BitVec 64
  seedLimb3 : BitVec 64
  deriving DecidableEq, Repr

instance : TranscriptEncode OspcPublicInstance where
  encodeTranscriptBytes inst :=
    encodeFrame (Native.bytesOfList (leb128 inst.protocolId ++ leb128 inst.numCycles))
      (encodeGoldilocksBytes inst.claimedSum)
      (encodeOspcReceipt256 (packReceiptLimbs256 inst.seedLimb0 inst.seedLimb1 inst.seedLimb2 inst.seedLimb3))

instance : LawfulTranscriptEncode OspcPublicInstance where
  encodeTranscriptBytes_injective {a b} h := by
    obtain ⟨h1, h2, h3⟩ := encodeFrame_injective h
    have hl : leb128 a.protocolId ++ leb128 a.numCycles = leb128 b.protocolId ++ leb128 b.numCycles := by
      simpa [Native.bytesOfList_toList] using congrArg (fun x => x.data.toList) h1
    obtain ⟨hp, htail⟩ := leb128_prefix_inj hl
    obtain ⟨hn, _⟩ := leb128_prefix_inj (r₁ := []) (r₂ := []) (by simpa [List.append_nil] using htail)
    have hsum := encodeGoldilocksBytes_injective h2
    have hunp := congrArg unpackReceiptLimbs256 (encodeOspcReceipt256_injective h3)
    rw [unpack_pack_receiptLimbs256, unpack_pack_receiptLimbs256] at hunp; simp only [Prod.mk.injEq] at hunp
    rcases a with ⟨p1, n1, s1, a0, a1, a2, a3⟩; rcases b with ⟨p2, n2, s2, b0, b1, b2, b3⟩
    simp only at hp hn hsum hunp; rcases hunp with ⟨rfl, rfl, rfl, rfl⟩; subst hp hn hsum; rfl

inductive OspcRefusal where
  | emptyTrace | deltaNetLinearityViolation | lratNotUnitOrConflict
  | sumcheckPolyDegreeExceeded | sumcheckSumMismatch | receiptMismatch | certWitnessMismatch
  deriving DecidableEq, Repr

structure OspcProverCycleTurn where
  rst : Bool
  tile0 : Tile0Input
  tile1 : Tile1Input
  tile2 : Tile2Input
  tile3 : Tile3Input
  tilePolys : Fin 4 → RoundPoly Goldilocks
  maxDeg : Nat
def OspcProverCycleTurn.inputsFor (turn : OspcProverCycleTurn) : Fin 4 → (Nat → BitVec 64)
  | ⟨0, _⟩ => turn.tile0.toPortEnv | ⟨1, _⟩ => turn.tile1.toPortEnv
  | ⟨2, _⟩ => turn.tile2.toPortEnv | ⟨3, _⟩ => turn.tile3.toPortEnv

structure Ospc4TileProverState where
  tiles : Fin 4 → MemState
  transcript : Transcript .instanceBound
  currentClaim : Goldilocks
  merkleRoot : Nat
  verifierReceipt256 : BitVec 256
  cycleCount : Nat
def tileMemStateBounded (m : RtlMemModule) (st : MemState) : Prop :=
  (∀ i : Nat, (st.regs i).toNat < 2 ^ memRegWidthOf m i) ∧ (∀ k : Nat, ∀ a : BitVec 64, (st.mems k a).toNat < 2 ^ ramDataWidthOf m k)
def tileSummaryWord64 : Fin 4 → MemState → BitVec 64
  | ⟨0, _⟩, st => st.regs 0 ^^^ st.regs 1 | ⟨1, _⟩, st => st.regs 0 ||| (st.regs 1 <<< 6)
  | ⟨2, _⟩, st => st.regs 0 ||| (st.regs 1 <<< 32) | ⟨3, _⟩, st => st.regs 0 ||| (st.regs 1 <<< 32)
def tileLeavesOf (tiles : Fin 4 → MemState) : Fin 4 → Nat := fun t => (tileSummaryWord64 t (tiles t)).toNat
def tileLeafList (tiles : Fin 4 → MemState) : List Nat :=
  [tileLeavesOf tiles ⟨0, by omega⟩, tileLeavesOf tiles ⟨1, by omega⟩, tileLeavesOf tiles ⟨2, by omega⟩, tileLeavesOf tiles ⟨3, by omega⟩]
def computeCycleReceipt256 (H : Hash) (trState : ByteArray) (merkleRoot : Nat) : BitVec 256 :=
  BitVec.ofNat 256 (digestWith H (ofBE trState.data.toList) merkleRoot)
def initOspcTiles : Fin 4 → MemState := fun t =>
  if t.val = 2 then ⟨fun i => if i = 1 then 1#64 else 0#64, fun _ _ => 0#64⟩ else ⟨fun _ => 0#64, fun _ _ => 0#64⟩
def initOspc4TileState (H : Hash) (inst : OspcPublicInstance) : Ospc4TileProverState :=
  let tr0 := Transcript.newUnseeded (encodeOspcReceipt256 (packReceiptLimbs256 inst.seedLimb0 inst.seedLimb1 inst.seedLimb2 inst.seedLimb3))
  let trRel := bindRelation "OBEND.OSPC.4TILE.Q2/v1" (Native.bytesOfList (leb128 4 ++ leb128 81)) (encodeGoldilocksBytes inst.claimedSum) tr0
  let btr := bindInstance inst trRel
  let mRoot := stepButterflyMerkle2Hop H (tileLeavesOf initOspcTiles) ⟨0, by omega⟩
  ⟨initOspcTiles, btr.transcript, inst.claimedSum, mRoot, computeCycleReceipt256 H btr.transcript.state mRoot, 0⟩
private theorem initOspc4TileState_tiles (H : Hash) (inst : OspcPublicInstance) : (initOspc4TileState H inst).tiles = initOspcTiles := rfl
private theorem initOspc4TileState_claim (H : Hash) (inst : OspcPublicInstance) : (initOspc4TileState H inst).currentClaim = inst.claimedSum := rfl
def tile3LratStepValid (st3 : MemState) : Bool :=
  let ap := (st3.regs 0).extractLsb' 0 32; let an := (st3.regs 1).extractLsb' 0 32; let w := LratStreamReg64.unpack (st3.regs 3)
  lratBitmaskConflict ap an w || lratBitmaskUnitPos ap an w || lratBitmaskUnitNeg ap an w
def stepOspc4TileCycle (H : Hash) (st : Ospc4TileProverState) (turn : OspcProverCycleTurn) :
    Except OspcRefusal Ospc4TileProverState :=
  let tiles' : Fin 4 → MemState := fun t => stepMemModule (ospcTileRtl t) turn.rst (turn.inputsFor t) (st.tiles t)
  if (tiles' ⟨2, by omega⟩).regs 1 != 1#64 then .error .deltaNetLinearityViolation
  else if !turn.rst && (turn.tile3.stepEn == 1#1) && !tile3LratStepValid (st.tiles ⟨3, by omega⟩) then .error .lratNotUnitOrConflict
  else
    let aggPoly := stepButterflySumcheck2Hop turn.tilePolys ⟨0, by omega⟩
    if !aggPoly.degLe turn.maxDeg then .error .sumcheckPolyDegreeExceeded
    else if CommRingOps.add (aggPoly.eval CommRingOps.zero) (aggPoly.eval CommRingOps.one) != st.currentClaim then .error .sumcheckSumMismatch
    else
      let sq := absorbAndSqueezeRound aggPoly st.transcript
      let mRoot := stepButterflyMerkle2Hop H (tileLeavesOf tiles') ⟨0, by omega⟩
      .ok ⟨tiles', sq.2, aggPoly.eval sq.1, mRoot, computeCycleReceipt256 H sq.2.state mRoot, st.cycleCount + 1⟩
def runOspc4TileTrace (H : Hash) : Ospc4TileProverState → List OspcProverCycleTurn → Except OspcRefusal Ospc4TileProverState
  | st, [] => .ok st
  | st, turn :: rest => match stepOspc4TileCycle H st turn with | .error e => .error e | .ok st' => runOspc4TileTrace H st' rest
private theorem bv_setWidth_toNat_lt {w : Nat} (hw : w ≤ 64) (x : BitVec w) : (x.setWidth 64).toNat < 2 ^ w := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by decide) hw))]; exact x.isLt
private theorem turn_inputs_bounded (turn : OspcProverCycleTurn) (t : Fin 4) (i : Nat) :
    (turn.inputsFor t i).toNat < 2 ^ inputWidth (ospcTileRtl t).core i := by
  match t with
  | ⟨0, _⟩ => match i with
    | 0 => exact bv_setWidth_toNat_lt (by decide) turn.tile0.opSel | 1 => exact turn.tile0.inLo64.isLt
    | 2 => exact bv_setWidth_toNat_lt (by decide) turn.tile0.inHi17 | 3 => exact bv_setWidth_toNat_lt (by decide) turn.tile0.camWe
    | 4 => exact bv_setWidth_toNat_lt (by decide) turn.tile0.camAddr | 5 => exact turn.tile0.camWdata.isLt | 6 => exact turn.tile0.camQtag.isLt
    | _ + 7 => simp [OspcProverCycleTurn.inputsFor, Tile0Input.toPortEnv, ospcTileRtl, tile0_exprcam_face4, inputWidth]
  | ⟨1, _⟩ => match i with
    | 0 => exact bv_setWidth_toNat_lt (by decide) turn.tile1.stepEn | 1 => exact bv_setWidth_toNat_lt (by decide) turn.tile1.symTag
    | 2 => exact bv_setWidth_toNat_lt (by decide) turn.tile1.lutWe | 3 => exact bv_setWidth_toNat_lt (by decide) turn.tile1.lutWaddr | 4 => exact turn.tile1.lutWdata.isLt
    | _ + 5 => simp [OspcProverCycleTurn.inputsFor, Tile1Input.toPortEnv, ospcTileRtl, tile1_discrtree_lut, inputWidth]
  | ⟨2, _⟩ => match i with
    | 0 => exact bv_setWidth_toNat_lt (by decide) turn.tile2.redexEn | 1 => exact turn.tile2.peerWord.pack.isLt
    | 2 => exact bv_setWidth_toNat_lt (by decide) turn.tile2.portWe | 3 => exact bv_setWidth_toNat_lt (by decide) turn.tile2.portAddr | 4 => exact turn.tile2.portWdata.pack.isLt
    | _ + 5 => simp [OspcProverCycleTurn.inputsFor, Tile2Input.toPortEnv, ospcTileRtl, tile2_deltanet_redex, inputWidth]
  | ⟨3, _⟩ => match i with
    | 0 => exact bv_setWidth_toNat_lt (by decide) turn.tile3.stepEn | 1 => exact bv_setWidth_toNat_lt (by decide) turn.tile3.clauseWe
    | 2 => exact bv_setWidth_toNat_lt (by decide) turn.tile3.clauseAddr | 3 => exact turn.tile3.clauseWdata.pack.isLt
    | _ + 4 => simp [OspcProverCycleTurn.inputsFor, Tile3Input.toPortEnv, ospcTileRtl, tile3_stream_lrat, inputWidth]
private theorem tile_stepMemModule_preserves_bounded (t : Fin 4) (rst : Bool) (inputs : Nat → BitVec 64) (st : MemState)
    (hIn : ∀ i, (inputs i).toNat < 2 ^ inputWidth (ospcTileRtl t).core i) (hSt : tileMemStateBounded (ospcTileRtl t) st) :
    tileMemStateBounded (ospcTileRtl t) (stepMemModule (ospcTileRtl t) rst inputs st) := by
  have hChk := ospcTileRtl_checkRtlMemModuleW t
  have hWidths : checkMemWidths (ospcTileRtl t) = true := by unfold checkRtlMemModuleW at hChk; simp only [Bool.and_eq_true] at hChk; exact hChk.2
  have hParts := checkMemWidths_parts (ospcTileRtl t) hWidths
  have hW := evalMemWireTable_lt (ospcTileRtl t) inputs st.regs hIn hSt.1 hWidths
  have hRegStep : ∀ r ∈ (ospcTileRtl t).core.regs,
      (regNextValue rst inputs (evalWireTable inputs st.regs (ospcTileRtl t).core.wires) st.regs r).toNat < 2 ^ memRegWidthOf (ospcTileRtl t) r.regIdx := by
    intro r hrMem; have hrSpec := hParts.2.1 r hrMem; obtain ⟨w, hw, hle⟩ := fitErrors_nil hrSpec.2.1
    have hNext := Nat.lt_of_lt_of_le (evalRtlExpr_lt_of_inferWidthE (memModuleWidthEnv (ospcTileRtl t)) inputs
      (evalWireTable inputs st.regs (ospcTileRtl t).core.wires) st.regs hIn hW hSt.1 r.nextExpr w hw) (Nat.pow_le_pow_right (by decide) hle)
    have hLtLen : r.regIdx < (ospcTileRtl t).core.regs.length := by
      match t with
      | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩ =>
        simp only [ospcTileRtl, tile0_exprcam_face4, tile1_discrtree_lut, tile2_deltanet_redex, tile3_stream_lrat, List.mem_cons, List.not_mem_nil, or_false] at hrMem
        rcases hrMem with rfl | rfl | rfl <;> simp [ospcTileRtl, tile0_exprcam_face4, tile1_discrtree_lut, tile2_deltanet_redex, tile3_stream_lrat]
    simp only [memRegWidthOf, hLtLen, ↓reduceIte, regNextValue]
    cases hk : r.resetKind with
    | resetFree => exact hNext
    | syncReset initVal =>
      cases rst
      · exact hNext
      · exact Nat.lt_of_lt_of_le Nat.lt_log2_self (Nat.pow_le_pow_right (by decide) (hrSpec.2.2 initVal hk))
  have hCoreRegs : ∀ i, (stepModuleRegs (ospcTileRtl t).core rst inputs st.regs i).toNat < 2 ^ memRegWidthOf (ospcTileRtl t) i := by
    unfold stepModuleRegs
    suffices ∀ (l : List RegSpec), (∀ r ∈ l, r ∈ (ospcTileRtl t).core.regs) →
        ∀ (acc : Nat → BitVec 64), (∀ i, (acc i).toNat < 2 ^ memRegWidthOf (ospcTileRtl t) i) →
        ∀ i, (l.foldl (fun nextSt r => let v := regNextValue rst inputs (evalWireTable inputs st.regs (ospcTileRtl t).core.wires) st.regs r; fun j => if j == r.regIdx then v else nextSt j) acc i).toNat < 2 ^ memRegWidthOf (ospcTileRtl t) i from
      this (ospcTileRtl t).core.regs (fun _ h => h) st.regs hSt.1
    intro l; induction l with
    | nil => intro _ acc hAcc i; exact hAcc i
    | cons r rest ih =>
      intro hSub acc hAcc i; simp only [List.foldl_cons]; apply ih (fun x hx => hSub x (List.mem_cons_of_mem _ hx)); intro j
      by_cases hj : j = r.regIdx
      · subst hj; simp only [beq_self_eq_true, ↓reduceIte]; exact hRegStep r (hSub r List.mem_cons_self)
      · simp only [beq_iff_eq, hj, ↓reduceIte]; exact hAcc j
  have hRamSingle : ∀ (m : RtlMemModule) (ram : SyncRamSpec), m.rams = [ram] → ram.ramIdx = 0 → ram.dataWidth = 64 →
      ramDataWidthOf m 0 = 64 → memRegWidthOf m (m.core.regs.length + 0) = 64 →
      (∀ i, (stepModuleRegs m.core rst inputs st.regs i).toNat < 2 ^ memRegWidthOf m i) →
      (∀ k a, (st.mems k a).toNat < 2 ^ ramDataWidthOf m k) → tileMemStateBounded m (stepMemModule m rst inputs st) := by
    intro m ram hrams hidx hdw hdw0 hmr hc hm; constructor
    · intro i; simp only [hrams, List.foldl_cons, List.foldl_nil, hidx]
      by_cases hi : i = m.core.regs.length + 0
      · subst hi; simp only [beq_self_eq_true, ↓reduceIte, hmr]
        have hlt := evalSyncRamReadNext_lt inputs (evalWireTable inputs st.regs m.core.wires) st.regs (st.mems 0) ram (by omega)
        rw [hdw] at hlt; exact hlt
      · simp only [beq_iff_eq, hi, ↓reduceIte]; exact hc i
    · intro k a; simp only [hrams, List.foldl_cons, List.foldl_nil, hidx]
      by_cases hk : k = 0
      · subst hk; simp only [beq_self_eq_true, ↓reduceIte, hdw0]
        have hlt := stepSyncRamArray_lt inputs (evalWireTable inputs st.regs m.core.wires) st.regs (st.mems 0) ram (by omega)
          (fun b => Nat.lt_of_lt_of_eq (hm 0 b) (congrArg (2 ^ ·) (hdw0.trans hdw.symm))) a
        rw [hdw] at hlt; exact hlt
      · simp only [beq_iff_eq, hk, ↓reduceIte]; exact hm k a
  match t with
  | ⟨0, _⟩ => exact hRamSingle tile0_exprcam_face4 _ rfl rfl rfl (by decide) (by decide) hCoreRegs hSt.2
  | ⟨1, _⟩ => exact hRamSingle tile1_discrtree_lut _ rfl rfl rfl (by decide) (by decide) hCoreRegs hSt.2
  | ⟨2, _⟩ => exact hRamSingle tile2_deltanet_redex _ rfl rfl rfl (by decide) (by decide) hCoreRegs hSt.2
  | ⟨3, _⟩ => exact hRamSingle tile3_stream_lrat _ rfl rfl rfl (by decide) (by decide) hCoreRegs hSt.2
private theorem initOspc4TileState_bounded (H : Hash) (inst : OspcPublicInstance) (t : Fin 4) :
    tileMemStateBounded (ospcTileRtl t) ((initOspc4TileState H inst).tiles t) := by
  constructor
  · intro i; match t with
    | ⟨0, _⟩ | ⟨1, _⟩ | ⟨3, _⟩ =>
      simp only [initOspc4TileState, initOspcTiles, show ¬(0 = 2) by decide, show ¬(1 = 2) by decide,
        show ¬(3 = 2) by decide, ↓reduceIte, BitVec.toNat_ofNat, Nat.zero_mod]; exact Nat.two_pow_pos _
    | ⟨2, _⟩ =>
      simp only [initOspc4TileState, initOspcTiles, ↓reduceIte]
      by_cases hi : i = 1
      · subst hi; simp [ospcTileRtl, tile2_deltanet_redex, memRegWidthOf, regWidthOf]
      · simp only [hi, ↓reduceIte, BitVec.toNat_ofNat, Nat.zero_mod]; exact Nat.two_pow_pos _
  · intro k a; match t with
    | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩ =>
      simp only [initOspc4TileState, initOspcTiles]; split <;> (simp only [BitVec.toNat_ofNat, Nat.zero_mod]; exact Nat.two_pow_pos _)

/-! ### Multi-Turn Trace Reachability (`OspcTraceReach`) & Soundness Theorems -/
def OspcCycleSpec (H : Hash) (st : Ospc4TileProverState) (turn : OspcProverCycleTurn) (st' : Ospc4TileProverState) : Prop :=
  let tiles' : Fin 4 → MemState := fun t => stepMemModule (ospcTileRtl t) turn.rst (turn.inputsFor t) (st.tiles t)
  let aggPoly := stepButterflySumcheck2Hop turn.tilePolys ⟨0, by omega⟩
  (tiles' ⟨2, by omega⟩).regs 1 = 1#64 ∧
  (turn.rst = false → turn.tile3.stepEn = 1#1 → tile3LratStepValid (st.tiles ⟨3, by omega⟩) = true) ∧
  aggPoly.degLe turn.maxDeg = true ∧
  CommRingOps.add (aggPoly.eval CommRingOps.zero) (aggPoly.eval CommRingOps.one) = st.currentClaim ∧
  st' = let sq := absorbAndSqueezeRound aggPoly st.transcript
        let mRoot := stepButterflyMerkle2Hop H (tileLeavesOf tiles') ⟨0, by omega⟩
        ⟨tiles', sq.2, aggPoly.eval sq.1, mRoot, computeCycleReceipt256 H sq.2.state mRoot, st.cycleCount + 1⟩

inductive OspcTraceReach (H : Hash) : Ospc4TileProverState → List OspcProverCycleTurn → Ospc4TileProverState → Prop where
  | nil (st : Ospc4TileProverState) : OspcTraceReach H st [] st
  | cons {st stMid stEnd : Ospc4TileProverState} {turn : OspcProverCycleTurn} {rest : List OspcProverCycleTurn} :
      OspcCycleSpec H st turn stMid → OspcTraceReach H stMid rest stEnd → OspcTraceReach H st (turn :: rest) stEnd

theorem stepOspc4TileCycle_eq_ok_iff (H : Hash) (st st' : Ospc4TileProverState) (turn : OspcProverCycleTurn) :
    stepOspc4TileCycle H st turn = .ok st' ↔ OspcCycleSpec H st turn st' := by
  unfold stepOspc4TileCycle OspcCycleSpec; dsimp only; constructor
  · intro h; split at h; · cases h
    · rename_i hLin; split at h; · cases h
      · rename_i hLrat; split at h; · cases h
        · rename_i hDeg; split at h; · cases h
          · rename_i hSum; simp only [Except.ok.injEq] at h
            refine ⟨by simpa using hLin, fun hrst hen => ?_, by simpa using hDeg, by simpa using hSum, h.symm⟩
            cases hv : tile3LratStepValid (st.tiles ⟨3, by omega⟩)
            · have hc : (!turn.rst && (turn.tile3.stepEn == 1#1) && !tile3LratStepValid (st.tiles ⟨3, by omega⟩)) = true := by
                rw [hrst, hen, hv]; rfl
              exact False.elim (hLrat hc)
            · rfl
  · rintro ⟨hLin, hLrat, hDeg, hSum, rfl⟩
    have h1 : ((stepMemModule (ospcTileRtl ⟨2, by omega⟩) turn.rst (turn.inputsFor ⟨2, by omega⟩) (st.tiles ⟨2, by omega⟩)).regs 1 != 1#64) = false := by
      simp only [hLin, bne_self_eq_false]
    have h2 : (!turn.rst && (turn.tile3.stepEn == 1#1) && !tile3LratStepValid (st.tiles ⟨3, by omega⟩)) = false := by
      cases hr : turn.rst
      · cases he : (turn.tile3.stepEn == 1#1)
        · simp
        · simp only [Bool.not_false, Bool.true_and, hLrat hr (eq_of_beq he), Bool.not_true]
      · simp
    have h3 : (!(stepButterflySumcheck2Hop turn.tilePolys ⟨0, by omega⟩).degLe turn.maxDeg) = false := by simp only [hDeg, Bool.not_true]
    have h4 : (CommRingOps.add ((stepButterflySumcheck2Hop turn.tilePolys ⟨0, by omega⟩).eval CommRingOps.zero)
        ((stepButterflySumcheck2Hop turn.tilePolys ⟨0, by omega⟩).eval CommRingOps.one) != st.currentClaim) = false := by simp only [hSum, bne_self_eq_false]
    simp only [h1, h2, h3, h4, Bool.false_eq_true, ↓reduceIte]

theorem runOspc4TileTrace_eq_ok_iff (H : Hash) :
    ∀ (turns : List OspcProverCycleTurn) (st stFinal : Ospc4TileProverState),
      runOspc4TileTrace H st turns = .ok stFinal ↔ OspcTraceReach H st turns stFinal
  | [], st, stFinal => ⟨fun h => by simp only [runOspc4TileTrace, Except.ok.injEq] at h; subst h; exact .nil st, fun h => by cases h; rfl⟩
  | turn :: rest, st, stFinal => by
    constructor
    · intro h; unfold runOspc4TileTrace at h
      cases hs : stepOspc4TileCycle H st turn with
      | error e => rw [hs] at h; cases h
      | ok stMid => rw [hs] at h; exact .cons ((stepOspc4TileCycle_eq_ok_iff H st stMid turn).mp hs) ((runOspc4TileTrace_eq_ok_iff H rest stMid stFinal).mp h)
    · intro h; cases h with
      | cons hSpec hRest => unfold runOspc4TileTrace; rw [(stepOspc4TileCycle_eq_ok_iff H st _ turn).mpr hSpec]; exact (runOspc4TileTrace_eq_ok_iff H rest _ stFinal).mpr hRest
private theorem merkle_butterfly_eq_leafList (H : Hash) (tiles : Fin 4 → MemState) :
    stepButterflyMerkle2Hop H (tileLeavesOf tiles) ⟨0, by omega⟩ = Obend.Receipt.Merkle.root H (tileLeafList tiles) := by
  have h := q2Butterfly_merkle_eq_canonical_root H (tileLeavesOf tiles ⟨0, by omega⟩) (tileLeavesOf tiles ⟨1, by omega⟩)
    (tileLeavesOf tiles ⟨2, by omega⟩) (tileLeavesOf tiles ⟨3, by omega⟩) ⟨0, by omega⟩
  have hfn : (fun i : Fin 4 => [tileLeavesOf tiles ⟨0, by omega⟩, tileLeavesOf tiles ⟨1, by omega⟩, tileLeavesOf tiles ⟨2, by omega⟩, tileLeavesOf tiles ⟨3, by omega⟩][i]) = tileLeavesOf tiles := by
    funext i; match i with | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩ => rfl
  rw [hfn] at h; exact h
private theorem traceReach_invariants (H : Hash) :
    ∀ {st stFinal : Ospc4TileProverState} {turns : List OspcProverCycleTurn},
      OspcTraceReach H st turns stFinal → (∀ t : Fin 4, tileMemStateBounded (ospcTileRtl t) (st.tiles t)) →
      (st.tiles ⟨2, by omega⟩).regs 1 = 1#64 → st.merkleRoot = Obend.Receipt.Merkle.root H (tileLeafList st.tiles) →
      stFinal.cycleCount = st.cycleCount + turns.length ∧ (∀ t : Fin 4, tileMemStateBounded (ospcTileRtl t) (stFinal.tiles t)) ∧
      (stFinal.tiles ⟨2, by omega⟩).regs 1 = 1#64 ∧ stFinal.merkleRoot = Obend.Receipt.Merkle.root H (tileLeafList stFinal.tiles)
  | _, _, [], .nil _, hBnd, hLin, hRoot => ⟨by simp, hBnd, hLin, hRoot⟩
  | st, _, turn :: rest, @OspcTraceReach.cons _ _ stMid _ _ _ hSpec hRest, hBnd, _, _ => by
    obtain ⟨hLinMid, _, _, _, hMidEq⟩ := hSpec
    have hBndMid : ∀ t : Fin 4, tileMemStateBounded (ospcTileRtl t) (stMid.tiles t) := fun t => by
      rw [hMidEq]; exact tile_stepMemModule_preserves_bounded t turn.rst (turn.inputsFor t) (st.tiles t) (turn_inputs_bounded turn t) (hBnd t)
    have hLinMid' : (stMid.tiles ⟨2, by omega⟩).regs 1 = 1#64 := by rw [hMidEq]; exact hLinMid
    have hRootMid : stMid.merkleRoot = Obend.Receipt.Merkle.root H (tileLeafList stMid.tiles) := by rw [hMidEq]; exact merkle_butterfly_eq_leafList H _
    obtain ⟨hCnt, hBndEnd, hLinEnd, hRootEnd⟩ := traceReach_invariants H hRest hBndMid hLinMid' hRootMid
    have hMidCnt : stMid.cycleCount = st.cycleCount + 1 := by rw [hMidEq]
    exact ⟨by simp only [List.length_cons]; omega, hBndEnd, hLinEnd, hRootEnd⟩

theorem ospc_four_tile_prover_multi_cycle_sound
    (H : Hash) (inst : OspcPublicInstance) (turns : List OspcProverCycleTurn) (stFinal : Ospc4TileProverState)
    (hRun : runOspc4TileTrace H (initOspc4TileState H inst) turns = .ok stFinal) :
    OspcTraceReach H (initOspc4TileState H inst) turns stFinal ∧ stFinal.cycleCount = turns.length ∧
    (∀ t : Fin 4, checkRtlMemModuleW (ospcTileRtl t) = true ∧ tileMemStateBounded (ospcTileRtl t) (stFinal.tiles t)) ∧
    (stFinal.tiles ⟨2, by omega⟩).regs 1 = 1#64 ∧
    stFinal.merkleRoot = Obend.Receipt.Merkle.root H (tileLeafList stFinal.tiles) ∧
    (encodeOspcReceipt256 stFinal.verifierReceipt256).size = 32 ∧
    (let (l0, l1, l2, l3) := unpackReceiptLimbs256 stFinal.verifierReceipt256; packReceiptLimbs256 l0 l1 l2 l3 = stFinal.verifierReceipt256) := by
  have hReach := (runOspc4TileTrace_eq_ok_iff H turns _ stFinal).mp hRun
  obtain ⟨hCnt, hBnd, hLin, hRoot⟩ := traceReach_invariants H hReach (initOspc4TileState_bounded H inst) rfl (merkle_butterfly_eq_leafList H _)
  have hCnt0 : (initOspc4TileState H inst).cycleCount = 0 := rfl
  exact ⟨hReach, by omega, fun t => ⟨ospcTileRtl_checkRtlMemModuleW t, hBnd t⟩, hLin, hRoot, encodeOspcReceipt256_size _, pack_unpack_receiptLimbs256 _⟩

theorem ospc_single_tile_fault_or_bad_poly_refused
    (H : Hash) (st : Ospc4TileProverState) (turn : OspcProverCycleTurn) (rest : List OspcProverCycleTurn) :
    let tiles' : Fin 4 → MemState := fun t => stepMemModule (ospcTileRtl t) turn.rst (turn.inputsFor t) (st.tiles t)
    let aggPoly := stepButterflySumcheck2Hop turn.tilePolys ⟨0, by omega⟩
    ((tiles' ⟨2, by omega⟩).regs 1 ≠ 1#64 → runOspc4TileTrace H st (turn :: rest) = .error .deltaNetLinearityViolation) ∧
    ((tiles' ⟨2, by omega⟩).regs 1 = 1#64 → turn.rst = false → turn.tile3.stepEn = 1#1 → tile3LratStepValid (st.tiles ⟨3, by omega⟩) = false →
      runOspc4TileTrace H st (turn :: rest) = .error .lratNotUnitOrConflict) ∧
    ((tiles' ⟨2, by omega⟩).regs 1 = 1#64 →
      (turn.rst = true ∨ turn.tile3.stepEn ≠ 1#1 ∨ tile3LratStepValid (st.tiles ⟨3, by omega⟩) = true) →
      aggPoly.degLe turn.maxDeg = false → runOspc4TileTrace H st (turn :: rest) = .error .sumcheckPolyDegreeExceeded) ∧
    ((tiles' ⟨2, by omega⟩).regs 1 = 1#64 →
      (turn.rst = true ∨ turn.tile3.stepEn ≠ 1#1 ∨ tile3LratStepValid (st.tiles ⟨3, by omega⟩) = true) →
      aggPoly.degLe turn.maxDeg = true →
      CommRingOps.add (aggPoly.eval CommRingOps.zero) (aggPoly.eval CommRingOps.one) ≠ st.currentClaim →
      runOspc4TileTrace H st (turn :: rest) = .error .sumcheckSumMismatch) := by
  dsimp only; refine ⟨?_, ?_, ?_, ?_⟩
  · intro hNe
    have hstep : stepOspc4TileCycle H st turn = .error .deltaNetLinearityViolation := by
      unfold stepOspc4TileCycle; simp only [bne_iff_ne.mpr hNe, ↓reduceIte]
    unfold runOspc4TileTrace; rw [hstep]
  · intro hLin hrst hen hBad
    have hc : (!turn.rst && (turn.tile3.stepEn == 1#1) && !tile3LratStepValid (st.tiles ⟨3, by omega⟩)) = true := by rw [hrst, hen, hBad]; rfl
    have hstep : stepOspc4TileCycle H st turn = .error .lratNotUnitOrConflict := by
      unfold stepOspc4TileCycle; simp only [hLin, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hc]
    unfold runOspc4TileTrace; rw [hstep]
  · intro hLin hLrat hDeg
    have hl : (!turn.rst && (turn.tile3.stepEn == 1#1) && !tile3LratStepValid (st.tiles ⟨3, by omega⟩)) = false := by
      rcases hLrat with hr | he | hv
      · rw [hr]; rfl
      · rw [beq_false_of_ne he]; simp
      · rw [hv]; simp
    have hstep : stepOspc4TileCycle H st turn = .error .sumcheckPolyDegreeExceeded := by
      unfold stepOspc4TileCycle; simp only [hLin, bne_self_eq_false, hl, hDeg, Bool.false_eq_true, Bool.not_false, ↓reduceIte]
    unfold runOspc4TileTrace; rw [hstep]
  · intro hLin hLrat hDeg hSum
    have hl : (!turn.rst && (turn.tile3.stepEn == 1#1) && !tile3LratStepValid (st.tiles ⟨3, by omega⟩)) = false := by
      rcases hLrat with hr | he | hv
      · rw [hr]; rfl
      · rw [beq_false_of_ne he]; simp
      · rw [hv]; simp
    have hstep : stepOspc4TileCycle H st turn = .error .sumcheckSumMismatch := by
      unfold stepOspc4TileCycle; simp only [hLin, bne_self_eq_false, hl, hDeg, bne_iff_ne.mpr hSum, Bool.false_eq_true, Bool.not_true, ↓reduceIte]
    unfold runOspc4TileTrace; rw [hstep]

/-! ### Inhabited Non-Tautological `Obend.Judge` (`ospcProverJudge`) -/

structure OspcProverObj where
  inst : OspcPublicInstance
  turns : List OspcProverCycleTurn
  expectedReceipt : BitVec 256

structure OspcProverCert where
  limb0 : BitVec 64
  limb1 : BitVec 64
  limb2 : BitVec 64
  limb3 : BitVec 64
  finalClaim : Goldilocks
  deriving DecidableEq, Repr
def OspcProverMeaning (o : OspcProverObj) (c : OspcProverCert) : Prop :=
  o.turns ≠ [] ∧ ∃ stFinal : Ospc4TileProverState,
    OspcTraceReach deployed (initOspc4TileState deployed o.inst) o.turns stFinal ∧
    stFinal.verifierReceipt256 = o.expectedReceipt ∧
    packReceiptLimbs256 c.limb0 c.limb1 c.limb2 c.limb3 = o.expectedReceipt ∧ c.finalClaim = stFinal.currentClaim
def checkOspcProver (r : Nat) (o : OspcProverObj) (c : OspcProverCert) : Obend.Judge.Verdict OspcRefusal :=
  if o.turns.length > r then .uncovered
  else if o.turns.isEmpty then .refused .emptyTrace []
  else match runOspc4TileTrace deployed (initOspc4TileState deployed o.inst) o.turns with
    | .error e => .refused e [0]
    | .ok stFinal =>
      if stFinal.verifierReceipt256 != o.expectedReceipt then .refused .receiptMismatch [1]
      else if packReceiptLimbs256 c.limb0 c.limb1 c.limb2 c.limb3 != o.expectedReceipt || c.finalClaim != stFinal.currentClaim then .refused .certWitnessMismatch [2]
      else .ok
private theorem checkOspcProver_of_reach (r : Nat) (o : OspcProverObj) (c : OspcProverCert)
    (stFinal : Ospc4TileProverState) (hr : o.turns.length ≤ r) (hne : o.turns ≠ [])
    (hReach : OspcTraceReach deployed (initOspc4TileState deployed o.inst) o.turns stFinal)
    (hRec : stFinal.verifierReceipt256 = o.expectedReceipt)
    (hLimb : packReceiptLimbs256 c.limb0 c.limb1 c.limb2 c.limb3 = o.expectedReceipt)
    (hClm : c.finalClaim = stFinal.currentClaim) :
    checkOspcProver r o c = .ok := by
  unfold checkOspcProver
  have hRun := (runOspc4TileTrace_eq_ok_iff deployed o.turns _ stFinal).mpr hReach
  have hemp : o.turns.isEmpty = false := by cases ht : o.turns <;> simp_all
  simp [show ¬(o.turns.length > r) by omega, hemp, hRun, hRec, hLimb, hClm]

def ospcRefutes : OspcRefusal → Bool | .certWitnessMismatch => false | _ => true

instance ospcProverJudge : Obend.Judge OspcProverObj OspcProverCert where
  Clause := OspcRefusal
  Meaning := OspcProverMeaning
  check := checkOspcProver
  refutes := ospcRefutes
  Fragment := fun o => o.turns ≠ []
  sound := by
    intro r o c h; unfold checkOspcProver at h
    split at h; · cases h
    · split at h; · cases h
      · rename_i hne
        cases hrun : runOspc4TileTrace deployed (initOspc4TileState deployed o.inst) o.turns with
        | error e => rw [hrun] at h; cases h
        | ok stFinal =>
          rw [hrun] at h
          cases hRec : (stFinal.verifierReceipt256 != o.expectedReceipt)
          · simp only [hRec, Bool.false_eq_true, ↓reduceIte] at h
            cases hLimb : (packReceiptLimbs256 c.limb0 c.limb1 c.limb2 c.limb3 != o.expectedReceipt)
            · cases hClm : (c.finalClaim != stFinal.currentClaim)
              · exact ⟨fun hemp => by simp [hemp] at hne, stFinal, (runOspc4TileTrace_eq_ok_iff deployed o.turns _ stFinal).mp hrun,
                  eq_of_beq (by simpa [bne] using hRec), eq_of_beq (by simpa [bne] using hLimb), eq_of_beq (by simpa [bne] using hClm)⟩
              · simp [hLimb, hClm] at h
            · simp [hLimb] at h
          · simp [hRec] at h
  refuted := by
    intro r o c k p hchk href c' ⟨hne, stFinal, hReach, hRec, _, _⟩
    have hRun := (runOspc4TileTrace_eq_ok_iff deployed o.turns _ stFinal).mpr hReach
    unfold checkOspcProver at hchk; split at hchk; · cases hchk
    · cases hemp : o.turns.isEmpty
      · simp only [hemp, Bool.false_eq_true, ↓reduceIte, hRun, hRec, bne_self_eq_false] at hchk
        cases hCert : (packReceiptLimbs256 c.limb0 c.limb1 c.limb2 c.limb3 != o.expectedReceipt || c.finalClaim != stFinal.currentClaim)
        · simp [hCert] at hchk
        · simp only [hCert, ↓reduceIte, Obend.Judge.Verdict.refused.injEq] at hchk; rcases hchk with ⟨rfl, _⟩; simp [ospcRefutes] at href
      · exact hne (List.isEmpty_iff.mp hemp)
  complete := by
    intro o _ ⟨c, hne, stFinal, hReach, hRec, hLimb, hClm⟩
    exact ⟨c, o.turns.length, checkOspcProver_of_reach _ o c stFinal (Nat.le_refl _) hne hReach hRec hLimb hClm⟩
  mono := by
    intro r r' o c hle hne; unfold checkOspcProver at hne ⊢
    by_cases hgt : o.turns.length > r
    · simp [hgt] at hne
    · simp [hgt, show ¬(o.turns.length > r') by omega]

theorem ospcProverJudge_inhabited (seed : BitVec 64) :
    ∃ (o : OspcProverObj) (c : OspcProverCert),
      ospcProverJudge.Fragment o ∧ ospcProverJudge.Meaning o c ∧ ospcProverJudge.check 1 o c = .ok := by
  let inst : OspcPublicInstance := ⟨1, 1, Goldilocks.zero, seed, 0#64, 0#64, 0#64⟩
  let zPort : DeltaPortWord64 := ⟨0#16, 0#2, 0#16, 0#2, 1#1, 0#27⟩
  let turn0 : OspcProverCycleTurn :=
    ⟨false, ⟨1#2, 0#64, 0#17, 0#1, 0#8, 0#64, 0#64⟩, ⟨0#1, 0#6, 0#1, 0#12, 0#64⟩,
     ⟨0#1, zPort, 0#1, 0#8, zPort⟩, ⟨0#1, 0#1, 0#8, ⟨0#32, 0#32⟩⟩, fun _ => ⟨[Goldilocks.zero, Goldilocks.zero]⟩, 1⟩
  let initSt := initOspc4TileState deployed inst
  let tiles' : Fin 4 → MemState := fun t => stepMemModule (ospcTileRtl t) turn0.rst (turn0.inputsFor t) (initSt.tiles t)
  let aggPoly := stepButterflySumcheck2Hop turn0.tilePolys ⟨0, by omega⟩
  let sq := absorbAndSqueezeRound aggPoly initSt.transcript
  let mRoot := stepButterflyMerkle2Hop deployed (tileLeavesOf tiles') ⟨0, by omega⟩
  let rec256 := computeCycleReceipt256 deployed sq.2.state mRoot
  let st1 : Ospc4TileProverState := ⟨tiles', sq.2, aggPoly.eval sq.1, mRoot, rec256, initSt.cycleCount + 1⟩
  let limbs := unpackReceiptLimbs256 rec256
  let o : OspcProverObj := ⟨inst, [turn0], rec256⟩; let c : OspcProverCert := ⟨limbs.1, limbs.2.1, limbs.2.2.1, limbs.2.2.2, aggPoly.eval sq.1⟩
  have hLin : (tiles' ⟨2, by omega⟩).regs 1 = 1#64 := by
    change (stepMemModule (ospcTileRtl ⟨2, by omega⟩) turn0.rst (turn0.inputsFor ⟨2, by omega⟩) ((initOspc4TileState deployed inst).tiles ⟨2, by omega⟩)).regs 1 = 1#64
    rw [initOspc4TileState_tiles]; decide +kernel
  have hDeg : aggPoly.degLe 1 = true := by decide
  have hSum : CommRingOps.add (aggPoly.eval CommRingOps.zero) (aggPoly.eval CommRingOps.one) = initSt.currentClaim := by
    rw [initOspc4TileState_claim]
    change CommRingOps.add (aggPoly.eval CommRingOps.zero) (aggPoly.eval CommRingOps.one) = Goldilocks.zero
    decide
  have hSpec : OspcCycleSpec deployed initSt turn0 st1 := ⟨hLin, fun _ hen => by simp [turn0] at hen, hDeg, hSum, rfl⟩
  have hReach : OspcTraceReach deployed initSt [turn0] st1 := .cons hSpec (.nil st1)
  have hLimbEq : packReceiptLimbs256 limbs.1 limbs.2.1 limbs.2.2.1 limbs.2.2.2 = rec256 :=
    pack_unpack_receiptLimbs256 rec256
  have hMean : OspcProverMeaning o c := ⟨List.cons_ne_nil _ _, st1, hReach, rfl, hLimbEq, rfl⟩
  exact ⟨o, c, List.cons_ne_nil _ _, hMean,
    checkOspcProver_of_reach 1 o c st1 (Nat.le_refl 1) (List.cons_ne_nil _ _) hReach rfl hLimbEq rfl⟩

end Obend.Hardware.OspcProver
end
