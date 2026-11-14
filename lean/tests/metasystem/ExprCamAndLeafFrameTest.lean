module
/-
# ExprCamAndLeafFrameTest — Ghost-Free `ExprCAM` Refinement & `LeafDef.reads` Frame Soundness

Verifies both Wave-4B `Carbon-8` compiler soundness upgrades end-to-end:
1. **`Obend.Lower.ExprCAM`**:
   - Ghost-free fixed-width `CamSlotEntry` (`handle : UInt32`, `word64 : CamWord64`, `tag : BitVec 4`,
     `symId : UInt32`, `child0 child1 child2 : UInt32` — zero embedded `KExpr` ASTs).
   - External inductive `RealizesExprAt` / `decodeCamDag` and `SlotRealizesExprAt` / `decodeSlotCamDag`
     hardware-to-host DAG refinement relations, determinism, and `internToHwExprCAM` / `internExpr`
     round-trip soundness.
   - Distinct symbol non-collision (`"a"` vs `"b"` constants and string literals) and 3-child `.letE`
     packing/decoding beyond 181 nodes without 16-bit Cantor pairing overflow.
   - `#tooth` mutation checks rejecting symbol-ID collision and `letE` child truncation.
2. **`Obend.Leaf.Emit`**:
   - Syntactic guard `checkNoEscapingSelf` (`selfProjOnly`) accepting `self` (`.bound d`) exclusively
     as the immediate target of static field projection `.get (.bound d) field`.
   - Frame soundness (`leafExpr_reads_frame_sound`, `leafExpr_reads_frame_sound_at`,
     `leafDef_reads_frame_sound`) and bare-`self` counterexample (`bare_self_falsifies_frame_without_guard`).
   - `#tooth` mutation checks confirming that dropping `checkNoEscapingSelf` or `checkBoundNotSelf`
     immediately falsifies the stored frame soundness proofs.
-/

public import Obend.Lower.Inductive
public import Obend.Lower.ExprCAM
public import Obend.Leaf.Emit
public import Obend.Tactic.Tooth
import all Obend.Lower.Inductive
import all Obend.Lower.ExprCAM
import all Obend.Leaf.Emit

public section

namespace Obend.Tests.Metasystem.ExprCamAndLeafFrameTest

open Obend.Core.Term
open Obend.Leaf
open Obend.Lower.Inductive
open Obend.Lower.LeanKernel
open Obend.Lower.ExprCAM

set_option autoImplicit false

/-! ## 1. Ghost-Free `CamSlotEntry`, `RealizesExprAt` / `decodeCamDag`, `"a"` vs `"b"` & `letE` > 181 -/

/-- Witness that `CamSlotEntry` consists purely of concrete fixed-width bounded hardware fields
(`UInt32`, `CamWord64`, `BitVec 4`) with zero host `KExpr` AST fields. -/
def mkConcreteHwSlotWitness (h s c0 c1 c2 : UInt32) (w : CamWord64) (t : BitVec 4) : CamSlotEntry :=
  { handle := h
  , word64 := w
  , tag    := t
  , symId  := s
  , child0 := c0
  , child1 := c1
  , child2 := c2 }

theorem camWord64_and_distinct_ab_sound (cam : HwExprCAM) (f : CamNodeFields) :
    unpackCamWord64 (packCamWord64 f) = f ∧
    (let cA := KExpr.const (KName.mkSimple "a") []
     let cB := KExpr.const (KName.mkSimple "b") []
     let sA := KExpr.lit (.strVal "a")
     let sB := KExpr.lit (.strVal "b")
     let (hCA, cam1) := internToHwExprCAM cA cam
     let (hCB, cam2) := internToHwExprCAM cB cam1
     let (hSA, cam3) := internToHwExprCAM sA cam
     let (hSB, cam4) := internToHwExprCAM sB cam3
     hCA ≠ hCB ∧
     RealizesExprAt cam2 hCA cA ∧
     RealizesExprAt cam2 hCB cB ∧
     decodeCamDag 1 cam2 hCA = some cA ∧
     decodeCamDag 1 cam2 hCB = some cB ∧
     hSA ≠ hSB ∧
     RealizesExprAt cam4 hSA sA ∧
     RealizesExprAt cam4 hSB sB ∧
     decodeCamDag 1 cam4 hSA = some sA ∧
     decodeCamDag 1 cam4 hSB = some sB) := by
  refine ⟨unpack_pack_camWord64 f, ?_⟩
  dsimp only
  have hNoColl := hwExprCam_distinct_symbols_no_collision cam
    (.constEntry (KName.mkSimple "a") [])
    (.constEntry (KName.mkSimple "b") [])
    (by decide)
    (KName.mkSimple "a") (KName.mkSimple "b") [] []
    (by decide)
    "a" "b"
    (by decide)
  obtain ⟨_, hCNe, rCA, rCB, hSNe, rSA, rSB⟩ := hNoColl
  exact ⟨hCNe, rCA, rCB,
    decodeCamDag_of_realizesExprAt rCA (Nat.le_refl 1),
    decodeCamDag_of_realizesExprAt rCB (Nat.le_refl 1),
    hSNe, rSA, rSB,
    decodeCamDag_of_realizesExprAt rSA (Nat.le_refl 1),
    decodeCamDag_of_realizesExprAt rSB (Nat.le_refl 1)⟩

theorem realizesExprAt_and_letE_beyond_181_sound
    (cam : HwExprCAM) (slot : Nat) (e ty val body : KExpr) :
    (RealizesExprAt cam slot e ↔ ∃ fuel, decodeCamDag fuel cam slot = some e) ∧
    cantorPairNat 186 187 = 69938 ∧
    (BitVec.ofNat 16 (cantorPairNat 186 187)).toNat ≠ cantorPairNat 186 187 ∧
    RealizesExprAt
      (internToHwExprCAM (.letE ty val body) (seedHwExprCamFVars 190)).2
      (internToHwExprCAM (.letE ty val body) (seedHwExprCamFVars 190)).1
      (.letE ty val body) ∧
    decodeCamDag (depth (.letE ty val body))
      (internToHwExprCAM (.letE ty val body) (seedHwExprCamFVars 190)).2
      (internToHwExprCAM (.letE ty val body) (seedHwExprCamFVars 190)).1 =
      some (.letE ty val body) ∧
    (let camSeed := seededExprCAM 190
     let letNode := KExpr.letE kNatConst (.fvar 500) (.fvar 501)
     let (camLet, hLet) := internExpr camSeed letNode
     camSeed.entries.length = 190 ∧
     uninternExpr camLet hLet = some letNode) := by
  have hLet := letE_beyond_181_no_cantor_overflow 186 187 (by decide) (by decide) ty val body
  exact ⟨realizesExprAt_iff_decodeCamDag cam slot e,
    hLet.2.1, hLet.2.2.1, hLet.2.2.2.1, hLet.2.2.2.2.1, hLet.2.2.2.2.2⟩

/-- Broken `allocPackedSymbol` mutant that aliases every symbol to index `0` (causing `"a"` and `"b"` to collide). -/
def allocPackedSymbolCollideZero (_ : HwCamSymbolEntry) (cam : HwExprCAM) : Nat × HwExprCAM :=
  (0, cam)

#tooth Obend.Lower.ExprCAM.hwExprCam_distinct_symbols_no_collision by mutation Obend.Lower.ExprCAM.allocPackedSymbol := allocPackedSymbolCollideZero

/-- Broken `mkHwCamLetE` mutant that drops the 3rd child `hb` (`h2 := 0`). -/
def mkHwCamLetEDropBody (ht hv _ : Nat) (cam : HwExprCAM) : Nat × HwExprCAM :=
  allocPackedNode { tag := 7, h0 := ht, h1 := hv, h2 := 0, symIdx := 0 } cam

#tooth Obend.Lower.ExprCAM.reconstructFromHwExprCAM_intern_roundtrip by mutation Obend.Lower.ExprCAM.mkHwCamLetE := mkHwCamLetEDropBody

/-! ## 2. `Obend.Leaf.Emit` — `checkNoEscapingSelf` Guard, Frame Soundness & `#tooth` Checks -/

theorem checkNoEscapingSelf_accepts_proj_and_rejects_bare_self (u1 u2 : Nat) :
    -- Safe static `self.x` projection (top-level and under binders) passes `checkNoEscapingSelf`:
    checkNoEscapingSelf (.get (.bound 0) "x") = true ∧
    checkNoEscapingSelf (.lam (.binary .add (.get (.bound 1) "x") (.bound 0))) = true ∧
    -- Bare `self` (`.bound 0`) anywhere outside `.get (.bound d) field` is rejected:
    checkNoEscapingSelf (.bound 0) = false ∧
    checkNoEscapingSelf (.app (.lam (.bound 0)) (.bound 0)) = false ∧
    checkNoEscapingSelf (.record [("leak", .bound 0)]) = false ∧
    checkNoEscapingSelf (.split (.bound 0) ["secret"] (.lam (.bound 0))) = false ∧
    -- Frame soundness on unread fields `"unused"`: varying `u1` vs `u2` leaves evaluation identical:
    evalLeafExpr 8 [] [("x", .nat 10), ("unused", .nat u1)]
      (.binary .add (.get (.bound 0) "x") (.nat 5)) =
    evalLeafExpr 8 [] [("x", .nat 10), ("unused", .nat u2)]
      (.binary .add (.get (.bound 0) "x") (.nat 5)) ∧
    -- Frame soundness under non-empty local bindings (`locals = [.nat 7]`, `self` at `.bound 1`):
    evalLeafExpr 8 [.nat 7] [("x", .nat 10), ("unused", .nat u1)]
      (.binary .add (.get (.bound 1) "x") (.bound 0)) =
    evalLeafExpr 8 [.nat 7] [("x", .nat 10), ("unused", .nat u2)]
      (.binary .add (.get (.bound 1) "x") (.bound 0)) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · apply leafExpr_reads_frame_sound 8
      [("x", .nat 10), ("unused", .nat u1)]
      [("x", .nat 10), ("unused", .nat u2)]
      (.binary .add (.get (.bound 0) "x") (.nat 5))
      rfl
    intro m hm
    simp [selfReads] at hm
    subst hm
    rfl
  · apply leafExpr_reads_frame_sound_at 8 [.nat 7]
      [("x", .nat 10), ("unused", .nat u1)]
      [("x", .nat 10), ("unused", .nat u2)]
      (.binary .add (.get (.bound 1) "x") (.bound 0))
      rfl
    intro m hm
    simp [selfReads] at hm
    subst hm
    rfl

theorem bare_self_counterexample_witness (v₁ v₂ : Nat) (hne : v₁ ≠ v₂) :
    checkNoEscapingSelf (.bound 0) = false ∧
    selfReads 0 (.bound 0) = [] ∧
    evalLeafExpr 4 [] [("secret", .nat v₁)] (.bound 0) ≠
    evalLeafExpr 4 [] [("secret", .nat v₂)] (.bound 0) := by
  have h := bare_self_falsifies_frame_without_guard v₁ v₂ hne
  exact ⟨h.1, h.2.2.1, h.2.2.2.2.2.2.1⟩

/-- Broken `checkNoEscapingSelf` mutant that permits bare `.bound` (`self`) to escape at top level. -/
def mutantAcceptBareSelf : LeafExpr → Bool
  | .bound _ => true
  | other => checkNoEscapingSelfAt 0 other

#tooth Obend.Leaf.leafExpr_reads_frame_sound by mutation Obend.Leaf.checkNoEscapingSelf := mutantAcceptBareSelf

/-- Broken `checkBoundNotSelf` mutant that permits `i == d` (`self`) as a bare variable reference. -/
def mutantBoundAllowSelf (i d : Nat) : Bool :=
  (i == d) || (i != d)

#tooth Obend.Leaf.leafExpr_reads_frame_sound_at by mutation Obend.Leaf.checkBoundNotSelf := mutantBoundAllowSelf

/-! ## 3. Axiom Hygiene Verification (`0 sorryAx`, `0 Classical.choice`, `0` Custom Axioms) -/

#print axioms Obend.Lower.ExprCAM.realizesExprAt_iff_decodeCamDag
#print axioms Obend.Lower.ExprCAM.RealizesExprAt.deterministic
#print axioms Obend.Lower.ExprCAM.internToHwExprCAM_realizesExprAt
#print axioms Obend.Lower.ExprCAM.hwExprCam_distinct_symbols_no_collision
#print axioms Obend.Lower.ExprCAM.letE_beyond_181_no_cantor_overflow
#print axioms Obend.Lower.ExprCAM.slotRealizesExprAt_iff_decodeSlotCamDag
#print axioms Obend.Lower.ExprCAM.intern_unintern_roundtrip
#print axioms Obend.Lower.ExprCAM.exprCam_handle_eq_imp_expr_eq
#print axioms Obend.Lower.ExprCAM.exprCam_roundtrip_sound
#print axioms Obend.Leaf.leafExpr_reads_frame_sound
#print axioms Obend.Leaf.leafExpr_reads_frame_sound_at
#print axioms Obend.Leaf.leafDef_reads_frame_sound
#print axioms Obend.Leaf.bare_self_falsifies_frame_without_guard

end Obend.Tests.Metasystem.ExprCamAndLeafFrameTest

end
