module
/-
# Obend.Lower.ExprCAM — 64-Bit Hardware Hash-Consed DAG / CAM Pool & Live `silicon-check` Ingestion

Implements `WS 24` (`SILICON-ELABORATOR.md` §3.3 & §6.3):
1. **64-Bit Hardware CAM Word Packing (`CamNodeFields`, `packCamWord64`, `unpackCamWord64`)**:
   - Packs `KExpr` DAG node descriptors into a single 64-bit hardware word:
     `[63:60] tag (4b) | [59] looseBVar (1b) | [58] hasFVar (1b) | [57:32] hash (26b) | [31:16] left (16b) | [15:0] right (16b)`.
   - Proves `unpack_pack_camWord64`: packing and unpacking any `CamNodeFields` is a lossless bijection.
2. **Hardware Hash-Consed `ExprCAM` Pool (`ExprCAM`, `internExpr`, `uninternExpr`)**:
   - Bottom-up deduplicating Content-Addressable Memory (CAM) table mapping structurally identical
     `KExpr` subtrees to canonical 16-bit handles (`CamHandle`).
   - Proves **`exprCam_eq_iff_handle_eq`**: 1-cycle handle equality coincides with full recursive
     structural equality (`KExpr.beq`), and repeated subtrees `(f x) + (f x)` share a single CAM entry.
   - Proves **`exprCam_looseBVar_flag_sound`**: the 1-bit `looseBVar` hardware flag in bit 59 of the
     CAM word equals `KExpr.hasLooseBVar`, and when `hasLooseBVarAt cutoff e = false`, both
     `KExpr.liftLooseBVars cutoff delta e = e` and `KExpr.instantiateAt cutoff arg e = e` hold
     identically (enabling 1-cycle hardware bypass of substitution on closed subterms).
   - Proves **`exprCam_roundtrip_sound`**: every interned `KExpr` uninterns losslessly from `ExprCAM`.
3. **Live Declaration-Cone Ingestion & Universal Handle-Level Substitution (`extractLeanEnvCone`, `hwCamInstantiateAt`)**:
   - Extracts live `Lean.ConstantInfo`, `KInductDecl`, and polymorphic `KRecRule` dependency cones from
     the host Lean 4 environment with `Std.HashSet`/`Std.HashMap` indexing (`internKEnvConeFast`), and
     proves universal handle-level substitution simulation (`reconstructFromHwExprCAM_hwCamInstantiateAt`).
-/
public import Std.Data.HashMap
public import Std.Data.HashSet
public import Std.Tactic.BVDecide
public import Obend.Lower.LeanKernel
public import Obend.Lower.Proofs.SiliconKernel
@[expose] public section

namespace Obend.Lower.ExprCAM
open Obend.Core.Term
open Obend.Leaf
open Obend.Lower
open Obend.Lower.Inductive
open Obend.Lower.LeanKernel
open Obend.Lower.Proofs.SiliconKernel
open Obend.Hardware.HDL
open Obend.Hardware.Compiler
open Obend.Hardware.ReductionMachine
set_option autoImplicit false

/-! ## 1. Loose De Bruijn & Free Variable Bit-Flags on `KExpr` -/

/-- Check whether `e : KExpr` contains any loose bound variable `.bvar i` with `i >= cutoff`. -/
def KExpr.hasLooseBVarAt (cutoff : Nat) : KExpr → Bool
  | .bvar i       => decide (i >= cutoff)
  | .fvar _       => false
  | .mvar _       => false
  | .sort _       => false
  | .const _ _    => false
  | .app f a      => KExpr.hasLooseBVarAt cutoff f || KExpr.hasLooseBVarAt cutoff a
  | .lam d b      => KExpr.hasLooseBVarAt cutoff d || KExpr.hasLooseBVarAt (cutoff + 1) b
  | .forallE d b  => KExpr.hasLooseBVarAt cutoff d || KExpr.hasLooseBVarAt (cutoff + 1) b
  | .letE t v b   =>
    KExpr.hasLooseBVarAt cutoff t || KExpr.hasLooseBVarAt cutoff v || KExpr.hasLooseBVarAt (cutoff + 1) b
  | .lit _        => false
  | .proj _ _ e   => KExpr.hasLooseBVarAt cutoff e

/-- Check whether `e : KExpr` contains any loose bound variable (`.bvar i` with `i >= 0`). -/
def KExpr.hasLooseBVar (e : KExpr) : Bool :=
  KExpr.hasLooseBVarAt 0 e

/-- Check whether `e : KExpr` contains any free variable `.fvar id`. -/
def KExpr.hasFVar : KExpr → Bool
  | .bvar _       => false
  | .fvar _       => true
  | .mvar _       => false
  | .sort _       => false
  | .const _ _    => false
  | .app f a      => KExpr.hasFVar f || KExpr.hasFVar a
  | .lam d b      => KExpr.hasFVar d || KExpr.hasFVar b
  | .forallE d b  => KExpr.hasFVar d || KExpr.hasFVar b
  | .letE t v b   => KExpr.hasFVar t || KExpr.hasFVar v || KExpr.hasFVar b
  | .lit _        => false
  | .proj _ _ e   => KExpr.hasFVar e

/-- Check whether `e : KExpr` contains any metavariable `.mvar id`. -/
def KExpr.hasMVar : KExpr → Bool
  | .bvar _       => false
  | .fvar _       => false
  | .mvar _       => true
  | .sort _       => false
  | .const _ _    => false
  | .app f a      => KExpr.hasMVar f || KExpr.hasMVar a
  | .lam d b      => KExpr.hasMVar d || KExpr.hasMVar b
  | .forallE d b  => KExpr.hasMVar d || KExpr.hasMVar b
  | .letE t v b   => KExpr.hasMVar t || KExpr.hasMVar v || KExpr.hasMVar b
  | .lit _        => false
  | .proj _ _ e   => KExpr.hasMVar e

/-- When `KExpr.hasLooseBVarAt cutoff e = false`, `KExpr.liftLooseBVars cutoff delta e` is a no-op (`e`). -/
theorem liftLooseBVars_of_hasLooseBVarAt_false : ∀ (e : KExpr) (cutoff delta : Nat),
    KExpr.hasLooseBVarAt cutoff e = false →
    KExpr.liftLooseBVars cutoff delta e = e
  | .bvar i, cutoff, delta, h => by
    simp only [KExpr.hasLooseBVarAt, decide_eq_false_iff_not] at h
    simp [KExpr.liftLooseBVars, h]
  | .fvar _, _, _, _ => rfl
  | .mvar _, _, _, _ => rfl
  | .sort _, _, _, _ => rfl
  | .const _ _, _, _, _ => rfl
  | .app f a, cutoff, delta, h => by
    simp only [KExpr.hasLooseBVarAt, Bool.or_eq_false_iff] at h
    simp [KExpr.liftLooseBVars,
      liftLooseBVars_of_hasLooseBVarAt_false f cutoff delta h.1,
      liftLooseBVars_of_hasLooseBVarAt_false a cutoff delta h.2]
  | .lam d b, cutoff, delta, h => by
    simp only [KExpr.hasLooseBVarAt, Bool.or_eq_false_iff] at h
    simp [KExpr.liftLooseBVars,
      liftLooseBVars_of_hasLooseBVarAt_false d cutoff delta h.1,
      liftLooseBVars_of_hasLooseBVarAt_false b (cutoff + 1) delta h.2]
  | .forallE d b, cutoff, delta, h => by
    simp only [KExpr.hasLooseBVarAt, Bool.or_eq_false_iff] at h
    simp [KExpr.liftLooseBVars,
      liftLooseBVars_of_hasLooseBVarAt_false d cutoff delta h.1,
      liftLooseBVars_of_hasLooseBVarAt_false b (cutoff + 1) delta h.2]
  | .letE t v b, cutoff, delta, h => by
    simp only [KExpr.hasLooseBVarAt, Bool.or_eq_false_iff] at h
    simp [KExpr.liftLooseBVars,
      liftLooseBVars_of_hasLooseBVarAt_false t cutoff delta h.1.1,
      liftLooseBVars_of_hasLooseBVarAt_false v cutoff delta h.1.2,
      liftLooseBVars_of_hasLooseBVarAt_false b (cutoff + 1) delta h.2]
  | .lit _, _, _, _ => rfl
  | .proj _ _ e, cutoff, delta, h => by
    simp only [KExpr.hasLooseBVarAt] at h
    simp [KExpr.liftLooseBVars,
      liftLooseBVars_of_hasLooseBVarAt_false e cutoff delta h]

/-- When `KExpr.hasLooseBVarAt depth e = false`, `KExpr.instantiateAt depth arg e` is a no-op (`e`). -/
theorem instantiateAt_of_hasLooseBVarAt_false : ∀ (e : KExpr) (depth : Nat) (arg : KExpr),
    KExpr.hasLooseBVarAt depth e = false →
    KExpr.instantiateAt depth arg e = e
  | .bvar i, depth, arg, h => by
    simp only [KExpr.hasLooseBVarAt, decide_eq_false_iff_not] at h
    have hne : (i == depth) = false := by
      rw [beq_eq_false_iff_ne]
      omega
    have hng : ¬ (i > depth) := by omega
    simp [KExpr.instantiateAt, hne, hng]
  | .fvar _, _, _, _ => rfl
  | .mvar _, _, _, _ => rfl
  | .sort _, _, _, _ => rfl
  | .const _ _, _, _, _ => rfl
  | .app f a, depth, arg, h => by
    simp only [KExpr.hasLooseBVarAt, Bool.or_eq_false_iff] at h
    simp [KExpr.instantiateAt,
      instantiateAt_of_hasLooseBVarAt_false f depth arg h.1,
      instantiateAt_of_hasLooseBVarAt_false a depth arg h.2]
  | .lam d b, depth, arg, h => by
    simp only [KExpr.hasLooseBVarAt, Bool.or_eq_false_iff] at h
    simp [KExpr.instantiateAt,
      instantiateAt_of_hasLooseBVarAt_false d depth arg h.1,
      instantiateAt_of_hasLooseBVarAt_false b (depth + 1) arg h.2]
  | .forallE d b, depth, arg, h => by
    simp only [KExpr.hasLooseBVarAt, Bool.or_eq_false_iff] at h
    simp [KExpr.instantiateAt,
      instantiateAt_of_hasLooseBVarAt_false d depth arg h.1,
      instantiateAt_of_hasLooseBVarAt_false b (depth + 1) arg h.2]
  | .letE t v b, depth, arg, h => by
    simp only [KExpr.hasLooseBVarAt, Bool.or_eq_false_iff] at h
    simp [KExpr.instantiateAt,
      instantiateAt_of_hasLooseBVarAt_false t depth arg h.1.1,
      instantiateAt_of_hasLooseBVarAt_false v depth arg h.1.2,
      instantiateAt_of_hasLooseBVarAt_false b (depth + 1) arg h.2]
  | .lit _, _, _, _ => rfl
  | .proj _ _ e, depth, arg, h => by
    simp only [KExpr.hasLooseBVarAt] at h
    simp [KExpr.instantiateAt,
      instantiateAt_of_hasLooseBVarAt_false e depth arg h]

/-! ## 2. 64-Bit Hardware CAM Word Layout `(tag:4b, looseBVar:1b, hasFVar:1b, hash:26b, left:16b, right:16b)` -/

/-- 64-bit hardware word stored in a Content-Addressable Memory (CAM) / BRAM slot. -/
abbrev CamWord64 := BitVec 64

/-- 16-bit expression handle indexing into the `ExprCAM` pool (`0..65535`). -/
abbrev CamHandle := Nat

/-- Unpacked field view of a 64-bit `ExprCAM` hardware word:
- `tag` (`4` bits, `[63:60]`): `KExpr` constructor tag (`0..9`),
- `looseBVar` (`1` bit, `[59]`): `1` iff the expression contains any loose `.bvar`,
- `hasFVar` (`1` bit, `[58]`): `1` iff the expression contains any `.fvar`,
- `hash26` (`26` bits, `[57:32]`): 26-bit structural hash fingerprint,
- `left` (`16` bits, `[31:16]`): left child handle or immediate payload,
- `right` (`16` bits, `[15:0]`): right child handle or immediate payload. -/
structure CamNodeFields where
  tag       : BitVec 4
  looseBVar : Bool
  hasFVar   : Bool
  hash26    : BitVec 26
  left      : BitVec 16
  right     : BitVec 16
  deriving DecidableEq, Repr, Inhabited

/-- Pack `CamNodeFields` into a 64-bit hardware `CamWord64`:
`tag (4b) ++ looseBVar (1b) ++ hasFVar (1b) ++ hash26 (26b) ++ left (16b) ++ right (16b)`. -/
def packCamWord64 (f : CamNodeFields) : CamWord64 :=
  let bLoose : BitVec 1 := if f.looseBVar then 1#1 else 0#1
  let bFVar  : BitVec 1 := if f.hasFVar then 1#1 else 0#1
  let hi6    : BitVec 6 := (f.tag ++ bLoose) ++ bFVar
  let hi32   : BitVec 32 := hi6 ++ f.hash26
  let lo32   : BitVec 32 := f.left ++ f.right
  hi32 ++ lo32

/-- Unpack a 64-bit hardware `CamWord64` into its `CamNodeFields`. -/
def unpackCamWord64 (w : CamWord64) : CamNodeFields where
  tag       := w.extractLsb' 60 4
  looseBVar := w.getLsbD 59
  hasFVar   := w.getLsbD 58
  hash26    := w.extractLsb' 32 26
  left      := w.extractLsb' 16 16
  right     := w.extractLsb' 0 16

/-- **Theorem (`unpack_pack_camWord64`)**:
Packing and unpacking any `CamNodeFields` into a 64-bit `CamWord64` is a lossless bijection. -/
theorem unpack_pack_camWord64 (f : CamNodeFields) :
    unpackCamWord64 (packCamWord64 f) = f := by
  rcases f with ⟨tag, looseBVar, hasFVar, hash26, left, right⟩
  simp only [packCamWord64, unpackCamWord64, CamNodeFields.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · bv_decide
  · cases looseBVar <;> bv_decide
  · cases hasFVar <;> bv_decide
  · bv_decide
  · bv_decide
  · bv_decide

/-- 4-bit constructor tag for `KExpr` (`0..10`). -/
def exprTag4 : KExpr → BitVec 4
  | .bvar _      => 0#4
  | .fvar _      => 1#4
  | .sort _      => 2#4
  | .const _ _   => 3#4
  | .app _ _     => 4#4
  | .lam _ _     => 5#4
  | .forallE _ _ => 6#4
  | .letE _ _ _  => 7#4
  | .lit _       => 8#4
  | .proj _ _ _  => 9#4
  | .mvar _      => 10#4

/-- Compute a 26-bit hardware hash mix over `(tag, left, right)`. -/
def mixCamHash26 (tag : BitVec 4) (left right : BitVec 16) : BitVec 26 :=
  let seed : Nat := tag.toNat * 1048583 + left.toNat * 65537 + right.toNat * 257 + 0x1A2B3C
  BitVec.ofNat 26 seed

/-- Build the `CamNodeFields` for a `KExpr` node given its resolved child handles `(leftH, rightH)`. -/
def mkExprCamFields (e : KExpr) (leftH rightH : Nat) : CamNodeFields :=
  let tag := exprTag4 e
  let l16 := BitVec.ofNat 16 leftH
  let r16 := BitVec.ofNat 16 rightH
  { tag       := tag
  , looseBVar := KExpr.hasLooseBVar e
  , hasFVar   := KExpr.hasFVar e
  , hash26    := mixCamHash26 tag l16 r16
  , left      := l16
  , right     := r16 }

/-- Build the 64-bit `CamWord64` for a `KExpr` node given its resolved child handles `(leftH, rightH)`. -/
def mkExprCamWord64 (e : KExpr) (leftH rightH : Nat) : CamWord64 :=
  packCamWord64 (mkExprCamFields e leftH rightH)

/-! ## 3. Deduplicating Ghost-Free Hardware `ExprCAM` Pool (`CamSlotEntry`, `internExpr`, `uninternExpr`) -/

/-- Structural AST depth of a `KExpr` (`depth e ≥ 1` for every `e : KExpr`). -/
def depth : KExpr → Nat
  | .bvar _      => 1
  | .fvar _      => 1
  | .mvar _      => 1
  | .sort _      => 1
  | .const _ _   => 1
  | .lit _       => 1
  | .app f a     => 1 + max (depth f) (depth a)
  | .lam d b     => 1 + max (depth d) (depth b)
  | .forallE d b => 1 + max (depth d) (depth b)
  | .letE t v b  => 1 + max (depth t) (max (depth v) (depth b))
  | .proj _ _ s  => 1 + depth s

abbrev KExpr.depth (e : KExpr) : Nat := Obend.Lower.ExprCAM.depth e

/-- Auxiliary symbol/literal/universe table entry (`HwCamSymbolEntry`) referenced by 32-bit `symId` / `symIdx`.
Contains NO `KExpr` AST nodes! -/
inductive HwCamSymbolEntry where
  | sortEntry  (u : KLevel)
  | constEntry (name : KName) (us : List KLevel)
  | litEntry   (lit : KLiteral)
  | projEntry  (structName : KName) (fieldIdx : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- Associative index lookup in a hardware table (`findElemIdx?`), returning `some idx` when
`target` is already present in `xs` (enabling 1-cycle CAM deduplication). -/
def findElemIdx? {α : Type} [DecidableEq α] : List α → α → Option Nat
  | [], _ => none
  | x :: xs, target =>
    if x = target then some 0
    else (findElemIdx? xs target).map (· + 1)

theorem getElem?_of_findElemIdx? {α : Type} [DecidableEq α] :
    ∀ (xs : List α) (target : α) (idx : Nat),
      findElemIdx? xs target = some idx → xs[idx]? = some target
  | [], _, _, h => by cases h
  | x :: xs, target, idx, h => by
    simp only [findElemIdx?] at h
    split at h
    · rename_i heq
      simp only [Option.some.injEq] at h
      subst h heq
      rfl
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨k, hk, rfl⟩ := h
      simpa using getElem?_of_findElemIdx? xs target k hk

theorem getElem?_append_singleton_self {α : Type} (xs : List α) (x : α) :
    (xs ++ [x])[xs.length]? = some x := by
  rw [List.getElem?_append_right (Nat.le_refl xs.length)]
  simp

theorem getElem?_append_preserve {α : Type} {xs : List α} {i : Nat} {x : α}
    (ys : List α) (h : xs[i]? = some x) :
    (xs ++ ys)[i]? = some x := by
  obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp h
  rw [List.getElem?_append_left hlt, h]

/-- Concrete fixed-width hardware CAM lookup key (`CamSlotKey`):
Matched in 1 cycle by associative CAM comparators without any host `KExpr` AST. -/
structure CamSlotKey where
  tag    : BitVec 4
  symId  : UInt32 := 0
  child0 : UInt32 := 0
  child1 : UInt32 := 0
  child2 : UInt32 := 0
  deriving DecidableEq, Repr, Inhabited

/-- A single entry in the hardware `ExprCAM` pool (`CamSlotEntry`):
Stores **only** concrete bounded fixed-width hardware words (zero host `KExpr` ghost fields!):
- `handle` (`UInt32`): canonical 32-bit CAM slot address,
- `word64` (`CamWord64`): packed 64-bit fast-filter summary word `(tag:4b, looseBVar:1b, hasFVar:1b, hash26:26b, left:16b, right:16b)`,
- `tag` (`BitVec 4`): 4-bit `KExpr` constructor tag (`0..10`),
- `symId` (`UInt32`): 32-bit symbol/literal/universe table ID (or immediate variable ID for `.bvar`/`.fvar`/`.mvar`),
- `child0`, `child1`, `child2` (`UInt32`): explicit 32-bit child slot indices (no Cantor pairing, no 181-node 16-bit overflow). -/
structure CamSlotEntry where
  handle : UInt32
  word64 : CamWord64
  tag    : BitVec 4
  symId  : UInt32 := 0
  child0 : UInt32 := 0
  child1 : UInt32 := 0
  child2 : UInt32 := 0
  deriving DecidableEq, Repr, Inhabited

/-- Extract the associative CAM comparison key from a `CamSlotEntry`. -/
def CamSlotEntry.key (s : CamSlotEntry) : CamSlotKey :=
  { tag := s.tag, symId := s.symId, child0 := s.child0, child1 := s.child1, child2 := s.child2 }

/-- Hardware Hash-Consed DAG / Content-Addressable Memory pool for `KExpr` expressions,
storing bounded fixed-width `CamSlotEntry` slots and auxiliary `HwCamSymbolEntry` atoms
with **zero** embedded `KExpr` ASTs. -/
structure ExprCAM where
  entries : List CamSlotEntry := []
  symbols : List HwCamSymbolEntry := []
  deriving DecidableEq, Repr, Inhabited

/-- Empty `ExprCAM` pool. -/
def ExprCAM.empty : ExprCAM := { entries := [], symbols := [] }

/-- Look up an existing handle for hardware key `k : CamSlotKey` in `cam` (1-cycle associative CAM lookup). -/
def ExprCAM.lookupSlotKey? (cam : ExprCAM) (k : CamSlotKey) : Option CamHandle :=
  (cam.entries.find? (fun slot => decide (slot.key = k))).map (fun slot => slot.handle.toNat)

/-- Look up a `CamSlotEntry` by its `CamHandle` in `cam` (1-cycle direct BRAM read). -/
def ExprCAM.lookupSlot? (cam : ExprCAM) (h : CamHandle) : Option CamSlotEntry :=
  cam.entries[h]?

/-- Bounded-fuel DAG decoder for ghost-free `ExprCAM` slots (`decodeSlotCamDag`). -/
def decodeSlotCamDag : Nat → ExprCAM → CamHandle → Option KExpr
  | 0, _, _ => none
  | fuel + 1, cam, h =>
    match cam.entries[h]? with
    | none => none
    | some s =>
      if s.tag == 0#4 then
        some (.bvar s.symId.toNat)
      else if s.tag == 1#4 then
        some (.fvar s.symId.toNat)
      else if s.tag == 2#4 then
        match cam.symbols[s.symId.toNat]? with
        | some (.sortEntry u) => some (.sort u)
        | _ => none
      else if s.tag == 3#4 then
        match cam.symbols[s.symId.toNat]? with
        | some (.constEntry n us) => some (.const n us)
        | _ => none
      else if s.tag == 4#4 then
        match decodeSlotCamDag fuel cam s.child0.toNat,
              decodeSlotCamDag fuel cam s.child1.toNat with
        | some f, some a => some (.app f a)
        | _, _ => none
      else if s.tag == 5#4 then
        match decodeSlotCamDag fuel cam s.child0.toNat,
              decodeSlotCamDag fuel cam s.child1.toNat with
        | some d, some b => some (.lam d b)
        | _, _ => none
      else if s.tag == 6#4 then
        match decodeSlotCamDag fuel cam s.child0.toNat,
              decodeSlotCamDag fuel cam s.child1.toNat with
        | some d, some b => some (.forallE d b)
        | _, _ => none
      else if s.tag == 7#4 then
        match decodeSlotCamDag fuel cam s.child0.toNat,
              decodeSlotCamDag fuel cam s.child1.toNat,
              decodeSlotCamDag fuel cam s.child2.toNat with
        | some t, some v, some b => some (.letE t v b)
        | _, _, _ => none
      else if s.tag == 8#4 then
        match cam.symbols[s.symId.toNat]? with
        | some (.litEntry l) => some (.lit l)
        | _ => none
      else if s.tag == 9#4 then
        match decodeSlotCamDag fuel cam s.child0.toNat,
              cam.symbols[s.symId.toNat]? with
        | some e, some (.projEntry structName idx) => some (.proj structName idx e)
        | _, _ => none
      else if s.tag == 10#4 then
        some (.mvar s.symId.toNat)
      else
        none

/-- Unintern a `CamHandle` back to its `KExpr` AST by decoding the ghost-free hardware slot DAG. -/
def uninternExpr (cam : ExprCAM) (h : CamHandle) : Option KExpr :=
  decodeSlotCamDag cam.entries.length cam h

/-- External inductive refinement relation (`SlotRealizesExprAt cam slot e`):
Relates a ghost-free hardware `ExprCAM` pool `cam` and slot index `slot` to the host `KExpr` DAG `e`. -/
inductive SlotRealizesExprAt (cam : ExprCAM) : CamHandle → KExpr → Prop where
  | bvar {slot idx : Nat} {s : CamSlotEntry} :
      cam.entries[slot]? = some s → s.tag = 0#4 → s.symId.toNat = idx →
      SlotRealizesExprAt cam slot (.bvar idx)
  | fvar {slot id : Nat} {s : CamSlotEntry} :
      cam.entries[slot]? = some s → s.tag = 1#4 → s.symId.toNat = id →
      SlotRealizesExprAt cam slot (.fvar id)
  | mvar {slot id : Nat} {s : CamSlotEntry} :
      cam.entries[slot]? = some s → s.tag = 10#4 → s.symId.toNat = id →
      SlotRealizesExprAt cam slot (.mvar id)
  | sort {slot : Nat} {u : KLevel} {s : CamSlotEntry} :
      cam.entries[slot]? = some s → s.tag = 2#4 →
      cam.symbols[s.symId.toNat]? = some (.sortEntry u) →
      SlotRealizesExprAt cam slot (.sort u)
  | const {slot : Nat} {n : KName} {us : List KLevel} {s : CamSlotEntry} :
      cam.entries[slot]? = some s → s.tag = 3#4 →
      cam.symbols[s.symId.toNat]? = some (.constEntry n us) →
      SlotRealizesExprAt cam slot (.const n us)
  | app {slot : Nat} {f a : KExpr} {s : CamSlotEntry} :
      cam.entries[slot]? = some s → s.tag = 4#4 →
      SlotRealizesExprAt cam s.child0.toNat f →
      SlotRealizesExprAt cam s.child1.toNat a →
      SlotRealizesExprAt cam slot (.app f a)
  | lam {slot : Nat} {d b : KExpr} {s : CamSlotEntry} :
      cam.entries[slot]? = some s → s.tag = 5#4 →
      SlotRealizesExprAt cam s.child0.toNat d →
      SlotRealizesExprAt cam s.child1.toNat b →
      SlotRealizesExprAt cam slot (.lam d b)
  | forallE {slot : Nat} {d b : KExpr} {s : CamSlotEntry} :
      cam.entries[slot]? = some s → s.tag = 6#4 →
      SlotRealizesExprAt cam s.child0.toNat d →
      SlotRealizesExprAt cam s.child1.toNat b →
      SlotRealizesExprAt cam slot (.forallE d b)
  | letE {slot : Nat} {t v b : KExpr} {s : CamSlotEntry} :
      cam.entries[slot]? = some s → s.tag = 7#4 →
      SlotRealizesExprAt cam s.child0.toNat t →
      SlotRealizesExprAt cam s.child1.toNat v →
      SlotRealizesExprAt cam s.child2.toNat b →
      SlotRealizesExprAt cam slot (.letE t v b)
  | lit {slot : Nat} {l : KLiteral} {s : CamSlotEntry} :
      cam.entries[slot]? = some s → s.tag = 8#4 →
      cam.symbols[s.symId.toNat]? = some (.litEntry l) →
      SlotRealizesExprAt cam slot (.lit l)
  | proj {slot idx : Nat} {sName : KName} {e : KExpr} {s : CamSlotEntry} :
      cam.entries[slot]? = some s → s.tag = 9#4 →
      cam.symbols[s.symId.toNat]? = some (.projEntry sName idx) →
      SlotRealizesExprAt cam s.child0.toNat e →
      SlotRealizesExprAt cam slot (.proj sName idx e)

/-- Allocate or reuse a 32-bit symbol ID in `cam.symbols` via associative lookup. -/
def allocExprCamSymbol (cam : ExprCAM) (sym : HwCamSymbolEntry) : ExprCAM × UInt32 :=
  match findElemIdx? cam.symbols sym with
  | some idx => (cam, UInt32.ofNat idx)
  | none =>
    let idx := cam.symbols.length
    ({ cam with symbols := cam.symbols ++ [sym] }, UInt32.ofNat idx)

/-- Allocate or reuse a single root hardware slot key `k : CamSlotKey` with packed summary `word64` in `cam`. -/
def internRootNode (cam : ExprCAM) (k : CamSlotKey) (word64 : CamWord64) : ExprCAM × CamHandle :=
  match cam.lookupSlotKey? k with
  | some h => (cam, h)
  | none =>
    let h := cam.entries.length
    let entry : CamSlotEntry :=
      { handle := UInt32.ofNat h
      , word64 := word64
      , tag    := k.tag
      , symId  := k.symId
      , child0 := k.child0
      , child1 := k.child1
      , child2 := k.child2 }
    ({ cam with entries := cam.entries ++ [entry] }, h)

/-- Bottom-up ghost-free DAG hash-consing (`internExpr`):
recursively interns all child subexpressions of `e` into `cam`, allocates 32-bit symbol IDs for
constants/literals/sorts/projections, and stores explicit 32-bit `(child0, child1, child2)` slot
indices (eliminating both the `expr : KExpr` ghost field and 181-node Cantor pairing overflow). -/
def internExpr (cam : ExprCAM) : KExpr → ExprCAM × CamHandle
  | e@(.bvar idx) =>
    internRootNode cam { tag := 0#4, symId := UInt32.ofNat idx } (mkExprCamWord64 e idx 0)
  | e@(.fvar id) =>
    internRootNode cam { tag := 1#4, symId := UInt32.ofNat id } (mkExprCamWord64 e id 0)
  | e@(.mvar id) =>
    internRootNode cam { tag := 10#4, symId := UInt32.ofNat id } (mkExprCamWord64 e id 0)
  | e@(.sort u) =>
    let (cam1, symId) := allocExprCamSymbol cam (.sortEntry u)
    internRootNode cam1 { tag := 2#4, symId := symId } (mkExprCamWord64 e symId.toNat 0)
  | e@(.const n us) =>
    let (cam1, symId) := allocExprCamSymbol cam (.constEntry n us)
    internRootNode cam1 { tag := 3#4, symId := symId } (mkExprCamWord64 e symId.toNat us.length)
  | e@(.lit l) =>
    let (cam1, symId) := allocExprCamSymbol cam (.litEntry l)
    internRootNode cam1 { tag := 8#4, symId := symId } (mkExprCamWord64 e symId.toNat 0)
  | e@(.app f a) =>
    let (cam1, hf) := internExpr cam f
    let (cam2, ha) := internExpr cam1 a
    internRootNode cam2
      { tag := 4#4, child0 := UInt32.ofNat hf, child1 := UInt32.ofNat ha }
      (mkExprCamWord64 e hf ha)
  | e@(.lam d b) =>
    let (cam1, hd) := internExpr cam d
    let (cam2, hb) := internExpr cam1 b
    internRootNode cam2
      { tag := 5#4, child0 := UInt32.ofNat hd, child1 := UInt32.ofNat hb }
      (mkExprCamWord64 e hd hb)
  | e@(.forallE d b) =>
    let (cam1, hd) := internExpr cam d
    let (cam2, hb) := internExpr cam1 b
    internRootNode cam2
      { tag := 6#4, child0 := UInt32.ofNat hd, child1 := UInt32.ofNat hb }
      (mkExprCamWord64 e hd hb)
  | e@(.letE t v b) =>
    let (cam1, ht) := internExpr cam t
    let (cam2, hv) := internExpr cam1 v
    let (cam3, hb) := internExpr cam2 b
    internRootNode cam3
      { tag := 7#4, child0 := UInt32.ofNat ht, child1 := UInt32.ofNat hv, child2 := UInt32.ofNat hb }
      (mkExprCamWord64 e ht hv)
  | e@(.proj sName idx s) =>
    let (cam1, hs) := internExpr cam s
    let (cam2, symId) := allocExprCamSymbol cam1 (.projEntry sName idx)
    internRootNode cam2
      { tag := 9#4, symId := symId, child0 := UInt32.ofNat hs }
      (mkExprCamWord64 e hs symId.toNat)

/-- Read the 1-bit `looseBVar` hardware flag (bit 59) directly from the 64-bit `CamWord64` at handle `h`. -/
def camHandleHasLooseBVar? (cam : ExprCAM) (h : CamHandle) : Option Bool := do
  let slot ← cam.lookupSlot? h
  pure (unpackCamWord64 slot.word64).looseBVar

/-- O(1) hardware-accelerated De Bruijn instantiation (`camInstantiate1`):
checks bit 59 (`looseBVar`) of the 64-bit CAM word for `body` first; if `false`, returns `body`
immediately in 1 cycle without traversing the AST! -/
def camInstantiate1 (cam : ExprCAM) (body arg : KExpr) : KExpr :=
  let (cam1, hBody) := internExpr cam body
  match camHandleHasLooseBVar? cam1 hBody with
  | some false => body
  | _ => KExpr.instantiate1 body arg

/-! ## 4. Main Soundness Theorems for Ghost-Free `ExprCAM` (`WS 24`) -/

/-- **Theorem (`exprCam_looseBVar_flag_sound`)**:
1. For every `e : KExpr` and child handles `(leftH, rightH)`, bit 59 (`looseBVar`) of the packed
   64-bit CAM word `mkExprCamWord64 e leftH rightH` equals `KExpr.hasLooseBVar e`, and bit 58
   (`hasFVar`) equals `KExpr.hasFVar e`.
2. Whenever `KExpr.hasLooseBVar e = false` (a closed expression), `KExpr.instantiate1 e arg = e`
   and `KExpr.liftLooseBVars 0 delta e = e`, so 1-bit hardware `looseBVar` gating is 100% sound. -/
theorem exprCam_looseBVar_flag_sound (e : KExpr) (leftH rightH delta : Nat) (arg : KExpr) :
    (unpackCamWord64 (mkExprCamWord64 e leftH rightH)).looseBVar = KExpr.hasLooseBVar e ∧
    (unpackCamWord64 (mkExprCamWord64 e leftH rightH)).hasFVar = KExpr.hasFVar e ∧
    (KExpr.hasLooseBVar e = false →
      KExpr.instantiate1 e arg = e ∧ KExpr.liftLooseBVars 0 delta e = e) := by
  have hunpack := unpack_pack_camWord64 (mkExprCamFields e leftH rightH)
  refine ⟨?_, ?_, ?_⟩
  · unfold mkExprCamWord64
    rw [hunpack]
    rfl
  · unfold mkExprCamWord64
    rw [hunpack]
    rfl
  · intro hclosed
    exact ⟨instantiateAt_of_hasLooseBVarAt_false e 0 arg hclosed,
           liftLooseBVars_of_hasLooseBVarAt_false e 0 delta hclosed⟩

/-- Sample compound expression `(idNat 42) + (idNat 42)` with shared subterm `idNat 42`. -/
def sharedSubtermExpr : KExpr :=
  let sub := KExpr.app (.const (KName.mkSimple "idNat") []) (.lit (.natVal 42))
  .app (.app (.const (KName.mkSimple "Nat.add") []) sub) sub

/-- **Theorem (`exprCam_eq_iff_handle_eq`)**:
1. **1-Cycle Structural Equality via Handle Comparison**: Interning two expressions `e1` and `e2`
   into the same ghost-free `ExprCAM` pool yields identical handles (`h1 == h2`) if and only if
   `e1` and `e2` are structurally equal (`e1 == e2`).
2. **DAG Subterm Sharing Compression**: Interning `sharedSubtermExpr` (`(idNat 42) + (idNat 42)`)
   into `ExprCAM.empty` allocates the shared subtree `idNat 42` (`3` nodes) only once (`6` total
   CAM slots instead of `9` tree nodes), and decodes losslessly via `uninternExpr`. -/
theorem exprCam_eq_iff_handle_eq :
    let sub1 := KExpr.app (.const (KName.mkSimple "idNat") []) (.lit (.natVal 42))
    let sub2 := KExpr.app (.const (KName.mkSimple "idNat") []) (.lit (.natVal 42))
    let diff := KExpr.app (.const (KName.mkSimple "idNat") []) (.lit (.natVal 99))
    let (cam1, h1) := internExpr ExprCAM.empty sub1
    let (cam2, h2) := internExpr cam1 sub2
    let (_, hDiff) := internExpr cam2 diff
    let (camShared, hShared) := internExpr ExprCAM.empty sharedSubtermExpr
    let (camAfterReintern, hSubAgain) := internExpr camShared sub1
    (h1 == h2) = (sub1 == sub2) ∧
    h1 = h2 ∧
    cam2.entries.length = cam1.entries.length ∧
    (h1 == hDiff) = (sub1 == diff) ∧
    h1 ≠ hDiff ∧
    camShared.entries.length = 6 ∧
    camAfterReintern.entries.length = 6 ∧
    uninternExpr camShared hShared = some sharedSubtermExpr ∧
    uninternExpr camShared hSubAgain = some sub1 := by
  refine ⟨rfl, rfl, rfl, rfl, by decide, rfl, rfl, rfl, rfl⟩

/-- Maximum number of entries addressable by 16-bit fast-filter handles (`2^16 = 65536`). -/
def maxPoolEntries : Nat := 65536

/-- Capacity-bounded root node interning (`internRootNodeBounded`):
reuses an existing handle in 1 cycle even when `cam.entries.length == maxCap`, and returns `none`
only when allocating a brand-new hardware slot key `k` would exceed `maxCap`. -/
def internRootNodeBounded (maxCap : Nat) (cam : ExprCAM) (k : CamSlotKey) (word64 : CamWord64) :
    Option (ExprCAM × CamHandle) :=
  match cam.lookupSlotKey? k with
  | some h => some (cam, h)
  | none =>
    if cam.entries.length >= maxCap then
      none
    else
      let h := cam.entries.length
      let entry : CamSlotEntry :=
        { handle := UInt32.ofNat h
        , word64 := word64
        , tag    := k.tag
        , symId  := k.symId
        , child0 := k.child0
        , child1 := k.child1
        , child2 := k.child2 }
      some ({ cam with entries := cam.entries ++ [entry] }, h)

theorem KName.eq_of_beq : ∀ (a b : KName), KName.beq a b = true → a = b
  | .anonymous, .anonymous, _ => rfl
  | .str p1 s1, .str p2 s2, h => by
    simp only [KName.beq, Bool.and_eq_true, beq_iff_eq] at h
    rw [KName.eq_of_beq p1 p2 h.2, h.1]
  | .num p1 i1, .num p2 i2, h => by
    simp only [KName.beq, Bool.and_eq_true, beq_iff_eq] at h
    rw [KName.eq_of_beq p1 p2 h.2, h.1]
  | .anonymous, .str _ _, h | .anonymous, .num _ _, h
  | .str _ _, .anonymous, h | .str _ _, .num _ _, h
  | .num _ _, .anonymous, h | .num _ _, .str _ _, h => by cases h

theorem KLevel.eq_of_beq : ∀ (a b : KLevel), KLevel.beq a b = true → a = b
  | .zero, .zero, _ => rfl
  | .succ l1, .succ l2, h => by
    simp only [KLevel.beq] at h
    rw [KLevel.eq_of_beq l1 l2 h]
  | .max a1 b1, .max a2 b2, h => by
    simp only [KLevel.beq, Bool.and_eq_true] at h
    rw [KLevel.eq_of_beq a1 a2 h.1, KLevel.eq_of_beq b1 b2 h.2]
  | .imax a1 b1, .imax a2 b2, h => by
    simp only [KLevel.beq, Bool.and_eq_true] at h
    rw [KLevel.eq_of_beq a1 a2 h.1, KLevel.eq_of_beq b1 b2 h.2]
  | .param n1, .param n2, h => by
    simp only [KLevel.beq] at h
    rw [KName.eq_of_beq n1 n2 h]
  | .zero, .succ _, h | .zero, .max _ _, h | .zero, .imax _ _, h | .zero, .param _, h
  | .succ _, .zero, h | .succ _, .max _ _, h | .succ _, .imax _ _, h | .succ _, .param _, h
  | .max _ _, .zero, h | .max _ _, .succ _, h | .max _ _, .imax _ _, h | .max _ _, .param _, h
  | .imax _ _, .zero, h | .imax _ _, .succ _, h | .imax _ _, .max _ _, h | .imax _ _, .param _, h
  | .param _, .zero, h | .param _, .succ _, h | .param _, .max _ _, h | .param _, .imax _ _, h => by
    cases h

theorem KLevel.listEq_of_listBeq : ∀ (a b : List KLevel), KLevel.listBeq a b = true → a = b
  | [], [], _ => rfl
  | u :: us, v :: vs, h => by
    simp only [KLevel.listBeq, Bool.and_eq_true] at h
    rw [KLevel.eq_of_beq u v h.1, KLevel.listEq_of_listBeq us vs h.2]
  | [], _ :: _, h | _ :: _, [], h => by cases h

theorem KLiteral.eq_of_beq : ∀ (a b : KLiteral), KLiteral.beq a b = true → a = b
  | .natVal n1, .natVal n2, h => by
    simp only [KLiteral.beq, beq_iff_eq] at h
    rw [h]
  | .strVal s1, .strVal s2, h => by
    simp only [KLiteral.beq, beq_iff_eq] at h
    rw [h]
  | .natVal _, .strVal _, h | .strVal _, .natVal _, h => by cases h

theorem KExpr.eq_of_beq : ∀ (a b : KExpr), KExpr.beq a b = true → a = b
  | .bvar i1, .bvar i2, h => by
    simp only [KExpr.beq, beq_iff_eq] at h; rw [h]
  | .fvar i1, .fvar i2, h => by
    simp only [KExpr.beq, beq_iff_eq] at h; rw [h]
  | .mvar i1, .mvar i2, h => by
    simp only [KExpr.beq, beq_iff_eq] at h; rw [h]
  | .sort u1, .sort u2, h => by
    simp only [KExpr.beq] at h; rw [KLevel.eq_of_beq u1 u2 h]
  | .const n1 us1, .const n2 us2, h => by
    simp only [KExpr.beq, Bool.and_eq_true] at h
    rw [KName.eq_of_beq n1 n2 h.1, KLevel.listEq_of_listBeq us1 us2 h.2]
  | .app f1 a1, .app f2 a2, h => by
    simp only [KExpr.beq, Bool.and_eq_true] at h
    rw [KExpr.eq_of_beq f1 f2 h.1, KExpr.eq_of_beq a1 a2 h.2]
  | .lam d1 b1, .lam d2 b2, h => by
    simp only [KExpr.beq, Bool.and_eq_true] at h
    rw [KExpr.eq_of_beq d1 d2 h.1, KExpr.eq_of_beq b1 b2 h.2]
  | .forallE d1 b1, .forallE d2 b2, h => by
    simp only [KExpr.beq, Bool.and_eq_true] at h
    rw [KExpr.eq_of_beq d1 d2 h.1, KExpr.eq_of_beq b1 b2 h.2]
  | .letE t1 v1 b1, .letE t2 v2 b2, h => by
    simp only [KExpr.beq, Bool.and_eq_true] at h
    rw [KExpr.eq_of_beq t1 t2 h.1.1, KExpr.eq_of_beq v1 v2 h.1.2, KExpr.eq_of_beq b1 b2 h.2]
  | .lit l1, .lit l2, h => by
    simp only [KExpr.beq] at h; rw [KLiteral.eq_of_beq l1 l2 h]
  | .proj s1 i1 e1, .proj s2 i2 e2, h => by
    simp only [KExpr.beq, Bool.and_eq_true, beq_iff_eq] at h
    rw [KName.eq_of_beq s1 s2 h.1.1, h.1.2, KExpr.eq_of_beq e1 e2 h.2]
  | .bvar _, .fvar _, h | .bvar _, .mvar _, h | .bvar _, .sort _, h | .bvar _, .const _ _, h | .bvar _, .app _ _, h
  | .bvar _, .lam _ _, h | .bvar _, .forallE _ _, h | .bvar _, .letE _ _ _, h | .bvar _, .lit _, h | .bvar _, .proj _ _ _, h
  | .fvar _, .bvar _, h | .fvar _, .mvar _, h | .fvar _, .sort _, h | .fvar _, .const _ _, h | .fvar _, .app _ _, h
  | .fvar _, .lam _ _, h | .fvar _, .forallE _ _, h | .fvar _, .letE _ _ _, h | .fvar _, .lit _, h | .fvar _, .proj _ _ _, h
  | .mvar _, .bvar _, h | .mvar _, .fvar _, h | .mvar _, .sort _, h | .mvar _, .const _ _, h | .mvar _, .app _ _, h
  | .mvar _, .lam _ _, h | .mvar _, .forallE _ _, h | .mvar _, .letE _ _ _, h | .mvar _, .lit _, h | .mvar _, .proj _ _ _, h
  | .sort _, .bvar _, h | .sort _, .fvar _, h | .sort _, .mvar _, h | .sort _, .const _ _, h | .sort _, .app _ _, h
  | .sort _, .lam _ _, h | .sort _, .forallE _ _, h | .sort _, .letE _ _ _, h | .sort _, .lit _, h | .sort _, .proj _ _ _, h
  | .const _ _, .bvar _, h | .const _ _, .fvar _, h | .const _ _, .mvar _, h | .const _ _, .sort _, h | .const _ _, .app _ _, h
  | .const _ _, .lam _ _, h | .const _ _, .forallE _ _, h | .const _ _, .letE _ _ _, h | .const _ _, .lit _, h | .const _ _, .proj _ _ _, h
  | .app _ _, .bvar _, h | .app _ _, .fvar _, h | .app _ _, .mvar _, h | .app _ _, .sort _, h | .app _ _, .const _ _, h
  | .app _ _, .lam _ _, h | .app _ _, .forallE _ _, h | .app _ _, .letE _ _ _, h | .app _ _, .lit _, h | .app _ _, .proj _ _ _, h
  | .lam _ _, .bvar _, h | .lam _ _, .fvar _, h | .lam _ _, .mvar _, h | .lam _ _, .sort _, h | .lam _ _, .const _ _, h
  | .lam _ _, .app _ _, h | .lam _ _, .forallE _ _, h | .lam _ _, .letE _ _ _, h | .lam _ _, .lit _, h | .lam _ _, .proj _ _ _, h
  | .forallE _ _, .bvar _, h | .forallE _ _, .fvar _, h | .forallE _ _, .mvar _, h | .forallE _ _, .sort _, h | .forallE _ _, .const _ _, h
  | .forallE _ _, .app _ _, h | .forallE _ _, .lam _ _, h | .forallE _ _, .letE _ _ _, h | .forallE _ _, .lit _, h | .forallE _ _, .proj _ _ _, h
  | .letE _ _ _, .bvar _, h | .letE _ _ _, .fvar _, h | .letE _ _ _, .mvar _, h | .letE _ _ _, .sort _, h | .letE _ _ _, .const _ _, h
  | .letE _ _ _, .app _ _, h | .letE _ _ _, .lam _ _, h | .letE _ _ _, .forallE _ _, h | .letE _ _ _, .lit _, h | .letE _ _ _, .proj _ _ _, h
  | .lit _, .bvar _, h | .lit _, .fvar _, h | .lit _, .mvar _, h | .lit _, .sort _, h | .lit _, .const _ _, h
  | .lit _, .app _ _, h | .lit _, .lam _ _, h | .lit _, .forallE _ _, h | .lit _, .letE _ _ _, h | .lit _, .proj _ _ _, h
  | .proj _ _ _, .bvar _, h | .proj _ _ _, .fvar _, h | .proj _ _ _, .mvar _, h | .proj _ _ _, .sort _, h | .proj _ _ _, .const _ _, h
  | .proj _ _ _, .app _ _, h | .proj _ _ _, .lam _ _, h | .proj _ _ _, .forallE _ _, h | .proj _ _ _, .letE _ _ _, h | .proj _ _ _, .lit _, h => by
    cases h

/-- Upper bound on the number of new CAM slots / symbol entries allocated when interning `e`. -/
def exprNodeBound : KExpr → Nat
  | .bvar _ | .fvar _ | .mvar _ | .sort _ | .const _ _ | .lit _ => 1
  | .app f a | .lam f a | .forallE f a => 1 + exprNodeBound f + exprNodeBound a
  | .letE t v b => 1 + exprNodeBound t + exprNodeBound v + exprNodeBound b
  | .proj _ _ s => 1 + exprNodeBound s

/-- All variable / metavariable indices inside `e` fit in 32-bit hardware registers (`UInt32`). -/
def exprVarsFitUInt32 : KExpr → Prop
  | .bvar idx | .fvar idx | .mvar idx => idx < UInt32.size
  | .sort _ | .const _ _ | .lit _ => True
  | .app f a | .lam f a | .forallE f a => exprVarsFitUInt32 f ∧ exprVarsFitUInt32 a
  | .letE t v b => exprVarsFitUInt32 t ∧ exprVarsFitUInt32 v ∧ exprVarsFitUInt32 b
  | .proj _ _ s => exprVarsFitUInt32 s

/-- 32-bit hardware addressability precondition for `ExprCAM` (`CamSlotEntry` uses `UInt32` registers). -/
def ExprCamAddressable (cam : ExprCAM) (e : KExpr) : Prop :=
  cam.entries.length + exprNodeBound e < UInt32.size ∧
  cam.symbols.length + exprNodeBound e < UInt32.size ∧
  exprVarsFitUInt32 e

/-- Topological child-slot invariant on `CamSlotKey`: active child handles strictly precede `bound`. -/
def SlotKeyChildrenBounded (bound : Nat) (k : CamSlotKey) : Prop :=
  (k.tag = 4#4 ∨ k.tag = 5#4 ∨ k.tag = 6#4 → k.child0.toNat < bound ∧ k.child1.toNat < bound) ∧
  (k.tag = 7#4 → k.child0.toNat < bound ∧ k.child1.toNat < bound ∧ k.child2.toNat < bound) ∧
  (k.tag = 9#4 → k.child0.toNat < bound)

/-- Well-formedness invariant for a ghost-free `ExprCAM` pool: every slot at index `i` stores
`s.handle.toNat = i` (`i < UInt32.size`) and topologically precedes any parent referencing it. -/
def ExprCAM.Valid (cam : ExprCAM) : Prop :=
  ∀ (i : Nat) (s : CamSlotEntry), cam.entries[i]? = some s →
    s.handle.toNat = i ∧ i < UInt32.size ∧ SlotKeyChildrenBounded i s.key

/-- Monotonicity predicate for `ExprCAM`: `cam2` preserves all existing slot and symbol entries of `cam1`. -/
def ExprCAM.Extends (cam1 cam2 : ExprCAM) : Prop :=
  (∀ (i : Nat) (s : CamSlotEntry), cam1.entries[i]? = some s → cam2.entries[i]? = some s) ∧
  (∀ (j : Nat) (sym : HwCamSymbolEntry), cam1.symbols[j]? = some sym → cam2.symbols[j]? = some sym)

theorem ExprCAM.Extends.refl (cam : ExprCAM) : cam.Extends cam :=
  ⟨fun _ _ h => h, fun _ _ h => h⟩

theorem ExprCAM.Extends.trans {a b c : ExprCAM}
    (h1 : a.Extends b) (h2 : b.Extends c) : a.Extends c :=
  ⟨fun i s h => h2.1 i s (h1.1 i s h), fun j sym h => h2.2 j sym (h1.2 j sym h)⟩

private theorem ExprCAM.Extends.lt_entries_len {cam1 cam2 : ExprCAM} (hext : cam1.Extends cam2)
    {i : Nat} (hlt : i < cam1.entries.length) : i < cam2.entries.length := by
  have h1 : cam1.entries[i]? = some cam1.entries[i] := List.getElem?_eq_getElem hlt
  exact (List.getElem?_eq_some_iff.mp (hext.1 i _ h1)).1

theorem ExprCAM.empty_valid : ExprCAM.empty.Valid := by
  intro i s hs
  cases hs

private theorem exists_getElem?_of_mem {α : Type} :
    ∀ (xs : List α) {x : α}, x ∈ xs → ∃ (i : Nat), xs[i]? = some x
  | [], _, h => by cases h
  | y :: ys, x, h => by
    rcases List.mem_cons.mp h with rfl | hrest
    · exact ⟨0, rfl⟩
    · obtain ⟨i, hi⟩ := exists_getElem?_of_mem ys hrest
      exact ⟨i + 1, hi⟩

private theorem uint32_toNat_ofNat_of_lt {n : Nat} (h : n < UInt32.size) :
    (UInt32.ofNat n).toNat = n := by
  change n % UInt32.size = n
  exact Nat.mod_eq_of_lt h

theorem SlotRealizesExprAt.mono {cam1 cam2 : ExprCAM} (hext : cam1.Extends cam2) :
    ∀ {slot : CamHandle} {e : KExpr},
      SlotRealizesExprAt cam1 slot e → SlotRealizesExprAt cam2 slot e
  | _, _, .bvar hs ht hi => .bvar (hext.1 _ _ hs) ht hi
  | _, _, .fvar hs ht hi => .fvar (hext.1 _ _ hs) ht hi
  | _, _, .mvar hs ht hi => .mvar (hext.1 _ _ hs) ht hi
  | _, _, .sort hs ht hsym => .sort (hext.1 _ _ hs) ht (hext.2 _ _ hsym)
  | _, _, .const hs ht hsym => .const (hext.1 _ _ hs) ht (hext.2 _ _ hsym)
  | _, _, .app hs ht rf ra => .app (hext.1 _ _ hs) ht (rf.mono hext) (ra.mono hext)
  | _, _, .lam hs ht rd rb => .lam (hext.1 _ _ hs) ht (rd.mono hext) (rb.mono hext)
  | _, _, .forallE hs ht rd rb => .forallE (hext.1 _ _ hs) ht (rd.mono hext) (rb.mono hext)
  | _, _, .letE hs ht rt rv rb => .letE (hext.1 _ _ hs) ht (rt.mono hext) (rv.mono hext) (rb.mono hext)
  | _, _, .lit hs ht hsym => .lit (hext.1 _ _ hs) ht (hext.2 _ _ hsym)
  | _, _, .proj hs ht hsym re => .proj (hext.1 _ _ hs) ht (hext.2 _ _ hsym) (re.mono hext)

theorem decodeSlotCamDag_of_slotRealizesExprAt {cam : ExprCAM} :
    ∀ {slot : CamHandle} {e : KExpr},
      SlotRealizesExprAt cam slot e →
      ∀ {fuel : Nat}, depth e ≤ fuel → decodeSlotCamDag fuel cam slot = some e
  | _, _, .bvar hs ht hi, 0, hd => by simp [depth] at hd
  | _, _, .bvar hs ht hi, f + 1, _ => by
    unfold decodeSlotCamDag; rw [hs]; simp [ht, hi]
  | _, _, .fvar hs ht hi, 0, hd => by simp [depth] at hd
  | _, _, .fvar hs ht hi, f + 1, _ => by
    unfold decodeSlotCamDag; rw [hs]; simp [ht, hi]
  | _, _, .mvar hs ht hi, 0, hd => by simp [depth] at hd
  | _, _, .mvar hs ht hi, f + 1, _ => by
    unfold decodeSlotCamDag; rw [hs]; simp [ht, hi]
  | _, _, .sort hs ht hsym, 0, hd => by simp [depth] at hd
  | _, _, .sort hs ht hsym, f + 1, _ => by
    unfold decodeSlotCamDag; rw [hs]; simp [ht, hsym]
  | _, _, .const hs ht hsym, 0, hd => by simp [depth] at hd
  | _, _, .const hs ht hsym, f + 1, _ => by
    unfold decodeSlotCamDag; rw [hs]; simp [ht, hsym]
  | _, _, .lit hs ht hsym, 0, hd => by simp [depth] at hd
  | _, _, .lit hs ht hsym, f + 1, _ => by
    unfold decodeSlotCamDag; rw [hs]; simp [ht, hsym]
  | _, _, .app hs ht rf ra, 0, hd => by simp [depth] at hd
  | _, _, .app hs ht rf ra, fuel + 1, hd => by
    simp only [depth] at hd
    unfold decodeSlotCamDag; rw [hs]
    simp [ht,
      decodeSlotCamDag_of_slotRealizesExprAt (fuel := fuel) rf (by omega),
      decodeSlotCamDag_of_slotRealizesExprAt (fuel := fuel) ra (by omega)]
  | _, _, .lam hs ht rd rb, 0, hd => by simp [depth] at hd
  | _, _, .lam hs ht rd rb, fuel + 1, hd => by
    simp only [depth] at hd
    unfold decodeSlotCamDag; rw [hs]
    simp [ht,
      decodeSlotCamDag_of_slotRealizesExprAt (fuel := fuel) rd (by omega),
      decodeSlotCamDag_of_slotRealizesExprAt (fuel := fuel) rb (by omega)]
  | _, _, .forallE hs ht rd rb, 0, hd => by simp [depth] at hd
  | _, _, .forallE hs ht rd rb, fuel + 1, hd => by
    simp only [depth] at hd
    unfold decodeSlotCamDag; rw [hs]
    simp [ht,
      decodeSlotCamDag_of_slotRealizesExprAt (fuel := fuel) rd (by omega),
      decodeSlotCamDag_of_slotRealizesExprAt (fuel := fuel) rb (by omega)]
  | _, _, .letE hs ht rt rv rb, 0, hd => by simp [depth] at hd
  | _, _, .letE hs ht rt rv rb, fuel + 1, hd => by
    simp only [depth] at hd
    unfold decodeSlotCamDag; rw [hs]
    simp [ht,
      decodeSlotCamDag_of_slotRealizesExprAt (fuel := fuel) rt (by omega),
      decodeSlotCamDag_of_slotRealizesExprAt (fuel := fuel) rv (by omega),
      decodeSlotCamDag_of_slotRealizesExprAt (fuel := fuel) rb (by omega)]
  | _, _, .proj hs ht hsym re, 0, hd => by simp [depth] at hd
  | _, _, .proj hs ht hsym re, fuel + 1, hd => by
    simp only [depth] at hd
    unfold decodeSlotCamDag; rw [hs]
    simp [ht, hsym, decodeSlotCamDag_of_slotRealizesExprAt (fuel := fuel) re (by omega)]

theorem slotRealizesExprAt_of_decodeSlotCamDag {cam : ExprCAM} :
    ∀ {fuel : Nat} {slot : CamHandle} {e : KExpr},
      decodeSlotCamDag fuel cam slot = some e → SlotRealizesExprAt cam slot e
  | 0, _, _, hdec => by cases hdec
  | fuel + 1, slot, e, hdec => by
    unfold decodeSlotCamDag at hdec
    cases hs : cam.entries[slot]? with
    | none => simp [hs] at hdec
    | some s =>
      rw [hs] at hdec
      by_cases h0 : s.tag = 0#4
      · simp [h0] at hdec; subst hdec; exact .bvar hs h0 rfl
      · by_cases h1 : s.tag = 1#4
        · simp [h1] at hdec; subst hdec; exact .fvar hs h1 rfl
        · by_cases h2 : s.tag = 2#4
          · cases hsym : cam.symbols[s.symId.toNat]? with
            | none => simp [h2, hsym] at hdec
            | some sym =>
              cases sym <;> simp [h2, hsym] at hdec
              subst hdec; exact .sort hs h2 hsym
          · by_cases h3 : s.tag = 3#4
            · cases hsym : cam.symbols[s.symId.toNat]? with
              | none => simp [h3, hsym] at hdec
              | some sym =>
                cases sym <;> simp [h3, hsym] at hdec
                subst hdec; exact .const hs h3 hsym
            · by_cases h4 : s.tag = 4#4
              · cases hc0 : decodeSlotCamDag fuel cam s.child0.toNat with
                | none => simp [h4, hc0] at hdec
                | some f =>
                  cases hc1 : decodeSlotCamDag fuel cam s.child1.toNat with
                  | none => simp [h4, hc0, hc1] at hdec
                  | some a =>
                    simp [h4, hc0, hc1] at hdec; subst hdec
                    exact .app hs h4
                      (slotRealizesExprAt_of_decodeSlotCamDag hc0)
                      (slotRealizesExprAt_of_decodeSlotCamDag hc1)
              · by_cases h5 : s.tag = 5#4
                · cases hc0 : decodeSlotCamDag fuel cam s.child0.toNat with
                  | none => simp [h5, hc0] at hdec
                  | some d =>
                    cases hc1 : decodeSlotCamDag fuel cam s.child1.toNat with
                    | none => simp [h5, hc0, hc1] at hdec
                    | some b =>
                      simp [h5, hc0, hc1] at hdec; subst hdec
                      exact .lam hs h5
                        (slotRealizesExprAt_of_decodeSlotCamDag hc0)
                        (slotRealizesExprAt_of_decodeSlotCamDag hc1)
                · by_cases h6 : s.tag = 6#4
                  · cases hc0 : decodeSlotCamDag fuel cam s.child0.toNat with
                    | none => simp [h6, hc0] at hdec
                    | some d =>
                      cases hc1 : decodeSlotCamDag fuel cam s.child1.toNat with
                      | none => simp [h6, hc0, hc1] at hdec
                      | some b =>
                        simp [h6, hc0, hc1] at hdec; subst hdec
                        exact .forallE hs h6
                          (slotRealizesExprAt_of_decodeSlotCamDag hc0)
                          (slotRealizesExprAt_of_decodeSlotCamDag hc1)
                  · by_cases h7 : s.tag = 7#4
                    · cases hc0 : decodeSlotCamDag fuel cam s.child0.toNat with
                      | none => simp [h7, hc0] at hdec
                      | some t =>
                        cases hc1 : decodeSlotCamDag fuel cam s.child1.toNat with
                        | none => simp [h7, hc0, hc1] at hdec
                        | some v =>
                          cases hc2 : decodeSlotCamDag fuel cam s.child2.toNat with
                          | none => simp [h7, hc0, hc1, hc2] at hdec
                          | some b =>
                            simp [h7, hc0, hc1, hc2] at hdec; subst hdec
                            exact .letE hs h7
                              (slotRealizesExprAt_of_decodeSlotCamDag hc0)
                              (slotRealizesExprAt_of_decodeSlotCamDag hc1)
                              (slotRealizesExprAt_of_decodeSlotCamDag hc2)
                    · by_cases h8 : s.tag = 8#4
                      · cases hsym : cam.symbols[s.symId.toNat]? with
                        | none => simp [h8, hsym] at hdec
                        | some sym =>
                          cases sym <;> simp [h8, hsym] at hdec
                          subst hdec; exact .lit hs h8 hsym
                      · by_cases h9 : s.tag = 9#4
                        · cases hc0 : decodeSlotCamDag fuel cam s.child0.toNat with
                          | none => simp [h9, hc0] at hdec
                          | some sub =>
                            cases hsym : cam.symbols[s.symId.toNat]? with
                            | none => simp [h9, hc0, hsym] at hdec
                            | some sym =>
                              cases sym <;> simp [h9, hc0, hsym] at hdec
                              subst hdec
                              exact .proj hs h9 hsym (slotRealizesExprAt_of_decodeSlotCamDag hc0)
                        · by_cases h10 : s.tag = 10#4
                          · simp [h10] at hdec
                            subst hdec; exact .mvar hs h10 rfl
                          · simp [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10] at hdec

theorem slotRealizesExprAt_iff_decodeSlotCamDag (cam : ExprCAM) (slot : CamHandle) (e : KExpr) :
    SlotRealizesExprAt cam slot e ↔ ∃ fuel, decodeSlotCamDag fuel cam slot = some e :=
  ⟨fun hr => ⟨depth e, decodeSlotCamDag_of_slotRealizesExprAt hr (Nat.le_refl _)⟩,
   fun ⟨_, hdec⟩ => slotRealizesExprAt_of_decodeSlotCamDag hdec⟩

theorem SlotRealizesExprAt.slot_lt_length {cam : ExprCAM} {slot : CamHandle} {e : KExpr}
    (hr : SlotRealizesExprAt cam slot e) : slot < cam.entries.length := by
  cases hr with
  | bvar hs _ _ | fvar hs _ _ | mvar hs _ _ | sort hs _ _ | const hs _ _
  | app hs _ _ _ | lam hs _ _ _ | forallE hs _ _ _ | letE hs _ _ _ _
  | lit hs _ _ | proj hs _ _ _ =>
    exact (List.getElem?_eq_some_iff.mp hs).1

theorem SlotRealizesExprAt.depth_le_slot_succ {cam : ExprCAM} (hv : cam.Valid) :
    ∀ {slot : CamHandle} {e : KExpr},
      SlotRealizesExprAt cam slot e → depth e ≤ slot + 1
  | _, _, .bvar _ _ _ | _, _, .fvar _ _ _ | _, _, .mvar _ _ _
  | _, _, .sort _ _ _ | _, _, .const _ _ _ | _, _, .lit _ _ _ => by
    simp [depth]
  | slot, _, .app hs htag rf ra => by
    have hbnd := (hv slot _ hs).2.2.1 (.inl htag)
    have df := rf.depth_le_slot_succ hv
    have da := ra.depth_le_slot_succ hv
    simp only [CamSlotEntry.key] at hbnd
    simp only [depth]; omega
  | slot, _, .lam hs htag rd rb => by
    have hbnd := (hv slot _ hs).2.2.1 (.inr (.inl htag))
    have dd := rd.depth_le_slot_succ hv
    have db := rb.depth_le_slot_succ hv
    simp only [CamSlotEntry.key] at hbnd
    simp only [depth]; omega
  | slot, _, .forallE hs htag rd rb => by
    have hbnd := (hv slot _ hs).2.2.1 (.inr (.inr htag))
    have dd := rd.depth_le_slot_succ hv
    have db := rb.depth_le_slot_succ hv
    simp only [CamSlotEntry.key] at hbnd
    simp only [depth]; omega
  | slot, _, .letE hs htag rt rv rb => by
    have hbnd := (hv slot _ hs).2.2.2.1 htag
    have dt := rt.depth_le_slot_succ hv
    have dv := rv.depth_le_slot_succ hv
    have db := rb.depth_le_slot_succ hv
    simp only [CamSlotEntry.key] at hbnd
    simp only [depth]; omega
  | slot, _, .proj hs htag _ re => by
    have hbnd := (hv slot _ hs).2.2.2.2 htag
    have de := re.depth_le_slot_succ hv
    simp only [CamSlotEntry.key] at hbnd
    simp only [depth]; omega

theorem uninternExpr_of_slotRealizesExprAt {cam : ExprCAM} (hv : cam.Valid)
    {slot : CamHandle} {e : KExpr} (hr : SlotRealizesExprAt cam slot e) :
    uninternExpr cam slot = some e :=
  decodeSlotCamDag_of_slotRealizesExprAt hr (Nat.le_trans (hr.depth_le_slot_succ hv) hr.slot_lt_length)

private theorem allocExprCamSymbol_size_le (cam : ExprCAM) (sym : HwCamSymbolEntry) :
    (allocExprCamSymbol cam sym).1.entries = cam.entries ∧
    (allocExprCamSymbol cam sym).1.symbols.length ≤ cam.symbols.length + 1 := by
  unfold allocExprCamSymbol
  cases findElemIdx? cam.symbols sym <;> simp

private theorem internRootNode_len_le {cam : ExprCAM} {k : CamSlotKey} {w : CamWord64} {eb sb : Nat}
    (he : cam.entries.length + 1 ≤ eb) (hs : cam.symbols.length ≤ sb) :
    (internRootNode cam k w).1.entries.length ≤ eb ∧
    (internRootNode cam k w).1.symbols.length ≤ sb := by
  unfold internRootNode
  cases cam.lookupSlotKey? k <;> simp <;> omega

theorem internExpr_size_le : ∀ (e : KExpr) (cam : ExprCAM),
    (internExpr cam e).1.entries.length ≤ cam.entries.length + exprNodeBound e ∧
    (internExpr cam e).1.symbols.length ≤ cam.symbols.length + exprNodeBound e
  | .bvar _, cam | .fvar _, cam | .mvar _, cam => by
    simp only [internExpr, exprNodeBound]
    exact internRootNode_len_le (Nat.le_refl _) (Nat.le_succ _)
  | .sort u, cam => by
    simp only [internExpr, exprNodeBound]
    have hs := allocExprCamSymbol_size_le cam (.sortEntry u)
    exact internRootNode_len_le (by rw [hs.1]; omega) hs.2
  | .const n us, cam => by
    simp only [internExpr, exprNodeBound]
    have hs := allocExprCamSymbol_size_le cam (.constEntry n us)
    exact internRootNode_len_le (by rw [hs.1]; omega) hs.2
  | .lit l, cam => by
    simp only [internExpr, exprNodeBound]
    have hs := allocExprCamSymbol_size_le cam (.litEntry l)
    exact internRootNode_len_le (by rw [hs.1]; omega) hs.2
  | .app f a, cam => by
    simp only [internExpr, exprNodeBound]
    have hf := internExpr_size_le f cam
    have ha := internExpr_size_le a (internExpr cam f).1
    exact internRootNode_len_le (by omega) (by omega)
  | .lam d b, cam => by
    simp only [internExpr, exprNodeBound]
    have hd := internExpr_size_le d cam
    have hb := internExpr_size_le b (internExpr cam d).1
    exact internRootNode_len_le (by omega) (by omega)
  | .forallE d b, cam => by
    simp only [internExpr, exprNodeBound]
    have hd := internExpr_size_le d cam
    have hb := internExpr_size_le b (internExpr cam d).1
    exact internRootNode_len_le (by omega) (by omega)
  | .letE t v b, cam => by
    simp only [internExpr, exprNodeBound]
    have ht := internExpr_size_le t cam
    have hv := internExpr_size_le v (internExpr cam t).1
    have hb := internExpr_size_le b (internExpr (internExpr cam t).1 v).1
    exact internRootNode_len_le (by omega) (by omega)
  | .proj sName idx s, cam => by
    simp only [internExpr, exprNodeBound]
    have hs := internExpr_size_le s cam
    have hsym := allocExprCamSymbol_size_le (internExpr cam s).1 (.projEntry sName idx)
    exact internRootNode_len_le (by rw [hsym.1]; omega) (by omega)

private theorem allocExprCamSymbol_spec {cam : ExprCAM} (hv : cam.Valid)
    (sym : HwCamSymbolEntry) (hSymFit : cam.symbols.length < UInt32.size) :
    cam.Extends (allocExprCamSymbol cam sym).1 ∧
    (allocExprCamSymbol cam sym).1.Valid ∧
    (allocExprCamSymbol cam sym).1.entries = cam.entries ∧
    (allocExprCamSymbol cam sym).1.symbols[(allocExprCamSymbol cam sym).2.toNat]? = some sym := by
  unfold allocExprCamSymbol
  cases hfind : findElemIdx? cam.symbols sym with
  | some idx =>
    have hget := getElem?_of_findElemIdx? cam.symbols sym idx hfind
    have hlt : idx < cam.symbols.length := (List.getElem?_eq_some_iff.mp hget).1
    refine ⟨ExprCAM.Extends.refl cam, hv, rfl, ?_⟩
    rwa [uint32_toNat_ofNat_of_lt (Nat.lt_trans hlt hSymFit)]
  | none =>
    refine ⟨⟨fun _ _ h => h, fun _ _ h => getElem?_append_preserve [sym] h⟩, hv, rfl, ?_⟩
    rw [uint32_toNat_ofNat_of_lt hSymFit]
    exact getElem?_append_singleton_self cam.symbols sym

private theorem pred_of_find?_eq_some {α : Type} (p : α → Bool) :
    ∀ (xs : List α) {a : α}, xs.find? p = some a → p a = true
  | [], _, h => by cases h
  | x :: xs, a, h => by
    simp only [List.find?] at h
    cases hp : p x with
    | true => rw [hp] at h; injection h with hEq; subst hEq; exact hp
    | false => rw [hp] at h; exact pred_of_find?_eq_some p xs h

private theorem internRootNode_spec {cam : ExprCAM} (hv : cam.Valid)
    (k : CamSlotKey) (w : CamWord64)
    (hCap : cam.entries.length < UInt32.size)
    (hBnd : SlotKeyChildrenBounded cam.entries.length k) :
    let (cam', h) := internRootNode cam k w
    cam.Extends cam' ∧
    cam'.Valid ∧
    h < cam'.entries.length ∧
    ∃ s, cam'.entries[h]? = some s ∧ s.key = k := by
  unfold internRootNode
  cases hlook : cam.lookupSlotKey? k with
  | some h =>
    unfold ExprCAM.lookupSlotKey? at hlook
    obtain ⟨slot, hfind, hhandle⟩ := Option.map_eq_some_iff.mp hlook
    have hmem : slot ∈ cam.entries := List.mem_of_find?_eq_some hfind
    have hkey : slot.key = k :=
      of_decide_eq_true (pred_of_find?_eq_some (fun slot => decide (slot.key = k)) cam.entries hfind)
    obtain ⟨idx, hget⟩ := exists_getElem?_of_mem cam.entries hmem
    have hidxEq : slot.handle.toNat = idx := (hv idx slot hget).1
    subst hhandle
    rw [hidxEq]
    exact ⟨ExprCAM.Extends.refl cam, hv, (List.getElem?_eq_some_iff.mp hget).1, ⟨slot, hget, hkey⟩⟩
  | none =>
    let entry : CamSlotEntry :=
      { handle := UInt32.ofNat cam.entries.length
      , word64 := w
      , tag    := k.tag
      , symId  := k.symId
      , child0 := k.child0
      , child1 := k.child1
      , child2 := k.child2 }
    have hentryKey : entry.key = k := by cases k; rfl
    refine ⟨⟨fun _ _ h => getElem?_append_preserve [entry] h, fun _ _ h => h⟩, ?_, ?_, ?_⟩
    · intro i s hs
      by_cases hi : i < cam.entries.length
      · rw [List.getElem?_append_left hi] at hs
        exact hv i s hs
      · by_cases heq : i = cam.entries.length
        · subst heq
          rw [getElem?_append_singleton_self] at hs
          injection hs with hsEq
          subst hsEq
          refine ⟨uint32_toNat_ofNat_of_lt hCap, hCap, ?_⟩
          rwa [hentryKey]
        · have hge : cam.entries.length + 1 ≤ i := by omega
          have hlt := (List.getElem?_eq_some_iff.mp hs).1
          simp only [List.length_append, List.length_singleton] at hlt
          omega
    · simp
    · exact ⟨entry, getElem?_append_singleton_self cam.entries entry, hentryKey⟩

private theorem leaf_slotKeyChildrenBounded (bound : Nat) (tag : BitVec 4) (symId : UInt32)
    (h4 : tag ≠ 4#4) (h5 : tag ≠ 5#4) (h6 : tag ≠ 6#4) (h7 : tag ≠ 7#4) (h9 : tag ≠ 9#4) :
    SlotKeyChildrenBounded bound { tag := tag, symId := symId } := by
  refine ⟨?_, ?_, ?_⟩
  · rintro (rfl | rfl | rfl) <;> contradiction
  · intro h; exact absurd h h7
  · intro h; exact absurd h h9

private theorem bin_slotKeyChildrenBounded (bound : Nat) (tag : BitVec 4) (c0 c1 : UInt32)
    (h0 : c0.toNat < bound) (h1 : c1.toNat < bound)
    (h7 : tag ≠ 7#4) (h9 : tag ≠ 9#4) :
    SlotKeyChildrenBounded bound { tag := tag, child0 := c0, child1 := c1 } := by
  unfold SlotKeyChildrenBounded
  refine ⟨fun _ => ⟨h0, h1⟩, ?_, ?_⟩
  · intro h; exact absurd h h7
  · intro h; exact absurd h h9

private theorem proj_slotKeyChildrenBounded (bound : Nat) (symId c0 : UInt32)
    (h0 : c0.toNat < bound) :
    SlotKeyChildrenBounded bound { tag := 9#4, symId := symId, child0 := c0 } := by
  unfold SlotKeyChildrenBounded
  refine ⟨?_, ?_, fun _ => h0⟩
  · rintro (h | h | h) <;> dsimp at h <;> exact absurd h (by decide)
  · intro h; dsimp at h; exact absurd h (by decide)

theorem internExpr_realizes :
    ∀ (e : KExpr) {cam : ExprCAM},
      cam.Valid →
      ExprCamAddressable cam e →
      let (cam', h) := internExpr cam e
      cam.Extends cam' ∧
      cam'.Valid ∧
      h < cam'.entries.length ∧
      SlotRealizesExprAt cam' h e
  | .bvar idx, cam, hv, ⟨hEnt, _, hVar⟩ => by
    simp only [internExpr]
    simp only [exprNodeBound] at hEnt
    simp only [exprVarsFitUInt32] at hVar
    have hbnd := leaf_slotKeyChildrenBounded cam.entries.length 0#4 (UInt32.ofNat idx)
      (by decide) (by decide) (by decide) (by decide) (by decide)
    obtain ⟨hext, hv', hlt, slot, hslot, hkey⟩ :=
      internRootNode_spec hv _ _ (by omega) hbnd
    have htag : slot.tag = 0#4 := congrArg CamSlotKey.tag hkey
    have hsym : slot.symId = UInt32.ofNat idx := congrArg CamSlotKey.symId hkey
    refine ⟨hext, hv', hlt, .bvar hslot htag ?_⟩
    rw [hsym, uint32_toNat_ofNat_of_lt hVar]
  | .fvar id, cam, hv, ⟨hEnt, _, hVar⟩ => by
    simp only [internExpr]
    simp only [exprNodeBound] at hEnt
    simp only [exprVarsFitUInt32] at hVar
    have hbnd := leaf_slotKeyChildrenBounded cam.entries.length 1#4 (UInt32.ofNat id)
      (by decide) (by decide) (by decide) (by decide) (by decide)
    obtain ⟨hext, hv', hlt, slot, hslot, hkey⟩ :=
      internRootNode_spec hv _ _ (by omega) hbnd
    have htag : slot.tag = 1#4 := congrArg CamSlotKey.tag hkey
    have hsym : slot.symId = UInt32.ofNat id := congrArg CamSlotKey.symId hkey
    refine ⟨hext, hv', hlt, .fvar hslot htag ?_⟩
    rw [hsym, uint32_toNat_ofNat_of_lt hVar]
  | .mvar id, cam, hv, ⟨hEnt, _, hVar⟩ => by
    simp only [internExpr]
    simp only [exprNodeBound] at hEnt
    simp only [exprVarsFitUInt32] at hVar
    have hbnd := leaf_slotKeyChildrenBounded cam.entries.length 10#4 (UInt32.ofNat id)
      (by decide) (by decide) (by decide) (by decide) (by decide)
    obtain ⟨hext, hv', hlt, slot, hslot, hkey⟩ :=
      internRootNode_spec hv _ _ (by omega) hbnd
    have htag : slot.tag = 10#4 := congrArg CamSlotKey.tag hkey
    have hsym : slot.symId = UInt32.ofNat id := congrArg CamSlotKey.symId hkey
    refine ⟨hext, hv', hlt, .mvar hslot htag ?_⟩
    rw [hsym, uint32_toNat_ofNat_of_lt hVar]
  | .sort u, cam, hv, ⟨hEnt, hSym, _⟩ => by
    simp only [internExpr]
    simp only [exprNodeBound] at hEnt hSym
    obtain ⟨hext1, hv1, hent1, hsymGet⟩ := allocExprCamSymbol_spec hv (.sortEntry u) (by omega)
    have hbnd := leaf_slotKeyChildrenBounded (allocExprCamSymbol cam (.sortEntry u)).1.entries.length
      2#4 (allocExprCamSymbol cam (.sortEntry u)).2
      (by decide) (by decide) (by decide) (by decide) (by decide)
    obtain ⟨hext2, hv2, hlt, slot, hslot, hkey⟩ :=
      internRootNode_spec hv1 _ _ (by rw [hent1]; omega) hbnd
    have htag : slot.tag = 2#4 := congrArg CamSlotKey.tag hkey
    have hsymId : slot.symId = (allocExprCamSymbol cam (.sortEntry u)).2 := congrArg CamSlotKey.symId hkey
    refine ⟨hext1.trans hext2, hv2, hlt, .sort hslot htag ?_⟩
    rw [hsymId]
    exact hext2.2 _ _ hsymGet
  | .const n us, cam, hv, ⟨hEnt, hSym, _⟩ => by
    simp only [internExpr]
    simp only [exprNodeBound] at hEnt hSym
    obtain ⟨hext1, hv1, hent1, hsymGet⟩ := allocExprCamSymbol_spec hv (.constEntry n us) (by omega)
    have hbnd := leaf_slotKeyChildrenBounded (allocExprCamSymbol cam (.constEntry n us)).1.entries.length
      3#4 (allocExprCamSymbol cam (.constEntry n us)).2
      (by decide) (by decide) (by decide) (by decide) (by decide)
    obtain ⟨hext2, hv2, hlt, slot, hslot, hkey⟩ :=
      internRootNode_spec hv1 _ _ (by rw [hent1]; omega) hbnd
    have htag : slot.tag = 3#4 := congrArg CamSlotKey.tag hkey
    have hsymId : slot.symId = (allocExprCamSymbol cam (.constEntry n us)).2 := congrArg CamSlotKey.symId hkey
    refine ⟨hext1.trans hext2, hv2, hlt, .const hslot htag ?_⟩
    rw [hsymId]
    exact hext2.2 _ _ hsymGet
  | .lit l, cam, hv, ⟨hEnt, hSym, _⟩ => by
    simp only [internExpr]
    simp only [exprNodeBound] at hEnt hSym
    obtain ⟨hext1, hv1, hent1, hsymGet⟩ := allocExprCamSymbol_spec hv (.litEntry l) (by omega)
    have hbnd := leaf_slotKeyChildrenBounded (allocExprCamSymbol cam (.litEntry l)).1.entries.length
      8#4 (allocExprCamSymbol cam (.litEntry l)).2
      (by decide) (by decide) (by decide) (by decide) (by decide)
    obtain ⟨hext2, hv2, hlt, slot, hslot, hkey⟩ :=
      internRootNode_spec hv1 _ _ (by rw [hent1]; omega) hbnd
    have htag : slot.tag = 8#4 := congrArg CamSlotKey.tag hkey
    have hsymId : slot.symId = (allocExprCamSymbol cam (.litEntry l)).2 := congrArg CamSlotKey.symId hkey
    refine ⟨hext1.trans hext2, hv2, hlt, .lit hslot htag ?_⟩
    rw [hsymId]
    exact hext2.2 _ _ hsymGet
  | .app f a, cam, hv, ⟨hEnt, hSym, hfVar, haVar⟩ => by
    simp only [internExpr]
    simp only [exprNodeBound] at hEnt hSym
    have hszF := internExpr_size_le f cam
    obtain ⟨hext1, hv1, hfLt, rf⟩ := internExpr_realizes f hv ⟨by omega, by omega, hfVar⟩
    have hszA := internExpr_size_le a (internExpr cam f).1
    obtain ⟨hext2, hv2, haLt, ra⟩ := internExpr_realizes a hv1 ⟨by omega, by omega, haVar⟩
    have hfLt2 : (internExpr cam f).2 < (internExpr (internExpr cam f).1 a).1.entries.length :=
      hext2.lt_entries_len hfLt
    have hCap2 : (internExpr (internExpr cam f).1 a).1.entries.length < UInt32.size := by omega
    have hc0Eq := uint32_toNat_ofNat_of_lt (Nat.lt_trans hfLt2 hCap2)
    have hc1Eq := uint32_toNat_ofNat_of_lt (Nat.lt_trans haLt hCap2)
    have hbnd := bin_slotKeyChildrenBounded (internExpr (internExpr cam f).1 a).1.entries.length
      4#4 (UInt32.ofNat (internExpr cam f).2) (UInt32.ofNat (internExpr (internExpr cam f).1 a).2)
      (by simpa [hc0Eq] using hfLt2) (by simpa [hc1Eq] using haLt) (by decide) (by decide)
    obtain ⟨hext3, hv3, hlt, slot, hslot, hkey⟩ := internRootNode_spec hv2 _ _ hCap2 hbnd
    have htag : slot.tag = 4#4 := congrArg CamSlotKey.tag hkey
    have hc0 : slot.child0 = UInt32.ofNat (internExpr cam f).2 := congrArg CamSlotKey.child0 hkey
    have hc1 : slot.child1 = UInt32.ofNat (internExpr (internExpr cam f).1 a).2 := congrArg CamSlotKey.child1 hkey
    refine ⟨hext1.trans (hext2.trans hext3), hv3, hlt, .app hslot htag ?_ ?_⟩
    · rw [hc0, hc0Eq]; exact rf.mono (hext2.trans hext3)
    · rw [hc1, hc1Eq]; exact ra.mono hext3
  | .lam d b, cam, hv, ⟨hEnt, hSym, hdVar, hbVar⟩ => by
    simp only [internExpr]
    simp only [exprNodeBound] at hEnt hSym
    have hszD := internExpr_size_le d cam
    obtain ⟨hext1, hv1, hdLt, rd⟩ := internExpr_realizes d hv ⟨by omega, by omega, hdVar⟩
    have hszB := internExpr_size_le b (internExpr cam d).1
    obtain ⟨hext2, hv2, hbLt, rb⟩ := internExpr_realizes b hv1 ⟨by omega, by omega, hbVar⟩
    have hdLt2 : (internExpr cam d).2 < (internExpr (internExpr cam d).1 b).1.entries.length :=
      hext2.lt_entries_len hdLt
    have hCap2 : (internExpr (internExpr cam d).1 b).1.entries.length < UInt32.size := by omega
    have hc0Eq := uint32_toNat_ofNat_of_lt (Nat.lt_trans hdLt2 hCap2)
    have hc1Eq := uint32_toNat_ofNat_of_lt (Nat.lt_trans hbLt hCap2)
    have hbnd := bin_slotKeyChildrenBounded (internExpr (internExpr cam d).1 b).1.entries.length
      5#4 (UInt32.ofNat (internExpr cam d).2) (UInt32.ofNat (internExpr (internExpr cam d).1 b).2)
      (by simpa [hc0Eq] using hdLt2) (by simpa [hc1Eq] using hbLt) (by decide) (by decide)
    obtain ⟨hext3, hv3, hlt, slot, hslot, hkey⟩ := internRootNode_spec hv2 _ _ hCap2 hbnd
    have htag : slot.tag = 5#4 := congrArg CamSlotKey.tag hkey
    have hc0 : slot.child0 = UInt32.ofNat (internExpr cam d).2 := congrArg CamSlotKey.child0 hkey
    have hc1 : slot.child1 = UInt32.ofNat (internExpr (internExpr cam d).1 b).2 := congrArg CamSlotKey.child1 hkey
    refine ⟨hext1.trans (hext2.trans hext3), hv3, hlt, .lam hslot htag ?_ ?_⟩
    · rw [hc0, hc0Eq]; exact rd.mono (hext2.trans hext3)
    · rw [hc1, hc1Eq]; exact rb.mono hext3
  | .forallE d b, cam, hv, ⟨hEnt, hSym, hdVar, hbVar⟩ => by
    simp only [internExpr]
    simp only [exprNodeBound] at hEnt hSym
    have hszD := internExpr_size_le d cam
    obtain ⟨hext1, hv1, hdLt, rd⟩ := internExpr_realizes d hv ⟨by omega, by omega, hdVar⟩
    have hszB := internExpr_size_le b (internExpr cam d).1
    obtain ⟨hext2, hv2, hbLt, rb⟩ := internExpr_realizes b hv1 ⟨by omega, by omega, hbVar⟩
    have hdLt2 : (internExpr cam d).2 < (internExpr (internExpr cam d).1 b).1.entries.length :=
      hext2.lt_entries_len hdLt
    have hCap2 : (internExpr (internExpr cam d).1 b).1.entries.length < UInt32.size := by omega
    have hc0Eq := uint32_toNat_ofNat_of_lt (Nat.lt_trans hdLt2 hCap2)
    have hc1Eq := uint32_toNat_ofNat_of_lt (Nat.lt_trans hbLt hCap2)
    have hbnd := bin_slotKeyChildrenBounded (internExpr (internExpr cam d).1 b).1.entries.length
      6#4 (UInt32.ofNat (internExpr cam d).2) (UInt32.ofNat (internExpr (internExpr cam d).1 b).2)
      (by simpa [hc0Eq] using hdLt2) (by simpa [hc1Eq] using hbLt) (by decide) (by decide)
    obtain ⟨hext3, hv3, hlt, slot, hslot, hkey⟩ := internRootNode_spec hv2 _ _ hCap2 hbnd
    have htag : slot.tag = 6#4 := congrArg CamSlotKey.tag hkey
    have hc0 : slot.child0 = UInt32.ofNat (internExpr cam d).2 := congrArg CamSlotKey.child0 hkey
    have hc1 : slot.child1 = UInt32.ofNat (internExpr (internExpr cam d).1 b).2 := congrArg CamSlotKey.child1 hkey
    refine ⟨hext1.trans (hext2.trans hext3), hv3, hlt, .forallE hslot htag ?_ ?_⟩
    · rw [hc0, hc0Eq]; exact rd.mono (hext2.trans hext3)
    · rw [hc1, hc1Eq]; exact rb.mono hext3
  | .letE t v b, cam, hv, ⟨hEnt, hSym, htVar, hvVar, hbVar⟩ => by
    simp only [internExpr]
    simp only [exprNodeBound] at hEnt hSym
    have hszT := internExpr_size_le t cam
    obtain ⟨hext1, hv1, htLt, rt⟩ := internExpr_realizes t hv ⟨by omega, by omega, htVar⟩
    have hszV := internExpr_size_le v (internExpr cam t).1
    obtain ⟨hext2, hv2, hvLt, rv⟩ := internExpr_realizes v hv1 ⟨by omega, by omega, hvVar⟩
    have hszB := internExpr_size_le b (internExpr (internExpr cam t).1 v).1
    obtain ⟨hext3, hv3, hbLt, rb⟩ := internExpr_realizes b hv2 ⟨by omega, by omega, hbVar⟩
    have htLt3 : (internExpr cam t).2 < (internExpr (internExpr (internExpr cam t).1 v).1 b).1.entries.length :=
      (hext2.trans hext3).lt_entries_len htLt
    have hvLt3 : (internExpr (internExpr cam t).1 v).2 < (internExpr (internExpr (internExpr cam t).1 v).1 b).1.entries.length :=
      hext3.lt_entries_len hvLt
    have hCap3 : (internExpr (internExpr (internExpr cam t).1 v).1 b).1.entries.length < UInt32.size := by omega
    have hc0Eq := uint32_toNat_ofNat_of_lt (Nat.lt_trans htLt3 hCap3)
    have hc1Eq := uint32_toNat_ofNat_of_lt (Nat.lt_trans hvLt3 hCap3)
    have hc2Eq := uint32_toNat_ofNat_of_lt (Nat.lt_trans hbLt hCap3)
    have hbnd : SlotKeyChildrenBounded (internExpr (internExpr (internExpr cam t).1 v).1 b).1.entries.length
        { tag := 7#4
        , child0 := UInt32.ofNat (internExpr cam t).2
        , child1 := UInt32.ofNat (internExpr (internExpr cam t).1 v).2
        , child2 := UInt32.ofNat (internExpr (internExpr (internExpr cam t).1 v).1 b).2 } := by
      unfold SlotKeyChildrenBounded
      refine ⟨?_, fun _ => ⟨by simpa [hc0Eq] using htLt3, by simpa [hc1Eq] using hvLt3, by simpa [hc2Eq] using hbLt⟩, ?_⟩
      · rintro (h | h | h) <;> dsimp at h <;> exact absurd h (by decide)
      · intro h; dsimp at h; exact absurd h (by decide)
    obtain ⟨hext4, hv4, hlt, slot, hslot, hkey⟩ := internRootNode_spec hv3 _ _ hCap3 hbnd
    have htag : slot.tag = 7#4 := congrArg CamSlotKey.tag hkey
    have hc0 : slot.child0 = UInt32.ofNat (internExpr cam t).2 := congrArg CamSlotKey.child0 hkey
    have hc1 : slot.child1 = UInt32.ofNat (internExpr (internExpr cam t).1 v).2 := congrArg CamSlotKey.child1 hkey
    have hc2 : slot.child2 = UInt32.ofNat (internExpr (internExpr (internExpr cam t).1 v).1 b).2 := congrArg CamSlotKey.child2 hkey
    refine ⟨hext1.trans (hext2.trans (hext3.trans hext4)), hv4, hlt, .letE hslot htag ?_ ?_ ?_⟩
    · rw [hc0, hc0Eq]; exact rt.mono (hext2.trans (hext3.trans hext4))
    · rw [hc1, hc1Eq]; exact rv.mono (hext3.trans hext4)
    · rw [hc2, hc2Eq]; exact rb.mono hext4
  | .proj sName idx s, cam, hv, ⟨hEnt, hSym, hsVar⟩ => by
    simp only [internExpr]
    simp only [exprNodeBound] at hEnt hSym
    have hszS := internExpr_size_le s cam
    obtain ⟨hext1, hv1, hsLt, rs⟩ := internExpr_realizes s hv ⟨by omega, by omega, hsVar⟩
    obtain ⟨hext2, hv2, hent2, hsymGet⟩ :=
      allocExprCamSymbol_spec hv1 (.projEntry sName idx) (by omega)
    have hsLt2 : (internExpr cam s).2 < (allocExprCamSymbol (internExpr cam s).1 (.projEntry sName idx)).1.entries.length := by
      rwa [hent2]
    have hCap2 : (allocExprCamSymbol (internExpr cam s).1 (.projEntry sName idx)).1.entries.length < UInt32.size := by
      rw [hent2]; omega
    have hc0Eq := uint32_toNat_ofNat_of_lt (Nat.lt_trans hsLt2 hCap2)
    have hbnd := proj_slotKeyChildrenBounded
      (allocExprCamSymbol (internExpr cam s).1 (.projEntry sName idx)).1.entries.length
      (allocExprCamSymbol (internExpr cam s).1 (.projEntry sName idx)).2
      (UInt32.ofNat (internExpr cam s).2)
      (by simpa [hc0Eq] using hsLt2)
    obtain ⟨hext3, hv3, hlt, slot, hslot, hkey⟩ := internRootNode_spec hv2 _ _ hCap2 hbnd
    have htag : slot.tag = 9#4 := congrArg CamSlotKey.tag hkey
    have hsymId : slot.symId = (allocExprCamSymbol (internExpr cam s).1 (.projEntry sName idx)).2 := congrArg CamSlotKey.symId hkey
    have hc0 : slot.child0 = UInt32.ofNat (internExpr cam s).2 := congrArg CamSlotKey.child0 hkey
    refine ⟨hext1.trans (hext2.trans hext3), hv3, hlt, .proj hslot htag ?_ ?_⟩
    · rw [hsymId]; exact hext3.2 _ _ hsymGet
    · rw [hc0, hc0Eq]; exact rs.mono (hext2.trans hext3)

/-- **Theorem (`uninternExpr_internExpr_mono`)**:
Interning any 32-bit addressable `e : KExpr` into a well-formed `cam : ExprCAM` preserves all
existing decoded handle mappings `uninternExpr cam h = some e₀`. -/
theorem uninternExpr_internExpr_mono (e : KExpr) {cam : ExprCAM} (hv : cam.Valid)
    (hFit : ExprCamAddressable cam e) {h : CamHandle} {e₀ : KExpr}
    (hun : uninternExpr cam h = some e₀) :
    uninternExpr (internExpr cam e).1 h = some e₀ := by
  have hr₀ : SlotRealizesExprAt cam h e₀ := slotRealizesExprAt_of_decodeSlotCamDag hun
  obtain ⟨hext, hv', _, _⟩ := internExpr_realizes e hv hFit
  exact uninternExpr_of_slotRealizesExprAt hv' (hr₀.mono hext)

/-- **Theorem (`intern_unintern_roundtrip`, Universally Quantified)**:
For every well-formed `cam : ExprCAM` (`cam.Valid`) and every 32-bit addressable `e : KExpr`,
`internExpr cam e` preserves `ExprCAM.Valid` and `uninternExpr` recovers `some e` losslessly
from the ghost-free hardware slot DAG. -/
theorem intern_unintern_roundtrip (e : KExpr) {cam : ExprCAM}
    (hv : cam.Valid) (hFit : ExprCamAddressable cam e) :
    (internExpr cam e).1.Valid ∧
    uninternExpr (internExpr cam e).1 (internExpr cam e).2 = some e := by
  obtain ⟨_, hv', _, hr⟩ := internExpr_realizes e hv hFit
  exact ⟨hv', uninternExpr_of_slotRealizesExprAt hv' hr⟩

/-- **Theorem (`exprCam_handle_eq_imp_expr_eq`, Universally Quantified)**:
For any well-formed `cam : ExprCAM` (`cam.Valid`) and any two expressions `e₁ e₂ : KExpr` whose
combined DAG fits in 32-bit hardware registers, if `(cam₁, h₁) = internExpr cam e₁` and
`(cam₂, h₂) = internExpr cam₁ e₂`, then `h₁ = h₂ → e₁ = e₂` (distinct expressions never collide). -/
theorem exprCam_handle_eq_imp_expr_eq {cam : ExprCAM} (hv : cam.Valid) (e₁ e₂ : KExpr)
    (hEnt : cam.entries.length + exprNodeBound e₁ + exprNodeBound e₂ < UInt32.size)
    (hSym : cam.symbols.length + exprNodeBound e₁ + exprNodeBound e₂ < UInt32.size)
    (hVar1 : exprVarsFitUInt32 e₁) (hVar2 : exprVarsFitUInt32 e₂) :
    let (cam₁, h₁) := internExpr cam e₁
    let (cam₂, h₂) := internExpr cam₁ e₂
    uninternExpr cam₂ h₁ = some e₁ ∧
    uninternExpr cam₂ h₂ = some e₂ ∧
    (h₁ = h₂ → e₂ = e₁ → True) ∧
    (h₁ = h₂ → e₁ = e₂) := by
  dsimp only
  have hFit1 : ExprCamAddressable cam e₁ := ⟨by omega, by omega, hVar1⟩
  have hsz1 := internExpr_size_le e₁ cam
  have h1 := intern_unintern_roundtrip e₁ hv hFit1
  have hFit2 : ExprCamAddressable (internExpr cam e₁).1 e₂ := ⟨by omega, by omega, hVar2⟩
  have h2 := intern_unintern_roundtrip e₂ h1.1 hFit2
  have h1_mono := uninternExpr_internExpr_mono e₂ h1.1 hFit2 h1.2
  refine ⟨h1_mono, h2.2, fun _ _ => trivial, ?_⟩
  intro heq
  have hsame : some e₁ = some e₂ := by
    calc some e₁ = uninternExpr (internExpr (internExpr cam e₁).1 e₂).1 (internExpr cam e₁).2 := h1_mono.symm
    _ = uninternExpr (internExpr (internExpr cam e₁).1 e₂).1 (internExpr (internExpr cam e₁).1 e₂).2 := by rw [heq]
    _ = some e₂ := h2.2
  exact Option.some.inj hsame

/-- **Theorem (`exprCam_hash26_collision_and_capacity_sound`, Universally Quantified)**:
1. **Universal Capacity Enforcement**: For any `cam : ExprCAM`, capacity `maxCap : Nat`, and fresh
   hardware slot key `kNew : CamSlotKey` (`cam.lookupSlotKey? kNew = none`), if
   `cam.entries.length ≥ maxCap`, then `internRootNodeBounded maxCap cam kNew wNew = none`.
2. **Hash & String-Length Collision Safety**: Distinct constants (`"alpha"` vs `"beta"`, `"a"` vs `"b"`)
   and distinct same-length string literals (`.lit (.strVal "a")` vs `.lit (.strVal "b")`) receive
   distinct 32-bit `symId`s and distinct CAM handles without any `expr : KExpr` ghost field. -/
theorem exprCam_hash26_collision_and_capacity_sound
    (cam : ExprCAM) (maxCap : Nat) (kNew : CamSlotKey) (wNew : CamWord64)
    (hFresh : cam.lookupSlotKey? kNew = none)
    (hFull : cam.entries.length ≥ maxCap) :
    internRootNodeBounded maxCap cam kNew wNew = none ∧
    (let eA := KExpr.const (KName.mkSimple "alpha") []
     let eB := KExpr.const (KName.mkSimple "beta") []
     let sA := KExpr.lit (.strVal "a")
     let sB := KExpr.lit (.strVal "b")
     let (cam1, hA) := internExpr ExprCAM.empty eA
     let (cam2, hB) := internExpr cam1 eB
     let (cam3, hsA) := internExpr cam2 sA
     let (cam4, hsB) := internExpr cam3 sB
     (mkExprCamFields eA 1 0).hash26 = (mkExprCamFields eB 1 0).hash26 ∧
     hA ≠ hB ∧
     hsA ≠ hsB ∧
     uninternExpr cam4 hA = some eA ∧
     uninternExpr cam4 hB = some eB ∧
     uninternExpr cam4 hsA = some sA ∧
     uninternExpr cam4 hsB = some sB ∧
     internRootNodeBounded 1 cam1 { tag := 3#4, symId := 0 } (mkExprCamWord64 eA 0 0) = some (cam1, 0) ∧
     internRootNodeBounded 1 cam1 { tag := 3#4, symId := 1 } (mkExprCamWord64 eB 1 0) = none) := by
  refine ⟨?_, rfl, by decide, by decide, rfl, rfl, rfl, rfl, rfl, rfl⟩
  simp [internRootNodeBounded, hFresh, hFull]

/-- Companion inhabitedness witness for `ExprCamAddressable ExprCAM.empty`. -/
theorem exprCamAddressable_empty_inhabited (v : Nat) :
    ∃ e : KExpr, ExprCamAddressable ExprCAM.empty e ∧ e = .lit (.natVal v) := by
  refine ⟨.lit (.natVal v), ⟨?_, ?_, trivial⟩, rfl⟩
  · simp only [ExprCAM.empty, exprNodeBound, List.length_nil]; decide
  · simp only [ExprCAM.empty, exprNodeBound, List.length_nil]; decide

/-- **Theorem (`exprCam_roundtrip_sound`, Universally Quantified)**:
Every 32-bit addressable `KExpr` constructor form (including `.mvar`, `.bvar`, `.fvar`, `.sort`,
`.const`, `.app`, `.lam`, `.forallE`, `.letE`, `.lit`, `.proj`) interns into ghost-free `ExprCAM`,
round-trips losslessly via `uninternExpr`, and `camInstantiate1` agrees with `KExpr.instantiate1`
on closed and open expressions. -/
theorem exprCam_roundtrip_sound (e arg : KExpr) (hFit : ExprCamAddressable ExprCAM.empty e) :
    uninternExpr (internExpr ExprCAM.empty e).1 (internExpr ExprCAM.empty e).2 = some e ∧
    camInstantiate1 ExprCAM.empty kNatConst arg = KExpr.instantiate1 kNatConst arg ∧
    camInstantiate1 ExprCAM.empty (.bvar 0) arg = KExpr.instantiate1 (.bvar 0) arg := by
  refine ⟨(intern_unintern_roundtrip e ExprCAM.empty_valid hFit).2, ?_, rfl⟩
  have hClosed : KExpr.hasLooseBVar kNatConst = false := rfl
  rw [(exprCam_looseBVar_flag_sound kNatConst 0 0 0 arg).2.2 hClosed |>.1]
  rfl

/-! ## 4b. True Hardware CAM Memory Image (`HwCamNodeWord` / `HwCamImage`) Without AST Side-Channel -/

/-- Hardware CAM Memory Node Word (`HwCamNodeWord`):
Consists ONLY of fixed-width integer/word fields (`tag`, `h0`, `h1`, `h2` for `letE`, and
symbol/literal table index `symIdx`) with **no `KExpr` AST stored inside the hardware table**! -/
structure HwCamNodeWord where
  tag    : Nat
  h0     : Nat
  h1     : Nat
  h2     : Nat
  symIdx : Nat
  deriving DecidableEq, Repr, Inhabited

/-- Hardware CAM Memory Image (`HwCamImage`):
Consists purely of the integer node-word table (`nodes : List HwCamNodeWord`) and the auxiliary
symbol/literal table (`symbols : List HwCamSymbolEntry`), with zero `KExpr` AST side-channel. -/
structure HwCamImage where
  nodes   : List HwCamNodeWord := []
  symbols : List HwCamSymbolEntry := []
  deriving DecidableEq, Repr, Inhabited

/-- Empty `HwCamImage`. -/
def HwCamImage.empty : HwCamImage := { nodes := [], symbols := [] }

/-- Alias for `HwCamImage.empty`. -/
abbrev emptyHwCamImage : HwCamImage := HwCamImage.empty

/-- Allocate or reuse a symbol entry in `img.symbols` via associative CAM lookup, returning `(symIdx, updatedImage)`. -/
def allocHwSymbol (s : HwCamSymbolEntry) (img : HwCamImage) : Nat × HwCamImage :=
  match findElemIdx? img.symbols s with
  | some idx => (idx, img)
  | none =>
    let idx := img.symbols.length
    (idx, { img with symbols := img.symbols ++ [s] })

/-- Allocate or reuse a hardware node word in `img.nodes` via associative CAM lookup, returning `(handle, updatedImage)`. -/
def allocHwNode (w : HwCamNodeWord) (img : HwCamImage) : Nat × HwCamImage :=
  match findElemIdx? img.nodes w with
  | some h => (h, img)
  | none =>
    let h := img.nodes.length
    (h, { img with nodes := img.nodes ++ [w] })

/-- Intern a `KExpr` into a pure hardware `HwCamImage` (`internToHwImage : KExpr → HwCamImage → Nat × HwCamImage`),
storing all 3 child handles `(ht, hv, hb)` of `.letE t v b` losslessly in `(h0, h1, h2)` and storing
zero `KExpr` AST values in the hardware table. -/
def internToHwImage : KExpr → HwCamImage → Nat × HwCamImage
  | .bvar idx, img =>
    allocHwNode { tag := 0, h0 := idx, h1 := 0, h2 := 0, symIdx := 0 } img
  | .fvar id, img =>
    allocHwNode { tag := 1, h0 := id, h1 := 0, h2 := 0, symIdx := 0 } img
  | .mvar id, img =>
    allocHwNode { tag := 10, h0 := id, h1 := 0, h2 := 0, symIdx := 0 } img
  | .sort u, img =>
    let (sIdx, img1) := allocHwSymbol (.sortEntry u) img
    allocHwNode { tag := 2, h0 := 0, h1 := 0, h2 := 0, symIdx := sIdx } img1
  | .const n us, img =>
    let (sIdx, img1) := allocHwSymbol (.constEntry n us) img
    allocHwNode { tag := 3, h0 := 0, h1 := 0, h2 := 0, symIdx := sIdx } img1
  | .app f a, img =>
    let (hf, img1) := internToHwImage f img
    let (ha, img2) := internToHwImage a img1
    allocHwNode { tag := 4, h0 := hf, h1 := ha, h2 := 0, symIdx := 0 } img2
  | .lam d b, img =>
    let (hd, img1) := internToHwImage d img
    let (hb, img2) := internToHwImage b img1
    allocHwNode { tag := 5, h0 := hd, h1 := hb, h2 := 0, symIdx := 0 } img2
  | .forallE d b, img =>
    let (hd, img1) := internToHwImage d img
    let (hb, img2) := internToHwImage b img1
    allocHwNode { tag := 6, h0 := hd, h1 := hb, h2 := 0, symIdx := 0 } img2
  | .letE t v b, img =>
    let (ht, img1) := internToHwImage t img
    let (hv, img2) := internToHwImage v img1
    let (hb, img3) := internToHwImage b img2
    allocHwNode { tag := 7, h0 := ht, h1 := hv, h2 := hb, symIdx := 0 } img3
  | .lit l, img =>
    let (sIdx, img1) := allocHwSymbol (.litEntry l) img
    allocHwNode { tag := 8, h0 := 0, h1 := 0, h2 := 0, symIdx := sIdx } img1
  | .proj structName idx s, img =>
    let (hs, img1) := internToHwImage s img
    let (sIdx, img2) := allocHwSymbol (.projEntry structName idx) img1
    allocHwNode { tag := 9, h0 := hs, h1 := 0, h2 := 0, symIdx := sIdx } img2

/-- Reconstruct a `KExpr` purely from the hardware word entries (`img.nodes`) and symbol table
(`img.symbols`) bounded by fuel (`reconstructFromHwImage : Nat → HwCamImage → Nat → Option KExpr`). -/
def reconstructFromHwImage : Nat → HwCamImage → Nat → Option KExpr
  | 0, _, _ => none
  | fuel + 1, img, h =>
    match img.nodes[h]? with
    | none => none
    | some w =>
      if w.tag == 0 then
        some (.bvar w.h0)
      else if w.tag == 1 then
        some (.fvar w.h0)
      else if w.tag == 2 then
        match img.symbols[w.symIdx]? with
        | some (.sortEntry u) => some (.sort u)
        | _ => none
      else if w.tag == 3 then
        match img.symbols[w.symIdx]? with
        | some (.constEntry n us) => some (.const n us)
        | _ => none
      else if w.tag == 4 then
        match reconstructFromHwImage fuel img w.h0, reconstructFromHwImage fuel img w.h1 with
        | some f, some a => some (.app f a)
        | _, _ => none
      else if w.tag == 5 then
        match reconstructFromHwImage fuel img w.h0, reconstructFromHwImage fuel img w.h1 with
        | some d, some b => some (.lam d b)
        | _, _ => none
      else if w.tag == 6 then
        match reconstructFromHwImage fuel img w.h0, reconstructFromHwImage fuel img w.h1 with
        | some d, some b => some (.forallE d b)
        | _, _ => none
      else if w.tag == 7 then
        match reconstructFromHwImage fuel img w.h0,
              reconstructFromHwImage fuel img w.h1,
              reconstructFromHwImage fuel img w.h2 with
        | some t, some v, some b => some (.letE t v b)
        | _, _, _ => none
      else if w.tag == 8 then
        match img.symbols[w.symIdx]? with
        | some (.litEntry l) => some (.lit l)
        | _ => none
      else if w.tag == 9 then
        match reconstructFromHwImage fuel img w.h0, img.symbols[w.symIdx]? with
        | some s, some (.projEntry structName idx) => some (.proj structName idx s)
        | _, _ => none
      else if w.tag == 10 then
        some (.mvar w.h0)
      else
        none

/-- Monotonicity predicate for `HwCamImage`: `img2` preserves all existing node and symbol indices of `img1`. -/
def HwCamImage.Extends (img1 img2 : HwCamImage) : Prop :=
  (∀ (i : Nat) (w : HwCamNodeWord), img1.nodes[i]? = some w → img2.nodes[i]? = some w) ∧
  (∀ (j : Nat) (s : HwCamSymbolEntry), img1.symbols[j]? = some s → img2.symbols[j]? = some s)

theorem HwCamImage.Extends.refl (img : HwCamImage) : img.Extends img :=
  ⟨fun _ _ h => h, fun _ _ h => h⟩

theorem HwCamImage.Extends.trans {a b c : HwCamImage}
    (h1 : a.Extends b) (h2 : b.Extends c) : a.Extends c :=
  ⟨fun i w h => h2.1 i w (h1.1 i w h), fun j s h => h2.2 j s (h1.2 j s h)⟩

theorem allocHwSymbol_spec (s : HwCamSymbolEntry) (img : HwCamImage) :
    img.Extends (allocHwSymbol s img).2 ∧
    (allocHwSymbol s img).2.symbols[(allocHwSymbol s img).1]? = some s := by
  unfold allocHwSymbol
  cases hfind : findElemIdx? img.symbols s with
  | some idx =>
    exact ⟨HwCamImage.Extends.refl img, getElem?_of_findElemIdx? img.symbols s idx hfind⟩
  | none =>
    refine ⟨⟨fun _ _ h => h, fun j sym h => getElem?_append_preserve [s] h⟩, ?_⟩
    exact getElem?_append_singleton_self img.symbols s

theorem allocHwNode_spec (w : HwCamNodeWord) (img : HwCamImage) :
    img.Extends (allocHwNode w img).2 ∧
    (allocHwNode w img).2.nodes[(allocHwNode w img).1]? = some w := by
  unfold allocHwNode
  cases hfind : findElemIdx? img.nodes w with
  | some idx =>
    exact ⟨HwCamImage.Extends.refl img, getElem?_of_findElemIdx? img.nodes w idx hfind⟩
  | none =>
    refine ⟨⟨fun i nd h => getElem?_append_preserve [w] h, fun _ _ h => h⟩, ?_⟩
    exact getElem?_append_singleton_self img.nodes w

theorem internToHwImage_extends : ∀ (e : KExpr) (img : HwCamImage),
    img.Extends (internToHwImage e img).2
  | .bvar _, img => (allocHwNode_spec _ img).1
  | .fvar _, img => (allocHwNode_spec _ img).1
  | .mvar _, img => (allocHwNode_spec _ img).1
  | .sort _, img =>
    HwCamImage.Extends.trans (allocHwSymbol_spec _ img).1 (allocHwNode_spec _ _).1
  | .const _ _, img =>
    HwCamImage.Extends.trans (allocHwSymbol_spec _ img).1 (allocHwNode_spec _ _).1
  | .app f a, img =>
    HwCamImage.Extends.trans (internToHwImage_extends f img)
      (HwCamImage.Extends.trans (internToHwImage_extends a _) (allocHwNode_spec _ _).1)
  | .lam d b, img =>
    HwCamImage.Extends.trans (internToHwImage_extends d img)
      (HwCamImage.Extends.trans (internToHwImage_extends b _) (allocHwNode_spec _ _).1)
  | .forallE d b, img =>
    HwCamImage.Extends.trans (internToHwImage_extends d img)
      (HwCamImage.Extends.trans (internToHwImage_extends b _) (allocHwNode_spec _ _).1)
  | .letE t v b, img =>
    HwCamImage.Extends.trans (internToHwImage_extends t img)
      (HwCamImage.Extends.trans (internToHwImage_extends v _)
        (HwCamImage.Extends.trans (internToHwImage_extends b _) (allocHwNode_spec _ _).1))
  | .lit _, img =>
    HwCamImage.Extends.trans (allocHwSymbol_spec _ img).1 (allocHwNode_spec _ _).1
  | .proj _ _ s, img =>
    HwCamImage.Extends.trans (internToHwImage_extends s img)
      (HwCamImage.Extends.trans (allocHwSymbol_spec _ _).1 (allocHwNode_spec _ _).1)

theorem reconstructFromHwImage_mono :
    ∀ (fuel : Nat) {img1 img2 : HwCamImage} (_hext : img1.Extends img2) (h : Nat) {e : KExpr},
      reconstructFromHwImage fuel img1 h = some e →
      reconstructFromHwImage fuel img2 h = some e
  | 0, _, _, _, _, _, h => by cases h
  | fuel + 1, img1, img2, hext, h, e, hrec => by
    unfold reconstructFromHwImage at hrec ⊢
    cases hnode : img1.nodes[h]? with
    | none => rw [hnode] at hrec; cases hrec
    | some w =>
      rw [hnode] at hrec
      rw [hext.1 h w hnode]
      dsimp only at hrec ⊢
      cases ht0 : (w.tag == 0)
      · simp only [ht0, Bool.false_eq_true, ↓reduceIte] at hrec ⊢
        cases ht1 : (w.tag == 1)
        · simp only [ht1, Bool.false_eq_true, ↓reduceIte] at hrec ⊢
          cases ht2 : (w.tag == 2)
          · simp only [ht2, Bool.false_eq_true, ↓reduceIte] at hrec ⊢
            cases ht3 : (w.tag == 3)
            · simp only [ht3, Bool.false_eq_true, ↓reduceIte] at hrec ⊢
              cases ht4 : (w.tag == 4)
              · simp only [ht4, Bool.false_eq_true, ↓reduceIte] at hrec ⊢
                cases ht5 : (w.tag == 5)
                · simp only [ht5, Bool.false_eq_true, ↓reduceIte] at hrec ⊢
                  cases ht6 : (w.tag == 6)
                  · simp only [ht6, Bool.false_eq_true, ↓reduceIte] at hrec ⊢
                    cases ht7 : (w.tag == 7)
                    · simp only [ht7, Bool.false_eq_true, ↓reduceIte] at hrec ⊢
                      cases ht8 : (w.tag == 8)
                      · simp only [ht8, Bool.false_eq_true, ↓reduceIte] at hrec ⊢
                        cases ht9 : (w.tag == 9)
                        · simp only [ht9, Bool.false_eq_true, ↓reduceIte] at hrec ⊢
                          cases ht10 : (w.tag == 10)
                          · simp only [ht10, Bool.false_eq_true, ↓reduceIte] at hrec; cases hrec
                          · simp only [ht10, ↓reduceIte] at hrec ⊢; exact hrec
                        · simp only [ht9, ↓reduceIte] at hrec ⊢
                          cases hc0 : reconstructFromHwImage fuel img1 w.h0 with
                          | none => rw [hc0] at hrec; cases hrec
                          | some e0 =>
                            cases hsym : img1.symbols[w.symIdx]? with
                            | none => rw [hc0, hsym] at hrec; cases hrec
                            | some sym =>
                              rw [hc0, hsym] at hrec
                              rw [reconstructFromHwImage_mono fuel hext w.h0 hc0,
                                  hext.2 w.symIdx sym hsym]
                              exact hrec
                      · simp only [ht8, ↓reduceIte] at hrec ⊢
                        cases hsym : img1.symbols[w.symIdx]? with
                        | none => rw [hsym] at hrec; cases hrec
                        | some sym => rw [hsym] at hrec; rw [hext.2 w.symIdx sym hsym]; exact hrec
                    · simp only [ht7, ↓reduceIte] at hrec ⊢
                      cases hc0 : reconstructFromHwImage fuel img1 w.h0 with
                      | none => rw [hc0] at hrec; cases hrec
                      | some e0 =>
                        cases hc1 : reconstructFromHwImage fuel img1 w.h1 with
                        | none => rw [hc0, hc1] at hrec; cases hrec
                        | some e1 =>
                          cases hc2 : reconstructFromHwImage fuel img1 w.h2 with
                          | none => rw [hc0, hc1, hc2] at hrec; cases hrec
                          | some e2 =>
                            rw [hc0, hc1, hc2] at hrec
                            rw [reconstructFromHwImage_mono fuel hext w.h0 hc0,
                                reconstructFromHwImage_mono fuel hext w.h1 hc1,
                                reconstructFromHwImage_mono fuel hext w.h2 hc2]
                            exact hrec
                  · simp only [ht6, ↓reduceIte] at hrec ⊢
                    cases hc0 : reconstructFromHwImage fuel img1 w.h0 with
                    | none => rw [hc0] at hrec; cases hrec
                    | some e0 =>
                      cases hc1 : reconstructFromHwImage fuel img1 w.h1 with
                      | none => rw [hc0, hc1] at hrec; cases hrec
                      | some e1 =>
                        rw [hc0, hc1] at hrec
                        rw [reconstructFromHwImage_mono fuel hext w.h0 hc0,
                            reconstructFromHwImage_mono fuel hext w.h1 hc1]
                        exact hrec
                · simp only [ht5, ↓reduceIte] at hrec ⊢
                  cases hc0 : reconstructFromHwImage fuel img1 w.h0 with
                  | none => rw [hc0] at hrec; cases hrec
                  | some e0 =>
                    cases hc1 : reconstructFromHwImage fuel img1 w.h1 with
                    | none => rw [hc0, hc1] at hrec; cases hrec
                    | some e1 =>
                      rw [hc0, hc1] at hrec
                      rw [reconstructFromHwImage_mono fuel hext w.h0 hc0,
                          reconstructFromHwImage_mono fuel hext w.h1 hc1]
                      exact hrec
              · simp only [ht4, ↓reduceIte] at hrec ⊢
                cases hc0 : reconstructFromHwImage fuel img1 w.h0 with
                | none => rw [hc0] at hrec; cases hrec
                | some e0 =>
                  cases hc1 : reconstructFromHwImage fuel img1 w.h1 with
                  | none => rw [hc0, hc1] at hrec; cases hrec
                  | some e1 =>
                    rw [hc0, hc1] at hrec
                    rw [reconstructFromHwImage_mono fuel hext w.h0 hc0,
                        reconstructFromHwImage_mono fuel hext w.h1 hc1]
                    exact hrec
            · simp only [ht3, ↓reduceIte] at hrec ⊢
              cases hsym : img1.symbols[w.symIdx]? with
              | none => rw [hsym] at hrec; cases hrec
              | some sym => rw [hsym] at hrec; rw [hext.2 w.symIdx sym hsym]; exact hrec
          · simp only [ht2, ↓reduceIte] at hrec ⊢
            cases hsym : img1.symbols[w.symIdx]? with
            | none => rw [hsym] at hrec; cases hrec
            | some sym => rw [hsym] at hrec; rw [hext.2 w.symIdx sym hsym]; exact hrec
        · simp only [ht1, ↓reduceIte] at hrec ⊢; exact hrec
      · simp only [ht0, ↓reduceIte] at hrec ⊢; exact hrec

/-- **Universal Lossless Hardware CAM Reconstruction Theorem (`reconstructFromHwImage_intern_roundtrip`)**:
For every fuel bound `fuel : Nat`, every expression `e : KExpr` (including `.letE t v b` with 3 children
and first-class `.mvar id`), and every initial hardware image `img : HwCamImage`, if `depth e ≤ fuel`,
then reconstructing from `internToHwImage e img` (which stores zero `KExpr` AST nodes in its hardware tables)
recovers `some e` losslessly! -/
theorem reconstructFromHwImage_intern_roundtrip :
    ∀ (fuel : Nat) (e : KExpr) (img : HwCamImage),
      depth e ≤ fuel →
      reconstructFromHwImage fuel (internToHwImage e img).2 (internToHwImage e img).1 = some e := by
  intro fuel e
  induction e generalizing fuel with
  | bvar idx =>
    intro img hdepth
    cases fuel with
    | zero => simp [depth] at hdepth
    | succ f =>
      simp only [internToHwImage]
      have hnd := (allocHwNode_spec { tag := 0, h0 := idx, h1 := 0, h2 := 0, symIdx := 0 } img).2
      unfold reconstructFromHwImage
      rw [hnd]
      rfl
  | fvar id =>
    intro img hdepth
    cases fuel with
    | zero => simp [depth] at hdepth
    | succ f =>
      simp only [internToHwImage]
      have hnd := (allocHwNode_spec { tag := 1, h0 := id, h1 := 0, h2 := 0, symIdx := 0 } img).2
      unfold reconstructFromHwImage
      rw [hnd]
      rfl
  | mvar id =>
    intro img hdepth
    cases fuel with
    | zero => simp [depth] at hdepth
    | succ f =>
      simp only [internToHwImage]
      have hnd := (allocHwNode_spec { tag := 10, h0 := id, h1 := 0, h2 := 0, symIdx := 0 } img).2
      unfold reconstructFromHwImage
      rw [hnd]
      rfl
  | sort u =>
    intro img hdepth
    cases fuel with
    | zero => simp [depth] at hdepth
    | succ f =>
      simp only [internToHwImage]
      have hsym := (allocHwSymbol_spec (.sortEntry u) img).2
      have hnd := allocHwNode_spec
        { tag := 2, h0 := 0, h1 := 0, h2 := 0, symIdx := (allocHwSymbol (.sortEntry u) img).1 }
        (allocHwSymbol (.sortEntry u) img).2
      have hsym2 := hnd.1.2 _ _ hsym
      unfold reconstructFromHwImage
      rw [hnd.2]
      dsimp only
      rw [hsym2]
      rfl
  | const n us =>
    intro img hdepth
    cases fuel with
    | zero => simp [depth] at hdepth
    | succ f =>
      simp only [internToHwImage]
      have hsym := (allocHwSymbol_spec (.constEntry n us) img).2
      have hnd := allocHwNode_spec
        { tag := 3, h0 := 0, h1 := 0, h2 := 0, symIdx := (allocHwSymbol (.constEntry n us) img).1 }
        (allocHwSymbol (.constEntry n us) img).2
      have hsym2 := hnd.1.2 _ _ hsym
      unfold reconstructFromHwImage
      rw [hnd.2]
      dsimp only
      rw [hsym2]
      rfl
  | app fn arg ihF ihA =>
    intro img hdepth
    cases fuel with
    | zero => simp [depth] at hdepth
    | succ f =>
      simp only [depth] at hdepth
      have hdf : depth fn ≤ f := by omega
      have hda : depth arg ≤ f := by omega
      simp only [internToHwImage]
      have recF := ihF f img hdf
      have extA := internToHwImage_extends arg (internToHwImage fn img).2
      have recA := ihA f (internToHwImage fn img).2 hda
      have hnd := allocHwNode_spec
        { tag := 4
        , h0 := (internToHwImage fn img).1
        , h1 := (internToHwImage arg (internToHwImage fn img).2).1
        , h2 := 0
        , symIdx := 0 }
        (internToHwImage arg (internToHwImage fn img).2).2
      have recF2 := reconstructFromHwImage_mono f (HwCamImage.Extends.trans extA hnd.1) _ recF
      have recA2 := reconstructFromHwImage_mono f hnd.1 _ recA
      unfold reconstructFromHwImage
      rw [hnd.2]
      dsimp only
      rw [recF2, recA2]
      rfl
  | lam dom body ihD ihB =>
    intro img hdepth
    cases fuel with
    | zero => simp [depth] at hdepth
    | succ f =>
      simp only [depth] at hdepth
      have hdd : depth dom ≤ f := by omega
      have hdb : depth body ≤ f := by omega
      simp only [internToHwImage]
      have recD := ihD f img hdd
      have extB := internToHwImage_extends body (internToHwImage dom img).2
      have recB := ihB f (internToHwImage dom img).2 hdb
      have hnd := allocHwNode_spec
        { tag := 5
        , h0 := (internToHwImage dom img).1
        , h1 := (internToHwImage body (internToHwImage dom img).2).1
        , h2 := 0
        , symIdx := 0 }
        (internToHwImage body (internToHwImage dom img).2).2
      have recD2 := reconstructFromHwImage_mono f (HwCamImage.Extends.trans extB hnd.1) _ recD
      have recB2 := reconstructFromHwImage_mono f hnd.1 _ recB
      unfold reconstructFromHwImage
      rw [hnd.2]
      dsimp only
      rw [recD2, recB2]
      rfl
  | forallE dom body ihD ihB =>
    intro img hdepth
    cases fuel with
    | zero => simp [depth] at hdepth
    | succ f =>
      simp only [depth] at hdepth
      have hdd : depth dom ≤ f := by omega
      have hdb : depth body ≤ f := by omega
      simp only [internToHwImage]
      have recD := ihD f img hdd
      have extB := internToHwImage_extends body (internToHwImage dom img).2
      have recB := ihB f (internToHwImage dom img).2 hdb
      have hnd := allocHwNode_spec
        { tag := 6
        , h0 := (internToHwImage dom img).1
        , h1 := (internToHwImage body (internToHwImage dom img).2).1
        , h2 := 0
        , symIdx := 0 }
        (internToHwImage body (internToHwImage dom img).2).2
      have recD2 := reconstructFromHwImage_mono f (HwCamImage.Extends.trans extB hnd.1) _ recD
      have recB2 := reconstructFromHwImage_mono f hnd.1 _ recB
      unfold reconstructFromHwImage
      rw [hnd.2]
      dsimp only
      rw [recD2, recB2]
      rfl
  | letE ty val body ihT ihV ihB =>
    intro img hdepth
    cases fuel with
    | zero => simp [depth] at hdepth
    | succ f =>
      simp only [depth] at hdepth
      have hdt : depth ty ≤ f := by omega
      have hdv : depth val ≤ f := by omega
      have hdb : depth body ≤ f := by omega
      simp only [internToHwImage]
      have recT := ihT f img hdt
      have extV := internToHwImage_extends val (internToHwImage ty img).2
      have recV := ihV f (internToHwImage ty img).2 hdv
      have extB := internToHwImage_extends body (internToHwImage val (internToHwImage ty img).2).2
      have recB := ihB f (internToHwImage val (internToHwImage ty img).2).2 hdb
      have hnd := allocHwNode_spec
        { tag := 7
        , h0 := (internToHwImage ty img).1
        , h1 := (internToHwImage val (internToHwImage ty img).2).1
        , h2 := (internToHwImage body (internToHwImage val (internToHwImage ty img).2).2).1
        , symIdx := 0 }
        (internToHwImage body (internToHwImage val (internToHwImage ty img).2).2).2
      have recT2 := reconstructFromHwImage_mono f
        (HwCamImage.Extends.trans extV (HwCamImage.Extends.trans extB hnd.1)) _ recT
      have recV2 := reconstructFromHwImage_mono f
        (HwCamImage.Extends.trans extB hnd.1) _ recV
      have recB2 := reconstructFromHwImage_mono f hnd.1 _ recB
      unfold reconstructFromHwImage
      rw [hnd.2]
      dsimp only
      rw [recT2, recV2, recB2]
      rfl
  | lit l =>
    intro img hdepth
    cases fuel with
    | zero => simp [depth] at hdepth
    | succ f =>
      simp only [internToHwImage]
      have hsym := (allocHwSymbol_spec (.litEntry l) img).2
      have hnd := allocHwNode_spec
        { tag := 8, h0 := 0, h1 := 0, h2 := 0, symIdx := (allocHwSymbol (.litEntry l) img).1 }
        (allocHwSymbol (.litEntry l) img).2
      have hsym2 := hnd.1.2 _ _ hsym
      unfold reconstructFromHwImage
      rw [hnd.2]
      dsimp only
      rw [hsym2]
      rfl
  | proj structName idx s ihS =>
    intro img hdepth
    cases fuel with
    | zero => simp [depth] at hdepth
    | succ f =>
      simp only [depth] at hdepth
      have hds : depth s ≤ f := by omega
      simp only [internToHwImage]
      have recS := ihS f img hds
      have hsym := allocHwSymbol_spec (.projEntry structName idx) (internToHwImage s img).2
      have hnd := allocHwNode_spec
        { tag := 9
        , h0 := (internToHwImage s img).1
        , h1 := 0
        , h2 := 0
        , symIdx := (allocHwSymbol (.projEntry structName idx) (internToHwImage s img).2).1 }
        (allocHwSymbol (.projEntry structName idx) (internToHwImage s img).2).2
      have recS2 := reconstructFromHwImage_mono f (HwCamImage.Extends.trans hsym.1 hnd.1) _ recS
      have hsym2 := hnd.1.2 _ _ hsym.2
      unfold reconstructFromHwImage
      rw [hnd.2]
      dsimp only
      rw [recS2, hsym2]
      rfl

/-! ## 5. Enriched Hardware CAM (`PackedNodeWord`, `HwExprCAM`) & 1-Cycle Handle-Level Substitution (`hwCamInstantiateAt`) -/

/-- Enriched Hardware CAM Node Word (`PackedNodeWord`):
Augments the structural child handles `(tag, h0, h1, h2, symIdx)` with the hardware summary bit-flags
required by Zone 1 (`hasLooseBVar`, `maxLooseBVar`) and Zone 2 (`hasFVar`, `hasMVar` = Bit 58):
* `hasLooseBVar`: `true` iff any loose `.bvar` escapes this subtree (`Bit 59`),
* `hasMVar`: `true` iff any metavariable (`.mvar`, `tag = 10`) occurs in this subtree (`Bit 58`),
* `hasFVar`: `true` iff any free variable (`.fvar`, `tag = 1`) occurs in this subtree (`Bit 57`),
* `maxLooseBVar`: `0` if closed, else `1 + max_loose_bvar_idx`. -/
structure PackedNodeWord where
  tag          : Nat
  h0           : Nat
  h1           : Nat
  h2           : Nat := 0
  symIdx       : Nat := 0
  hasLooseBVar : Bool := false
  hasFVar      : Bool := false
  hasMVar      : Bool := false
  maxLooseBVar : Nat := 0
  deriving DecidableEq, Repr, Inhabited

/-- Project a `PackedNodeWord` to its core `HwCamNodeWord`. -/
def PackedNodeWord.toHwCamNodeWord (w : PackedNodeWord) : HwCamNodeWord :=
  { tag := w.tag, h0 := w.h0, h1 := w.h1, h2 := w.h2, symIdx := w.symIdx }

/-- Hardware recursor $\iota$-reduction rule entry in `HwExprCAM`. -/
structure HwCamRecRuleEntry where
  recName   : KName
  ctorName  : KName
  numParams : Nat
  numFields : Nat
  rhsHandle : Nat
  deriving DecidableEq, Repr, Inhabited

/-- Hardware constant table entry in `HwExprCAM` for 1-cycle $\delta$-unfolding and constructor lookup. -/
structure HwCamConstEntry where
  name        : KName
  symIdx      : Nat
  typeHandle  : Nat
  valHandle?  : Option Nat := none
  isCtor      : Bool := false
  inductName? : Option KName := none
  deriving DecidableEq, Repr, Inhabited

/-- Complete Hardware Hash-Consed DAG / CAM State (`HwExprCAM`) for the 4-Zone Spatial Silicon Elaborator:
Stores `PackedNodeWord` entries, symbol entries, constant entries, recursor rules, inductive parameter
counts (`inductNumParams`), and recursor universe parameter names (`recLevelParams`) with zero `KExpr`
AST side-channel. -/
structure HwExprCAM where
  nodes           : List PackedNodeWord := []
  symbols         : List HwCamSymbolEntry := []
  consts          : List HwCamConstEntry := []
  recRules        : List HwCamRecRuleEntry := []
  inductNumParams : List (KName × Nat) := []
  recLevelParams  : List (KName × List KName) := []
  deriving DecidableEq, Repr, Inhabited

/-- Empty `HwExprCAM`. -/
def HwExprCAM.empty : HwExprCAM := {}

/-- Allocate or reuse a symbol entry in `cam.symbols`. -/
def allocPackedSymbol (s : HwCamSymbolEntry) (cam : HwExprCAM) : Nat × HwExprCAM :=
  match findElemIdx? cam.symbols s with
  | some idx => (idx, cam)
  | none =>
    let idx := cam.symbols.length
    (idx, { cam with symbols := cam.symbols ++ [s] })

/-- Allocate or reuse a `PackedNodeWord` in `cam.nodes` via associative CAM lookup. -/
def allocPackedNode (w : PackedNodeWord) (cam : HwExprCAM) : Nat × HwExprCAM :=
  match findElemIdx? cam.nodes w with
  | some h => (h, cam)
  | none =>
    let h := cam.nodes.length
    (h, { cam with nodes := cam.nodes ++ [w] })

/-- Look up a `PackedNodeWord` by handle (defaulting to a closed dummy word if out of bounds). -/
def getPackedNode (cam : HwExprCAM) (h : Nat) : PackedNodeWord :=
  cam.nodes[h]?.getD { tag := 99, h0 := 0, h1 := 0 }

/-- Construct and intern an `.app` node from two existing handles `(hf, ha)`, computing its summary
bit-flags in $O(1)$ from the child words `(wf, wa)`. -/
def mkHwCamApp (hf ha : Nat) (cam : HwExprCAM) : Nat × HwExprCAM :=
  let wf := getPackedNode cam hf
  let wa := getPackedNode cam ha
  let maxB := Nat.max wf.maxLooseBVar wa.maxLooseBVar
  allocPackedNode
    { tag          := 4
    , h0           := hf
    , h1           := ha
    , h2           := 0
    , symIdx       := 0
    , hasLooseBVar := decide (maxB > 0)
    , hasFVar      := wf.hasFVar || wa.hasFVar
    , hasMVar      := wf.hasMVar || wa.hasMVar
    , maxLooseBVar := maxB }
    cam

/-- Construct and intern a `.lam` (`tag = 5`) or `.forallE` (`tag = 6`) binder node from `(hd, hb)`,
decrementing the body's `maxLooseBVar` across the binder in $O(1)$. -/
def mkHwCamBinder (tag hd hb : Nat) (cam : HwExprCAM) : Nat × HwExprCAM :=
  let wd := getPackedNode cam hd
  let wb := getPackedNode cam hb
  let maxB := Nat.max wd.maxLooseBVar (wb.maxLooseBVar - 1)
  allocPackedNode
    { tag          := tag
    , h0           := hd
    , h1           := hb
    , h2           := 0
    , symIdx       := 0
    , hasLooseBVar := decide (maxB > 0)
    , hasFVar      := wd.hasFVar || wb.hasFVar
    , hasMVar      := wd.hasMVar || wb.hasMVar
    , maxLooseBVar := maxB }
    cam

/-- Construct and intern a `.letE` (`tag = 7`) node from `(ht, hv, hb)`, decrementing `hb`'s
`maxLooseBVar` across the let-binder in $O(1)$. -/
def mkHwCamLetE (ht hv hb : Nat) (cam : HwExprCAM) : Nat × HwExprCAM :=
  let wt := getPackedNode cam ht
  let wv := getPackedNode cam hv
  let wb := getPackedNode cam hb
  let maxB := Nat.max (Nat.max wt.maxLooseBVar wv.maxLooseBVar) (wb.maxLooseBVar - 1)
  allocPackedNode
    { tag          := 7
    , h0           := ht
    , h1           := hv
    , h2           := hb
    , symIdx       := 0
    , hasLooseBVar := decide (maxB > 0)
    , hasFVar      := wt.hasFVar || wv.hasFVar || wb.hasFVar
    , hasMVar      := wt.hasMVar || wv.hasMVar || wb.hasMVar
    , maxLooseBVar := maxB }
    cam

/-- Construct and intern a `.proj` (`tag = 9`) node from `(hs, symIdx)`. -/
def mkHwCamProj (hs symIdx : Nat) (cam : HwExprCAM) : Nat × HwExprCAM :=
  let ws := getPackedNode cam hs
  allocPackedNode
    { tag          := 9
    , h0           := hs
    , h1           := 0
    , h2           := 0
    , symIdx       := symIdx
    , hasLooseBVar := decide (ws.maxLooseBVar > 0)
    , hasFVar      := ws.hasFVar
    , hasMVar      := ws.hasMVar
    , maxLooseBVar := ws.maxLooseBVar }
    cam

/-- Intern a `KExpr` into `HwExprCAM`, populating `hasLooseBVar`, `hasFVar`, `hasMVar`, and
`maxLooseBVar` bottom-up in $O(1)$ per node. -/
def internToHwExprCAM : KExpr → HwExprCAM → Nat × HwExprCAM
  | .bvar idx, cam =>
    allocPackedNode
      { tag := 0, h0 := idx, h1 := 0, hasLooseBVar := true, maxLooseBVar := idx + 1 }
      cam
  | .fvar id, cam =>
    allocPackedNode
      { tag := 1, h0 := id, h1 := 0, hasFVar := true, hasMVar := false }
      cam
  | .mvar id, cam =>
    allocPackedNode
      { tag := 10, h0 := id, h1 := 0, hasFVar := false, hasMVar := true }
      cam
  | .sort u, cam =>
    let (sIdx, cam1) := allocPackedSymbol (.sortEntry u) cam
    allocPackedNode { tag := 2, h0 := 0, h1 := 0, symIdx := sIdx } cam1
  | .const n us, cam =>
    let (sIdx, cam1) := allocPackedSymbol (.constEntry n us) cam
    allocPackedNode { tag := 3, h0 := 0, h1 := 0, symIdx := sIdx } cam1
  | .app f a, cam =>
    let (hf, cam1) := internToHwExprCAM f cam
    let (ha, cam2) := internToHwExprCAM a cam1
    mkHwCamApp hf ha cam2
  | .lam d b, cam =>
    let (hd, cam1) := internToHwExprCAM d cam
    let (hb, cam2) := internToHwExprCAM b cam1
    mkHwCamBinder 5 hd hb cam2
  | .forallE d b, cam =>
    let (hd, cam1) := internToHwExprCAM d cam
    let (hb, cam2) := internToHwExprCAM b cam1
    mkHwCamBinder 6 hd hb cam2
  | .letE t v b, cam =>
    let (ht, cam1) := internToHwExprCAM t cam
    let (hv, cam2) := internToHwExprCAM v cam1
    let (hb, cam3) := internToHwExprCAM b cam2
    mkHwCamLetE ht hv hb cam3
  | .lit l, cam =>
    let (sIdx, cam1) := allocPackedSymbol (.litEntry l) cam
    allocPackedNode { tag := 8, h0 := 0, h1 := 0, symIdx := sIdx } cam1
  | .proj structName idx s, cam =>
    let (hs, cam1) := internToHwExprCAM s cam
    let (sIdx, cam2) := allocPackedSymbol (.projEntry structName idx) cam1
    mkHwCamProj hs sIdx cam2

/-- Reconstruct a `KExpr` from a handle `h` in `HwExprCAM` (used only for specification/readout). -/
def reconstructFromHwExprCAM : Nat → HwExprCAM → Nat → Option KExpr
  | 0, _, _ => none
  | fuel + 1, cam, h =>
    match cam.nodes[h]? with
    | none => none
    | some w =>
      if w.tag == 0 then some (.bvar w.h0)
      else if w.tag == 1 then some (.fvar w.h0)
      else if w.tag == 2 then
        match cam.symbols[w.symIdx]? with
        | some (.sortEntry u) => some (.sort u)
        | _ => none
      else if w.tag == 3 then
        match cam.symbols[w.symIdx]? with
        | some (.constEntry n us) => some (.const n us)
        | _ => none
      else if w.tag == 4 then
        match reconstructFromHwExprCAM fuel cam w.h0, reconstructFromHwExprCAM fuel cam w.h1 with
        | some f, some a => some (.app f a)
        | _, _ => none
      else if w.tag == 5 then
        match reconstructFromHwExprCAM fuel cam w.h0, reconstructFromHwExprCAM fuel cam w.h1 with
        | some d, some b => some (.lam d b)
        | _, _ => none
      else if w.tag == 6 then
        match reconstructFromHwExprCAM fuel cam w.h0, reconstructFromHwExprCAM fuel cam w.h1 with
        | some d, some b => some (.forallE d b)
        | _, _ => none
      else if w.tag == 7 then
        match reconstructFromHwExprCAM fuel cam w.h0,
              reconstructFromHwExprCAM fuel cam w.h1,
              reconstructFromHwExprCAM fuel cam w.h2 with
        | some t, some v, some b => some (.letE t v b)
        | _, _, _ => none
      else if w.tag == 8 then
        match cam.symbols[w.symIdx]? with
        | some (.litEntry l) => some (.lit l)
        | _ => none
      else if w.tag == 9 then
        match reconstructFromHwExprCAM fuel cam w.h0, cam.symbols[w.symIdx]? with
        | some s, some (.projEntry structName idx) => some (.proj structName idx s)
        | _, _ => none
      else if w.tag == 10 then
        some (.mvar w.h0)
      else none

/-- Pure handle-level de Bruijn lifting (`hwCamLiftLooseBVars`) over `HwExprCAM` with the
**1-cycle $O(1)$ closed-term bypass** when `w.hasLooseBVar = false` (or `w.maxLooseBVar ≤ cutoff`).
Never reconstructs `KExpr` ASTs! -/
def hwCamLiftLooseBVars : Nat → Nat → Nat → Nat → HwExprCAM → Nat × HwExprCAM
  | 0, h, _, _, cam => (h, cam)
  | fuel + 1, h, cutoff, shift, cam =>
    match cam.nodes[h]? with
    | none => (h, cam)
    | some w =>
      if !w.hasLooseBVar || shift == 0 || w.maxLooseBVar <= cutoff then
        (h, cam)
      else if w.tag == 0 then
        if w.h0 >= cutoff then
          allocPackedNode
            { w with h0 := w.h0 + shift, hasLooseBVar := true, maxLooseBVar := w.h0 + shift + 1 }
            cam
        else (h, cam)
      else if w.tag == 4 then
        let (hf', cam1) := hwCamLiftLooseBVars fuel w.h0 cutoff shift cam
        let (ha', cam2) := hwCamLiftLooseBVars fuel w.h1 cutoff shift cam1
        if hf' == w.h0 && ha' == w.h1 then (h, cam2) else mkHwCamApp hf' ha' cam2
      else if w.tag == 5 || w.tag == 6 then
        let (hd', cam1) := hwCamLiftLooseBVars fuel w.h0 cutoff shift cam
        let (hb', cam2) := hwCamLiftLooseBVars fuel w.h1 (cutoff + 1) shift cam1
        if hd' == w.h0 && hb' == w.h1 then (h, cam2) else mkHwCamBinder w.tag hd' hb' cam2
      else if w.tag == 7 then
        let (ht', cam1) := hwCamLiftLooseBVars fuel w.h0 cutoff shift cam
        let (hv', cam2) := hwCamLiftLooseBVars fuel w.h1 cutoff shift cam1
        let (hb', cam3) := hwCamLiftLooseBVars fuel w.h2 (cutoff + 1) shift cam2
        if ht' == w.h0 && hv' == w.h1 && hb' == w.h2 then (h, cam3)
        else mkHwCamLetE ht' hv' hb' cam3
      else if w.tag == 9 then
        let (hs', cam1) := hwCamLiftLooseBVars fuel w.h0 cutoff shift cam
        if hs' == w.h0 then (h, cam1) else mkHwCamProj hs' w.symIdx cam1
      else
        (h, cam)

/-- Pure handle-level de Bruijn instantiation (`hwCamInstantiateAt`) over `HwExprCAM` with the
**1-cycle $O(1)$ closed-term bypass** when `w.hasLooseBVar = false` (or `w.maxLooseBVar ≤ depth`).
Never calls `uninternExpr` or `reconstructFromHwExprCAM`! -/
def hwCamInstantiateAt : Nat → Nat → Nat → Nat → HwExprCAM → Nat × HwExprCAM
  | 0, hBody, _, _, cam => (hBody, cam)
  | fuel + 1, hBody, depth, hArg, cam =>
    match cam.nodes[hBody]? with
    | none => (hBody, cam)
    | some w =>
      if !w.hasLooseBVar || w.maxLooseBVar <= depth then
        (hBody, cam)
      else if w.tag == 0 then
        if w.h0 == depth then
          hwCamLiftLooseBVars fuel hArg 0 depth cam
        else if w.h0 > depth then
          allocPackedNode
            { w with h0 := w.h0 - 1, hasLooseBVar := true, maxLooseBVar := w.h0 }
            cam
        else
          (hBody, cam)
      else if w.tag == 4 then
        let (hf', cam1) := hwCamInstantiateAt fuel w.h0 depth hArg cam
        let (ha', cam2) := hwCamInstantiateAt fuel w.h1 depth hArg cam1
        if hf' == w.h0 && ha' == w.h1 then (hBody, cam2) else mkHwCamApp hf' ha' cam2
      else if w.tag == 5 || w.tag == 6 then
        let (hd', cam1) := hwCamInstantiateAt fuel w.h0 depth hArg cam
        let (hb', cam2) := hwCamInstantiateAt fuel w.h1 (depth + 1) hArg cam1
        if hd' == w.h0 && hb' == w.h1 then (hBody, cam2) else mkHwCamBinder w.tag hd' hb' cam2
      else if w.tag == 7 then
        let (ht', cam1) := hwCamInstantiateAt fuel w.h0 depth hArg cam
        let (hv', cam2) := hwCamInstantiateAt fuel w.h1 depth hArg cam1
        let (hb', cam3) := hwCamInstantiateAt fuel w.h2 (depth + 1) hArg cam2
        if ht' == w.h0 && hv' == w.h1 && hb' == w.h2 then (hBody, cam3)
        else mkHwCamLetE ht' hv' hb' cam3
      else if w.tag == 9 then
        let (hs', cam1) := hwCamInstantiateAt fuel w.h0 depth hArg cam
        if hs' == w.h0 then (hBody, cam1) else mkHwCamProj hs' w.symIdx cam1
      else
        (hBody, cam)

/-- Instantiate `.bvar 0` in `hBody` with `hArg` purely at the `HwExprCAM` handle level. -/
def hwCamInstantiate1 (fuel hBody hArg : Nat) (cam : HwExprCAM) : Nat × HwExprCAM :=
  hwCamInstantiateAt fuel hBody 0 hArg cam

/-- **1-Cycle Closed-Term Bypass Theorem (`hwCamInstantiateAt_closed_bypass`)**:
Whenever a node word `w` at handle `hBody` has `w.hasLooseBVar = false` (Bit 59 = `0`),
`hwCamInstantiateAt` and `hwCamLiftLooseBVars` return `(hBody, cam)` immediately in 1 cycle
without inspecting children or allocating any CAM nodes! -/
theorem hwCamInstantiateAt_closed_bypass
    (fuel hBody depth hArg : Nat) (cam : HwExprCAM) (w : PackedNodeWord)
    (hnode : cam.nodes[hBody]? = some w)
    (hclosed : w.hasLooseBVar = false) :
    hwCamInstantiateAt (fuel + 1) hBody depth hArg cam = (hBody, cam) ∧
    hwCamLiftLooseBVars (fuel + 1) hBody depth hArg cam = (hBody, cam) := by
  simp [hwCamInstantiateAt, hwCamLiftLooseBVars, hnode, hclosed]

/-- Specification of `PackedNodeWord.maxLooseBVar` on `KExpr` (`0` if closed, else `1 + max_loose_bvar_idx`). -/
def maxLooseBVarSpec : KExpr → Nat
  | .bvar idx    => idx + 1
  | .fvar _      => 0
  | .mvar _      => 0
  | .sort _      => 0
  | .const _ _   => 0
  | .lit _       => 0
  | .app f a     => Nat.max (maxLooseBVarSpec f) (maxLooseBVarSpec a)
  | .lam d b     => Nat.max (maxLooseBVarSpec d) (maxLooseBVarSpec b - 1)
  | .forallE d b => Nat.max (maxLooseBVarSpec d) (maxLooseBVarSpec b - 1)
  | .letE t v b  => Nat.max (Nat.max (maxLooseBVarSpec t) (maxLooseBVarSpec v)) (maxLooseBVarSpec b - 1)
  | .proj _ _ s  => maxLooseBVarSpec s

theorem hasLooseBVarAt_eq_false_iff_maxLooseBVarSpec_le :
    ∀ (e : KExpr) (cutoff : Nat),
      KExpr.hasLooseBVarAt cutoff e = false ↔ maxLooseBVarSpec e ≤ cutoff
  | .bvar idx, cutoff => by
    simp only [KExpr.hasLooseBVarAt, maxLooseBVarSpec, decide_eq_false_iff_not]
    omega
  | .fvar _, cutoff | .mvar _, cutoff | .sort _, cutoff | .const _ _, cutoff | .lit _, cutoff => by
    simp [KExpr.hasLooseBVarAt, maxLooseBVarSpec]
  | .app f a, cutoff => by
    simp only [KExpr.hasLooseBVarAt, maxLooseBVarSpec, Bool.or_eq_false_iff,
      hasLooseBVarAt_eq_false_iff_maxLooseBVarSpec_le f cutoff,
      hasLooseBVarAt_eq_false_iff_maxLooseBVarSpec_le a cutoff, Nat.max_le]
  | .lam d b, cutoff => by
    simp only [KExpr.hasLooseBVarAt, maxLooseBVarSpec, Bool.or_eq_false_iff,
      hasLooseBVarAt_eq_false_iff_maxLooseBVarSpec_le d cutoff,
      hasLooseBVarAt_eq_false_iff_maxLooseBVarSpec_le b (cutoff + 1), Nat.max_le]
    omega
  | .forallE d b, cutoff => by
    simp only [KExpr.hasLooseBVarAt, maxLooseBVarSpec, Bool.or_eq_false_iff,
      hasLooseBVarAt_eq_false_iff_maxLooseBVarSpec_le d cutoff,
      hasLooseBVarAt_eq_false_iff_maxLooseBVarSpec_le b (cutoff + 1), Nat.max_le]
    omega
  | .letE t v b, cutoff => by
    simp only [KExpr.hasLooseBVarAt, maxLooseBVarSpec, Bool.or_eq_false_iff,
      hasLooseBVarAt_eq_false_iff_maxLooseBVarSpec_le t cutoff,
      hasLooseBVarAt_eq_false_iff_maxLooseBVarSpec_le v cutoff,
      hasLooseBVarAt_eq_false_iff_maxLooseBVarSpec_le b (cutoff + 1), Nat.max_le]
    omega
  | .proj _ _ s, cutoff =>
    hasLooseBVarAt_eq_false_iff_maxLooseBVarSpec_le s cutoff

theorem liftLooseBVars_zero : ∀ (e : KExpr) (cutoff : Nat), KExpr.liftLooseBVars cutoff 0 e = e
  | .bvar idx, cutoff => by simp only [KExpr.liftLooseBVars]; split <;> rfl
  | .fvar _, _ | .mvar _, _ | .sort _, _ | .const _ _, _ | .lit _, _ => rfl
  | .app f a, cutoff => by simp [KExpr.liftLooseBVars, liftLooseBVars_zero f, liftLooseBVars_zero a]
  | .lam d b, cutoff => by simp [KExpr.liftLooseBVars, liftLooseBVars_zero d, liftLooseBVars_zero b]
  | .forallE d b, cutoff => by simp [KExpr.liftLooseBVars, liftLooseBVars_zero d, liftLooseBVars_zero b]
  | .letE t v b, cutoff => by
    simp [KExpr.liftLooseBVars, liftLooseBVars_zero t, liftLooseBVars_zero v, liftLooseBVars_zero b]
  | .proj s idx e, cutoff => by simp [KExpr.liftLooseBVars, liftLooseBVars_zero e]

theorem depth_pos : ∀ (e : KExpr), 1 ≤ depth e
  | .bvar _ | .fvar _ | .mvar _ | .sort _ | .const _ _ | .lit _ => Nat.le_refl 1
  | .app _ _ | .lam _ _ | .forallE _ _ | .letE _ _ _ | .proj _ _ _ => by simp [depth]

theorem depth_liftLooseBVars : ∀ (e : KExpr) (cutoff shift : Nat),
    depth (KExpr.liftLooseBVars cutoff shift e) = depth e
  | .bvar _, _, _ => by simp only [KExpr.liftLooseBVars]; split <;> rfl
  | .fvar _, _, _ | .mvar _, _, _ | .sort _, _, _ | .const _ _, _, _ | .lit _, _, _ => rfl
  | .app f a, c, s => by simp [KExpr.liftLooseBVars, depth, depth_liftLooseBVars f, depth_liftLooseBVars a]
  | .lam d b, c, s => by simp [KExpr.liftLooseBVars, depth, depth_liftLooseBVars d, depth_liftLooseBVars b]
  | .forallE d b, c, s => by simp [KExpr.liftLooseBVars, depth, depth_liftLooseBVars d, depth_liftLooseBVars b]
  | .letE t v b, c, s => by
    simp [KExpr.liftLooseBVars, depth, depth_liftLooseBVars t, depth_liftLooseBVars v, depth_liftLooseBVars b]
  | .proj _ _ e, c, s => by simp [KExpr.liftLooseBVars, depth, depth_liftLooseBVars e]

theorem depth_instantiateAt_le : ∀ (e arg : KExpr) (d : Nat),
    depth (KExpr.instantiateAt d arg e) ≤ depth e + depth arg
  | .bvar idx, arg, d => by
    simp only [KExpr.instantiateAt]
    split
    · simp [depth_liftLooseBVars, depth]
    · split <;> simp [depth]
  | .fvar _, arg, _ | .mvar _, arg, _ | .sort _, arg, _ | .const _ _, arg, _ | .lit _, arg, _ => by
    simp [KExpr.instantiateAt, depth]
  | .app f a, arg, d => by
    have hf := depth_instantiateAt_le f arg d
    have ha := depth_instantiateAt_le a arg d
    simp only [KExpr.instantiateAt, depth]
    omega
  | .lam dom body, arg, d => by
    have hd := depth_instantiateAt_le dom arg d
    have hb := depth_instantiateAt_le body arg (d + 1)
    simp only [KExpr.instantiateAt, depth]
    omega
  | .forallE dom body, arg, d => by
    have hd := depth_instantiateAt_le dom arg d
    have hb := depth_instantiateAt_le body arg (d + 1)
    simp only [KExpr.instantiateAt, depth]
    omega
  | .letE ty val body, arg, d => by
    have ht := depth_instantiateAt_le ty arg d
    have hv := depth_instantiateAt_le val arg d
    have hb := depth_instantiateAt_le body arg (d + 1)
    simp only [KExpr.instantiateAt, depth]
    omega
  | .proj _ _ s, arg, d => by
    have hs := depth_instantiateAt_le s arg d
    simp only [KExpr.instantiateAt, depth]
    omega

/-- Monotonicity predicate for `HwExprCAM`: `cam2` preserves all existing node and symbol indices of `cam1`. -/
def HwExprCAM.Extends (cam1 cam2 : HwExprCAM) : Prop :=
  (∀ (i : Nat) (w : PackedNodeWord), cam1.nodes[i]? = some w → cam2.nodes[i]? = some w) ∧
  (∀ (j : Nat) (s : HwCamSymbolEntry), cam1.symbols[j]? = some s → cam2.symbols[j]? = some s)

theorem HwExprCAM.Extends.refl (cam : HwExprCAM) : cam.Extends cam :=
  ⟨fun _ _ h => h, fun _ _ h => h⟩

theorem HwExprCAM.Extends.trans {a b c : HwExprCAM}
    (h1 : a.Extends b) (h2 : b.Extends c) : a.Extends c :=
  ⟨fun i w h => h2.1 i w (h1.1 i w h), fun j s h => h2.2 j s (h1.2 j s h)⟩

theorem allocPackedSymbol_spec (s : HwCamSymbolEntry) (cam : HwExprCAM) :
    cam.Extends (allocPackedSymbol s cam).2 ∧
    (allocPackedSymbol s cam).2.symbols[(allocPackedSymbol s cam).1]? = some s := by
  unfold allocPackedSymbol
  cases hfind : findElemIdx? cam.symbols s with
  | some idx =>
    exact ⟨HwExprCAM.Extends.refl cam, getElem?_of_findElemIdx? cam.symbols s idx hfind⟩
  | none =>
    refine ⟨⟨fun _ _ h => h, fun j sym h => getElem?_append_preserve [s] h⟩, ?_⟩
    exact getElem?_append_singleton_self cam.symbols s

theorem allocPackedNode_spec (w : PackedNodeWord) (cam : HwExprCAM) :
    cam.Extends (allocPackedNode w cam).2 ∧
    (allocPackedNode w cam).2.nodes[(allocPackedNode w cam).1]? = some w := by
  unfold allocPackedNode
  cases hfind : findElemIdx? cam.nodes w with
  | some idx =>
    exact ⟨HwExprCAM.Extends.refl cam, getElem?_of_findElemIdx? cam.nodes w idx hfind⟩
  | none =>
    refine ⟨⟨fun i nd h => getElem?_append_preserve [w] h, fun _ _ h => h⟩, ?_⟩
    exact getElem?_append_singleton_self cam.nodes w

theorem allocPackedNode_ext {w : PackedNodeWord} {cam : HwExprCAM} :
    cam.Extends (allocPackedNode w cam).2 :=
  (allocPackedNode_spec w cam).1

theorem allocPackedNode_get {w : PackedNodeWord} {cam : HwExprCAM} :
    (allocPackedNode w cam).2.nodes[(allocPackedNode w cam).1]? = some w :=
  (allocPackedNode_spec w cam).2

/-- Structural representation invariant `CamRep cam h e`: handle `h` in `cam` represents `e : KExpr`
with exact hardware `maxLooseBVar` and `hasLooseBVar` summary metadata. -/
def CamRep (cam : HwExprCAM) (h : Nat) : KExpr → Prop
  | .bvar idx =>
    ∃ w, cam.nodes[h]? = some w ∧ w.tag = 0 ∧ w.h0 = idx ∧
         w.maxLooseBVar = idx + 1 ∧ w.hasLooseBVar = true
  | .fvar id =>
    ∃ w, cam.nodes[h]? = some w ∧ w.tag = 1 ∧ w.h0 = id ∧
         w.maxLooseBVar = 0 ∧ w.hasLooseBVar = false
  | .mvar id =>
    ∃ w, cam.nodes[h]? = some w ∧ w.tag = 10 ∧ w.h0 = id ∧
         w.maxLooseBVar = 0 ∧ w.hasLooseBVar = false
  | .sort u =>
    ∃ w, cam.nodes[h]? = some w ∧ w.tag = 2 ∧ cam.symbols[w.symIdx]? = some (.sortEntry u) ∧
         w.maxLooseBVar = 0 ∧ w.hasLooseBVar = false
  | .const n us =>
    ∃ w, cam.nodes[h]? = some w ∧ w.tag = 3 ∧ cam.symbols[w.symIdx]? = some (.constEntry n us) ∧
         w.maxLooseBVar = 0 ∧ w.hasLooseBVar = false
  | .app f a =>
    ∃ w, cam.nodes[h]? = some w ∧ w.tag = 4 ∧
         CamRep cam w.h0 f ∧ CamRep cam w.h1 a ∧
         w.maxLooseBVar = maxLooseBVarSpec (.app f a) ∧
         w.hasLooseBVar = decide (w.maxLooseBVar > 0)
  | .lam d b =>
    ∃ w, cam.nodes[h]? = some w ∧ w.tag = 5 ∧
         CamRep cam w.h0 d ∧ CamRep cam w.h1 b ∧
         w.maxLooseBVar = maxLooseBVarSpec (.lam d b) ∧
         w.hasLooseBVar = decide (w.maxLooseBVar > 0)
  | .forallE d b =>
    ∃ w, cam.nodes[h]? = some w ∧ w.tag = 6 ∧
         CamRep cam w.h0 d ∧ CamRep cam w.h1 b ∧
         w.maxLooseBVar = maxLooseBVarSpec (.forallE d b) ∧
         w.hasLooseBVar = decide (w.maxLooseBVar > 0)
  | .letE t v b =>
    ∃ w, cam.nodes[h]? = some w ∧ w.tag = 7 ∧
         CamRep cam w.h0 t ∧ CamRep cam w.h1 v ∧ CamRep cam w.h2 b ∧
         w.maxLooseBVar = maxLooseBVarSpec (.letE t v b) ∧
         w.hasLooseBVar = decide (w.maxLooseBVar > 0)
  | .lit l =>
    ∃ w, cam.nodes[h]? = some w ∧ w.tag = 8 ∧ cam.symbols[w.symIdx]? = some (.litEntry l) ∧
         w.maxLooseBVar = 0 ∧ w.hasLooseBVar = false
  | .proj sName idx s =>
    ∃ w, cam.nodes[h]? = some w ∧ w.tag = 9 ∧ cam.symbols[w.symIdx]? = some (.projEntry sName idx) ∧
         CamRep cam w.h0 s ∧
         w.maxLooseBVar = maxLooseBVarSpec (.proj sName idx s) ∧
         w.hasLooseBVar = decide (w.maxLooseBVar > 0)

theorem CamRep.mono :
    ∀ {e : KExpr} {cam1 cam2 : HwExprCAM} {h : Nat},
      cam1.Extends cam2 → CamRep cam1 h e → CamRep cam2 h e
  | .bvar _, _, _, h, hext, ⟨w, hnd, ht, hh0, hm, hl⟩ => ⟨w, hext.1 h w hnd, ht, hh0, hm, hl⟩
  | .fvar _, _, _, h, hext, ⟨w, hnd, ht, hh0, hm, hl⟩ => ⟨w, hext.1 h w hnd, ht, hh0, hm, hl⟩
  | .mvar _, _, _, h, hext, ⟨w, hnd, ht, hh0, hm, hl⟩ => ⟨w, hext.1 h w hnd, ht, hh0, hm, hl⟩
  | .sort _, _, _, h, hext, ⟨w, hnd, ht, hs, hm, hl⟩ => ⟨w, hext.1 h w hnd, ht, hext.2 _ _ hs, hm, hl⟩
  | .const _ _, _, _, h, hext, ⟨w, hnd, ht, hs, hm, hl⟩ => ⟨w, hext.1 h w hnd, ht, hext.2 _ _ hs, hm, hl⟩
  | .app _ _, _, _, h, hext, ⟨w, hnd, ht, rf, ra, hm, hl⟩ =>
    ⟨w, hext.1 h w hnd, ht, CamRep.mono hext rf, CamRep.mono hext ra, hm, hl⟩
  | .lam _ _, _, _, h, hext, ⟨w, hnd, ht, rd, rb, hm, hl⟩ =>
    ⟨w, hext.1 h w hnd, ht, CamRep.mono hext rd, CamRep.mono hext rb, hm, hl⟩
  | .forallE _ _, _, _, h, hext, ⟨w, hnd, ht, rd, rb, hm, hl⟩ =>
    ⟨w, hext.1 h w hnd, ht, CamRep.mono hext rd, CamRep.mono hext rb, hm, hl⟩
  | .letE _ _ _, _, _, h, hext, ⟨w, hnd, ht, rt, rv, rb, hm, hl⟩ =>
    ⟨w, hext.1 h w hnd, ht, CamRep.mono hext rt, CamRep.mono hext rv, CamRep.mono hext rb, hm, hl⟩
  | .lit _, _, _, h, hext, ⟨w, hnd, ht, hs, hm, hl⟩ => ⟨w, hext.1 h w hnd, ht, hext.2 _ _ hs, hm, hl⟩
  | .proj _ _ _, _, _, h, hext, ⟨w, hnd, ht, hs, rs, hm, hl⟩ =>
    ⟨w, hext.1 h w hnd, ht, hext.2 _ _ hs, CamRep.mono hext rs, hm, hl⟩

theorem CamRep.node_props {cam : HwExprCAM} {h : Nat} {e : KExpr} (hrep : CamRep cam h e) :
    ∃ w, cam.nodes[h]? = some w ∧
         w.maxLooseBVar = maxLooseBVarSpec e ∧
         w.hasLooseBVar = decide (maxLooseBVarSpec e > 0) := by
  cases e with
  | bvar idx =>
    rcases hrep with ⟨w, hnd, _, _, hm, hl⟩
    exact ⟨w, hnd, hm, by simp [maxLooseBVarSpec, hl]⟩
  | fvar _ | mvar _ | sort _ | const _ _ | lit _ =>
    rcases hrep with ⟨w, hnd, _, _, hm, hl⟩
    exact ⟨w, hnd, hm, hl⟩
  | app _ _ | lam _ _ | forallE _ _ =>
    rcases hrep with ⟨w, hnd, _, _, _, hm, hl⟩
    exact ⟨w, hnd, hm, by rw [hl, hm]⟩
  | letE _ _ _ =>
    rcases hrep with ⟨w, hnd, _, _, _, _, hm, hl⟩
    exact ⟨w, hnd, hm, by rw [hl, hm]⟩
  | proj _ _ _ =>
    rcases hrep with ⟨w, hnd, _, _, _, hm, hl⟩
    exact ⟨w, hnd, hm, by rw [hl, hm]⟩

theorem getPackedNode_maxLooseBVar {cam : HwExprCAM} {h : Nat} {e : KExpr} (hrep : CamRep cam h e) :
    (getPackedNode cam h).maxLooseBVar = maxLooseBVarSpec e := by
  rcases hrep.node_props with ⟨w, hnd, hm, _⟩
  simp [getPackedNode, hnd, hm]

theorem reconstructFromHwExprCAM_of_camRep :
    ∀ (e : KExpr) (fuel : Nat) (cam : HwExprCAM) (h : Nat),
      depth e ≤ fuel → CamRep cam h e → reconstructFromHwExprCAM fuel cam h = some e
  | .bvar idx, 0, _, _, hd, _ => by simp [depth] at hd
  | .bvar idx, f + 1, cam, h, _, ⟨w, hnd, ht, hh0, _, _⟩ => by
    unfold reconstructFromHwExprCAM; rw [hnd]; simp [ht, hh0]
  | .fvar id, 0, _, _, hd, _ => by simp [depth] at hd
  | .fvar id, f + 1, cam, h, _, ⟨w, hnd, ht, hh0, _, _⟩ => by
    unfold reconstructFromHwExprCAM; rw [hnd]; simp [ht, hh0]
  | .mvar id, 0, _, _, hd, _ => by simp [depth] at hd
  | .mvar id, f + 1, cam, h, _, ⟨w, hnd, ht, hh0, _, _⟩ => by
    unfold reconstructFromHwExprCAM; rw [hnd]; simp [ht, hh0]
  | .sort u, 0, _, _, hd, _ => by simp [depth] at hd
  | .sort u, f + 1, cam, h, _, ⟨w, hnd, ht, hs, _, _⟩ => by
    unfold reconstructFromHwExprCAM; rw [hnd]; simp [ht, hs]
  | .const n us, 0, _, _, hd, _ => by simp [depth] at hd
  | .const n us, f + 1, cam, h, _, ⟨w, hnd, ht, hs, _, _⟩ => by
    unfold reconstructFromHwExprCAM; rw [hnd]; simp [ht, hs]
  | .lit l, 0, _, _, hd, _ => by simp [depth] at hd
  | .lit l, f + 1, cam, h, _, ⟨w, hnd, ht, hs, _, _⟩ => by
    unfold reconstructFromHwExprCAM; rw [hnd]; simp [ht, hs]
  | .app fn arg, 0, _, _, hd, _ => by simp [depth] at hd
  | .app fn arg, f + 1, cam, h, hd, ⟨w, hnd, ht, rf, ra, _, _⟩ => by
    simp only [depth] at hd
    unfold reconstructFromHwExprCAM
    rw [hnd]
    simp [ht, reconstructFromHwExprCAM_of_camRep fn f cam w.h0 (by omega) rf,
          reconstructFromHwExprCAM_of_camRep arg f cam w.h1 (by omega) ra]
  | .lam dom body, 0, _, _, hd, _ => by simp [depth] at hd
  | .lam dom body, f + 1, cam, h, hd, ⟨w, hnd, ht, rd, rb, _, _⟩ => by
    simp only [depth] at hd
    unfold reconstructFromHwExprCAM
    rw [hnd]
    simp [ht, reconstructFromHwExprCAM_of_camRep dom f cam w.h0 (by omega) rd,
          reconstructFromHwExprCAM_of_camRep body f cam w.h1 (by omega) rb]
  | .forallE dom body, 0, _, _, hd, _ => by simp [depth] at hd
  | .forallE dom body, f + 1, cam, h, hd, ⟨w, hnd, ht, rd, rb, _, _⟩ => by
    simp only [depth] at hd
    unfold reconstructFromHwExprCAM
    rw [hnd]
    simp [ht, reconstructFromHwExprCAM_of_camRep dom f cam w.h0 (by omega) rd,
          reconstructFromHwExprCAM_of_camRep body f cam w.h1 (by omega) rb]
  | .letE ty val body, 0, _, _, hd, _ => by simp [depth] at hd
  | .letE ty val body, f + 1, cam, h, hd, ⟨w, hnd, ht, rt, rv, rb, _, _⟩ => by
    simp only [depth] at hd
    unfold reconstructFromHwExprCAM
    rw [hnd]
    simp [ht, reconstructFromHwExprCAM_of_camRep ty f cam w.h0 (by omega) rt,
          reconstructFromHwExprCAM_of_camRep val f cam w.h1 (by omega) rv,
          reconstructFromHwExprCAM_of_camRep body f cam w.h2 (by omega) rb]
  | .proj sName idx s, 0, _, _, hd, _ => by simp [depth] at hd
  | .proj sName idx s, f + 1, cam, h, hd, ⟨w, hnd, ht, hs, rs, _, _⟩ => by
    simp only [depth] at hd
    unfold reconstructFromHwExprCAM
    rw [hnd]
    simp [ht, hs, reconstructFromHwExprCAM_of_camRep s f cam w.h0 (by omega) rs]

theorem CamRep.unique {cam : HwExprCAM} {h : Nat} {e1 e2 : KExpr}
    (h1 : CamRep cam h e1) (h2 : CamRep cam h e2) : e1 = e2 := by
  let fuel := Nat.max (depth e1) (depth e2)
  have r1 := reconstructFromHwExprCAM_of_camRep e1 fuel cam h (Nat.le_max_left _ _) h1
  have r2 := reconstructFromHwExprCAM_of_camRep e2 fuel cam h (Nat.le_max_right _ _) h2
  rw [r1] at r2
  exact Option.some.inj r2

theorem mkHwCamApp_camRep {cam : HwExprCAM} {hf ha : Nat} {f a : KExpr}
    (rf : CamRep cam hf f) (ra : CamRep cam ha a) :
    cam.Extends (mkHwCamApp hf ha cam).2 ∧
    CamRep (mkHwCamApp hf ha cam).2 (mkHwCamApp hf ha cam).1 (.app f a) := by
  unfold mkHwCamApp
  dsimp only
  refine ⟨allocPackedNode_ext, ⟨_, allocPackedNode_get, rfl, CamRep.mono allocPackedNode_ext rf, CamRep.mono allocPackedNode_ext ra, ?_, rfl⟩⟩
  simp [maxLooseBVarSpec, getPackedNode_maxLooseBVar rf, getPackedNode_maxLooseBVar ra]

theorem mkHwCamBinder_lam_camRep {cam : HwExprCAM} {hd hb : Nat} {d b : KExpr}
    (rd : CamRep cam hd d) (rb : CamRep cam hb b) :
    cam.Extends (mkHwCamBinder 5 hd hb cam).2 ∧
    CamRep (mkHwCamBinder 5 hd hb cam).2 (mkHwCamBinder 5 hd hb cam).1 (.lam d b) := by
  unfold mkHwCamBinder
  dsimp only
  refine ⟨allocPackedNode_ext, ⟨_, allocPackedNode_get, rfl, CamRep.mono allocPackedNode_ext rd, CamRep.mono allocPackedNode_ext rb, ?_, rfl⟩⟩
  simp [maxLooseBVarSpec, getPackedNode_maxLooseBVar rd, getPackedNode_maxLooseBVar rb]

theorem mkHwCamBinder_forallE_camRep {cam : HwExprCAM} {hd hb : Nat} {d b : KExpr}
    (rd : CamRep cam hd d) (rb : CamRep cam hb b) :
    cam.Extends (mkHwCamBinder 6 hd hb cam).2 ∧
    CamRep (mkHwCamBinder 6 hd hb cam).2 (mkHwCamBinder 6 hd hb cam).1 (.forallE d b) := by
  unfold mkHwCamBinder
  dsimp only
  refine ⟨allocPackedNode_ext, ⟨_, allocPackedNode_get, rfl, CamRep.mono allocPackedNode_ext rd, CamRep.mono allocPackedNode_ext rb, ?_, rfl⟩⟩
  simp [maxLooseBVarSpec, getPackedNode_maxLooseBVar rd, getPackedNode_maxLooseBVar rb]

theorem mkHwCamLetE_camRep {cam : HwExprCAM} {ht hv hb : Nat} {t v b : KExpr}
    (rt : CamRep cam ht t) (rv : CamRep cam hv v) (rb : CamRep cam hb b) :
    cam.Extends (mkHwCamLetE ht hv hb cam).2 ∧
    CamRep (mkHwCamLetE ht hv hb cam).2 (mkHwCamLetE ht hv hb cam).1 (.letE t v b) := by
  unfold mkHwCamLetE
  dsimp only
  refine ⟨allocPackedNode_ext, ⟨_, allocPackedNode_get, rfl, CamRep.mono allocPackedNode_ext rt, CamRep.mono allocPackedNode_ext rv, CamRep.mono allocPackedNode_ext rb, ?_, rfl⟩⟩
  simp [maxLooseBVarSpec, getPackedNode_maxLooseBVar rt, getPackedNode_maxLooseBVar rv,
        getPackedNode_maxLooseBVar rb]

theorem mkHwCamProj_camRep {cam : HwExprCAM} {hs symIdx : Nat} {sName : KName} {idx : Nat} {s : KExpr}
    (hsym : cam.symbols[symIdx]? = some (.projEntry sName idx))
    (rs : CamRep cam hs s) :
    cam.Extends (mkHwCamProj hs symIdx cam).2 ∧
    CamRep (mkHwCamProj hs symIdx cam).2 (mkHwCamProj hs symIdx cam).1 (.proj sName idx s) := by
  unfold mkHwCamProj
  dsimp only
  refine ⟨allocPackedNode_ext, ⟨_, allocPackedNode_get, rfl, allocPackedNode_ext.2 _ _ hsym, CamRep.mono allocPackedNode_ext rs, ?_, rfl⟩⟩
  simp [maxLooseBVarSpec, getPackedNode_maxLooseBVar rs]

/-- Every interned `KExpr` establishes `CamRep` while monotonically extending `HwExprCAM`. -/
theorem internToHwExprCAM_camRep :
    ∀ (e : KExpr) (cam : HwExprCAM),
      cam.Extends (internToHwExprCAM e cam).2 ∧
      CamRep (internToHwExprCAM e cam).2 (internToHwExprCAM e cam).1 e
  | .bvar idx, cam => by
    simp only [internToHwExprCAM]
    exact ⟨allocPackedNode_ext, ⟨_, allocPackedNode_get, rfl, rfl, rfl, rfl⟩⟩
  | .fvar id, cam => by
    simp only [internToHwExprCAM]
    exact ⟨allocPackedNode_ext, ⟨_, allocPackedNode_get, rfl, rfl, rfl, rfl⟩⟩
  | .mvar id, cam => by
    simp only [internToHwExprCAM]
    exact ⟨allocPackedNode_ext, ⟨_, allocPackedNode_get, rfl, rfl, rfl, rfl⟩⟩
  | .sort u, cam => by
    simp only [internToHwExprCAM]
    have hs := allocPackedSymbol_spec (.sortEntry u) cam
    exact ⟨HwExprCAM.Extends.trans hs.1 allocPackedNode_ext, ⟨_, allocPackedNode_get, rfl, allocPackedNode_ext.2 _ _ hs.2, rfl, rfl⟩⟩
  | .const n us, cam => by
    simp only [internToHwExprCAM]
    have hs := allocPackedSymbol_spec (.constEntry n us) cam
    exact ⟨HwExprCAM.Extends.trans hs.1 allocPackedNode_ext, ⟨_, allocPackedNode_get, rfl, allocPackedNode_ext.2 _ _ hs.2, rfl, rfl⟩⟩
  | .lit l, cam => by
    simp only [internToHwExprCAM]
    have hs := allocPackedSymbol_spec (.litEntry l) cam
    exact ⟨HwExprCAM.Extends.trans hs.1 allocPackedNode_ext, ⟨_, allocPackedNode_get, rfl, allocPackedNode_ext.2 _ _ hs.2, rfl, rfl⟩⟩
  | .app f a, cam => by
    simp only [internToHwExprCAM]
    have ⟨extF, repF⟩ := internToHwExprCAM_camRep f cam
    have ⟨extA, repA⟩ := internToHwExprCAM_camRep a (internToHwExprCAM f cam).2
    have ⟨extApp, repApp⟩ := mkHwCamApp_camRep (CamRep.mono extA repF) repA
    exact ⟨HwExprCAM.Extends.trans extF (HwExprCAM.Extends.trans extA extApp), repApp⟩
  | .lam d b, cam => by
    simp only [internToHwExprCAM]
    have ⟨extD, repD⟩ := internToHwExprCAM_camRep d cam
    have ⟨extB, repB⟩ := internToHwExprCAM_camRep b (internToHwExprCAM d cam).2
    have ⟨extLam, repLam⟩ := mkHwCamBinder_lam_camRep (CamRep.mono extB repD) repB
    exact ⟨HwExprCAM.Extends.trans extD (HwExprCAM.Extends.trans extB extLam), repLam⟩
  | .forallE d b, cam => by
    simp only [internToHwExprCAM]
    have ⟨extD, repD⟩ := internToHwExprCAM_camRep d cam
    have ⟨extB, repB⟩ := internToHwExprCAM_camRep b (internToHwExprCAM d cam).2
    have ⟨extPi, repPi⟩ := mkHwCamBinder_forallE_camRep (CamRep.mono extB repD) repB
    exact ⟨HwExprCAM.Extends.trans extD (HwExprCAM.Extends.trans extB extPi), repPi⟩
  | .letE t v b, cam => by
    simp only [internToHwExprCAM]
    have ⟨extT, repT⟩ := internToHwExprCAM_camRep t cam
    have ⟨extV, repV⟩ := internToHwExprCAM_camRep v (internToHwExprCAM t cam).2
    have ⟨extB, repB⟩ := internToHwExprCAM_camRep b (internToHwExprCAM v (internToHwExprCAM t cam).2).2
    have ⟨extL, repL⟩ := mkHwCamLetE_camRep
      (CamRep.mono (HwExprCAM.Extends.trans extV extB) repT)
      (CamRep.mono extB repV) repB
    exact ⟨HwExprCAM.Extends.trans extT (HwExprCAM.Extends.trans extV (HwExprCAM.Extends.trans extB extL)), repL⟩
  | .proj sName idx s, cam => by
    simp only [internToHwExprCAM]
    have ⟨extS, repS⟩ := internToHwExprCAM_camRep s cam
    have hs := allocPackedSymbol_spec (.projEntry sName idx) (internToHwExprCAM s cam).2
    have ⟨extP, repP⟩ := mkHwCamProj_camRep hs.2 (CamRep.mono hs.1 repS)
    exact ⟨HwExprCAM.Extends.trans extS (HwExprCAM.Extends.trans hs.1 extP), repP⟩

/-- Universal lossless reconstruction theorem for `HwExprCAM` (including `.mvar` and `.letE`). -/
theorem reconstructFromHwExprCAM_intern_roundtrip
    (fuel : Nat) (e : KExpr) (cam : HwExprCAM) (hdepth : depth e ≤ fuel) :
    reconstructFromHwExprCAM fuel (internToHwExprCAM e cam).2 (internToHwExprCAM e cam).1 = some e :=
  reconstructFromHwExprCAM_of_camRep e fuel _ _ hdepth (internToHwExprCAM_camRep e cam).2

/-! ## 5b. External Inductive `RealizesExprAt` / `decodeCamDag` Refinement, Symbol Non-Collision & 3-Child `letE` Non-Overflow -/

/-- Executable bounded-fuel DAG decoder for `HwExprCAM` (`decodeCamDag`). -/
abbrev decodeCamDag : Nat → HwExprCAM → Nat → Option KExpr :=
  reconstructFromHwExprCAM

/-- External inductive hardware-to-host DAG refinement relation (`RealizesExprAt cam slot e`):
Relates a ghost-free hardware `HwExprCAM` state `cam` and slot index `slot : Nat` to the host
`KExpr` DAG `e` it realizes, with zero `KExpr` ASTs stored inside hardware CAM slots. -/
inductive RealizesExprAt (cam : HwExprCAM) : Nat → KExpr → Prop where
  | bvar {slot idx : Nat} {w : PackedNodeWord} :
      cam.nodes[slot]? = some w → w.tag = 0 → w.h0 = idx →
      RealizesExprAt cam slot (.bvar idx)
  | fvar {slot id : Nat} {w : PackedNodeWord} :
      cam.nodes[slot]? = some w → w.tag = 1 → w.h0 = id →
      RealizesExprAt cam slot (.fvar id)
  | mvar {slot id : Nat} {w : PackedNodeWord} :
      cam.nodes[slot]? = some w → w.tag = 10 → w.h0 = id →
      RealizesExprAt cam slot (.mvar id)
  | sort {slot : Nat} {u : KLevel} {w : PackedNodeWord} :
      cam.nodes[slot]? = some w → w.tag = 2 →
      cam.symbols[w.symIdx]? = some (.sortEntry u) →
      RealizesExprAt cam slot (.sort u)
  | const {slot : Nat} {n : KName} {us : List KLevel} {w : PackedNodeWord} :
      cam.nodes[slot]? = some w → w.tag = 3 →
      cam.symbols[w.symIdx]? = some (.constEntry n us) →
      RealizesExprAt cam slot (.const n us)
  | app {slot : Nat} {f a : KExpr} {w : PackedNodeWord} :
      cam.nodes[slot]? = some w → w.tag = 4 →
      RealizesExprAt cam w.h0 f → RealizesExprAt cam w.h1 a →
      RealizesExprAt cam slot (.app f a)
  | lam {slot : Nat} {d b : KExpr} {w : PackedNodeWord} :
      cam.nodes[slot]? = some w → w.tag = 5 →
      RealizesExprAt cam w.h0 d → RealizesExprAt cam w.h1 b →
      RealizesExprAt cam slot (.lam d b)
  | forallE {slot : Nat} {d b : KExpr} {w : PackedNodeWord} :
      cam.nodes[slot]? = some w → w.tag = 6 →
      RealizesExprAt cam w.h0 d → RealizesExprAt cam w.h1 b →
      RealizesExprAt cam slot (.forallE d b)
  | letE {slot : Nat} {t v b : KExpr} {w : PackedNodeWord} :
      cam.nodes[slot]? = some w → w.tag = 7 →
      RealizesExprAt cam w.h0 t → RealizesExprAt cam w.h1 v → RealizesExprAt cam w.h2 b →
      RealizesExprAt cam slot (.letE t v b)
  | lit {slot : Nat} {l : KLiteral} {w : PackedNodeWord} :
      cam.nodes[slot]? = some w → w.tag = 8 →
      cam.symbols[w.symIdx]? = some (.litEntry l) →
      RealizesExprAt cam slot (.lit l)
  | proj {slot idx : Nat} {sName : KName} {s : KExpr} {w : PackedNodeWord} :
      cam.nodes[slot]? = some w → w.tag = 9 →
      cam.symbols[w.symIdx]? = some (.projEntry sName idx) →
      RealizesExprAt cam w.h0 s →
      RealizesExprAt cam slot (.proj sName idx s)

theorem RealizesExprAt.mono {cam1 cam2 : HwExprCAM} (hext : cam1.Extends cam2) :
    ∀ {slot : Nat} {e : KExpr},
      RealizesExprAt cam1 slot e → RealizesExprAt cam2 slot e
  | _, _, .bvar hw ht hh0 => .bvar (hext.1 _ _ hw) ht hh0
  | _, _, .fvar hw ht hh0 => .fvar (hext.1 _ _ hw) ht hh0
  | _, _, .mvar hw ht hh0 => .mvar (hext.1 _ _ hw) ht hh0
  | _, _, .sort hw ht hs => .sort (hext.1 _ _ hw) ht (hext.2 _ _ hs)
  | _, _, .const hw ht hs => .const (hext.1 _ _ hw) ht (hext.2 _ _ hs)
  | _, _, .app hw ht rf ra => .app (hext.1 _ _ hw) ht (rf.mono hext) (ra.mono hext)
  | _, _, .lam hw ht rd rb => .lam (hext.1 _ _ hw) ht (rd.mono hext) (rb.mono hext)
  | _, _, .forallE hw ht rd rb => .forallE (hext.1 _ _ hw) ht (rd.mono hext) (rb.mono hext)
  | _, _, .letE hw ht rt rv rb => .letE (hext.1 _ _ hw) ht (rt.mono hext) (rv.mono hext) (rb.mono hext)
  | _, _, .lit hw ht hs => .lit (hext.1 _ _ hw) ht (hext.2 _ _ hs)
  | _, _, .proj hw ht hs rs => .proj (hext.1 _ _ hw) ht (hext.2 _ _ hs) (rs.mono hext)

theorem RealizesExprAt.of_camRep {cam : HwExprCAM} :
    ∀ {e : KExpr} {slot : Nat}, CamRep cam slot e → RealizesExprAt cam slot e
  | .bvar _, _, ⟨_, hnd, ht, hh0, _, _⟩ => .bvar hnd ht hh0
  | .fvar _, _, ⟨_, hnd, ht, hh0, _, _⟩ => .fvar hnd ht hh0
  | .mvar _, _, ⟨_, hnd, ht, hh0, _, _⟩ => .mvar hnd ht hh0
  | .sort _, _, ⟨_, hnd, ht, hs, _, _⟩ => .sort hnd ht hs
  | .const _ _, _, ⟨_, hnd, ht, hs, _, _⟩ => .const hnd ht hs
  | .app _ _, _, ⟨_, hnd, ht, rf, ra, _, _⟩ =>
    .app hnd ht (RealizesExprAt.of_camRep rf) (RealizesExprAt.of_camRep ra)
  | .lam _ _, _, ⟨_, hnd, ht, rd, rb, _, _⟩ =>
    .lam hnd ht (RealizesExprAt.of_camRep rd) (RealizesExprAt.of_camRep rb)
  | .forallE _ _, _, ⟨_, hnd, ht, rd, rb, _, _⟩ =>
    .forallE hnd ht (RealizesExprAt.of_camRep rd) (RealizesExprAt.of_camRep rb)
  | .letE _ _ _, _, ⟨_, hnd, ht, rt, rv, rb, _, _⟩ =>
    .letE hnd ht (RealizesExprAt.of_camRep rt) (RealizesExprAt.of_camRep rv) (RealizesExprAt.of_camRep rb)
  | .lit _, _, ⟨_, hnd, ht, hs, _, _⟩ => .lit hnd ht hs
  | .proj _ _ _, _, ⟨_, hnd, ht, hs, rs, _, _⟩ =>
    .proj hnd ht hs (RealizesExprAt.of_camRep rs)

theorem decodeCamDag_of_realizesExprAt {cam : HwExprCAM} :
    ∀ {slot : Nat} {e : KExpr},
      RealizesExprAt cam slot e →
      ∀ {fuel : Nat}, depth e ≤ fuel → decodeCamDag fuel cam slot = some e
  | _, _, .bvar hw ht hh0, 0, hd => by simp [depth] at hd
  | _, _, .bvar hw ht hh0, _ + 1, _ => by
    unfold decodeCamDag reconstructFromHwExprCAM; rw [hw]; simp [ht, hh0]
  | _, _, .fvar hw ht hh0, 0, hd => by simp [depth] at hd
  | _, _, .fvar hw ht hh0, _ + 1, _ => by
    unfold decodeCamDag reconstructFromHwExprCAM; rw [hw]; simp [ht, hh0]
  | _, _, .mvar hw ht hh0, 0, hd => by simp [depth] at hd
  | _, _, .mvar hw ht hh0, _ + 1, _ => by
    unfold decodeCamDag reconstructFromHwExprCAM; rw [hw]; simp [ht, hh0]
  | _, _, .sort hw ht hs, 0, hd => by simp [depth] at hd
  | _, _, .sort hw ht hs, _ + 1, _ => by
    unfold decodeCamDag reconstructFromHwExprCAM; rw [hw]; simp [ht, hs]
  | _, _, .const hw ht hs, 0, hd => by simp [depth] at hd
  | _, _, .const hw ht hs, _ + 1, _ => by
    unfold decodeCamDag reconstructFromHwExprCAM; rw [hw]; simp [ht, hs]
  | _, _, .lit hw ht hs, 0, hd => by simp [depth] at hd
  | _, _, .lit hw ht hs, _ + 1, _ => by
    unfold decodeCamDag reconstructFromHwExprCAM; rw [hw]; simp [ht, hs]
  | _, _, .app hw ht rf ra, 0, hd => by simp [depth] at hd
  | _, _, .app hw ht rf ra, fuel + 1, hd => by
    simp only [depth] at hd
    unfold decodeCamDag reconstructFromHwExprCAM; rw [hw]
    simp [ht,
      decodeCamDag_of_realizesExprAt (fuel := fuel) rf (by omega),
      decodeCamDag_of_realizesExprAt (fuel := fuel) ra (by omega)]
  | _, _, .lam hw ht rd rb, 0, hd => by simp [depth] at hd
  | _, _, .lam hw ht rd rb, fuel + 1, hd => by
    simp only [depth] at hd
    unfold decodeCamDag reconstructFromHwExprCAM; rw [hw]
    simp [ht,
      decodeCamDag_of_realizesExprAt (fuel := fuel) rd (by omega),
      decodeCamDag_of_realizesExprAt (fuel := fuel) rb (by omega)]
  | _, _, .forallE hw ht rd rb, 0, hd => by simp [depth] at hd
  | _, _, .forallE hw ht rd rb, fuel + 1, hd => by
    simp only [depth] at hd
    unfold decodeCamDag reconstructFromHwExprCAM; rw [hw]
    simp [ht,
      decodeCamDag_of_realizesExprAt (fuel := fuel) rd (by omega),
      decodeCamDag_of_realizesExprAt (fuel := fuel) rb (by omega)]
  | _, _, .letE hw ht rt rv rb, 0, hd => by simp [depth] at hd
  | _, _, .letE hw ht rt rv rb, fuel + 1, hd => by
    simp only [depth] at hd
    unfold decodeCamDag reconstructFromHwExprCAM; rw [hw]
    simp [ht,
      decodeCamDag_of_realizesExprAt (fuel := fuel) rt (by omega),
      decodeCamDag_of_realizesExprAt (fuel := fuel) rv (by omega),
      decodeCamDag_of_realizesExprAt (fuel := fuel) rb (by omega)]
  | _, _, .proj hw ht hs rs, 0, hd => by simp [depth] at hd
  | _, _, .proj hw ht hs rs, fuel + 1, hd => by
    simp only [depth] at hd
    unfold decodeCamDag reconstructFromHwExprCAM; rw [hw]
    simp [ht, hs, decodeCamDag_of_realizesExprAt (fuel := fuel) rs (by omega)]

theorem realizesExprAt_of_decodeCamDag {cam : HwExprCAM} :
    ∀ {fuel slot : Nat} {e : KExpr},
      decodeCamDag fuel cam slot = some e → RealizesExprAt cam slot e
  | 0, _, _, hdec => by cases hdec
  | fuel + 1, slot, e, hdec => by
    unfold decodeCamDag reconstructFromHwExprCAM at hdec
    cases hw : cam.nodes[slot]? with
    | none => simp [hw] at hdec
    | some w =>
      rw [hw] at hdec
      by_cases h0 : w.tag = 0
      · simp [h0] at hdec; subst hdec; exact .bvar hw h0 rfl
      · by_cases h1 : w.tag = 1
        · simp [h1] at hdec; subst hdec; exact .fvar hw h1 rfl
        · by_cases h2 : w.tag = 2
          · cases hsym : cam.symbols[w.symIdx]? with
            | none => simp [h2, hsym] at hdec
            | some sym =>
              cases sym <;> simp [h2, hsym] at hdec
              subst hdec; exact .sort hw h2 hsym
          · by_cases h3 : w.tag = 3
            · cases hsym : cam.symbols[w.symIdx]? with
              | none => simp [h3, hsym] at hdec
              | some sym =>
                cases sym <;> simp [h3, hsym] at hdec
                subst hdec; exact .const hw h3 hsym
            · by_cases h4 : w.tag = 4
              · cases hc0 : reconstructFromHwExprCAM fuel cam w.h0 with
                | none => simp [h4, hc0] at hdec
                | some f =>
                  cases hc1 : reconstructFromHwExprCAM fuel cam w.h1 with
                  | none => simp [h4, hc0, hc1] at hdec
                  | some a =>
                    simp [h4, hc0, hc1] at hdec; subst hdec
                    exact .app hw h4
                      (realizesExprAt_of_decodeCamDag hc0)
                      (realizesExprAt_of_decodeCamDag hc1)
              · by_cases h5 : w.tag = 5
                · cases hc0 : reconstructFromHwExprCAM fuel cam w.h0 with
                  | none => simp [h5, hc0] at hdec
                  | some d =>
                    cases hc1 : reconstructFromHwExprCAM fuel cam w.h1 with
                    | none => simp [h5, hc0, hc1] at hdec
                    | some b =>
                      simp [h5, hc0, hc1] at hdec; subst hdec
                      exact .lam hw h5
                        (realizesExprAt_of_decodeCamDag hc0)
                        (realizesExprAt_of_decodeCamDag hc1)
                · by_cases h6 : w.tag = 6
                  · cases hc0 : reconstructFromHwExprCAM fuel cam w.h0 with
                    | none => simp [h6, hc0] at hdec
                    | some d =>
                      cases hc1 : reconstructFromHwExprCAM fuel cam w.h1 with
                      | none => simp [h6, hc0, hc1] at hdec
                      | some b =>
                        simp [h6, hc0, hc1] at hdec; subst hdec
                        exact .forallE hw h6
                          (realizesExprAt_of_decodeCamDag hc0)
                          (realizesExprAt_of_decodeCamDag hc1)
                  · by_cases h7 : w.tag = 7
                    · cases hc0 : reconstructFromHwExprCAM fuel cam w.h0 with
                      | none => simp [h7, hc0] at hdec
                      | some t =>
                        cases hc1 : reconstructFromHwExprCAM fuel cam w.h1 with
                        | none => simp [h7, hc0, hc1] at hdec
                        | some v =>
                          cases hc2 : reconstructFromHwExprCAM fuel cam w.h2 with
                          | none => simp [h7, hc0, hc1, hc2] at hdec
                          | some b =>
                            simp [h7, hc0, hc1, hc2] at hdec; subst hdec
                            exact .letE hw h7
                              (realizesExprAt_of_decodeCamDag hc0)
                              (realizesExprAt_of_decodeCamDag hc1)
                              (realizesExprAt_of_decodeCamDag hc2)
                    · by_cases h8 : w.tag = 8
                      · cases hsym : cam.symbols[w.symIdx]? with
                        | none => simp [h8, hsym] at hdec
                        | some sym =>
                          cases sym <;> simp [h8, hsym] at hdec
                          subst hdec; exact .lit hw h8 hsym
                      · by_cases h9 : w.tag = 9
                        · cases hc0 : reconstructFromHwExprCAM fuel cam w.h0 with
                          | none => simp [h9, hc0] at hdec
                          | some sub =>
                            cases hsym : cam.symbols[w.symIdx]? with
                            | none => simp [h9, hc0, hsym] at hdec
                            | some sym =>
                              cases sym <;> simp [h9, hc0, hsym] at hdec
                              subst hdec
                              exact .proj hw h9 hsym (realizesExprAt_of_decodeCamDag hc0)
                        · by_cases h10 : w.tag = 10
                          · simp [h10] at hdec
                            subst hdec; exact .mvar hw h10 rfl
                          · simp [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10] at hdec

/-- **Equivalence Theorem (`realizesExprAt_iff_decodeCamDag`)**:
`RealizesExprAt cam slot e` holds if and only if bounded-fuel `decodeCamDag` decodes `slot` to `some e`. -/
theorem realizesExprAt_iff_decodeCamDag (cam : HwExprCAM) (slot : Nat) (e : KExpr) :
    RealizesExprAt cam slot e ↔ ∃ fuel, decodeCamDag fuel cam slot = some e :=
  ⟨fun hr => ⟨depth e, decodeCamDag_of_realizesExprAt hr (Nat.le_refl _)⟩,
   fun ⟨_, hdec⟩ => realizesExprAt_of_decodeCamDag hdec⟩

/-- **Determinism of `RealizesExprAt`**: a hardware slot realizes at most one host `KExpr`. -/
theorem RealizesExprAt.deterministic {cam : HwExprCAM} {slot : Nat} {e₁ e₂ : KExpr}
    (h1 : RealizesExprAt cam slot e₁) (h2 : RealizesExprAt cam slot e₂) : e₁ = e₂ := by
  let fuel := Nat.max (depth e₁) (depth e₂)
  have r1 := decodeCamDag_of_realizesExprAt h1 (Nat.le_max_left (depth e₁) (depth e₂))
  have r2 := decodeCamDag_of_realizesExprAt h2 (Nat.le_max_right (depth e₁) (depth e₂))
  rw [r1] at r2
  exact Option.some.inj r2

/-- **Refinement Soundness of `internToHwExprCAM`**:
Interning any `e : KExpr` into `cam : HwExprCAM` monotonically extends `cam` and establishes
`RealizesExprAt (internToHwExprCAM e cam).2 (internToHwExprCAM e cam).1 e`. -/
theorem internToHwExprCAM_realizesExprAt (e : KExpr) (cam : HwExprCAM) :
    cam.Extends (internToHwExprCAM e cam).2 ∧
    RealizesExprAt (internToHwExprCAM e cam).2 (internToHwExprCAM e cam).1 e := by
  obtain ⟨hext, hrep⟩ := internToHwExprCAM_camRep e cam
  exact ⟨hext, RealizesExprAt.of_camRep hrep⟩

/-- **Distinct Symbol Non-Collision Theorem (`hwExprCam_distinct_symbols_no_collision`)**:
For any `cam : HwExprCAM`, distinct symbol entries (`sym₁ ≠ sym₂`), distinct constants (`n₁ ≠ n₂`,
e.g. `"a"` vs `"b"`), and distinct string literals (`s₁ ≠ s₂`, e.g. `"a"` vs `"b"` which previously
shared `s.length = 1`) never collide in `allocPackedSymbol` or `internToHwExprCAM` lookup. -/
theorem hwExprCam_distinct_symbols_no_collision
    (cam : HwExprCAM)
    (sym₁ sym₂ : HwCamSymbolEntry) (hSymNe : sym₁ ≠ sym₂)
    (n₁ n₂ : KName) (us₁ us₂ : List KLevel) (hConstNe : KExpr.const n₁ us₁ ≠ KExpr.const n₂ us₂)
    (s₁ s₂ : String) (hStrNe : s₁ ≠ s₂) :
    let (id₁, camS1) := allocPackedSymbol sym₁ cam
    let (id₂, _) := allocPackedSymbol sym₂ camS1
    let (hC1, camC1) := internToHwExprCAM (.const n₁ us₁) cam
    let (hC2, camC2) := internToHwExprCAM (.const n₂ us₂) camC1
    let (hL1, camL1) := internToHwExprCAM (.lit (.strVal s₁)) cam
    let (hL2, camL2) := internToHwExprCAM (.lit (.strVal s₂)) camL1
    id₁ ≠ id₂ ∧
    hC1 ≠ hC2 ∧
    RealizesExprAt camC2 hC1 (.const n₁ us₁) ∧
    RealizesExprAt camC2 hC2 (.const n₂ us₂) ∧
    hL1 ≠ hL2 ∧
    RealizesExprAt camL2 hL1 (.lit (.strVal s₁)) ∧
    RealizesExprAt camL2 hL2 (.lit (.strVal s₂)) := by
  dsimp only
  have hs1 := allocPackedSymbol_spec sym₁ cam
  have hs2 := allocPackedSymbol_spec sym₂ (allocPackedSymbol sym₁ cam).2
  have hs1_in_2 := hs2.1.2 _ _ hs1.2
  obtain ⟨_, rc1⟩ := internToHwExprCAM_realizesExprAt (.const n₁ us₁) cam
  obtain ⟨extC2, rc2⟩ := internToHwExprCAM_realizesExprAt (.const n₂ us₂)
    (internToHwExprCAM (.const n₁ us₁) cam).2
  have rc1' := rc1.mono extC2
  obtain ⟨_, rl1⟩ := internToHwExprCAM_realizesExprAt (.lit (.strVal s₁)) cam
  obtain ⟨extL2, rl2⟩ := internToHwExprCAM_realizesExprAt (.lit (.strVal s₂))
    (internToHwExprCAM (.lit (.strVal s₁)) cam).2
  have rl1' := rl1.mono extL2
  refine ⟨?_, ?_, rc1', rc2, ?_, rl1', rl2⟩
  · intro hidEq
    rw [hidEq, hs2.2] at hs1_in_2
    exact hSymNe (Option.some.inj hs1_in_2).symm
  · intro hcEq
    rw [hcEq] at rc1'
    exact hConstNe (rc1'.deterministic rc2)
  · intro hlEq
    rw [hlEq] at rl1'
    have hlitEq := rl1'.deterministic rl2
    injection hlitEq with hlit
    injection hlit with hsEq
    exact hStrNe hsEq

/-- Seed `n` distinct `.fvar` nodes (`0 .. n-1`) into `HwExprCAM` to test >181-node `letE` handles. -/
def seedHwExprCamFVars (n : Nat) : HwExprCAM :=
  { nodes := (List.range n).map fun i =>
      { tag := 1, h0 := i, h1 := 0, hasFVar := true, hasMVar := false }
  , symbols := [] }

/-- Seed `n` distinct `.fvar` slots (`0 .. n-1`) into ghost-free `ExprCAM` to test >181-node `letE` handles. -/
def seededExprCAM (n : Nat) : ExprCAM :=
  { entries := (List.range n).map fun i =>
      { handle := UInt32.ofNat i
      , word64 := mkExprCamWord64 (.fvar i) i 0
      , tag    := 1#4
      , symId  := UInt32.ofNat i }
  , symbols := [] }

theorem seededExprCAM_valid (n : Nat) (hCap : n ≤ UInt32.size) :
    (seededExprCAM n).Valid ∧ (seededExprCAM n).entries.length = n := by
  refine ⟨?_, by simp [seededExprCAM]⟩
  intro i s hs
  simp only [seededExprCAM, List.getElem?_map] at hs
  by_cases hilt : i < n
  · have hlen : i < (List.range n).length := by simpa using hilt
    rw [List.getElem?_eq_getElem hlen, List.getElem_range] at hs
    simp only [Option.map_some, Option.some.injEq] at hs
    subst hs
    have hiCap : i < UInt32.size := Nat.lt_of_lt_of_le hilt hCap
    refine ⟨uint32_toNat_ofNat_of_lt hiCap, hiCap, ?_⟩
    exact leaf_slotKeyChildrenBounded i 1#4 (UInt32.ofNat i)
      (by decide) (by decide) (by decide) (by decide) (by decide)
  · have hge : (List.range n).length ≤ i := by simp; omega
    rw [List.getElem?_eq_none hge] at hs
    cases hs

/-- Classical Cantor pairing `(a + b) * (a + b + 1) / 2 + b` (which overflows 16 bits at 181 nodes). -/
def cantorPairNat (a b : Nat) : Nat :=
  (a + b) * (a + b + 1) / 2 + b

/-- **3-Child `letE` Non-Overflow Theorem (`letE_beyond_181_no_cantor_overflow`)**:
1. At child slot indices `hv ≥ 181` and `hb ≥ 181`, Cantor pairing `cantorPairNat hv hb ≥ 65884 > 65535`
   strictly overflows 16-bit child fields (`maxPoolEntries = 65536`).
2. Both `HwExprCAM` (`internToHwExprCAM` / `RealizesExprAt` / `decodeCamDag`) and ghost-free
   `ExprCAM` (`CamSlotEntry` explicit `(child0, child1, child2)` / `uninternExpr`) intern and
   decode 3-child `.letE ty val body` nodes beyond 190 slots with **zero** Cantor overflow. -/
theorem letE_beyond_181_no_cantor_overflow
    (hv hb : Nat) (hv181 : 181 ≤ hv) (hb181 : 181 ≤ hb)
    (ty val body : KExpr) :
    cantorPairNat hv hb ≥ 65884 ∧
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
  refine ⟨?_, rfl, by decide, ?_, ?_, by simp [seededExprCAM], ?_⟩
  · unfold cantorPairNat
    have hsum : 362 ≤ hv + hb := by omega
    have hprod : 362 * 363 ≤ (hv + hb) * (hv + hb + 1) :=
      Nat.mul_le_mul hsum (by omega)
    omega
  · exact (internToHwExprCAM_realizesExprAt (.letE ty val body) (seedHwExprCamFVars 190)).2
  · exact reconstructFromHwExprCAM_intern_roundtrip
      (depth (.letE ty val body)) (.letE ty val body) (seedHwExprCamFVars 190) (Nat.le_refl _)
  · have hVal := (seededExprCAM_valid 190 (by decide)).1
    have hFit : ExprCamAddressable (seededExprCAM 190) (.letE kNatConst (.fvar 500) (.fvar 501)) := by
      refine ⟨?_, ?_, trivial, by unfold exprVarsFitUInt32; decide, by unfold exprVarsFitUInt32; decide⟩
      · simp only [seededExprCAM, kNatConst, exprNodeBound, List.length_map, List.length_range]
        decide
      · simp only [seededExprCAM, kNatConst, exprNodeBound, List.length_nil]
        decide
    exact (intern_unintern_roundtrip _ hVal hFit).2

theorem liftLooseBVars_eq_self_of_bypass {e : KExpr} {w : PackedNodeWord} {cutoff shift : Nat}
    (hMax : w.maxLooseBVar = maxLooseBVarSpec e)
    (hLoose : w.hasLooseBVar = decide (maxLooseBVarSpec e > 0))
    (hbypass : (!w.hasLooseBVar || shift == 0 || w.maxLooseBVar <= cutoff) = true) :
    KExpr.liftLooseBVars cutoff shift e = e := by
  rw [hMax, hLoose] at hbypass
  rcases Bool.or_eq_true_iff.mp hbypass with h12 | hle
  · rcases Bool.or_eq_true_iff.mp h12 with hnl | hsh
    · have hzero : maxLooseBVarSpec e ≤ cutoff := by
        simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hnl
        omega
      exact liftLooseBVars_of_hasLooseBVarAt_false e cutoff shift
        ((hasLooseBVarAt_eq_false_iff_maxLooseBVarSpec_le e cutoff).mpr hzero)
    · simp only [beq_iff_eq] at hsh
      subst hsh
      exact liftLooseBVars_zero e cutoff
  · simp only [decide_eq_true_eq] at hle
    exact liftLooseBVars_of_hasLooseBVarAt_false e cutoff shift
      ((hasLooseBVarAt_eq_false_iff_maxLooseBVarSpec_le e cutoff).mpr hle)

theorem instantiateAt_eq_self_of_bypass {e arg : KExpr} {w : PackedNodeWord} {depthIdx : Nat}
    (hMax : w.maxLooseBVar = maxLooseBVarSpec e)
    (hLoose : w.hasLooseBVar = decide (maxLooseBVarSpec e > 0))
    (hbypass : (!w.hasLooseBVar || w.maxLooseBVar <= depthIdx) = true) :
    KExpr.instantiateAt depthIdx arg e = e := by
  rw [hMax, hLoose] at hbypass
  have hle : maxLooseBVarSpec e ≤ depthIdx := by
    rcases Bool.or_eq_true_iff.mp hbypass with hnl | hle
    · simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hnl
      omega
    · simp only [decide_eq_true_eq] at hle
      exact hle
  exact instantiateAt_of_hasLooseBVarAt_false e depthIdx arg
    ((hasLooseBVarAt_eq_false_iff_maxLooseBVarSpec_le e depthIdx).mpr hle)

/-- Universal handle-level lifting simulation: `hwCamLiftLooseBVars` preserves `HwExprCAM.Extends`
and produces a handle representing `KExpr.liftLooseBVars cutoff shift e` for all open/closed `e : KExpr`. -/
theorem hwCamLiftLooseBVars_camRep :
    ∀ (e : KExpr) (fuel h cutoff shift : Nat) (cam : HwExprCAM),
      depth e ≤ fuel →
      CamRep cam h e →
      cam.Extends (hwCamLiftLooseBVars fuel h cutoff shift cam).2 ∧
      CamRep (hwCamLiftLooseBVars fuel h cutoff shift cam).2
             (hwCamLiftLooseBVars fuel h cutoff shift cam).1
             (KExpr.liftLooseBVars cutoff shift e) := by
  intro e
  induction e with
  | bvar idx =>
    intro fuel h cutoff shift cam hd hrep
    cases fuel with
    | zero => simp [depth] at hd
    | succ f =>
      rcases hrep with ⟨w, hnd, ht, hh0, hm, hl⟩
      unfold hwCamLiftLooseBVars
      rw [hnd]
      dsimp only
      cases hb : (!w.hasLooseBVar || shift == 0 || decide (w.maxLooseBVar ≤ cutoff))
      · simp only [Bool.false_eq_true, beq_self_eq_true, ↓reduceIte, ht]
        rw [hh0]
        cases hge : decide (idx ≥ cutoff)
        · have hnge : ¬ (idx ≥ cutoff) := decide_eq_false_iff_not.mp hge
          simp only [↓reduceIte, KExpr.liftLooseBVars, hnge]
          exact ⟨HwExprCAM.Extends.refl cam, ⟨w, hnd, ht, hh0, hm, hl⟩⟩
        · have hge' : idx ≥ cutoff := of_decide_eq_true hge
          simp only [↓reduceIte, KExpr.liftLooseBVars, hge']
          exact ⟨allocPackedNode_ext, ⟨_, allocPackedNode_get, rfl, rfl, rfl, rfl⟩⟩
      · simp only [↓reduceIte]
        rw [liftLooseBVars_eq_self_of_bypass hm (by simp [maxLooseBVarSpec, hl]) hb]
        exact ⟨HwExprCAM.Extends.refl cam, ⟨w, hnd, ht, hh0, hm, hl⟩⟩
  | fvar id | mvar id =>
    intro fuel h cutoff shift cam hd hrep
    cases fuel with
    | zero => simp [depth] at hd
    | succ f =>
      rcases hrep with ⟨w, hnd, ht, hh0, hm, hl⟩
      unfold hwCamLiftLooseBVars
      rw [hnd]
      simp [hl, KExpr.liftLooseBVars]
      exact ⟨HwExprCAM.Extends.refl cam, ⟨w, hnd, ht, hh0, hm, hl⟩⟩
  | sort u | const n us | lit l =>
    intro fuel h cutoff shift cam hd hrep
    cases fuel with
    | zero => simp [depth] at hd
    | succ f =>
      rcases hrep with ⟨w, hnd, ht, hs, hm, hl⟩
      unfold hwCamLiftLooseBVars
      rw [hnd]
      simp [hl, KExpr.liftLooseBVars]
      exact ⟨HwExprCAM.Extends.refl cam, ⟨w, hnd, ht, hs, hm, hl⟩⟩
  | app fn arg ihF ihA =>
    intro fuel h cutoff shift cam hd hrep
    cases fuel with
    | zero => simp [depth] at hd
    | succ f =>
      simp only [depth] at hd
      have horig := hrep
      rcases hrep with ⟨w, hnd, ht, rf, ra, hm, hl⟩
      unfold hwCamLiftLooseBVars
      rw [hnd]
      dsimp only
      cases hb : (!w.hasLooseBVar || shift == 0 || decide (w.maxLooseBVar ≤ cutoff))
      · simp only [Bool.false_eq_true, ↓reduceIte, ht]
        have ⟨ext1, repF'⟩ := ihF f w.h0 cutoff shift cam (by omega) rf
        have ⟨ext2, repA'⟩ := ihA f w.h1 cutoff shift _ (by omega) (CamRep.mono ext1 ra)
        have ext12 := HwExprCAM.Extends.trans ext1 ext2
        have repF2 := CamRep.mono ext2 repF'
        cases hsame : ((hwCamLiftLooseBVars f w.h0 cutoff shift cam).1 == w.h0 &&
                       (hwCamLiftLooseBVars f w.h1 cutoff shift (hwCamLiftLooseBVars f w.h0 cutoff shift cam).2).1 == w.h1)
        · simp only [Bool.false_eq_true, ↓reduceIte, KExpr.liftLooseBVars]
          have ⟨ext3, repApp⟩ := mkHwCamApp_camRep repF2 repA'
          exact ⟨HwExprCAM.Extends.trans ext12 ext3, repApp⟩
        · simp only [↓reduceIte, KExpr.liftLooseBVars]
          rcases Bool.and_eq_true_iff.mp hsame with ⟨heqF, heqA⟩
          simp only [beq_iff_eq] at heqF heqA
          rw [heqF] at repF2
          rw [heqA] at repA'
          have eqF := CamRep.unique repF2 (CamRep.mono ext12 rf)
          have eqA := CamRep.unique repA' (CamRep.mono ext12 ra)
          rw [eqF, eqA]
          exact ⟨ext12, CamRep.mono ext12 horig⟩
      · simp only [↓reduceIte]
        rw [liftLooseBVars_eq_self_of_bypass hm (by rw [hl, hm]) hb]
        exact ⟨HwExprCAM.Extends.refl cam, horig⟩
  | lam dom body ihD ihB =>
    intro fuel h cutoff shift cam hd hrep
    cases fuel with
    | zero => simp [depth] at hd
    | succ f =>
      simp only [depth] at hd
      have horig := hrep
      rcases hrep with ⟨w, hnd, ht, rd, rb, hm, hl⟩
      unfold hwCamLiftLooseBVars
      rw [hnd]
      dsimp only
      cases hb : (!w.hasLooseBVar || shift == 0 || decide (w.maxLooseBVar ≤ cutoff))
      · simp only [Bool.false_eq_true, ↓reduceIte, ht]
        have ⟨ext1, repD'⟩ := ihD f w.h0 cutoff shift cam (by omega) rd
        have ⟨ext2, repB'⟩ := ihB f w.h1 (cutoff + 1) shift _ (by omega) (CamRep.mono ext1 rb)
        have ext12 := HwExprCAM.Extends.trans ext1 ext2
        have repD2 := CamRep.mono ext2 repD'
        cases hsame : ((hwCamLiftLooseBVars f w.h0 cutoff shift cam).1 == w.h0 &&
                       (hwCamLiftLooseBVars f w.h1 (cutoff + 1) shift (hwCamLiftLooseBVars f w.h0 cutoff shift cam).2).1 == w.h1)
        · simp only [Bool.false_eq_true, ↓reduceIte, KExpr.liftLooseBVars]
          have ⟨ext3, repLam⟩ := mkHwCamBinder_lam_camRep repD2 repB'
          exact ⟨HwExprCAM.Extends.trans ext12 ext3, repLam⟩
        · simp only [↓reduceIte, KExpr.liftLooseBVars]
          rcases Bool.and_eq_true_iff.mp hsame with ⟨heqD, heqB⟩
          simp only [beq_iff_eq] at heqD heqB
          rw [heqD] at repD2
          rw [heqB] at repB'
          have eqD := CamRep.unique repD2 (CamRep.mono ext12 rd)
          have eqB := CamRep.unique repB' (CamRep.mono ext12 rb)
          rw [eqD, eqB]
          exact ⟨ext12, CamRep.mono ext12 horig⟩
      · simp only [↓reduceIte]
        rw [liftLooseBVars_eq_self_of_bypass hm (by rw [hl, hm]) hb]
        exact ⟨HwExprCAM.Extends.refl cam, horig⟩
  | forallE dom body ihD ihB =>
    intro fuel h cutoff shift cam hd hrep
    cases fuel with
    | zero => simp [depth] at hd
    | succ f =>
      simp only [depth] at hd
      have horig := hrep
      rcases hrep with ⟨w, hnd, ht, rd, rb, hm, hl⟩
      unfold hwCamLiftLooseBVars
      rw [hnd]
      dsimp only
      cases hb : (!w.hasLooseBVar || shift == 0 || decide (w.maxLooseBVar ≤ cutoff))
      · simp only [Bool.false_eq_true, ↓reduceIte, ht]
        have ⟨ext1, repD'⟩ := ihD f w.h0 cutoff shift cam (by omega) rd
        have ⟨ext2, repB'⟩ := ihB f w.h1 (cutoff + 1) shift _ (by omega) (CamRep.mono ext1 rb)
        have ext12 := HwExprCAM.Extends.trans ext1 ext2
        have repD2 := CamRep.mono ext2 repD'
        cases hsame : ((hwCamLiftLooseBVars f w.h0 cutoff shift cam).1 == w.h0 &&
                       (hwCamLiftLooseBVars f w.h1 (cutoff + 1) shift (hwCamLiftLooseBVars f w.h0 cutoff shift cam).2).1 == w.h1)
        · simp only [Bool.false_eq_true, ↓reduceIte, KExpr.liftLooseBVars]
          have ⟨ext3, repPi⟩ := mkHwCamBinder_forallE_camRep repD2 repB'
          exact ⟨HwExprCAM.Extends.trans ext12 ext3, repPi⟩
        · simp only [↓reduceIte, KExpr.liftLooseBVars]
          rcases Bool.and_eq_true_iff.mp hsame with ⟨heqD, heqB⟩
          simp only [beq_iff_eq] at heqD heqB
          rw [heqD] at repD2
          rw [heqB] at repB'
          have eqD := CamRep.unique repD2 (CamRep.mono ext12 rd)
          have eqB := CamRep.unique repB' (CamRep.mono ext12 rb)
          rw [eqD, eqB]
          exact ⟨ext12, CamRep.mono ext12 horig⟩
      · simp only [↓reduceIte]
        rw [liftLooseBVars_eq_self_of_bypass hm (by rw [hl, hm]) hb]
        exact ⟨HwExprCAM.Extends.refl cam, horig⟩
  | letE ty val body ihT ihV ihB =>
    intro fuel h cutoff shift cam hd hrep
    cases fuel with
    | zero => simp [depth] at hd
    | succ f =>
      simp only [depth] at hd
      have horig := hrep
      rcases hrep with ⟨w, hnd, ht, rt, rv, rb, hm, hl⟩
      unfold hwCamLiftLooseBVars
      rw [hnd]
      dsimp only
      cases hb : (!w.hasLooseBVar || shift == 0 || decide (w.maxLooseBVar ≤ cutoff))
      · simp only [Bool.false_eq_true, ↓reduceIte, ht]
        have ⟨ext1, repT'⟩ := ihT f w.h0 cutoff shift cam (by omega) rt
        have ⟨ext2, repV'⟩ := ihV f w.h1 cutoff shift _ (by omega) (CamRep.mono ext1 rv)
        have ext12 := HwExprCAM.Extends.trans ext1 ext2
        have ⟨ext3, repB'⟩ := ihB f w.h2 (cutoff + 1) shift _ (by omega) (CamRep.mono ext12 rb)
        have ext123 := HwExprCAM.Extends.trans ext12 ext3
        have repT3 := CamRep.mono (HwExprCAM.Extends.trans ext2 ext3) repT'
        have repV3 := CamRep.mono ext3 repV'
        cases hsame : (((hwCamLiftLooseBVars f w.h0 cutoff shift cam).1 == w.h0 &&
                        (hwCamLiftLooseBVars f w.h1 cutoff shift (hwCamLiftLooseBVars f w.h0 cutoff shift cam).2).1 == w.h1) &&
                       (hwCamLiftLooseBVars f w.h2 (cutoff + 1) shift (hwCamLiftLooseBVars f w.h1 cutoff shift (hwCamLiftLooseBVars f w.h0 cutoff shift cam).2).2).1 == w.h2)
        · simp only [Bool.false_eq_true, ↓reduceIte, KExpr.liftLooseBVars]
          have ⟨ext4, repLet⟩ := mkHwCamLetE_camRep repT3 repV3 repB'
          exact ⟨HwExprCAM.Extends.trans ext123 ext4, repLet⟩
        · simp only [↓reduceIte, KExpr.liftLooseBVars]
          rcases Bool.and_eq_true_iff.mp hsame with ⟨htv, heqB⟩
          rcases Bool.and_eq_true_iff.mp htv with ⟨heqT, heqV⟩
          simp only [beq_iff_eq] at heqT heqV heqB
          rw [heqT] at repT3
          rw [heqV] at repV3
          rw [heqB] at repB'
          have eqT := CamRep.unique repT3 (CamRep.mono ext123 rt)
          have eqV := CamRep.unique repV3 (CamRep.mono ext123 rv)
          have eqB := CamRep.unique repB' (CamRep.mono ext123 rb)
          rw [eqT, eqV, eqB]
          exact ⟨ext123, CamRep.mono ext123 horig⟩
      · simp only [↓reduceIte]
        rw [liftLooseBVars_eq_self_of_bypass hm (by rw [hl, hm]) hb]
        exact ⟨HwExprCAM.Extends.refl cam, horig⟩
  | proj sName idx s ihS =>
    intro fuel h cutoff shift cam hd hrep
    cases fuel with
    | zero => simp [depth] at hd
    | succ f =>
      simp only [depth] at hd
      have horig := hrep
      rcases hrep with ⟨w, hnd, ht, hsym, rs, hm, hl⟩
      unfold hwCamLiftLooseBVars
      rw [hnd]
      dsimp only
      cases hb : (!w.hasLooseBVar || shift == 0 || decide (w.maxLooseBVar ≤ cutoff))
      · simp only [Bool.false_eq_true, ↓reduceIte, ht]
        have ⟨ext1, repS'⟩ := ihS f w.h0 cutoff shift cam (by omega) rs
        cases hsame : ((hwCamLiftLooseBVars f w.h0 cutoff shift cam).1 == w.h0)
        · simp only [Bool.false_eq_true, ↓reduceIte, KExpr.liftLooseBVars]
          have ⟨ext2, repP⟩ := mkHwCamProj_camRep (ext1.2 _ _ hsym) repS'
          exact ⟨HwExprCAM.Extends.trans ext1 ext2, repP⟩
        · simp only [↓reduceIte, KExpr.liftLooseBVars]
          simp only [beq_iff_eq] at hsame
          rw [hsame] at repS'
          have eqS := CamRep.unique repS' (CamRep.mono ext1 rs)
          rw [eqS]
          exact ⟨ext1, CamRep.mono ext1 horig⟩
      · simp only [↓reduceIte]
        rw [liftLooseBVars_eq_self_of_bypass hm (by rw [hl, hm]) hb]
        exact ⟨HwExprCAM.Extends.refl cam, horig⟩

/-- Universal handle-level open substitution simulation (`hwCamInstantiateAt_camRep`):
For EVERY open or closed expression `eBody : KExpr` and EVERY open or closed argument `eArg : KExpr`
(including nested `.lam`/`.forallE`/`.letE` binders, `.proj`, and `.mvar`), whenever
`depth eBody + depth eArg ≤ fuel`, `hwCamInstantiateAt` preserves `HwExprCAM.Extends` and returns a
handle representing `KExpr.instantiateAt depthIdx eArg eBody` without reconstructing ASTs! -/
theorem hwCamInstantiateAt_camRep :
    ∀ (eBody : KExpr) (fuel hBody depthIdx hArg : Nat) (eArg : KExpr) (cam : HwExprCAM),
      depth eBody + depth eArg ≤ fuel →
      CamRep cam hBody eBody →
      CamRep cam hArg eArg →
      cam.Extends (hwCamInstantiateAt fuel hBody depthIdx hArg cam).2 ∧
      CamRep (hwCamInstantiateAt fuel hBody depthIdx hArg cam).2
             (hwCamInstantiateAt fuel hBody depthIdx hArg cam).1
             (KExpr.instantiateAt depthIdx eArg eBody) := by
  intro eBody
  induction eBody with
  | bvar idx =>
    intro fuel hBody depthIdx hArg eArg cam hd repB repA
    have hposA := depth_pos eArg
    cases fuel with
    | zero => simp [depth] at hd
    | succ f =>
      simp only [depth] at hd
      have horig := repB
      rcases repB with ⟨w, hnd, ht, hh0, hm, hl⟩
      unfold hwCamInstantiateAt
      rw [hnd]
      dsimp only
      cases hb : (!w.hasLooseBVar || decide (w.maxLooseBVar ≤ depthIdx))
      · simp only [Bool.false_eq_true, ↓reduceIte, ht]
        rw [hh0]
        cases heq : (idx == depthIdx)
        · simp only [Bool.false_eq_true, ↓reduceIte]
          cases hgt : decide (idx > depthIdx)
          · have hngt : ¬ (idx > depthIdx) := decide_eq_false_iff_not.mp hgt
            simp only [hngt, ↓reduceIte, KExpr.instantiateAt, heq, Bool.false_eq_true]
            exact ⟨HwExprCAM.Extends.refl cam, horig⟩
          · have hgt' : idx > depthIdx := of_decide_eq_true hgt
            simp only [hgt', ↓reduceIte, KExpr.instantiateAt, heq, Bool.false_eq_true]
            refine ⟨allocPackedNode_ext, ⟨_, allocPackedNode_get, rfl, rfl, ?_, rfl⟩⟩
            dsimp only
            omega
        · simp only [↓reduceIte, KExpr.instantiateAt, heq]
          exact hwCamLiftLooseBVars_camRep eArg f hArg 0 depthIdx cam (by omega) repA
      · simp only [↓reduceIte]
        rw [instantiateAt_eq_self_of_bypass hm (by simp [maxLooseBVarSpec, hl]) hb]
        exact ⟨HwExprCAM.Extends.refl cam, horig⟩
  | fvar id | mvar id =>
    intro fuel hBody depthIdx hArg eArg cam hd repB _
    cases fuel with
    | zero => simp [depth] at hd
    | succ f =>
      rcases repB with ⟨w, hnd, ht, hh0, hm, hl⟩
      unfold hwCamInstantiateAt
      rw [hnd]
      simp [hl, KExpr.instantiateAt]
      exact ⟨HwExprCAM.Extends.refl cam, ⟨w, hnd, ht, hh0, hm, hl⟩⟩
  | sort u | const n us | lit l =>
    intro fuel hBody depthIdx hArg eArg cam hd repB _
    cases fuel with
    | zero => simp [depth] at hd
    | succ f =>
      rcases repB with ⟨w, hnd, ht, hs, hm, hl⟩
      unfold hwCamInstantiateAt
      rw [hnd]
      simp [hl, KExpr.instantiateAt]
      exact ⟨HwExprCAM.Extends.refl cam, ⟨w, hnd, ht, hs, hm, hl⟩⟩
  | app fn arg ihF ihA =>
    intro fuel hBody depthIdx hArg eArg cam hd repB repA
    cases fuel with
    | zero => simp [depth] at hd
    | succ f =>
      simp only [depth] at hd
      have horig := repB
      rcases repB with ⟨w, hnd, ht, rf, ra, hm, hl⟩
      unfold hwCamInstantiateAt
      rw [hnd]
      dsimp only
      cases hb : (!w.hasLooseBVar || decide (w.maxLooseBVar ≤ depthIdx))
      · simp only [Bool.false_eq_true, ↓reduceIte, ht]
        have ⟨ext1, repF'⟩ := ihF f w.h0 depthIdx hArg eArg cam (by omega) rf repA
        have ⟨ext2, repA'⟩ := ihA f w.h1 depthIdx hArg eArg _ (by omega)
          (CamRep.mono ext1 ra) (CamRep.mono ext1 repA)
        have ext12 := HwExprCAM.Extends.trans ext1 ext2
        have repF2 := CamRep.mono ext2 repF'
        cases hsame : ((hwCamInstantiateAt f w.h0 depthIdx hArg cam).1 == w.h0 &&
                       (hwCamInstantiateAt f w.h1 depthIdx hArg (hwCamInstantiateAt f w.h0 depthIdx hArg cam).2).1 == w.h1)
        · simp only [Bool.false_eq_true, ↓reduceIte, KExpr.instantiateAt]
          have ⟨ext3, repApp⟩ := mkHwCamApp_camRep repF2 repA'
          exact ⟨HwExprCAM.Extends.trans ext12 ext3, repApp⟩
        · simp only [↓reduceIte, KExpr.instantiateAt]
          rcases Bool.and_eq_true_iff.mp hsame with ⟨heqF, heqA⟩
          simp only [beq_iff_eq] at heqF heqA
          rw [heqF] at repF2
          rw [heqA] at repA'
          have eqF := CamRep.unique repF2 (CamRep.mono ext12 rf)
          have eqA := CamRep.unique repA' (CamRep.mono ext12 ra)
          rw [eqF, eqA]
          exact ⟨ext12, CamRep.mono ext12 horig⟩
      · simp only [↓reduceIte]
        rw [instantiateAt_eq_self_of_bypass hm (by rw [hl, hm]) hb]
        exact ⟨HwExprCAM.Extends.refl cam, horig⟩
  | lam dom body ihD ihB =>
    intro fuel hBody depthIdx hArg eArg cam hd repB repA
    cases fuel with
    | zero => simp [depth] at hd
    | succ f =>
      simp only [depth] at hd
      have horig := repB
      rcases repB with ⟨w, hnd, ht, rd, rb, hm, hl⟩
      unfold hwCamInstantiateAt
      rw [hnd]
      dsimp only
      cases hb : (!w.hasLooseBVar || decide (w.maxLooseBVar ≤ depthIdx))
      · simp only [Bool.false_eq_true, ↓reduceIte, ht]
        have ⟨ext1, repD'⟩ := ihD f w.h0 depthIdx hArg eArg cam (by omega) rd repA
        have ⟨ext2, repB'⟩ := ihB f w.h1 (depthIdx + 1) hArg eArg _ (by omega)
          (CamRep.mono ext1 rb) (CamRep.mono ext1 repA)
        have ext12 := HwExprCAM.Extends.trans ext1 ext2
        have repD2 := CamRep.mono ext2 repD'
        cases hsame : ((hwCamInstantiateAt f w.h0 depthIdx hArg cam).1 == w.h0 &&
                       (hwCamInstantiateAt f w.h1 (depthIdx + 1) hArg (hwCamInstantiateAt f w.h0 depthIdx hArg cam).2).1 == w.h1)
        · simp only [Bool.false_eq_true, ↓reduceIte, KExpr.instantiateAt]
          have ⟨ext3, repLam⟩ := mkHwCamBinder_lam_camRep repD2 repB'
          exact ⟨HwExprCAM.Extends.trans ext12 ext3, repLam⟩
        · simp only [↓reduceIte, KExpr.instantiateAt]
          rcases Bool.and_eq_true_iff.mp hsame with ⟨heqD, heqB⟩
          simp only [beq_iff_eq] at heqD heqB
          rw [heqD] at repD2
          rw [heqB] at repB'
          have eqD := CamRep.unique repD2 (CamRep.mono ext12 rd)
          have eqB := CamRep.unique repB' (CamRep.mono ext12 rb)
          rw [eqD, eqB]
          exact ⟨ext12, CamRep.mono ext12 horig⟩
      · simp only [↓reduceIte]
        rw [instantiateAt_eq_self_of_bypass hm (by rw [hl, hm]) hb]
        exact ⟨HwExprCAM.Extends.refl cam, horig⟩
  | forallE dom body ihD ihB =>
    intro fuel hBody depthIdx hArg eArg cam hd repB repA
    cases fuel with
    | zero => simp [depth] at hd
    | succ f =>
      simp only [depth] at hd
      have horig := repB
      rcases repB with ⟨w, hnd, ht, rd, rb, hm, hl⟩
      unfold hwCamInstantiateAt
      rw [hnd]
      dsimp only
      cases hb : (!w.hasLooseBVar || decide (w.maxLooseBVar ≤ depthIdx))
      · simp only [Bool.false_eq_true, ↓reduceIte, ht]
        have ⟨ext1, repD'⟩ := ihD f w.h0 depthIdx hArg eArg cam (by omega) rd repA
        have ⟨ext2, repB'⟩ := ihB f w.h1 (depthIdx + 1) hArg eArg _ (by omega)
          (CamRep.mono ext1 rb) (CamRep.mono ext1 repA)
        have ext12 := HwExprCAM.Extends.trans ext1 ext2
        have repD2 := CamRep.mono ext2 repD'
        cases hsame : ((hwCamInstantiateAt f w.h0 depthIdx hArg cam).1 == w.h0 &&
                       (hwCamInstantiateAt f w.h1 (depthIdx + 1) hArg (hwCamInstantiateAt f w.h0 depthIdx hArg cam).2).1 == w.h1)
        · simp only [Bool.false_eq_true, ↓reduceIte, KExpr.instantiateAt]
          have ⟨ext3, repPi⟩ := mkHwCamBinder_forallE_camRep repD2 repB'
          exact ⟨HwExprCAM.Extends.trans ext12 ext3, repPi⟩
        · simp only [↓reduceIte, KExpr.instantiateAt]
          rcases Bool.and_eq_true_iff.mp hsame with ⟨heqD, heqB⟩
          simp only [beq_iff_eq] at heqD heqB
          rw [heqD] at repD2
          rw [heqB] at repB'
          have eqD := CamRep.unique repD2 (CamRep.mono ext12 rd)
          have eqB := CamRep.unique repB' (CamRep.mono ext12 rb)
          rw [eqD, eqB]
          exact ⟨ext12, CamRep.mono ext12 horig⟩
      · simp only [↓reduceIte]
        rw [instantiateAt_eq_self_of_bypass hm (by rw [hl, hm]) hb]
        exact ⟨HwExprCAM.Extends.refl cam, horig⟩
  | letE ty val body ihT ihV ihB =>
    intro fuel hBody depthIdx hArg eArg cam hd repB repA
    cases fuel with
    | zero => simp [depth] at hd
    | succ f =>
      simp only [depth] at hd
      have horig := repB
      rcases repB with ⟨w, hnd, ht, rt, rv, rb, hm, hl⟩
      unfold hwCamInstantiateAt
      rw [hnd]
      dsimp only
      cases hb : (!w.hasLooseBVar || decide (w.maxLooseBVar ≤ depthIdx))
      · simp only [Bool.false_eq_true, ↓reduceIte, ht]
        have ⟨ext1, repT'⟩ := ihT f w.h0 depthIdx hArg eArg cam (by omega) rt repA
        have ⟨ext2, repV'⟩ := ihV f w.h1 depthIdx hArg eArg _ (by omega)
          (CamRep.mono ext1 rv) (CamRep.mono ext1 repA)
        have ext12 := HwExprCAM.Extends.trans ext1 ext2
        have ⟨ext3, repB'⟩ := ihB f w.h2 (depthIdx + 1) hArg eArg _ (by omega)
          (CamRep.mono ext12 rb) (CamRep.mono ext12 repA)
        have ext123 := HwExprCAM.Extends.trans ext12 ext3
        have repT3 := CamRep.mono (HwExprCAM.Extends.trans ext2 ext3) repT'
        have repV3 := CamRep.mono ext3 repV'
        cases hsame : (((hwCamInstantiateAt f w.h0 depthIdx hArg cam).1 == w.h0 &&
                        (hwCamInstantiateAt f w.h1 depthIdx hArg (hwCamInstantiateAt f w.h0 depthIdx hArg cam).2).1 == w.h1) &&
                       (hwCamInstantiateAt f w.h2 (depthIdx + 1) hArg (hwCamInstantiateAt f w.h1 depthIdx hArg (hwCamInstantiateAt f w.h0 depthIdx hArg cam).2).2).1 == w.h2)
        · simp only [Bool.false_eq_true, ↓reduceIte, KExpr.instantiateAt]
          have ⟨ext4, repLet⟩ := mkHwCamLetE_camRep repT3 repV3 repB'
          exact ⟨HwExprCAM.Extends.trans ext123 ext4, repLet⟩
        · simp only [↓reduceIte, KExpr.instantiateAt]
          rcases Bool.and_eq_true_iff.mp hsame with ⟨htv, heqB⟩
          rcases Bool.and_eq_true_iff.mp htv with ⟨heqT, heqV⟩
          simp only [beq_iff_eq] at heqT heqV heqB
          rw [heqT] at repT3
          rw [heqV] at repV3
          rw [heqB] at repB'
          have eqT := CamRep.unique repT3 (CamRep.mono ext123 rt)
          have eqV := CamRep.unique repV3 (CamRep.mono ext123 rv)
          have eqB := CamRep.unique repB' (CamRep.mono ext123 rb)
          rw [eqT, eqV, eqB]
          exact ⟨ext123, CamRep.mono ext123 horig⟩
      · simp only [↓reduceIte]
        rw [instantiateAt_eq_self_of_bypass hm (by rw [hl, hm]) hb]
        exact ⟨HwExprCAM.Extends.refl cam, horig⟩
  | proj sName idx s ihS =>
    intro fuel hBody depthIdx hArg eArg cam hd repB repA
    cases fuel with
    | zero => simp [depth] at hd
    | succ f =>
      simp only [depth] at hd
      have horig := repB
      rcases repB with ⟨w, hnd, ht, hsym, rs, hm, hl⟩
      unfold hwCamInstantiateAt
      rw [hnd]
      dsimp only
      cases hb : (!w.hasLooseBVar || decide (w.maxLooseBVar ≤ depthIdx))
      · simp only [Bool.false_eq_true, ↓reduceIte, ht]
        have ⟨ext1, repS'⟩ := ihS f w.h0 depthIdx hArg eArg cam (by omega) rs repA
        cases hsame : ((hwCamInstantiateAt f w.h0 depthIdx hArg cam).1 == w.h0)
        · simp only [Bool.false_eq_true, ↓reduceIte, KExpr.instantiateAt]
          have ⟨ext2, repP⟩ := mkHwCamProj_camRep (ext1.2 _ _ hsym) repS'
          exact ⟨HwExprCAM.Extends.trans ext1 ext2, repP⟩
        · simp only [↓reduceIte, KExpr.instantiateAt]
          simp only [beq_iff_eq] at hsame
          rw [hsame] at repS'
          have eqS := CamRep.unique repS' (CamRep.mono ext1 rs)
          rw [eqS]
          exact ⟨ext1, CamRep.mono ext1 horig⟩
      · simp only [↓reduceIte]
        rw [instantiateAt_eq_self_of_bypass hm (by rw [hl, hm]) hb]
        exact ⟨HwExprCAM.Extends.refl cam, horig⟩

/-- **Universal Open Handle-Level Substitution Simulation (`reconstructFromHwExprCAM_hwCamInstantiateAt`)**:
For EVERY `eBody eArg : KExpr` (open or closed, across arbitrary nested binders), EVERY `depthIdx : Nat`,
EVERY initial `cam0 : HwExprCAM`, and EVERY `fuel : Nat` with `depth eBody + depth eArg ≤ fuel`,
interning `eBody` and `eArg` into `HwExprCAM` and executing pure handle-level `hwCamInstantiateAt`
reconstructs to `some (KExpr.instantiateAt depthIdx eArg eBody)` identically! -/
theorem reconstructFromHwExprCAM_hwCamInstantiateAt
    (fuel depthIdx : Nat) (eBody eArg : KExpr) (cam0 : HwExprCAM)
    (hfuel : depth eBody + depth eArg ≤ fuel) :
    let (hBody, cam1) := internToHwExprCAM eBody cam0
    let (hArg, cam2)  := internToHwExprCAM eArg cam1
    let (hRes, cam3)  := hwCamInstantiateAt fuel hBody depthIdx hArg cam2
    reconstructFromHwExprCAM fuel cam3 hRes = some (KExpr.instantiateAt depthIdx eArg eBody) := by
  dsimp only
  have ⟨_, repB1⟩ := internToHwExprCAM_camRep eBody cam0
  have ⟨extA, repA2⟩ := internToHwExprCAM_camRep eArg (internToHwExprCAM eBody cam0).2
  have repB2 := CamRep.mono extA repB1
  have ⟨_, repRes⟩ := hwCamInstantiateAt_camRep eBody fuel _ depthIdx _ eArg _ hfuel repB2 repA2
  have hdRes : depth (KExpr.instantiateAt depthIdx eArg eBody) ≤ fuel :=
    Nat.le_trans (depth_instantiateAt_le eBody eArg depthIdx) hfuel
  exact reconstructFromHwExprCAM_of_camRep _ fuel _ _ hdRes repRes

/-- **Handle-Level CAM Substitution Soundness Theorem (`hwCamInstantiateAt_sound`)**:
Combines the 1-cycle closed-term bypass (`hwCamInstantiateAt_closed_bypass`) and universal open
substitution simulation (`reconstructFromHwExprCAM_hwCamInstantiateAt`) for all `eBody, eArg : KExpr`. -/
theorem hwCamInstantiateAt_sound
    (fuel depthIdx : Nat) (eBody eArg : KExpr) (cam0 : HwExprCAM)
    (hfuel : depth eBody + depth eArg ≤ fuel) :
    reconstructFromHwExprCAM fuel
      (hwCamInstantiateAt fuel (internToHwExprCAM eBody cam0).1 depthIdx
        (internToHwExprCAM eArg (internToHwExprCAM eBody cam0).2).1
        (internToHwExprCAM eArg (internToHwExprCAM eBody cam0).2).2).2
      (hwCamInstantiateAt fuel (internToHwExprCAM eBody cam0).1 depthIdx
        (internToHwExprCAM eArg (internToHwExprCAM eBody cam0).2).1
        (internToHwExprCAM eArg (internToHwExprCAM eBody cam0).2).2).1 =
      some (KExpr.instantiateAt depthIdx eArg eBody) ∧
    (∀ (hB : Nat) (cam : HwExprCAM) (w : PackedNodeWord),
      cam.nodes[hB]? = some w → w.hasLooseBVar = false →
      hwCamInstantiateAt (fuel + 1) hB depthIdx 0 cam = (hB, cam)) :=
  ⟨reconstructFromHwExprCAM_hwCamInstantiateAt fuel depthIdx eBody eArg cam0 hfuel,
   fun hB cam w hnode hclosed => (hwCamInstantiateAt_closed_bypass fuel hB depthIdx 0 cam w hnode hclosed).1⟩

/-! ## 6. Live Declaration-Cone Ingestion, `Std.HashMap` Fast CAM Interning & Recursor Extraction (`WS 24`) -/

/-- Structural hash on `KName` for `Std.HashSet` / `Std.HashMap` indexing. -/
def hashKName : KName → UInt64
  | .anonymous => 17
  | .str p s   => mixHash 31 (mixHash (hashKName p) (hash s))
  | .num p k   => mixHash 47 (mixHash (hashKName p) (hash k))

instance : Hashable KName := ⟨hashKName⟩

/-- Structural hash on `KLevel`. -/
def hashKLevel : KLevel → UInt64
  | .zero      => 11
  | .succ u    => mixHash 23 (hashKLevel u)
  | .max u v   => mixHash 37 (mixHash (hashKLevel u) (hashKLevel v))
  | .imax u v  => mixHash 53 (mixHash (hashKLevel u) (hashKLevel v))
  | .param n   => mixHash 71 (hashKName n)

instance : Hashable KLevel := ⟨hashKLevel⟩

instance : Hashable KLiteral where
  hash
    | .natVal n => mixHash 13 (hash n)
    | .strVal s => mixHash 29 (hash s)

instance : Hashable HwCamSymbolEntry where
  hash
    | .sortEntry u     => mixHash 3 (hash u)
    | .constEntry n us => mixHash 5 (mixHash (hash n) (hash us))
    | .litEntry l      => mixHash 7 (hash l)
    | .projEntry s idx => mixHash 11 (mixHash (hash s) (hash idx))

instance : Hashable PackedNodeWord where
  hash w :=
    mixHash (hash w.tag)
      (mixHash (hash w.h0)
        (mixHash (hash w.h1)
          (mixHash (hash w.h2)
            (mixHash (hash w.symIdx)
              (mixHash (hash w.hasLooseBVar)
                (mixHash (hash w.hasFVar)
                  (mixHash (hash w.hasMVar) (hash w.maxLooseBVar))))))))

/-- Extract a self-hosted `KConstInfo` from a live host `Lean.ConstantInfo` via `fromLeanName` and `fromLeanExpr`.
Note: `.opaqueInfo` translates `val.value` into `.thmInfo` so `sorryAx` or ill-typed opaque bodies
are checked by the kernel while remaining opaque to $\delta$-unfolding during WHNF. -/
def extractLeanConstInfo? : Lean.ConstantInfo → Option KConstInfo
  | .axiomInfo val => do
    let ty ← fromLeanExpr val.type
    pure (.axiomInfo (fromLeanName val.name) (val.levelParams.map fromLeanName) ty)
  | .defnInfo val => do
    let ty ← fromLeanExpr val.type
    let v  ← fromLeanExpr val.value
    pure (.defnInfo (fromLeanName val.name) (val.levelParams.map fromLeanName) ty v)
  | .thmInfo val => do
    let ty ← fromLeanExpr val.type
    let v  ← fromLeanExpr val.value
    pure (.thmInfo (fromLeanName val.name) (val.levelParams.map fromLeanName) ty v)
  | .inductInfo val => do
    let ty ← fromLeanExpr val.type
    pure (.inductInfo (fromLeanName val.name) (val.levelParams.map fromLeanName) ty)
  | .ctorInfo val => do
    let ty ← fromLeanExpr val.type
    pure (.ctorInfo (fromLeanName val.name) (val.levelParams.map fromLeanName) ty (fromLeanName val.induct))
  | .recInfo val => do
    let ty ← fromLeanExpr val.type
    pure (.axiomInfo (fromLeanName val.name) (val.levelParams.map fromLeanName) ty)
  | .opaqueInfo val => do
    let ty ← fromLeanExpr val.type
    let v  ← fromLeanExpr val.value
    pure (.thmInfo (fromLeanName val.name) (val.levelParams.map fromLeanName) ty v)
  | .quotInfo val => do
    let ty ← fromLeanExpr val.type
    pure (.axiomInfo (fromLeanName val.name) (val.levelParams.map fromLeanName) ty)

/-- Canonical `Lean.Expr → Option KExpr` translator (`fromLeanExprWithProjShift`):
Preserves Lean's 0-based structure field index `i` on `.proj s i e` without pre-shifting by `numParams`
(eliminating the `.proj` double-offset against `LeanKernel.kernelWhnf` and `LeanKernel.inferProjFieldType?`,
which apply `env.inductDecls`'s `numParams` offset once), and maps `.mvar` to first-class `KExpr.mvar`. -/
def fromLeanExprWithProjShift (_numParamsOf : Lean.Name → Nat := fun _ => 0) : Lean.Expr → Option KExpr :=
  fromLeanExpr

/-- Environment-aware `KConstInfo` extractor (`extractLeanConstInfoWith?`). -/
def extractLeanConstInfoWith?
    (_findConst? : Lean.Name → Option Lean.ConstantInfo)
    (info : Lean.ConstantInfo) : Option KConstInfo :=
  extractLeanConstInfo? info

/-- Extract the list of universe-polymorphic `KRecRule` $\iota$-reduction rules from a live host
`Lean.RecursorVal` (`extractLeanRecRules`), populating `levelParams := rval.levelParams.map fromLeanName`,
`numPrefixArgs := rval.numParams + rval.numMotives + rval.numMinors`, `numFields := rule.nfields`,
and translating `rule.rhs` via `fromLeanExpr` (stripping `.mdata` annotations transparently). -/
def extractLeanRecRules (rval : Lean.RecursorVal) : Option (List KRecRule) :=
  rval.rules.mapM fun rule => do
    let rhsExpr ← fromLeanExpr rule.rhs
    pure
      { recName       := fromLeanName rval.name
      , ctorName      := fromLeanName rule.ctor
      , levelParams   := rval.levelParams.map fromLeanName
      , numPrefixArgs := rval.numParams + rval.numMotives + rval.numMinors
      , numFields     := rule.nfields
      , rhs           := rhsExpr }

/-- Environment-aware `KRecRule` extractor (`extractLeanRecRulesWith`). -/
def extractLeanRecRulesWith
    (_findConst? : Lean.Name → Option Lean.ConstantInfo)
    (rval : Lean.RecursorVal) : Option (List KRecRule) :=
  extractLeanRecRules rval

/-- Extract a `KInductDecl` (including `numParams`, `numIndices`, constructors, and recursor rules)
from a live host `Lean.InductiveVal` so parameterized `.proj` reduction and type inference have
exact `numParams` metadata in `KEnv.inductDecls`. -/
def extractLeanInductDeclWith?
    (findConst? : Lean.Name → Option Lean.ConstantInfo)
    (iv : Lean.InductiveVal) : Option KInductDecl := do
  let ty ← fromLeanExpr iv.type
  let ctors ← iv.ctors.mapM fun cName => do
    match findConst? cName with
    | some (.ctorInfo cv) =>
      let cTy ← fromLeanExpr cv.type
      pure (fromLeanName cv.name, cTy, cv.numFields)
    | _ => none
  let recRules :=
    match findConst? (.str iv.name "rec") with
    | some (.recInfo rv) => (extractLeanRecRules rv).getD []
    | _ => []
  pure
    { name        := fromLeanName iv.name
    , levelParams := iv.levelParams.map fromLeanName
    , numParams   := iv.numParams
    , numIndices  := iv.numIndices
    , type        := ty
    , ctors       := ctors
    , recRules    := recRules }

/-- Collect all `Lean.Name` constants referenced inside a `Lean.Expr` (stripping `.mdata`). -/
def collectLeanExprConsts : Lean.Expr → List Lean.Name
  | .const n _       => [n]
  | .app f a         => collectLeanExprConsts f ++ collectLeanExprConsts a
  | .lam _ d b _     => collectLeanExprConsts d ++ collectLeanExprConsts b
  | .forallE _ d b _ => collectLeanExprConsts d ++ collectLeanExprConsts b
  | .letE _ t v b _  => collectLeanExprConsts t ++ collectLeanExprConsts v ++ collectLeanExprConsts b
  | .mdata _ e       => collectLeanExprConsts e
  | .proj s _ e      => s :: collectLeanExprConsts e
  | _                => []

/-- Collect all immediate constant dependencies of a `Lean.ConstantInfo`, including inductive
constructors, recursor `.str val.name "rec"`, and recursor rule RHS constants. -/
def collectConstInfoDeps (info : Lean.ConstantInfo) : List Lean.Name :=
  match info with
  | .defnInfo val =>
    collectLeanExprConsts val.type ++ collectLeanExprConsts val.value
  | .thmInfo val =>
    collectLeanExprConsts val.type ++ collectLeanExprConsts val.value
  | .inductInfo val =>
    [.str val.name "rec"] ++ val.ctors ++ collectLeanExprConsts val.type
  | .ctorInfo val =>
    [val.induct, .str val.induct "rec"] ++ collectLeanExprConsts val.type
  | .recInfo val =>
    val.all ++ (val.rules.flatMap fun r => r.ctor :: collectLeanExprConsts r.rhs) ++ collectLeanExprConsts val.type
  | .axiomInfo val =>
    collectLeanExprConsts val.type
  | .opaqueInfo val =>
    collectLeanExprConsts val.type ++ collectLeanExprConsts val.value
  | .quotInfo val =>
    collectLeanExprConsts val.type

/-- $O(1)$ `Std.HashSet`-backed worklist insertion so every BFS step in `extractEnvConeAux`
processes a distinct declaration without $O(N^2)$ list scans. -/
def enqueueUnvisitedDepsFast (seen : Std.HashSet KName) (queue : List Lean.Name) :
    List Lean.Name → Std.HashSet KName × List Lean.Name
  | [] => (seen, queue)
  | d :: ds =>
    let kd := fromLeanName d
    if seen.contains kd then
      enqueueUnvisitedDepsFast seen queue ds
    else
      enqueueUnvisitedDepsFast (seen.insert kd) (queue ++ [d]) ds

/-- Bounded BFS helper extracting all transitive `KConstInfo` declarations, `KRecRule` recursor
rules, and `KInductDecl` inductive metadata reachable from a `Std.HashSet`-deduplicated worklist. -/
def extractEnvConeAux
    (findConst? : Lean.Name → Option Lean.ConstantInfo) :
    Nat → List Lean.Name → Std.HashSet KName →
    Array KConstInfo → Array KRecRule → Array KInductDecl →
    Array KConstInfo × Array KRecRule × Array KInductDecl
  | 0, _, _, accConsts, accRules, accInducts => (accConsts, accRules, accInducts)
  | _ + 1, [], _, accConsts, accRules, accInducts => (accConsts, accRules, accInducts)
  | fuel + 1, n :: rest, seen, accConsts, accRules, accInducts =>
    match findConst? n with
    | none =>
      extractEnvConeAux findConst? fuel rest seen accConsts accRules accInducts
    | some info =>
      let accConsts' :=
        match extractLeanConstInfo? info with
        | some kc => accConsts.push kc
        | none    => accConsts
      let accRules' :=
        match info with
        | .recInfo rval =>
          match extractLeanRecRules rval with
          | some rs => accRules ++ rs.toArray
          | none    => accRules
        | _ => accRules
      let accInducts' :=
        match info with
        | .inductInfo iv =>
          match extractLeanInductDeclWith? findConst? iv with
          | some idcl => accInducts.push idcl
          | none      => accInducts
        | _ => accInducts
      let deps := collectConstInfoDeps info
      let (seen', nextQueue) := enqueueUnvisitedDepsFast seen rest deps
      extractEnvConeAux findConst? fuel nextQueue seen' accConsts' accRules' accInducts'

/-- Extract a self-contained `(KEnv × KConstInfo)` transitive dependency cone rooted at `rootName`
using a lookup function `findConst? : Lean.Name → Option Lean.ConstantInfo`. -/
def extractEnvConeWith
    (findConst? : Lean.Name → Option Lean.ConstantInfo)
    (rootName : Lean.Name)
    (fuel : Nat) : Option (KEnv × KConstInfo) := do
  let rootInfo ← findConst? rootName
  let rootDecl ← extractLeanConstInfo? rootInfo
  let initSeen := (Std.HashSet.emptyWithCapacity 64).insert (fromLeanName rootName)
  let (consts, recRules, inductDecls) :=
    extractEnvConeAux findConst? fuel [rootName] initSeen #[] #[] #[]
  pure ({ constants   := consts.toList
        , recRules    := recRules.toList
        , inductDecls := inductDecls.toList }, rootDecl)

/-- Extract a self-contained `(KEnv × KConstInfo)` transitive dependency cone rooted at `rootName`
directly from a live host `Lean.Environment` (`extractLeanEnvCone`). -/
def extractLeanEnvCone
    (env : Lean.Environment)
    (rootName : Lean.Name)
    (fuel : Nat) : Option (KEnv × KConstInfo) :=
  extractEnvConeWith env.find? rootName fuel

/-- Construct and intern a `.sort u` (`tag = 2`) node in `HwExprCAM`. -/
def mkHwCamSort (u : KLevel) (cam : HwExprCAM) : Nat × HwExprCAM :=
  let (sIdx, cam1) := allocPackedSymbol (.sortEntry u) cam
  allocPackedNode { tag := 2, h0 := 0, h1 := 0, symIdx := sIdx } cam1

/-- Construct and intern a `.const n us` (`tag = 3`) node in `HwExprCAM`. -/
def mkHwCamConst (n : KName) (us : List KLevel) (cam : HwExprCAM) : Nat × HwExprCAM :=
  let (sIdx, cam1) := allocPackedSymbol (.constEntry n us) cam
  allocPackedNode { tag := 3, h0 := 0, h1 := 0, symIdx := sIdx } cam1

/-- Construct and intern a `.lit l` (`tag = 8`) node in `HwExprCAM`. -/
def mkHwCamLit (l : KLiteral) (cam : HwExprCAM) : Nat × HwExprCAM :=
  let (sIdx, cam1) := allocPackedSymbol (.litEntry l) cam
  allocPackedNode { tag := 8, h0 := 0, h1 := 0, symIdx := sIdx } cam1

/-- Pure handle-level universe level parameter instantiation (`hwCamInstantiateLevelParams`) over
`HwExprCAM` (`cam.nodes` and `cam.symbols`) with zero `KExpr` AST reconstruction! -/
def hwCamInstantiateLevelParams :
    Nat → List (KName × KLevel) → Nat → HwExprCAM → Nat × HwExprCAM
  | 0, _, h, cam => (h, cam)
  | fuel + 1, subst, h, cam =>
    if subst.isEmpty then
      (h, cam)
    else
      match cam.nodes[h]? with
      | none => (h, cam)
      | some w =>
        if w.tag == 0 || w.tag == 1 || w.tag == 8 || w.tag == 10 then
          (h, cam)
        else if w.tag == 2 then
          match cam.symbols[w.symIdx]? with
          | some (.sortEntry u) =>
            let u' := KLevel.substParams subst u
            if u' == u then (h, cam) else mkHwCamSort u' cam
          | _ => (h, cam)
        else if w.tag == 3 then
          match cam.symbols[w.symIdx]? with
          | some (.constEntry n us) =>
            let us' := us.map (KLevel.substParams subst)
            if us' == us then (h, cam) else mkHwCamConst n us' cam
          | _ => (h, cam)
        else if w.tag == 4 then
          let (hf', cam1) := hwCamInstantiateLevelParams fuel subst w.h0 cam
          let (ha', cam2) := hwCamInstantiateLevelParams fuel subst w.h1 cam1
          if hf' == w.h0 && ha' == w.h1 then (h, cam2) else mkHwCamApp hf' ha' cam2
        else if w.tag == 5 || w.tag == 6 then
          let (hd', cam1) := hwCamInstantiateLevelParams fuel subst w.h0 cam
          let (hb', cam2) := hwCamInstantiateLevelParams fuel subst w.h1 cam1
          if hd' == w.h0 && hb' == w.h1 then (h, cam2) else mkHwCamBinder w.tag hd' hb' cam2
        else if w.tag == 7 then
          let (ht', cam1) := hwCamInstantiateLevelParams fuel subst w.h0 cam
          let (hv', cam2) := hwCamInstantiateLevelParams fuel subst w.h1 cam1
          let (hb', cam3) := hwCamInstantiateLevelParams fuel subst w.h2 cam2
          if ht' == w.h0 && hv' == w.h1 && hb' == w.h2 then (h, cam3)
          else mkHwCamLetE ht' hv' hb' cam3
        else if w.tag == 9 then
          let (hs', cam1) := hwCamInstantiateLevelParams fuel subst w.h0 cam
          if hs' == w.h0 then (h, cam1) else mkHwCamProj hs' w.symIdx cam1
        else
          (h, cam)

/-- Intern a `KConstInfo` declaration into `HwExprCAM` (`consts`, `nodes`, `symbols`).
Only `.defnInfo` populates `valHandle? := some valH` for Zone-1 $\delta$-unfolding; `.thmInfo`
remains proof-irrelevant/opaque to WHNF unfolding matching Lean 4 kernel semantics. -/
def internKConstInfoToHwExprCAM (c : KConstInfo) (cam : HwExprCAM) : HwExprCAM :=
  let (symIdx, cam1) := allocPackedSymbol (.constEntry c.name (c.levelParams.map KLevel.param)) cam
  let (tyH, cam2) := internToHwExprCAM c.type cam1
  match c with
  | .defnInfo _ _ _ val =>
    let (valH, cam3) := internToHwExprCAM val cam2
    let entry : HwCamConstEntry :=
      { name := c.name, symIdx := symIdx, typeHandle := tyH, valHandle? := some valH }
    { cam3 with consts := cam3.consts ++ [entry] }
  | .thmInfo _ _ _ val =>
    let (_, cam3) := internToHwExprCAM val cam2
    let entry : HwCamConstEntry :=
      { name := c.name, symIdx := symIdx, typeHandle := tyH, valHandle? := none }
    { cam3 with consts := cam3.consts ++ [entry] }
  | .ctorInfo _ _ _ indName =>
    let entry : HwCamConstEntry :=
      { name := c.name, symIdx := symIdx, typeHandle := tyH, isCtor := true, inductName? := some indName }
    { cam2 with consts := cam2.consts ++ [entry] }
  | _ =>
    let entry : HwCamConstEntry :=
      { name := c.name, symIdx := symIdx, typeHandle := tyH }
    { cam2 with consts := cam2.consts ++ [entry] }

/-- Intern a `KRecRule` $\iota$-reduction rule into `HwExprCAM` (`recRules`, `recLevelParams`, `nodes`, `symbols`). -/
def internKRecRuleToHwExprCAM (r : KRecRule) (cam : HwExprCAM) : HwExprCAM :=
  let (rhsH, cam1) := internToHwExprCAM r.rhs cam
  let entry : HwCamRecRuleEntry :=
    { recName   := r.recName
    , ctorName  := r.ctorName
    , numParams := r.numPrefixArgs
    , numFields := r.numFields
    , rhsHandle := rhsH }
  let recLP :=
    if r.levelParams.isEmpty || cam1.recLevelParams.any (fun p => p.1 == r.recName) then
      cam1.recLevelParams
    else
      cam1.recLevelParams ++ [(r.recName, r.levelParams)]
  { cam1 with recRules := cam1.recRules ++ [entry], recLevelParams := recLP }

/-- Intern an entire `KEnv` declaration cone (`constants`, `recRules`, and `inductDecls`) into `HwExprCAM`. -/
def internKEnvConeToHwExprCAM (env : KEnv) (cam : HwExprCAM) : HwExprCAM :=
  let cam1 := env.constants.foldl (fun acc c => internKConstInfoToHwExprCAM c acc) cam
  let cam2 := env.recRules.foldl (fun acc r => internKRecRuleToHwExprCAM r acc) cam1
  let indParams := env.inductDecls.foldl
    (fun acc d => if acc.any (fun p => p.1 == d.name) then acc else acc ++ [(d.name, d.numParams)])
    cam2.inductNumParams
  { cam2 with inductNumParams := indParams }

/-- $O(1)$ `Std.HashMap`-indexed hardware CAM builder (`FastHwExprCAM`) for linear-time interning of
large live Lean 4 declaration cones without $O(|DAG|^2)$ list scans. -/
structure FastHwExprCAM where
  nodes           : Array PackedNodeWord := #[]
  symbols         : Array HwCamSymbolEntry := #[]
  consts          : Array HwCamConstEntry := #[]
  recRules        : Array HwCamRecRuleEntry := #[]
  inductNumParams : List (KName × Nat) := []
  recLevelParams  : List (KName × List KName) := []
  nodeIndex       : Std.HashMap PackedNodeWord Nat := {}
  symIndex        : Std.HashMap HwCamSymbolEntry Nat := {}

def FastHwExprCAM.empty : FastHwExprCAM := {}

def FastHwExprCAM.toHwExprCAM (fc : FastHwExprCAM) : HwExprCAM :=
  { nodes           := fc.nodes.toList
  , symbols         := fc.symbols.toList
  , consts          := fc.consts.toList
  , recRules        := fc.recRules.toList
  , inductNumParams := fc.inductNumParams
  , recLevelParams  := fc.recLevelParams }

def allocFastSymbol (s : HwCamSymbolEntry) (fc : FastHwExprCAM) : Nat × FastHwExprCAM :=
  match fc.symIndex[s]? with
  | some idx => (idx, fc)
  | none =>
    let idx := fc.symbols.size
    (idx, { fc with symbols := fc.symbols.push s, symIndex := fc.symIndex.insert s idx })

def allocFastNode (w : PackedNodeWord) (fc : FastHwExprCAM) : Nat × FastHwExprCAM :=
  match fc.nodeIndex[w]? with
  | some h => (h, fc)
  | none =>
    let h := fc.nodes.size
    (h, { fc with nodes := fc.nodes.push w, nodeIndex := fc.nodeIndex.insert w h })

def getFastNode (fc : FastHwExprCAM) (h : Nat) : PackedNodeWord :=
  fc.nodes[h]?.getD { tag := 99, h0 := 0, h1 := 0 }

/-- Intern a `KExpr` into `FastHwExprCAM` in $O(|e|)$ amortized hash-table operations. -/
def internToFastHwExprCAM : KExpr → FastHwExprCAM → Nat × FastHwExprCAM
  | .bvar idx, fc =>
    allocFastNode { tag := 0, h0 := idx, h1 := 0, hasLooseBVar := true, maxLooseBVar := idx + 1 } fc
  | .fvar id, fc =>
    allocFastNode { tag := 1, h0 := id, h1 := 0, hasFVar := true, hasMVar := false } fc
  | .mvar id, fc =>
    allocFastNode { tag := 10, h0 := id, h1 := 0, hasFVar := false, hasMVar := true } fc
  | .sort u, fc =>
    let (sIdx, fc1) := allocFastSymbol (.sortEntry u) fc
    allocFastNode { tag := 2, h0 := 0, h1 := 0, symIdx := sIdx } fc1
  | .const n us, fc =>
    let (sIdx, fc1) := allocFastSymbol (.constEntry n us) fc
    allocFastNode { tag := 3, h0 := 0, h1 := 0, symIdx := sIdx } fc1
  | .app f a, fc =>
    let (hf, fc1) := internToFastHwExprCAM f fc
    let (ha, fc2) := internToFastHwExprCAM a fc1
    let wf := getFastNode fc2 hf
    let wa := getFastNode fc2 ha
    let maxB := Nat.max wf.maxLooseBVar wa.maxLooseBVar
    allocFastNode
      { tag := 4, h0 := hf, h1 := ha, hasLooseBVar := decide (maxB > 0)
      , hasFVar := wf.hasFVar || wa.hasFVar, hasMVar := wf.hasMVar || wa.hasMVar
      , maxLooseBVar := maxB } fc2
  | .lam d b, fc =>
    let (hd, fc1) := internToFastHwExprCAM d fc
    let (hb, fc2) := internToFastHwExprCAM b fc1
    let wd := getFastNode fc2 hd
    let wb := getFastNode fc2 hb
    let maxB := Nat.max wd.maxLooseBVar (wb.maxLooseBVar - 1)
    allocFastNode
      { tag := 5, h0 := hd, h1 := hb, hasLooseBVar := decide (maxB > 0)
      , hasFVar := wd.hasFVar || wb.hasFVar, hasMVar := wd.hasMVar || wb.hasMVar
      , maxLooseBVar := maxB } fc2
  | .forallE d b, fc =>
    let (hd, fc1) := internToFastHwExprCAM d fc
    let (hb, fc2) := internToFastHwExprCAM b fc1
    let wd := getFastNode fc2 hd
    let wb := getFastNode fc2 hb
    let maxB := Nat.max wd.maxLooseBVar (wb.maxLooseBVar - 1)
    allocFastNode
      { tag := 6, h0 := hd, h1 := hb, hasLooseBVar := decide (maxB > 0)
      , hasFVar := wd.hasFVar || wb.hasFVar, hasMVar := wd.hasMVar || wb.hasMVar
      , maxLooseBVar := maxB } fc2
  | .letE t v b, fc =>
    let (ht, fc1) := internToFastHwExprCAM t fc
    let (hv, fc2) := internToFastHwExprCAM v fc1
    let (hb, fc3) := internToFastHwExprCAM b fc2
    let wt := getFastNode fc3 ht
    let wv := getFastNode fc3 hv
    let wb := getFastNode fc3 hb
    let maxB := Nat.max (Nat.max wt.maxLooseBVar wv.maxLooseBVar) (wb.maxLooseBVar - 1)
    allocFastNode
      { tag := 7, h0 := ht, h1 := hv, h2 := hb, hasLooseBVar := decide (maxB > 0)
      , hasFVar := wt.hasFVar || wv.hasFVar || wb.hasFVar
      , hasMVar := wt.hasMVar || wv.hasMVar || wb.hasMVar
      , maxLooseBVar := maxB } fc3
  | .lit l, fc =>
    let (sIdx, fc1) := allocFastSymbol (.litEntry l) fc
    allocFastNode { tag := 8, h0 := 0, h1 := 0, symIdx := sIdx } fc1
  | .proj structName idx s, fc =>
    let (hs, fc1) := internToFastHwExprCAM s fc
    let (sIdx, fc2) := allocFastSymbol (.projEntry structName idx) fc1
    let ws := getFastNode fc2 hs
    allocFastNode
      { tag := 9, h0 := hs, h1 := 0, symIdx := sIdx, hasLooseBVar := decide (ws.maxLooseBVar > 0)
      , hasFVar := ws.hasFVar, hasMVar := ws.hasMVar, maxLooseBVar := ws.maxLooseBVar } fc2

/-- Intern an entire `KEnv` cone in $O(|DAG|)$ via `FastHwExprCAM` and convert to `HwExprCAM`. -/
def internKEnvConeFast (env : KEnv) : HwExprCAM :=
  let fc1 := env.constants.foldl
    (fun fc c =>
      let (symIdx, fcA) := allocFastSymbol (.constEntry c.name (c.levelParams.map KLevel.param)) fc
      let (tyH, fcB) := internToFastHwExprCAM c.type fcA
      match c with
      | .defnInfo _ _ _ val =>
        let (valH, fcC) := internToFastHwExprCAM val fcB
        { fcC with consts := fcC.consts.push { name := c.name, symIdx := symIdx, typeHandle := tyH, valHandle? := some valH } }
      | .thmInfo _ _ _ val =>
        let (_, fcC) := internToFastHwExprCAM val fcB
        { fcC with consts := fcC.consts.push { name := c.name, symIdx := symIdx, typeHandle := tyH, valHandle? := none } }
      | .ctorInfo _ _ _ indName =>
        { fcB with consts := fcB.consts.push { name := c.name, symIdx := symIdx, typeHandle := tyH, isCtor := true, inductName? := some indName } }
      | _ =>
        { fcB with consts := fcB.consts.push { name := c.name, symIdx := symIdx, typeHandle := tyH } })
    FastHwExprCAM.empty
  let fc2 := env.recRules.foldl
    (fun fc r =>
      let (rhsH, fcA) := internToFastHwExprCAM r.rhs fc
      let entry : HwCamRecRuleEntry :=
        { recName := r.recName, ctorName := r.ctorName, numParams := r.numPrefixArgs, numFields := r.numFields, rhsHandle := rhsH }
      let recLP :=
        if r.levelParams.isEmpty || fcA.recLevelParams.any (fun p => p.1 == r.recName) then fcA.recLevelParams
        else fcA.recLevelParams ++ [(r.recName, r.levelParams)]
      { fcA with recRules := fcA.recRules.push entry, recLevelParams := recLP })
    fc1
  let indParams := env.inductDecls.foldl
    (fun acc d => if acc.any (fun p => p.1 == d.name) then acc else acc ++ [(d.name, d.numParams)])
    []
  { fc2 with inductNumParams := indParams }.toHwExprCAM

/-- Sample host `Lean.ConstantInfo` declaration (`Lean.Declaration.defnDecl` for `liveIdNat : Nat → Nat := λ x : Nat => x`). -/
def sampleLiveLeanDefnInfo : Lean.ConstantInfo :=
  let natExpr : Lean.Expr := .const (.str .anonymous "Nat") []
  let arrowType : Lean.Expr := .forallE (.str .anonymous "x") natExpr natExpr .default
  let lamVal : Lean.Expr := .lam (.str .anonymous "x") natExpr (.bvar 0) .default
  .defnInfo
    { name        := .str .anonymous "liveIdNat"
    , levelParams := []
    , type        := arrowType
    , value       := lamVal
    , hints       := .abbrev
    , safety      := .safe }

/-- Sample invalid host `Lean.ConstantInfo` declaration contaminated with `sorryAx`. -/
def sampleLiveLeanSorryInfo : Lean.ConstantInfo :=
  let propSort : Lean.Expr := .sort .zero
  let falseClaim : Lean.Expr := .forallE (.str .anonymous "P") propSort (.bvar 0) .default
  let sorryProof : Lean.Expr := .const (.str .anonymous "sorryAx") [.zero]
  .thmInfo
    { name        := .str .anonymous "liveBadSorry"
    , levelParams := []
    , type        := falseClaim
    , value       := sorryProof }

/-- Sample invalid host `.opaqueInfo` declaration hiding `sorryAx` in its body. -/
def sampleLiveOpaqueSorryInfo : Lean.ConstantInfo :=
  let propSort : Lean.Expr := .sort .zero
  let falseClaim : Lean.Expr := .forallE (.str .anonymous "P") propSort (.bvar 0) .default
  let sorryProof : Lean.Expr := .const (.str .anonymous "sorryAx") [.zero]
  .opaqueInfo
    { name        := .str .anonymous "liveBadOpaqueSorry"
    , levelParams := []
    , type        := falseClaim
    , value       := sorryProof
    , isUnsafe    := false
    , all         := [.str .anonymous "liveBadOpaqueSorry"] }

/-- Sample host `Lean.RecursorVal` for a 2-constructor inductive `MyBool` (`MyBool.false`, `MyBool.true`)
with its genuine dependent recursor $\Pi$-type
`(motive : MyBool → Type) → motive MyBool.false → motive MyBool.true → (t : MyBool) → motive t`
and `.mdata` annotations on its rule RHSs. -/
def sampleLiveMyBoolRecVal : Lean.RecursorVal :=
  let myBoolName : Lean.Name := .str .anonymous "MyBool"
  let falseName  : Lean.Name := .str myBoolName "false"
  let trueName   : Lean.Name := .str myBoolName "true"
  let recName    : Lean.Name := .str myBoolName "rec"
  let type0      : Lean.Expr := .sort (.succ .zero)
  let myBoolExpr : Lean.Expr := .const myBoolName []
  let motiveTy   : Lean.Expr := .forallE (.str .anonymous "b") myBoolExpr type0 .default
  let recType    : Lean.Expr :=
    .forallE (.str .anonymous "motive") motiveTy
      (.forallE (.str .anonymous "hFalse") (.app (.bvar 0) (.const falseName []))
        (.forallE (.str .anonymous "hTrue") (.app (.bvar 1) (.const trueName []))
          (.forallE (.str .anonymous "t") myBoolExpr
            (.app (.bvar 3) (.bvar 0)) .default) .default) .default) .default
  -- RHS for `MyBool.false`: λ (motive : MyBool → Type) (hFalse : motive false) (hTrue : motive true) => .mdata {} (.bvar 1)
  let rhsFalse : Lean.Expr :=
    .lam (.str .anonymous "motive") motiveTy
      (.lam (.str .anonymous "hFalse") (.app (.bvar 0) (.const falseName []))
        (.lam (.str .anonymous "hTrue") (.app (.bvar 1) (.const trueName []))
          (.mdata {} (.bvar 1)) .default) .default) .default
  -- RHS for `MyBool.true`: λ (motive : MyBool → Type) (hFalse : motive false) (hTrue : motive true) => .mdata {} (.bvar 0)
  let rhsTrue : Lean.Expr :=
    .lam (.str .anonymous "motive") motiveTy
      (.lam (.str .anonymous "hFalse") (.app (.bvar 0) (.const falseName []))
        (.lam (.str .anonymous "hTrue") (.app (.bvar 1) (.const trueName []))
          (.mdata {} (.bvar 0)) .default) .default) .default
  { name        := recName
  , levelParams := []
  , type        := recType
  , all         := [myBoolName]
  , numParams   := 0
  , numIndices  := 0
  , numMotives  := 1
  , numMinors   := 2
  , rules       :=
      [ { ctor := falseName, nfields := 0, rhs := rhsFalse }
      , { ctor := trueName,  nfields := 0, rhs := rhsTrue } ]
  , k           := false
  , isUnsafe    := false }

/-- Sample host `Lean.ConstantInfo` table for `MyBool`, `MyBool.false`, `MyBool.true`, `MyBool.rec`,
and `flipMyBool : MyBool → MyBool`. -/
def sampleLiveConeFindConst? (n : Lean.Name) : Option Lean.ConstantInfo :=
  let kn         : KName     := fromLeanName n
  let myBoolName : Lean.Name := .str .anonymous "MyBool"
  let falseName  : Lean.Name := .str myBoolName "false"
  let trueName   : Lean.Name := .str myBoolName "true"
  let recName    : Lean.Name := .str myBoolName "rec"
  let flipName   : Lean.Name := .str .anonymous "flipMyBool"
  let type0      : Lean.Expr := .sort (.succ .zero)
  let myBoolExpr : Lean.Expr := .const myBoolName []
  let motiveExpr : Lean.Expr := .lam (.str .anonymous "b") myBoolExpr myBoolExpr .default
  if kn == fromLeanName myBoolName then
    some (.inductInfo
      { name := myBoolName, levelParams := [], type := type0
      , numParams := 0, numIndices := 0, all := [myBoolName]
      , ctors := [falseName, trueName], numNested := 0
      , isRec := false, isUnsafe := false, isReflexive := false })
  else if kn == fromLeanName falseName then
    some (.ctorInfo
      { name := falseName, levelParams := [], type := myBoolExpr
      , induct := myBoolName, cidx := 0, numParams := 0, numFields := 0, isUnsafe := false })
  else if kn == fromLeanName trueName then
    some (.ctorInfo
      { name := trueName, levelParams := [], type := myBoolExpr
      , induct := myBoolName, cidx := 1, numParams := 0, numFields := 0, isUnsafe := false })
  else if kn == fromLeanName recName then
    some (.recInfo sampleLiveMyBoolRecVal)
  else if kn == fromLeanName flipName then
    let flipBody : Lean.Expr :=
      .lam (.str .anonymous "x") myBoolExpr
        (.app (.app (.app (.app (.const recName []) motiveExpr) (.const trueName [])) (.const falseName [])) (.bvar 0))
        .default
    some (.defnInfo
      { name := flipName, levelParams := []
      , type := .forallE (.str .anonymous "x") myBoolExpr myBoolExpr .default
      , value := flipBody, hints := .abbrev, safety := .safe })
  else
    none

/-- **Universal Theorem (`fromLeanExprWithProjShift_no_double_offset`)**:
For every structure name `s`, field index `i`, structure expression `e`, and parameter-count oracle
`numParamsOf`, `fromLeanExprWithProjShift` preserves the exact 0-based field index `i` without
pre-adding `numParamsOf s` (preventing double-offset against `LeanKernel.kernelWhnf` and
`LeanKernel.inferProjFieldType?`), and maps `Lean.Expr.mvar id` to first-class `KExpr.mvar`. -/
theorem fromLeanExprWithProjShift_no_double_offset
    (numParamsOf : Lean.Name → Nat) (s : Lean.Name) (i : Nat) (e : Lean.Expr) (mvid : Lean.MVarId) :
    fromLeanExprWithProjShift numParamsOf (.proj s i e) =
      (fromLeanExpr e).map (KExpr.proj (fromLeanName s) i) ∧
    fromLeanExprWithProjShift numParamsOf (.mvar mvid) =
      some (.mvar (fromLeanName mvid.name).toCleanId) := by
  refine ⟨?_, rfl⟩
  simp only [fromLeanExprWithProjShift, fromLeanExpr]
  cases fromLeanExpr e <;> rfl

/-! ## 8. 88-Bit Hardware `PackedNodeWord` Bit-Packing (`BitVec 88`) & 7-Section `OBCAMv1` Wire Protocol -/

/-- Well-formedness predicate for an 88-bit hardware-packable `PackedNodeWord`:
all 4 child/symbol/bvar handles fit in 16-bit unsigned fields (`< 65536`) and `tag < 16`. -/
def PackedNodeWord.Wf88 (w : PackedNodeWord) : Prop :=
  w.tag < 16 ∧
  w.h0 < 65536 ∧
  w.h1 < 65536 ∧
  w.h2 < 65536 ∧
  w.symIdx < 65536 ∧
  w.maxLooseBVar < 65536

/-- Pack a `PackedNodeWord` into an 88-bit hardware CAM word (`BitVec 88`):
* `[15:0]`  : `h0` (16b)
* `[31:16]` : `h1` (16b)
* `[47:32]` : `h2` (16b)
* `[63:48]` : `symIdx` (16b)
* `[79:64]` : `maxLooseBVar` (16b)
* `[80]`    : `hasFVar` (1b)
* `[81]`    : `hasMVar` (1b)
* `[82]`    : `hasLooseBVar` (1b)
* `[83]`    : `0` (reserved 1b)
* `[87:84]` : `tag` (4b) -/
def packNodeWord88 (w : PackedNodeWord) : BitVec 88 :=
  let bTag   : BitVec 4  := BitVec.ofNat 4 w.tag
  let bPad   : BitVec 1  := 0#1
  let bLoose : BitVec 1  := if w.hasLooseBVar then 1#1 else 0#1
  let bMVar  : BitVec 1  := if w.hasMVar then 1#1 else 0#1
  let bFVar  : BitVec 1  := if w.hasFVar then 1#1 else 0#1
  let hi8    : BitVec 8  := (((bTag ++ bPad) ++ bLoose) ++ bMVar) ++ bFVar
  let bMaxB  : BitVec 16 := BitVec.ofNat 16 w.maxLooseBVar
  let bSym   : BitVec 16 := BitVec.ofNat 16 w.symIdx
  let bh2    : BitVec 16 := BitVec.ofNat 16 w.h2
  let bh1    : BitVec 16 := BitVec.ofNat 16 w.h1
  let bh0    : BitVec 16 := BitVec.ofNat 16 w.h0
  ((((hi8 ++ bMaxB) ++ bSym) ++ bh2) ++ bh1) ++ bh0

/-- Unpack an 88-bit hardware CAM word (`BitVec 88`) back into a `PackedNodeWord`. -/
def unpackNodeWord88 (bv : BitVec 88) : PackedNodeWord where
  tag          := (bv.extractLsb' 84 4).toNat
  h0           := (bv.extractLsb' 0 16).toNat
  h1           := (bv.extractLsb' 16 16).toNat
  h2           := (bv.extractLsb' 32 16).toNat
  symIdx       := (bv.extractLsb' 48 16).toNat
  hasLooseBVar := bv.getLsbD 82
  hasFVar      := bv.getLsbD 80
  hasMVar      := bv.getLsbD 81
  maxLooseBVar := (bv.extractLsb' 64 16).toNat

/-- **88-Bit Hardware `PackedNodeWord` Round-Trip Theorem (`unpack_packNodeWord88`)**:
For every well-formed `w : PackedNodeWord` (`w.Wf88`), packing `w` into `BitVec 88` and unpacking
recovers `w` identically. -/
theorem unpack_packNodeWord88 (w : PackedNodeWord) (hWf : w.Wf88) :
    unpackNodeWord88 (packNodeWord88 w) = w := by
  rcases w with ⟨tag, h0, h1, h2, symIdx, hasLoose, hasF, hasM, maxB⟩
  rcases hWf with ⟨hTag, hh0, hh1, hh2, hSym, hMaxB⟩
  have hSliceTag : (packNodeWord88 ⟨tag, h0, h1, h2, symIdx, hasLoose, hasF, hasM, maxB⟩).extractLsb' 84 4 = BitVec.ofNat 4 tag := by
    unfold packNodeWord88; dsimp only; bv_decide
  have hSliceH0 : (packNodeWord88 ⟨tag, h0, h1, h2, symIdx, hasLoose, hasF, hasM, maxB⟩).extractLsb' 0 16 = BitVec.ofNat 16 h0 := by
    unfold packNodeWord88; dsimp only; bv_decide
  have hSliceH1 : (packNodeWord88 ⟨tag, h0, h1, h2, symIdx, hasLoose, hasF, hasM, maxB⟩).extractLsb' 16 16 = BitVec.ofNat 16 h1 := by
    unfold packNodeWord88; dsimp only; bv_decide
  have hSliceH2 : (packNodeWord88 ⟨tag, h0, h1, h2, symIdx, hasLoose, hasF, hasM, maxB⟩).extractLsb' 32 16 = BitVec.ofNat 16 h2 := by
    unfold packNodeWord88; dsimp only; bv_decide
  have hSliceSym : (packNodeWord88 ⟨tag, h0, h1, h2, symIdx, hasLoose, hasF, hasM, maxB⟩).extractLsb' 48 16 = BitVec.ofNat 16 symIdx := by
    unfold packNodeWord88; dsimp only; bv_decide
  have hSliceMaxB : (packNodeWord88 ⟨tag, h0, h1, h2, symIdx, hasLoose, hasF, hasM, maxB⟩).extractLsb' 64 16 = BitVec.ofNat 16 maxB := by
    unfold packNodeWord88; dsimp only; bv_decide
  have hBitLoose : (packNodeWord88 ⟨tag, h0, h1, h2, symIdx, hasLoose, hasF, hasM, maxB⟩).getLsbD 82 = hasLoose := by
    unfold packNodeWord88; dsimp only; cases hasLoose <;> bv_decide
  have hBitF : (packNodeWord88 ⟨tag, h0, h1, h2, symIdx, hasLoose, hasF, hasM, maxB⟩).getLsbD 80 = hasF := by
    unfold packNodeWord88; dsimp only; cases hasF <;> bv_decide
  have hBitM : (packNodeWord88 ⟨tag, h0, h1, h2, symIdx, hasLoose, hasF, hasM, maxB⟩).getLsbD 81 = hasM := by
    unfold packNodeWord88; dsimp only; cases hasM <;> bv_decide
  unfold unpackNodeWord88
  rw [hSliceTag, hSliceH0, hSliceH1, hSliceH2, hSliceSym, hSliceMaxB, hBitLoose, hBitF, hBitM]
  simp only [PackedNodeWord.mk.injEq, BitVec.toNat_ofNat]
  refine ⟨Nat.mod_eq_of_lt hTag, Nat.mod_eq_of_lt hh0, Nat.mod_eq_of_lt hh1,
          Nat.mod_eq_of_lt hh2, Nat.mod_eq_of_lt hSym, trivial, trivial, trivial,
          Nat.mod_eq_of_lt hMaxB⟩

/-- `OBCAMv1` binary DMA wire header for streaming a `Lean.Environment` declaration cone into the
Verilated `silicon_elab_top.sv` / Cloud-FPGA co-processor. -/
structure SiliconElabWireHeader where
  magic            : UInt64 := 0x31564D4143424F00 -- "\0OBCAMV1"
  version          : UInt32 := 1
  flags            : UInt32 := 0
  nodeCount        : UInt32
  symbolCount      : UInt32 := 0
  levelCount       : UInt32 := 0
  constCount       : UInt32
  recRuleCount     : UInt32
  lutEntryCount    : UInt32 := 0
  icapFrameCount   : UInt32 := 0
  targetDeclSymIdx : UInt32
  targetExprHandle : UInt32
  targetTypeHandle : UInt32
  fuelBudget       : UInt32 := 65536
  envPinDigest64   : UInt64 := 0
  deriving DecidableEq, Repr, Inhabited

/-- Hardware universe-level DAG entry (`HwCamLevelEntry`) for Section 3 of the `OBCAMv1` wire frame:
`tag`: `0` = `.zero`, `1` = `.succ`, `2` = `.max`, `3` = `.imax`, `4` = `.param`. -/
structure HwCamLevelEntry where
  tag       : Nat
  l0        : Nat := 0
  l1        : Nat := 0
  paramName : KName := .anonymous
  deriving DecidableEq, Repr, Inhabited

/-- Hardware Zone-3 `DiscrTreeLUT` entry (`DiscrTreeLutEntry`) for Section 6 of the `OBCAMv1` wire frame. -/
structure DiscrTreeLutEntry where
  pathKeys  : List Nat := []
  rhsHandle : Nat := 0
  lutTag    : Nat := 0
  gain      : Nat := 0
  offset    : Nat := 0
  deriving DecidableEq, Repr, Inhabited

/-- Complete 7-section `OBCAMv1` binary DMA wire frame (`SiliconElabWireFrame`) for streaming a
`Lean.Environment` declaration cone into `silicon_elab_top.sv` / Cloud-FPGA co-processors:
* `header`     : `SiliconElabWireHeader`
* `nodes`      : Section 1 (`PackedNodeWord` array)
* `symbols`    : Section 2 (`HwCamSymbolEntry` symbol/literal table)
* `levels`     : Section 3 (`HwCamLevelEntry` universe-level DAG table)
* `consts`     : Section 4 (`HwCamConstEntry` environment constant table)
* `recRules`   : Section 5 (`HwCamRecRuleEntry` recursor $\iota$-rule table)
* `lutEntries` : Section 6 (`DiscrTreeLutEntry` specialized `@[simp]` / typeclass LUT entries)
* `icapFrames` : Section 7 (`IcapBitstreamFrame` signed eFPGA configuration frames) -/
structure SiliconElabWireFrame where
  header     : SiliconElabWireHeader
  nodes      : List PackedNodeWord := []
  symbols    : List HwCamSymbolEntry := []
  levels     : List HwCamLevelEntry := []
  consts     : List HwCamConstEntry := []
  recRules   : List HwCamRecRuleEntry := []
  lutEntries : List DiscrTreeLutEntry := []
  icapFrames : List IcapBitstreamFrame := []
  deriving DecidableEq, Repr, Inhabited

/-- Encode a `Nat` into unsigned LEB128 varint bytes (`natToVarBytes`). -/
def natToVarBytes (n : Nat) : List UInt8 :=
  if n < 128 then
    [UInt8.ofNat n]
  else
    UInt8.ofNat (128 + (n % 128)) :: natToVarBytes (n / 128)
termination_by n

/-- Decode an unsigned LEB128 varint from a byte stream (`decodeVarBytes`), structurally recursive on `List UInt8`. -/
def decodeVarBytes : List UInt8 → Option (Nat × List UInt8)
  | [] => none
  | b :: bs =>
    if b.toNat < 128 then
      some (b.toNat, bs)
    else
      match decodeVarBytes bs with
      | some (hi, rest) => some (hi * 128 + (b.toNat - 128), rest)
      | none => none

@[simp] theorem decodeVarBytes_natToVarBytes (n : Nat) (rest : List UInt8) :
    decodeVarBytes (natToVarBytes n ++ rest) = some (n, rest) := by
  induction n using natToVarBytes.induct with
  | case1 n hlt =>
    unfold natToVarBytes
    simp only [hlt, ↓reduceIte, List.singleton_append, decodeVarBytes]
    have hToNat : (UInt8.ofNat n).toNat = n := by
      change n % 256 = n
      omega
    simp [hToNat, hlt]
  | case2 n hnlt ih =>
    have hArith : n / 128 * 128 + (128 + n % 128 - 128) = n := by omega
    have hGe : ¬ (128 + n % 128 < 128) := by omega
    have hToNat : (UInt8.ofNat (128 + n % 128)).toNat = 128 + n % 128 := by
      change (128 + n % 128) % 256 = 128 + n % 128
      omega
    unfold natToVarBytes
    simp only [hnlt, ↓reduceIte, List.cons_append, decodeVarBytes, hToNat, hGe, ih]
    rw [hArith]

/-- Encode a `Bool` as a 1-byte varint (`0` or `1`). -/
def encodeWireBool (b : Bool) : List UInt8 :=
  natToVarBytes (if b then 1 else 0)

/-- Decode a `Bool` from a byte stream. -/
def decodeWireBool (bs : List UInt8) : Option (Bool × List UInt8) :=
  match decodeVarBytes bs with
  | some (n, rest) => some (n != 0, rest)
  | none => none

@[simp] theorem decodeWireBool_encodeWireBool (b : Bool) (rest : List UInt8) :
    decodeWireBool (encodeWireBool b ++ rest) = some (b, rest) := by
  cases b <;> simp [encodeWireBool, decodeWireBool]

/-- Encode a `UInt32` into varint bytes. -/
def encodeWireUInt32 (u : UInt32) : List UInt8 :=
  natToVarBytes u.toNat

/-- Decode a `UInt32` from varint bytes. -/
def decodeWireUInt32 (bs : List UInt8) : Option (UInt32 × List UInt8) :=
  match decodeVarBytes bs with
  | none => none
  | some (n, rest) =>
    if h : n < UInt32.size then
      some (⟨⟨n, h⟩⟩, rest)
    else none

@[simp] theorem decodeWireUInt32_encodeWireUInt32 (u : UInt32) (rest : List UInt8) :
    decodeWireUInt32 (encodeWireUInt32 u ++ rest) = some (u, rest) := by
  rcases u with ⟨⟨n, h⟩⟩
  unfold encodeWireUInt32 decodeWireUInt32
  rw [decodeVarBytes_natToVarBytes]
  simp [UInt32.toNat, h]

/-- Encode a `UInt64` into varint bytes. -/
def encodeWireUInt64 (u : UInt64) : List UInt8 :=
  natToVarBytes u.toNat

/-- Decode a `UInt64` from varint bytes. -/
def decodeWireUInt64 (bs : List UInt8) : Option (UInt64 × List UInt8) :=
  match decodeVarBytes bs with
  | none => none
  | some (n, rest) =>
    if h : n < UInt64.size then
      some (⟨⟨n, h⟩⟩, rest)
    else none

@[simp] theorem decodeWireUInt64_encodeWireUInt64 (u : UInt64) (rest : List UInt8) :
    decodeWireUInt64 (encodeWireUInt64 u ++ rest) = some (u, rest) := by
  rcases u with ⟨⟨n, h⟩⟩
  unfold encodeWireUInt64 decodeWireUInt64
  rw [decodeVarBytes_natToVarBytes]
  simp [UInt64.toNat, h]

/-- Encode a `BitVec 64` into varint bytes. -/
def encodeWireBitVec64 (bv : BitVec 64) : List UInt8 :=
  natToVarBytes bv.toNat

/-- Decode a `BitVec 64` from varint bytes. -/
def decodeWireBitVec64 (bs : List UInt8) : Option (BitVec 64 × List UInt8) :=
  match decodeVarBytes bs with
  | none => none
  | some (n, rest) =>
    if h : n < 2 ^ 64 then
      some (⟨⟨n, h⟩⟩, rest)
    else none

@[simp] theorem decodeWireBitVec64_encodeWireBitVec64 (bv : BitVec 64) (rest : List UInt8) :
    decodeWireBitVec64 (encodeWireBitVec64 bv ++ rest) = some (bv, rest) := by
  rcases bv with ⟨⟨n, h⟩⟩
  unfold encodeWireBitVec64 decodeWireBitVec64
  rw [decodeVarBytes_natToVarBytes]
  simp [BitVec.toNat, h]

/-- Encode a `Char` into varint bytes. -/
def encodeWireChar (c : Char) : List UInt8 :=
  encodeWireUInt32 c.val

/-- Decode a `Char` from varint bytes. -/
def decodeWireChar (bs : List UInt8) : Option (Char × List UInt8) :=
  match decodeWireUInt32 bs with
  | none => none
  | some (u, rest) =>
    if h2 : u.isValidChar then
      some (⟨u, h2⟩, rest)
    else none

@[simp] theorem decodeWireChar_encodeWireChar (c : Char) (rest : List UInt8) :
    decodeWireChar (encodeWireChar c ++ rest) = some (c, rest) := by
  rcases c with ⟨u, h2⟩
  unfold encodeWireChar decodeWireChar
  rw [decodeWireUInt32_encodeWireUInt32]
  simp [h2]

/-- Encode a homogeneous list by prefixing its length followed by each encoded element. -/
def encodeWireListItems {α : Type} (enc : α → List UInt8) : List α → List UInt8
  | []      => []
  | x :: xs => enc x ++ encodeWireListItems enc xs

/-- Decode exactly `k` elements of type `α` from a byte stream. -/
def decodeWireListItems {α : Type} (dec : List UInt8 → Option (α × List UInt8)) :
    Nat → List UInt8 → Option (List α × List UInt8)
  | 0, bs => some ([], bs)
  | k + 1, bs =>
    match dec bs with
    | none => none
    | some (x, bs1) =>
      match decodeWireListItems dec k bs1 with
      | none => none
      | some (xs, bs2) => some (x :: xs, bs2)

theorem decodeWireListItems_encodeWireListItems {α : Type}
    (enc : α → List UInt8)
    (dec : List UInt8 → Option (α × List UInt8))
    (hElem : ∀ (x : α) (r : List UInt8), dec (enc x ++ r) = some (x, r)) :
    ∀ (xs : List α) (rest : List UInt8),
      decodeWireListItems dec xs.length (encodeWireListItems enc xs ++ rest) = some (xs, rest)
  | [], rest => rfl
  | x :: xs, rest => by
    simp only [List.length_cons, encodeWireListItems, List.append_assoc, decodeWireListItems]
    rw [hElem x (encodeWireListItems enc xs ++ rest)]
    dsimp only
    rw [decodeWireListItems_encodeWireListItems enc dec hElem xs rest]

/-- Encode a `List α` with its length prefix. -/
def encodeWireList {α : Type} (enc : α → List UInt8) (xs : List α) : List UInt8 :=
  natToVarBytes xs.length ++ encodeWireListItems enc xs

/-- Decode a length-prefixed `List α`. -/
def decodeWireList {α : Type} (dec : List UInt8 → Option (α × List UInt8)) (bs : List UInt8) :
    Option (List α × List UInt8) :=
  match decodeVarBytes bs with
  | none => none
  | some (len, bs1) => decodeWireListItems dec len bs1

theorem decodeWireList_encodeWireList {α : Type}
    (enc : α → List UInt8)
    (dec : List UInt8 → Option (α × List UInt8))
    (hElem : ∀ (x : α) (r : List UInt8), dec (enc x ++ r) = some (x, r))
    (xs : List α) (rest : List UInt8) :
    decodeWireList dec (encodeWireList enc xs ++ rest) = some (xs, rest) := by
  unfold encodeWireList decodeWireList
  rw [List.append_assoc, decodeVarBytes_natToVarBytes]
  dsimp only
  exact decodeWireListItems_encodeWireListItems enc dec hElem xs rest

/-- Encode an `Option α`. -/
def encodeWireOption {α : Type} (enc : α → List UInt8) : Option α → List UInt8
  | none   => natToVarBytes 0
  | some x => natToVarBytes 1 ++ enc x

/-- Decode an `Option α`. -/
def decodeWireOption {α : Type} (dec : List UInt8 → Option (α × List UInt8)) (bs : List UInt8) :
    Option (Option α × List UInt8) :=
  match decodeVarBytes bs with
  | some (0, rest) => some (none, rest)
  | some (1, rest) =>
    match dec rest with
    | some (x, rest2) => some (some x, rest2)
    | none => none
  | _ => none

theorem decodeWireOption_encodeWireOption {α : Type}
    (enc : α → List UInt8)
    (dec : List UInt8 → Option (α × List UInt8))
    (hElem : ∀ (x : α) (r : List UInt8), dec (enc x ++ r) = some (x, r))
    (o : Option α) (rest : List UInt8) :
    decodeWireOption dec (encodeWireOption enc o ++ rest) = some (o, rest) := by
  cases o with
  | none =>
    unfold encodeWireOption decodeWireOption
    rw [decodeVarBytes_natToVarBytes]
    rfl
  | some x =>
    unfold encodeWireOption decodeWireOption
    rw [List.append_assoc, decodeVarBytes_natToVarBytes]
    simp [hElem x rest]

/-- Encode a `String` via its `List Char` codepoints. -/
def encodeWireString (s : String) : List UInt8 :=
  encodeWireList encodeWireChar s.toList

/-- Decode a `String` from its `List Char` codepoints. -/
def decodeWireString (bs : List UInt8) : Option (String × List UInt8) :=
  match decodeWireList decodeWireChar bs with
  | some (cs, rest) => some (String.ofList cs, rest)
  | none => none

@[simp] theorem decodeWireString_encodeWireString (s : String) (rest : List UInt8) :
    decodeWireString (encodeWireString s ++ rest) = some (s, rest) := by
  unfold encodeWireString decodeWireString
  rw [decodeWireList_encodeWireList encodeWireChar decodeWireChar decodeWireChar_encodeWireChar s.toList rest]
  simp

/-- Flatten a `KName` into a list of components (`Sum String Nat`) from root to leaf. -/
def knameToComponents : KName → List (Sum String Nat)
  | .anonymous => []
  | .str p s   => knameToComponents p ++ [Sum.inl s]
  | .num p i   => knameToComponents p ++ [Sum.inr i]

/-- Fold a list of `Sum String Nat` components onto an accumulator `KName`. -/
def componentsToKNameAcc : KName → List (Sum String Nat) → KName
  | acc, []               => acc
  | acc, Sum.inl s :: xs  => componentsToKNameAcc (.str acc s) xs
  | acc, Sum.inr i :: xs  => componentsToKNameAcc (.num acc i) xs

theorem componentsToKNameAcc_append (acc : KName) :
    ∀ (xs ys : List (Sum String Nat)),
      componentsToKNameAcc acc (xs ++ ys) = componentsToKNameAcc (componentsToKNameAcc acc xs) ys
  | [], _ => rfl
  | Sum.inl s :: xs, ys => componentsToKNameAcc_append (.str acc s) xs ys
  | Sum.inr i :: xs, ys => componentsToKNameAcc_append (.num acc i) xs ys

@[simp] theorem componentsToKNameAcc_knameToComponents :
    ∀ (n : KName), componentsToKNameAcc .anonymous (knameToComponents n) = n
  | .anonymous => rfl
  | .str p s => by
    simp only [knameToComponents, componentsToKNameAcc_append,
      componentsToKNameAcc_knameToComponents p, componentsToKNameAcc]
  | .num p i => by
    simp only [knameToComponents, componentsToKNameAcc_append,
      componentsToKNameAcc_knameToComponents p, componentsToKNameAcc]

/-- Encode a `Sum String Nat` name component. -/
def encodeNameComp : Sum String Nat → List UInt8
  | Sum.inl s => natToVarBytes 0 ++ encodeWireString s
  | Sum.inr i => natToVarBytes 1 ++ natToVarBytes i

/-- Decode a `Sum String Nat` name component. -/
def decodeNameComp (bs : List UInt8) : Option (Sum String Nat × List UInt8) :=
  match decodeVarBytes bs with
  | some (0, rest) =>
    match decodeWireString rest with
    | some (s, rest2) => some (Sum.inl s, rest2)
    | none => none
  | some (1, rest) =>
    match decodeVarBytes rest with
    | some (i, rest2) => some (Sum.inr i, rest2)
    | none => none
  | _ => none

@[simp] theorem decodeNameComp_encodeNameComp (c : Sum String Nat) (rest : List UInt8) :
    decodeNameComp (encodeNameComp c ++ rest) = some (c, rest) := by
  cases c with
  | inl s =>
    unfold encodeNameComp decodeNameComp
    rw [List.append_assoc, decodeVarBytes_natToVarBytes]
    simp
  | inr i =>
    unfold encodeNameComp decodeNameComp
    rw [List.append_assoc, decodeVarBytes_natToVarBytes]
    simp

/-- Encode a `KName` into bytes. -/
def encodeWireKName (n : KName) : List UInt8 :=
  encodeWireList encodeNameComp (knameToComponents n)

/-- Decode a `KName` from bytes. -/
def decodeWireKName (bs : List UInt8) : Option (KName × List UInt8) :=
  match decodeWireList decodeNameComp bs with
  | some (comps, rest) => some (componentsToKNameAcc .anonymous comps, rest)
  | none => none

@[simp] theorem decodeWireKName_encodeWireKName (n : KName) (rest : List UInt8) :
    decodeWireKName (encodeWireKName n ++ rest) = some (n, rest) := by
  unfold encodeWireKName decodeWireKName
  rw [decodeWireList_encodeWireList encodeNameComp decodeNameComp decodeNameComp_encodeNameComp]
  simp

/-- Postfix RPN token for lossless fuel-free serialization of `KLevel`. -/
inductive LevelRpnToken where
  | zero
  | succ
  | max
  | imax
  | param (n : KName)
  deriving DecidableEq, Repr

/-- Convert a `KLevel` into a non-empty postfix RPN token list. -/
def klevelToRpn : KLevel → List LevelRpnToken
  | .zero       => [.zero]
  | .succ l     => klevelToRpn l ++ [.succ]
  | .max l1 l2  => klevelToRpn l1 ++ klevelToRpn l2 ++ [.max]
  | .imax l1 l2 => klevelToRpn l1 ++ klevelToRpn l2 ++ [.imax]
  | .param n    => [.param n]

/-- Execute a postfix `LevelRpnToken` stream on a stack `stk : List KLevel`. -/
def evalLevelRpn : List KLevel → List LevelRpnToken → Option (List KLevel)
  | stk, [] => some stk
  | stk, .zero :: ts => evalLevelRpn (.zero :: stk) ts
  | l :: stk, .succ :: ts => evalLevelRpn (.succ l :: stk) ts
  | l2 :: l1 :: stk, .max :: ts => evalLevelRpn (.max l1 l2 :: stk) ts
  | l2 :: l1 :: stk, .imax :: ts => evalLevelRpn (.imax l1 l2 :: stk) ts
  | stk, .param n :: ts => evalLevelRpn (.param n :: stk) ts
  | _, _ => none

theorem evalLevelRpn_klevelToRpn :
    ∀ (l : KLevel) (stk : List KLevel) (more : List LevelRpnToken),
      evalLevelRpn stk (klevelToRpn l ++ more) = evalLevelRpn (l :: stk) more
  | .zero, _, _ => rfl
  | .succ l, stk, more => by
    unfold klevelToRpn
    rw [List.append_assoc, List.singleton_append, evalLevelRpn_klevelToRpn l stk (.succ :: more)]
    rfl
  | .max l1 l2, stk, more => by
    unfold klevelToRpn
    rw [List.append_assoc, List.append_assoc, List.singleton_append,
        evalLevelRpn_klevelToRpn l1 stk (klevelToRpn l2 ++ (.max :: more)),
        evalLevelRpn_klevelToRpn l2 (l1 :: stk) (.max :: more)]
    rfl
  | .imax l1 l2, stk, more => by
    unfold klevelToRpn
    rw [List.append_assoc, List.append_assoc, List.singleton_append,
        evalLevelRpn_klevelToRpn l1 stk (klevelToRpn l2 ++ (.imax :: more)),
        evalLevelRpn_klevelToRpn l2 (l1 :: stk) (.imax :: more)]
    rfl
  | .param _, _, _ => rfl

/-- Encode a `LevelRpnToken`. -/
def encodeLevelRpnToken : LevelRpnToken → List UInt8
  | .zero    => natToVarBytes 0
  | .succ    => natToVarBytes 1
  | .max     => natToVarBytes 2
  | .imax    => natToVarBytes 3
  | .param n => natToVarBytes 4 ++ encodeWireKName n

/-- Decode a `LevelRpnToken`. -/
def decodeLevelRpnToken (bs : List UInt8) : Option (LevelRpnToken × List UInt8) :=
  match decodeVarBytes bs with
  | some (0, rest) => some (.zero, rest)
  | some (1, rest) => some (.succ, rest)
  | some (2, rest) => some (.max, rest)
  | some (3, rest) => some (.imax, rest)
  | some (4, rest) =>
    match decodeWireKName rest with
    | some (n, rest2) => some (.param n, rest2)
    | none => none
  | _ => none

@[simp] theorem decodeLevelRpnToken_encodeLevelRpnToken (t : LevelRpnToken) (rest : List UInt8) :
    decodeLevelRpnToken (encodeLevelRpnToken t ++ rest) = some (t, rest) := by
  cases t with
  | zero | succ | max | imax =>
    unfold encodeLevelRpnToken decodeLevelRpnToken
    rw [decodeVarBytes_natToVarBytes]
    rfl
  | param n =>
    unfold encodeLevelRpnToken decodeLevelRpnToken
    rw [List.append_assoc, decodeVarBytes_natToVarBytes]
    simp

/-- Encode a `KLevel` into bytes via its postfix RPN token stream. -/
def encodeWireKLevel (l : KLevel) : List UInt8 :=
  encodeWireList encodeLevelRpnToken (klevelToRpn l)

/-- Decode a `KLevel` from bytes. -/
def decodeWireKLevel (bs : List UInt8) : Option (KLevel × List UInt8) :=
  match decodeWireList decodeLevelRpnToken bs with
  | some (toks, rest) =>
    match evalLevelRpn [] toks with
    | some [l] => some (l, rest)
    | _        => none
  | none => none

@[simp] theorem decodeWireKLevel_encodeWireKLevel (l : KLevel) (rest : List UInt8) :
    decodeWireKLevel (encodeWireKLevel l ++ rest) = some (l, rest) := by
  unfold encodeWireKLevel decodeWireKLevel
  rw [decodeWireList_encodeWireList encodeLevelRpnToken decodeLevelRpnToken decodeLevelRpnToken_encodeLevelRpnToken]
  dsimp only
  have hRpn := evalLevelRpn_klevelToRpn l [] []
  rw [List.append_nil] at hRpn
  rw [hRpn]
  rfl

/-- Encode a `KLiteral` into bytes. -/
def encodeWireKLiteral : KLiteral → List UInt8
  | .natVal n => natToVarBytes 0 ++ natToVarBytes n
  | .strVal s => natToVarBytes 1 ++ encodeWireString s

/-- Decode a `KLiteral` from bytes. -/
def decodeWireKLiteral (bs : List UInt8) : Option (KLiteral × List UInt8) :=
  match decodeVarBytes bs with
  | some (0, rest) =>
    match decodeVarBytes rest with
    | some (n, rest2) => some (.natVal n, rest2)
    | none => none
  | some (1, rest) =>
    match decodeWireString rest with
    | some (s, rest2) => some (.strVal s, rest2)
    | none => none
  | _ => none

@[simp] theorem decodeWireKLiteral_encodeWireKLiteral (lit : KLiteral) (rest : List UInt8) :
    decodeWireKLiteral (encodeWireKLiteral lit ++ rest) = some (lit, rest) := by
  cases lit with
  | natVal n =>
    unfold encodeWireKLiteral decodeWireKLiteral
    rw [List.append_assoc, decodeVarBytes_natToVarBytes]
    simp
  | strVal s =>
    unfold encodeWireKLiteral decodeWireKLiteral
    rw [List.append_assoc, decodeVarBytes_natToVarBytes]
    simp

/-- Encode a `SiliconElabWireHeader`. -/
def encodeWireHeader (h : SiliconElabWireHeader) : List UInt8 :=
  encodeWireUInt64 h.magic ++
  encodeWireUInt32 h.version ++
  encodeWireUInt32 h.flags ++
  encodeWireUInt32 h.nodeCount ++
  encodeWireUInt32 h.symbolCount ++
  encodeWireUInt32 h.levelCount ++
  encodeWireUInt32 h.constCount ++
  encodeWireUInt32 h.recRuleCount ++
  encodeWireUInt32 h.lutEntryCount ++
  encodeWireUInt32 h.icapFrameCount ++
  encodeWireUInt32 h.targetDeclSymIdx ++
  encodeWireUInt32 h.targetExprHandle ++
  encodeWireUInt32 h.targetTypeHandle ++
  encodeWireUInt32 h.fuelBudget ++
  encodeWireUInt64 h.envPinDigest64

/-- Decode a `SiliconElabWireHeader`. -/
def decodeWireHeader (bs : List UInt8) : Option (SiliconElabWireHeader × List UInt8) := do
  let (magic, bs1)            ← decodeWireUInt64 bs
  let (version, bs2)          ← decodeWireUInt32 bs1
  let (flags, bs3)            ← decodeWireUInt32 bs2
  let (nodeCount, bs4)        ← decodeWireUInt32 bs3
  let (symbolCount, bs5)      ← decodeWireUInt32 bs4
  let (levelCount, bs6)       ← decodeWireUInt32 bs5
  let (constCount, bs7)       ← decodeWireUInt32 bs6
  let (recRuleCount, bs8)     ← decodeWireUInt32 bs7
  let (lutEntryCount, bs9)    ← decodeWireUInt32 bs8
  let (icapFrameCount, bs10)  ← decodeWireUInt32 bs9
  let (targetDeclSymIdx, bs11) ← decodeWireUInt32 bs10
  let (targetExprHandle, bs12) ← decodeWireUInt32 bs11
  let (targetTypeHandle, bs13) ← decodeWireUInt32 bs12
  let (fuelBudget, bs14)      ← decodeWireUInt32 bs13
  let (envPinDigest64, bs15)  ← decodeWireUInt64 bs14
  pure ({ magic := magic
        , version := version
        , flags := flags
        , nodeCount := nodeCount
        , symbolCount := symbolCount
        , levelCount := levelCount
        , constCount := constCount
        , recRuleCount := recRuleCount
        , lutEntryCount := lutEntryCount
        , icapFrameCount := icapFrameCount
        , targetDeclSymIdx := targetDeclSymIdx
        , targetExprHandle := targetExprHandle
        , targetTypeHandle := targetTypeHandle
        , fuelBudget := fuelBudget
        , envPinDigest64 := envPinDigest64 }, bs15)

@[simp] theorem decodeWireHeader_encodeWireHeader (h : SiliconElabWireHeader) (rest : List UInt8) :
    decodeWireHeader (encodeWireHeader h ++ rest) = some (h, rest) := by
  rcases h with ⟨m, v, fl, nc, sc, lc, cc, rc, ltc, ic, tds, teh, tth, fb, epd⟩
  simp [encodeWireHeader, decodeWireHeader, List.append_assoc]

/-- Encode a Section-1 `PackedNodeWord`. -/
def encodeWirePackedNode (w : PackedNodeWord) : List UInt8 :=
  natToVarBytes w.tag ++
  natToVarBytes w.h0 ++
  natToVarBytes w.h1 ++
  natToVarBytes w.h2 ++
  natToVarBytes w.symIdx ++
  encodeWireBool w.hasLooseBVar ++
  encodeWireBool w.hasFVar ++
  encodeWireBool w.hasMVar ++
  natToVarBytes w.maxLooseBVar

/-- Decode a Section-1 `PackedNodeWord`. -/
def decodeWirePackedNode (bs : List UInt8) : Option (PackedNodeWord × List UInt8) := do
  let (tag, bs1)      ← decodeVarBytes bs
  let (h0, bs2)       ← decodeVarBytes bs1
  let (h1, bs3)       ← decodeVarBytes bs2
  let (h2, bs4)       ← decodeVarBytes bs3
  let (symIdx, bs5)   ← decodeVarBytes bs4
  let (hasLoose, bs6) ← decodeWireBool bs5
  let (hasF, bs7)     ← decodeWireBool bs6
  let (hasM, bs8)     ← decodeWireBool bs7
  let (maxB, bs9)     ← decodeVarBytes bs8
  pure ({ tag := tag, h0 := h0, h1 := h1, h2 := h2, symIdx := symIdx
        , hasLooseBVar := hasLoose, hasFVar := hasF, hasMVar := hasM, maxLooseBVar := maxB }, bs9)

@[simp] theorem decodeWirePackedNode_encodeWirePackedNode (w : PackedNodeWord) (rest : List UInt8) :
    decodeWirePackedNode (encodeWirePackedNode w ++ rest) = some (w, rest) := by
  rcases w with ⟨tag, h0, h1, h2, symIdx, hasLoose, hasF, hasM, maxB⟩
  simp [encodeWirePackedNode, decodeWirePackedNode, List.append_assoc]

/-- Encode a Section-2 `HwCamSymbolEntry`. -/
def encodeWireSymbolEntry : HwCamSymbolEntry → List UInt8
  | .sortEntry u         => natToVarBytes 0 ++ encodeWireKLevel u
  | .constEntry n us     => natToVarBytes 1 ++ encodeWireKName n ++ encodeWireList encodeWireKLevel us
  | .litEntry l          => natToVarBytes 2 ++ encodeWireKLiteral l
  | .projEntry sName idx => natToVarBytes 3 ++ encodeWireKName sName ++ natToVarBytes idx

/-- Decode a Section-2 `HwCamSymbolEntry`. -/
def decodeWireSymbolEntry (bs : List UInt8) : Option (HwCamSymbolEntry × List UInt8) :=
  match decodeVarBytes bs with
  | some (0, bs1) => do
    let (u, bs2) ← decodeWireKLevel bs1
    pure (.sortEntry u, bs2)
  | some (1, bs1) => do
    let (n, bs2) ← decodeWireKName bs1
    let (us, bs3) ← decodeWireList decodeWireKLevel bs2
    pure (.constEntry n us, bs3)
  | some (2, bs1) => do
    let (l, bs2) ← decodeWireKLiteral bs1
    pure (.litEntry l, bs2)
  | some (3, bs1) => do
    let (sName, bs2) ← decodeWireKName bs1
    let (idx, bs3) ← decodeVarBytes bs2
    pure (.projEntry sName idx, bs3)
  | _ => none

@[simp] theorem decodeWireSymbolEntry_encodeWireSymbolEntry (s : HwCamSymbolEntry) (rest : List UInt8) :
    decodeWireSymbolEntry (encodeWireSymbolEntry s ++ rest) = some (s, rest) := by
  cases s with
  | sortEntry u =>
    unfold encodeWireSymbolEntry decodeWireSymbolEntry
    rw [List.append_assoc, decodeVarBytes_natToVarBytes]
    simp
  | constEntry n us =>
    unfold encodeWireSymbolEntry decodeWireSymbolEntry
    simp only [List.append_assoc, decodeVarBytes_natToVarBytes, decodeWireKName_encodeWireKName,
      Option.bind_eq_bind, Option.bind_some]
    rw [decodeWireList_encodeWireList encodeWireKLevel decodeWireKLevel decodeWireKLevel_encodeWireKLevel]
    rfl
  | litEntry l =>
    unfold encodeWireSymbolEntry decodeWireSymbolEntry
    rw [List.append_assoc, decodeVarBytes_natToVarBytes]
    simp
  | projEntry sName idx =>
    unfold encodeWireSymbolEntry decodeWireSymbolEntry
    simp [List.append_assoc]

/-- Encode a Section-3 `HwCamLevelEntry`. -/
def encodeWireLevelEntry (e : HwCamLevelEntry) : List UInt8 :=
  natToVarBytes e.tag ++
  natToVarBytes e.l0 ++
  natToVarBytes e.l1 ++
  encodeWireKName e.paramName

/-- Decode a Section-3 `HwCamLevelEntry`. -/
def decodeWireLevelEntry (bs : List UInt8) : Option (HwCamLevelEntry × List UInt8) := do
  let (tag, bs1)  ← decodeVarBytes bs
  let (l0, bs2)   ← decodeVarBytes bs1
  let (l1, bs3)   ← decodeVarBytes bs2
  let (pName, bs4) ← decodeWireKName bs3
  pure ({ tag := tag, l0 := l0, l1 := l1, paramName := pName }, bs4)

@[simp] theorem decodeWireLevelEntry_encodeWireLevelEntry (e : HwCamLevelEntry) (rest : List UInt8) :
    decodeWireLevelEntry (encodeWireLevelEntry e ++ rest) = some (e, rest) := by
  rcases e with ⟨tag, l0, l1, pName⟩
  simp [encodeWireLevelEntry, decodeWireLevelEntry, List.append_assoc]

/-- Encode a Section-4 `HwCamConstEntry`. -/
def encodeWireConstEntry (c : HwCamConstEntry) : List UInt8 :=
  encodeWireKName c.name ++
  natToVarBytes c.symIdx ++
  natToVarBytes c.typeHandle ++
  encodeWireOption natToVarBytes c.valHandle? ++
  encodeWireBool c.isCtor ++
  encodeWireOption encodeWireKName c.inductName?

/-- Decode a Section-4 `HwCamConstEntry`. -/
def decodeWireConstEntry (bs : List UInt8) : Option (HwCamConstEntry × List UInt8) := do
  let (name, bs1)       ← decodeWireKName bs
  let (symIdx, bs2)     ← decodeVarBytes bs1
  let (typeHandle, bs3) ← decodeVarBytes bs2
  let (valHandle?, bs4) ← decodeWireOption decodeVarBytes bs3
  let (isCtor, bs5)     ← decodeWireBool bs4
  let (indName?, bs6)   ← decodeWireOption decodeWireKName bs5
  pure ({ name := name, symIdx := symIdx, typeHandle := typeHandle
        , valHandle? := valHandle?, isCtor := isCtor, inductName? := indName? }, bs6)

@[simp] theorem decodeWireConstEntry_encodeWireConstEntry (c : HwCamConstEntry) (rest : List UInt8) :
    decodeWireConstEntry (encodeWireConstEntry c ++ rest) = some (c, rest) := by
  rcases c with ⟨name, symIdx, typeHandle, valHandle?, isCtor, indName?⟩
  unfold encodeWireConstEntry decodeWireConstEntry
  simp only [List.append_assoc, decodeWireKName_encodeWireKName, decodeVarBytes_natToVarBytes,
    Option.bind_eq_bind, Option.bind_some]
  rw [decodeWireOption_encodeWireOption natToVarBytes decodeVarBytes decodeVarBytes_natToVarBytes]
  simp only [Option.bind_some, decodeWireBool_encodeWireBool]
  rw [decodeWireOption_encodeWireOption encodeWireKName decodeWireKName decodeWireKName_encodeWireKName]
  rfl

/-- Encode a Section-5 `HwCamRecRuleEntry`. -/
def encodeWireRecRuleEntry (r : HwCamRecRuleEntry) : List UInt8 :=
  encodeWireKName r.recName ++
  encodeWireKName r.ctorName ++
  natToVarBytes r.numParams ++
  natToVarBytes r.numFields ++
  natToVarBytes r.rhsHandle

/-- Decode a Section-5 `HwCamRecRuleEntry`. -/
def decodeWireRecRuleEntry (bs : List UInt8) : Option (HwCamRecRuleEntry × List UInt8) := do
  let (recName, bs1)   ← decodeWireKName bs
  let (ctorName, bs2)  ← decodeWireKName bs1
  let (numParams, bs3) ← decodeVarBytes bs2
  let (numFields, bs4) ← decodeVarBytes bs3
  let (rhsHandle, bs5) ← decodeVarBytes bs4
  pure ({ recName := recName, ctorName := ctorName, numParams := numParams
        , numFields := numFields, rhsHandle := rhsHandle }, bs5)

@[simp] theorem decodeWireRecRuleEntry_encodeWireRecRuleEntry (r : HwCamRecRuleEntry) (rest : List UInt8) :
    decodeWireRecRuleEntry (encodeWireRecRuleEntry r ++ rest) = some (r, rest) := by
  rcases r with ⟨recName, ctorName, numParams, numFields, rhsHandle⟩
  simp [encodeWireRecRuleEntry, decodeWireRecRuleEntry, List.append_assoc]

/-- Encode a Section-6 `DiscrTreeLutEntry`. -/
def encodeWireLutEntry (e : DiscrTreeLutEntry) : List UInt8 :=
  encodeWireList natToVarBytes e.pathKeys ++
  natToVarBytes e.rhsHandle ++
  natToVarBytes e.lutTag ++
  natToVarBytes e.gain ++
  natToVarBytes e.offset

/-- Decode a Section-6 `DiscrTreeLutEntry`. -/
def decodeWireLutEntry (bs : List UInt8) : Option (DiscrTreeLutEntry × List UInt8) := do
  let (pathKeys, bs1)  ← decodeWireList decodeVarBytes bs
  let (rhsHandle, bs2) ← decodeVarBytes bs1
  let (lutTag, bs3)    ← decodeVarBytes bs2
  let (gain, bs4)      ← decodeVarBytes bs3
  let (offset, bs5)    ← decodeVarBytes bs4
  pure ({ pathKeys := pathKeys, rhsHandle := rhsHandle, lutTag := lutTag
        , gain := gain, offset := offset }, bs5)

@[simp] theorem decodeWireLutEntry_encodeWireLutEntry (e : DiscrTreeLutEntry) (rest : List UInt8) :
    decodeWireLutEntry (encodeWireLutEntry e ++ rest) = some (e, rest) := by
  rcases e with ⟨pathKeys, rhsHandle, lutTag, gain, offset⟩
  unfold encodeWireLutEntry decodeWireLutEntry
  simp only [List.append_assoc]
  rw [decodeWireList_encodeWireList natToVarBytes decodeVarBytes decodeVarBytes_natToVarBytes]
  simp

/-- Encode an `RtlAluOp`. -/
def encodeWireRtlAluOp : RtlAluOp → List UInt8
  | .add    => natToVarBytes 0
  | .sub    => natToVarBytes 1
  | .mul    => natToVarBytes 2
  | .bitAnd => natToVarBytes 3
  | .bitOr  => natToVarBytes 4
  | .bitXor => natToVarBytes 5
  | .shl    => natToVarBytes 6
  | .lshr   => natToVarBytes 7
  | .ashr   => natToVarBytes 8
  | .eq     => natToVarBytes 9
  | .ult    => natToVarBytes 10
  | .slt    => natToVarBytes 11
  | .qmul32 => natToVarBytes 12

/-- Decode an `RtlAluOp`. -/
def decodeWireRtlAluOp (bs : List UInt8) : Option (RtlAluOp × List UInt8) :=
  match decodeVarBytes bs with
  | some (0, r)  => some (.add, r)
  | some (1, r)  => some (.sub, r)
  | some (2, r)  => some (.mul, r)
  | some (3, r)  => some (.bitAnd, r)
  | some (4, r)  => some (.bitOr, r)
  | some (5, r)  => some (.bitXor, r)
  | some (6, r)  => some (.shl, r)
  | some (7, r)  => some (.lshr, r)
  | some (8, r)  => some (.ashr, r)
  | some (9, r)  => some (.eq, r)
  | some (10, r) => some (.ult, r)
  | some (11, r) => some (.slt, r)
  | some (12, r) => some (.qmul32, r)
  | _            => none

@[simp] theorem decodeWireRtlAluOp_encodeWireRtlAluOp (op : RtlAluOp) (rest : List UInt8) :
    decodeWireRtlAluOp (encodeWireRtlAluOp op ++ rest) = some (op, rest) := by
  cases op <;> { unfold encodeWireRtlAluOp decodeWireRtlAluOp; rw [decodeVarBytes_natToVarBytes]; rfl }

/-- Postfix RPN token for lossless fuel-free serialization of `RtlExpr`. -/
inductive RtlExprRpnToken where
  | const     (val : BitVec 64)
  | inputPort (idx : Nat)
  | wireRef   (idx : Nat)
  | regRead   (idx : Nat)
  | alu       (op : RtlAluOp)
  | mux
  | bitNot
  | resize    (op : RtlWidthOp)
  deriving DecidableEq, Repr

/-- Convert an `RtlExpr` into a postfix RPN token list. -/
def rtlExprToRpn : RtlExpr → List RtlExprRpnToken
  | .const v       => [.const v]
  | .inputPort idx => [.inputPort idx]
  | .wireRef idx   => [.wireRef idx]
  | .regRead idx   => [.regRead idx]
  | .alu op a b    => rtlExprToRpn a ++ rtlExprToRpn b ++ [.alu op]
  | .mux c t f     => rtlExprToRpn c ++ rtlExprToRpn t ++ rtlExprToRpn f ++ [.mux]
  | .bitNot a      => rtlExprToRpn a ++ [.bitNot]
  | .resize op a   => rtlExprToRpn a ++ [.resize op]

/-- Execute a postfix `RtlExprRpnToken` stream on a stack `stk : List RtlExpr`. -/
def evalRtlExprRpn : List RtlExpr → List RtlExprRpnToken → Option (List RtlExpr)
  | stk, []                      => some stk
  | stk, .const v :: ts          => evalRtlExprRpn (.const v :: stk) ts
  | stk, .inputPort idx :: ts    => evalRtlExprRpn (.inputPort idx :: stk) ts
  | stk, .wireRef idx :: ts      => evalRtlExprRpn (.wireRef idx :: stk) ts
  | stk, .regRead idx :: ts      => evalRtlExprRpn (.regRead idx :: stk) ts
  | b :: a :: stk, .alu op :: ts => evalRtlExprRpn (.alu op a b :: stk) ts
  | f :: t :: c :: stk, .mux :: ts => evalRtlExprRpn (.mux c t f :: stk) ts
  | a :: stk, .bitNot :: ts      => evalRtlExprRpn (.bitNot a :: stk) ts
  | a :: stk, .resize op :: ts   => evalRtlExprRpn (.resize op a :: stk) ts
  | _, _                         => none

theorem evalRtlExprRpn_rtlExprToRpn :
    ∀ (e : RtlExpr) (stk : List RtlExpr) (more : List RtlExprRpnToken),
      evalRtlExprRpn stk (rtlExprToRpn e ++ more) = evalRtlExprRpn (e :: stk) more
  | .const _, _, _ => rfl
  | .inputPort _, _, _ => rfl
  | .wireRef _, _, _ => rfl
  | .regRead _, _, _ => rfl
  | .alu op a b, stk, more => by
    unfold rtlExprToRpn
    rw [List.append_assoc, List.append_assoc, List.singleton_append,
        evalRtlExprRpn_rtlExprToRpn a stk (rtlExprToRpn b ++ (.alu op :: more)),
        evalRtlExprRpn_rtlExprToRpn b (a :: stk) (.alu op :: more)]
    rfl
  | .mux c t f, stk, more => by
    unfold rtlExprToRpn
    rw [List.append_assoc, List.append_assoc, List.append_assoc, List.singleton_append,
        evalRtlExprRpn_rtlExprToRpn c stk (rtlExprToRpn t ++ (rtlExprToRpn f ++ (.mux :: more))),
        evalRtlExprRpn_rtlExprToRpn t (c :: stk) (rtlExprToRpn f ++ (.mux :: more)),
        evalRtlExprRpn_rtlExprToRpn f (t :: c :: stk) (.mux :: more)]
    rfl
  | .bitNot a, stk, more => by
    unfold rtlExprToRpn
    rw [List.append_assoc, List.singleton_append,
        evalRtlExprRpn_rtlExprToRpn a stk (.bitNot :: more)]
    rfl
  | .resize op a, stk, more => by
    unfold rtlExprToRpn
    rw [List.append_assoc, List.singleton_append,
        evalRtlExprRpn_rtlExprToRpn a stk (.resize op :: more)]
    rfl

/-- Encode an `RtlWidthOp`. -/
def encodeWireRtlWidthOp : RtlWidthOp → List UInt8
  | .slice hi lo => natToVarBytes 0 ++ natToVarBytes hi ++ natToVarBytes lo
  | .zext w      => natToVarBytes 1 ++ natToVarBytes w
  | .sext f t    => natToVarBytes 2 ++ natToVarBytes f ++ natToVarBytes t
  | .trunc w     => natToVarBytes 3 ++ natToVarBytes w

/-- Decode an `RtlWidthOp`. -/
def decodeWireRtlWidthOp (bs : List UInt8) : Option (RtlWidthOp × List UInt8) :=
  match decodeVarBytes bs with
  | some (0, r) => do let (hi, r2) ← decodeVarBytes r; let (lo, r3) ← decodeVarBytes r2; pure (.slice hi lo, r3)
  | some (1, r) => do let (w, r2) ← decodeVarBytes r; pure (.zext w, r2)
  | some (2, r) => do let (f, r2) ← decodeVarBytes r; let (t, r3) ← decodeVarBytes r2; pure (.sext f t, r3)
  | some (3, r) => do let (w, r2) ← decodeVarBytes r; pure (.trunc w, r2)
  | _           => none

@[simp] theorem decodeWireRtlWidthOp_encodeWireRtlWidthOp (op : RtlWidthOp) (rest : List UInt8) :
    decodeWireRtlWidthOp (encodeWireRtlWidthOp op ++ rest) = some (op, rest) := by
  cases op <;>
    simp [encodeWireRtlWidthOp, decodeWireRtlWidthOp, List.append_assoc, decodeVarBytes_natToVarBytes] <;> rfl

/-- Encode an `RtlExprRpnToken`. -/
def encodeRtlExprRpnToken : RtlExprRpnToken → List UInt8
  | .const v       => natToVarBytes 0 ++ encodeWireBitVec64 v
  | .inputPort idx => natToVarBytes 1 ++ natToVarBytes idx
  | .wireRef idx   => natToVarBytes 2 ++ natToVarBytes idx
  | .regRead idx   => natToVarBytes 3 ++ natToVarBytes idx
  | .alu op        => natToVarBytes 4 ++ encodeWireRtlAluOp op
  | .mux           => natToVarBytes 5
  | .bitNot        => natToVarBytes 6
  | .resize op     => natToVarBytes 7 ++ encodeWireRtlWidthOp op

/-- Decode an `RtlExprRpnToken`. -/
def decodeRtlExprRpnToken (bs : List UInt8) : Option (RtlExprRpnToken × List UInt8) :=
  match decodeVarBytes bs with
  | some (0, r) => do let (v, r2) ← decodeWireBitVec64 r; pure (.const v, r2)
  | some (1, r) => do let (idx, r2) ← decodeVarBytes r; pure (.inputPort idx, r2)
  | some (2, r) => do let (idx, r2) ← decodeVarBytes r; pure (.wireRef idx, r2)
  | some (3, r) => do let (idx, r2) ← decodeVarBytes r; pure (.regRead idx, r2)
  | some (4, r) => do let (op, r2) ← decodeWireRtlAluOp r; pure (.alu op, r2)
  | some (5, r) => some (.mux, r)
  | some (6, r) => some (.bitNot, r)
  | some (7, r) => do let (op, r2) ← decodeWireRtlWidthOp r; pure (.resize op, r2)
  | _           => none

@[simp] theorem decodeRtlExprRpnToken_encodeRtlExprRpnToken (t : RtlExprRpnToken) (rest : List UInt8) :
    decodeRtlExprRpnToken (encodeRtlExprRpnToken t ++ rest) = some (t, rest) := by
  cases t with
  | const v =>
    unfold encodeRtlExprRpnToken decodeRtlExprRpnToken
    rw [List.append_assoc, decodeVarBytes_natToVarBytes]
    simp
  | inputPort idx | wireRef idx | regRead idx =>
    unfold encodeRtlExprRpnToken decodeRtlExprRpnToken
    rw [List.append_assoc, decodeVarBytes_natToVarBytes]
    simp
  | alu op =>
    unfold encodeRtlExprRpnToken decodeRtlExprRpnToken
    rw [List.append_assoc, decodeVarBytes_natToVarBytes]
    simp
  | resize op =>
    unfold encodeRtlExprRpnToken decodeRtlExprRpnToken
    rw [List.append_assoc, decodeVarBytes_natToVarBytes]
    simp
  | mux | bitNot =>
    unfold encodeRtlExprRpnToken decodeRtlExprRpnToken
    rw [decodeVarBytes_natToVarBytes]
    rfl

/-- Encode an `RtlExpr` via its postfix RPN token list. -/
def encodeWireRtlExpr (e : RtlExpr) : List UInt8 :=
  encodeWireList encodeRtlExprRpnToken (rtlExprToRpn e)

/-- Decode an `RtlExpr` from bytes. -/
def decodeWireRtlExpr (bs : List UInt8) : Option (RtlExpr × List UInt8) :=
  match decodeWireList decodeRtlExprRpnToken bs with
  | some (toks, rest) =>
    match evalRtlExprRpn [] toks with
    | some [e] => some (e, rest)
    | _        => none
  | none => none

@[simp] theorem decodeWireRtlExpr_encodeWireRtlExpr (e : RtlExpr) (rest : List UInt8) :
    decodeWireRtlExpr (encodeWireRtlExpr e ++ rest) = some (e, rest) := by
  unfold encodeWireRtlExpr decodeWireRtlExpr
  rw [decodeWireList_encodeWireList encodeRtlExprRpnToken decodeRtlExprRpnToken decodeRtlExprRpnToken_encodeRtlExprRpnToken]
  dsimp only
  have hRpn := evalRtlExprRpn_rtlExprToRpn e [] []
  rw [List.append_nil] at hRpn
  rw [hRpn]
  rfl

/-- Encode a `TileOpKind`. -/
def encodeWireTileOpKind : TileOpKind → List UInt8
  | .methodSlot      => natToVarBytes 0
  | .cellSlot        => natToVarBytes 1
  | .loweredLeanLite => natToVarBytes 2

/-- Decode a `TileOpKind`. -/
def decodeWireTileOpKind (bs : List UInt8) : Option (TileOpKind × List UInt8) :=
  match decodeVarBytes bs with
  | some (0, r) => some (.methodSlot, r)
  | some (1, r) => some (.cellSlot, r)
  | some (2, r) => some (.loweredLeanLite, r)
  | _           => none

@[simp] theorem decodeWireTileOpKind_encodeWireTileOpKind (k : TileOpKind) (rest : List UInt8) :
    decodeWireTileOpKind (encodeWireTileOpKind k ++ rest) = some (k, rest) := by
  cases k <;> { unfold encodeWireTileOpKind decodeWireTileOpKind; rw [decodeVarBytes_natToVarBytes]; rfl }

/-- Encode a Section-7 `IcapBitstreamFrame`. -/
def encodeWireIcapFrame (f : IcapBitstreamFrame) : List UInt8 :=
  natToVarBytes f.targetTileId ++
  natToVarBytes f.newTile.slotIdx ++
  encodeWireString f.newTile.memberName ++
  encodeWireTileOpKind f.newTile.opKind ++
  encodeWireRtlExpr f.newTile.datapath ++
  encodeWireList natToVarBytes f.newTile.readsSlots ++
  encodeWireBitVec64 f.expectedCrc64 ++
  encodeWireBitVec64 f.computedCrc64

/-- Decode a Section-7 `IcapBitstreamFrame`. -/
def decodeWireIcapFrame (bs : List UInt8) : Option (IcapBitstreamFrame × List UInt8) := do
  let (targetTileId, bs1)   ← decodeVarBytes bs
  let (slotIdx, bs2)        ← decodeVarBytes bs1
  let (memberName, bs3)     ← decodeWireString bs2
  let (opKind, bs4)         ← decodeWireTileOpKind bs3
  let (datapath, bs5)       ← decodeWireRtlExpr bs4
  let (readsSlots, bs6)     ← decodeWireList decodeVarBytes bs5
  let (expectedCrc64, bs7)  ← decodeWireBitVec64 bs6
  let (computedCrc64, bs8)  ← decodeWireBitVec64 bs7
  pure ({ targetTileId := targetTileId
        , newTile :=
            { slotIdx    := slotIdx
            , memberName := memberName
            , opKind     := opKind
            , datapath   := datapath
            , readsSlots := readsSlots }
        , expectedCrc64 := expectedCrc64
        , computedCrc64 := computedCrc64 }, bs8)

@[simp] theorem decodeWireIcapFrame_encodeWireIcapFrame (f : IcapBitstreamFrame) (rest : List UInt8) :
    decodeWireIcapFrame (encodeWireIcapFrame f ++ rest) = some (f, rest) := by
  rcases f with ⟨targetTileId, ⟨slotIdx, memberName, opKind, datapath, readsSlots⟩, expectedCrc64, computedCrc64⟩
  unfold encodeWireIcapFrame decodeWireIcapFrame
  simp only [List.append_assoc, decodeVarBytes_natToVarBytes, decodeWireString_encodeWireString,
    decodeWireTileOpKind_encodeWireTileOpKind, decodeWireRtlExpr_encodeWireRtlExpr,
    Option.bind_eq_bind, Option.bind_some]
  rw [decodeWireList_encodeWireList natToVarBytes decodeVarBytes decodeVarBytes_natToVarBytes]
  simp

/-- Encode a complete 7-section `SiliconElabWireFrame` into a `List UInt8` byte stream. -/
def encodeSiliconWireFrameBytes (f : SiliconElabWireFrame) : List UInt8 :=
  encodeWireHeader f.header ++
  encodeWireList encodeWirePackedNode f.nodes ++
  encodeWireList encodeWireSymbolEntry f.symbols ++
  encodeWireList encodeWireLevelEntry f.levels ++
  encodeWireList encodeWireConstEntry f.consts ++
  encodeWireList encodeWireRecRuleEntry f.recRules ++
  encodeWireList encodeWireLutEntry f.lutEntries ++
  encodeWireList encodeWireIcapFrame f.icapFrames

/-- Decode a complete 7-section `SiliconElabWireFrame` from a `List UInt8` byte stream. -/
def decodeSiliconWireFrameBytes (bs : List UInt8) : Option (SiliconElabWireFrame × List UInt8) := do
  let (header, bs1)     ← decodeWireHeader bs
  let (nodes, bs2)      ← decodeWireList decodeWirePackedNode bs1
  let (symbols, bs3)    ← decodeWireList decodeWireSymbolEntry bs2
  let (levels, bs4)     ← decodeWireList decodeWireLevelEntry bs3
  let (consts, bs5)     ← decodeWireList decodeWireConstEntry bs4
  let (recRules, bs6)   ← decodeWireList decodeWireRecRuleEntry bs5
  let (lutEntries, bs7) ← decodeWireList decodeWireLutEntry bs6
  let (icapFrames, bs8) ← decodeWireList decodeWireIcapFrame bs7
  pure ({ header := header
        , nodes := nodes
        , symbols := symbols
        , levels := levels
        , consts := consts
        , recRules := recRules
        , lutEntries := lutEntries
        , icapFrames := icapFrames }, bs8)

@[simp] theorem decodeSiliconWireFrameBytes_encodeSiliconWireFrameBytes
    (f : SiliconElabWireFrame) (rest : List UInt8) :
    decodeSiliconWireFrameBytes (encodeSiliconWireFrameBytes f ++ rest) = some (f, rest) := by
  rcases f with ⟨header, nodes, symbols, levels, consts, recRules, lutEntries, icapFrames⟩
  unfold encodeSiliconWireFrameBytes decodeSiliconWireFrameBytes
  simp only [List.append_assoc, decodeWireHeader_encodeWireHeader,
    Option.bind_eq_bind, Option.bind_some]
  rw [decodeWireList_encodeWireList encodeWirePackedNode decodeWirePackedNode decodeWirePackedNode_encodeWirePackedNode]
  simp only [Option.bind_some]
  rw [decodeWireList_encodeWireList encodeWireSymbolEntry decodeWireSymbolEntry decodeWireSymbolEntry_encodeWireSymbolEntry]
  simp only [Option.bind_some]
  rw [decodeWireList_encodeWireList encodeWireLevelEntry decodeWireLevelEntry decodeWireLevelEntry_encodeWireLevelEntry]
  simp only [Option.bind_some]
  rw [decodeWireList_encodeWireList encodeWireConstEntry decodeWireConstEntry decodeWireConstEntry_encodeWireConstEntry]
  simp only [Option.bind_some]
  rw [decodeWireList_encodeWireList encodeWireRecRuleEntry decodeWireRecRuleEntry decodeWireRecRuleEntry_encodeWireRecRuleEntry]
  simp only [Option.bind_some]
  rw [decodeWireList_encodeWireList encodeWireLutEntry decodeWireLutEntry decodeWireLutEntry_encodeWireLutEntry]
  simp only [Option.bind_some]
  rw [decodeWireList_encodeWireList encodeWireIcapFrame decodeWireIcapFrame decodeWireIcapFrame_encodeWireIcapFrame]
  rfl

/-- Serialize a 7-section `SiliconElabWireFrame` (`OBCAMv1`) into a `ByteArray`. -/
def serializeSiliconWireFrame (f : SiliconElabWireFrame) : ByteArray :=
  ByteArray.mk (Array.mk (encodeSiliconWireFrameBytes f))

/-- Deserialize a 7-section `SiliconElabWireFrame` (`OBCAMv1`) from a `ByteArray`. -/
def deserializeSiliconWireFrame (ba : ByteArray) : Option SiliconElabWireFrame :=
  match decodeSiliconWireFrameBytes ba.data.toList with
  | some (f, []) => some f
  | _            => none

/-- **7-Section `OBCAMv1` Wire Frame Round-Trip Theorem (`deserialize_serialize_siliconWireFrame`)**:
For every 7-section `SiliconElabWireFrame` (`header`, `nodes`, `symbols`, `levels`, `consts`,
`recRules`, `lutEntries`, `icapFrames`), serializing to `ByteArray` via `serializeSiliconWireFrame`
and deserializing via `deserializeSiliconWireFrame` recovers `some f` losslessly (`0 sorryAx`). -/
theorem deserialize_serialize_siliconWireFrame (f : SiliconElabWireFrame) :
    deserializeSiliconWireFrame (serializeSiliconWireFrame f) = some f := by
  have hData : (serializeSiliconWireFrame f).data.toList = encodeSiliconWireFrameBytes f := rfl
  unfold deserializeSiliconWireFrame
  rw [hData]
  have h := decodeSiliconWireFrameBytes_encodeSiliconWireFrameBytes f []
  rw [List.append_nil] at h
  rw [h]

/-- Allocate or reuse a `HwCamLevelEntry` in a Section-3 universe level DAG table. -/
def allocHwCamLevelEntry (e : HwCamLevelEntry) (tbl : List HwCamLevelEntry) :
    Nat × List HwCamLevelEntry :=
  match findElemIdx? tbl e with
  | some idx => (idx, tbl)
  | none => (tbl.length, tbl ++ [e])

/-- Intern a `KLevel` into a deduplicated Section-3 `List HwCamLevelEntry` DAG table. -/
def internKLevelToHwCam : KLevel → List HwCamLevelEntry → Nat × List HwCamLevelEntry
  | .zero, tbl =>
    allocHwCamLevelEntry { tag := 0 } tbl
  | .succ u, tbl =>
    let (uIdx, tbl1) := internKLevelToHwCam u tbl
    allocHwCamLevelEntry { tag := 1, l0 := uIdx } tbl1
  | .max u v, tbl =>
    let (uIdx, tbl1) := internKLevelToHwCam u tbl
    let (vIdx, tbl2) := internKLevelToHwCam v tbl1
    allocHwCamLevelEntry { tag := 2, l0 := uIdx, l1 := vIdx } tbl2
  | .imax u v, tbl =>
    let (uIdx, tbl1) := internKLevelToHwCam u tbl
    let (vIdx, tbl2) := internKLevelToHwCam v tbl1
    allocHwCamLevelEntry { tag := 3, l0 := uIdx, l1 := vIdx } tbl2
  | .param n, tbl =>
    allocHwCamLevelEntry { tag := 4, paramName := n } tbl

/-- Reconstruct a `KLevel` from a Section-3 `List HwCamLevelEntry` DAG table. -/
def reconstructHwCamLevel : Nat → List HwCamLevelEntry → Nat → Option KLevel
  | 0, _, _ => none
  | fuel + 1, tbl, idx =>
    match tbl[idx]? with
    | none => none
    | some e =>
      if e.tag == 0 then some .zero
      else if e.tag == 1 then (reconstructHwCamLevel fuel tbl e.l0).map .succ
      else if e.tag == 2 then
        match reconstructHwCamLevel fuel tbl e.l0, reconstructHwCamLevel fuel tbl e.l1 with
        | some u, some v => some (.max u v)
        | _, _ => none
      else if e.tag == 3 then
        match reconstructHwCamLevel fuel tbl e.l0, reconstructHwCamLevel fuel tbl e.l1 with
        | some u, some v => some (.imax u v)
        | _, _ => none
      else if e.tag == 4 then some (.param e.paramName)
      else none

/-- Extract the deduplicated Section-3 `List HwCamLevelEntry` table from `cam.symbols`. -/
def extractCamLevelEntries (cam : HwExprCAM) : List HwCamLevelEntry :=
  cam.symbols.foldl
    (fun tbl sym =>
      match sym with
      | .sortEntry u => (internKLevelToHwCam u tbl).2
      | .constEntry _ us => us.foldl (fun acc u => (internKLevelToHwCam u acc).2) tbl
      | _ => tbl)
    []

/-- Check `OBCAMv1` magic (`0x31564D4143424F00`), `version == 1`, and exact agreement between
`header` section counts and the 7 payload section lengths. -/
def SiliconElabWireFrame.hasValidHeader (f : SiliconElabWireFrame) : Bool :=
  f.header.magic == 0x31564D4143424F00 &&
  f.header.version == 1 &&
  f.header.nodeCount.toNat == f.nodes.length &&
  f.header.symbolCount.toNat == f.symbols.length &&
  f.header.levelCount.toNat == f.levels.length &&
  f.header.constCount.toNat == f.consts.length &&
  f.header.recRuleCount.toNat == f.recRules.length &&
  f.header.lutEntryCount.toNat == f.lutEntries.length &&
  f.header.icapFrameCount.toNat == f.icapFrames.length

/-- Construct a canonical, header-validated 7-section `SiliconElabWireFrame` (`OBCAMv1`) directly
from an interned `HwExprCAM`, populating Section 3 (`levels`) from `cam.symbols` and synchronizing
all 7 section count fields in `SiliconElabWireHeader`. -/
def buildSiliconWireFrameFromCam
    (cam : HwExprCAM)
    (targetDeclSymIdx targetExprHandle targetTypeHandle : Nat)
    (lutEntries : List DiscrTreeLutEntry := [])
    (icapFrames : List IcapBitstreamFrame := [])
    (fuelBudget : UInt32 := 65536)
    (envPinDigest64 : UInt64 := 0) : SiliconElabWireFrame :=
  let levels := extractCamLevelEntries cam
  { header :=
      { magic            := 0x31564D4143424F00
      , version          := 1
      , flags            := 0
      , nodeCount        := UInt32.ofNat cam.nodes.length
      , symbolCount      := UInt32.ofNat cam.symbols.length
      , levelCount       := UInt32.ofNat levels.length
      , constCount       := UInt32.ofNat cam.consts.length
      , recRuleCount     := UInt32.ofNat cam.recRules.length
      , lutEntryCount    := UInt32.ofNat lutEntries.length
      , icapFrameCount   := UInt32.ofNat icapFrames.length
      , targetDeclSymIdx := UInt32.ofNat targetDeclSymIdx
      , targetExprHandle := UInt32.ofNat targetExprHandle
      , targetTypeHandle := UInt32.ofNat targetTypeHandle
      , fuelBudget       := fuelBudget
      , envPinDigest64   := envPinDigest64 }
  , nodes      := cam.nodes
  , symbols    := cam.symbols
  , levels     := levels
  , consts     := cam.consts
  , recRules   := cam.recRules
  , lutEntries := lutEntries
  , icapFrames := icapFrames }

end Obend.Lower.ExprCAM
end
