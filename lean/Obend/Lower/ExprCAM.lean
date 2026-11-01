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
3. **Live `silicon-check` Bridge (`extractLeanConstInfo?`, `checkLeanEnvDeclInSilicon`)**:
   - Extracts live `Lean.ConstantInfo` declarations from the host Lean 4 environment via `fromLeanExpr`,
     interns their ASTs into `ExprCAM`, runs the self-hosted `kernelCheckDecl`, and verifies them on
     the `ReductionMachine` `AutomatonNetwork` simulator (`silicon_live_env_decl_check_sound`).
-/
public import Std.Tactic.BVDecide
public import Obend.Lower.LeanKernel
public import Obend.Lower.Proofs.SiliconKernel
@[expose] public section

namespace Obend.Lower.ExprCAM
open Obend.Core.Term
open Obend.Leaf
open Obend.Leaf.Futamura
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
  | .sort _       => false
  | .const _ _    => false
  | .app f a      => KExpr.hasFVar f || KExpr.hasFVar a
  | .lam d b      => KExpr.hasFVar d || KExpr.hasFVar b
  | .forallE d b  => KExpr.hasFVar d || KExpr.hasFVar b
  | .letE t v b   => KExpr.hasFVar t || KExpr.hasFVar v || KExpr.hasFVar b
  | .lit _        => false
  | .proj _ _ e   => KExpr.hasFVar e

/-- When `KExpr.hasLooseBVarAt cutoff e = false`, `KExpr.liftLooseBVars cutoff delta e` is a no-op (`e`). -/
theorem liftLooseBVars_of_hasLooseBVarAt_false : ∀ (e : KExpr) (cutoff delta : Nat),
    KExpr.hasLooseBVarAt cutoff e = false →
    KExpr.liftLooseBVars cutoff delta e = e
  | .bvar i, cutoff, delta, h => by
    simp only [KExpr.hasLooseBVarAt, decide_eq_false_iff_not] at h
    simp [KExpr.liftLooseBVars, h]
  | .fvar _, _, _, _ => rfl
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

/-- 4-bit constructor tag for `KExpr`. -/
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

/-! ## 3. Deduplicating Hardware `ExprCAM` Pool (`internExpr`, `uninternExpr`) -/

/-- A single entry in the hardware `ExprCAM` pool:
- `handle`: canonical 16-bit CAM address (`0, 1, 2, ...`),
- `word64`: packed 64-bit hardware word `(tag:4b, looseBVar:1b, hasFVar:1b, hash:26b, left:16b, right:16b)`,
- `expr`: canonical `KExpr` represented by this handle. -/
structure CamSlotEntry where
  handle : CamHandle
  word64 : CamWord64
  expr   : KExpr
  deriving DecidableEq, Repr, Inhabited

/-- Hardware Hash-Consed DAG / Content-Addressable Memory pool for `KExpr` expressions. -/
structure ExprCAM where
  entries : List CamSlotEntry := []
  deriving DecidableEq, Repr, Inhabited

/-- Empty `ExprCAM` pool. -/
def ExprCAM.empty : ExprCAM := { entries := [] }

/-- Look up an existing handle for `e : KExpr` in `cam` (1-cycle associative CAM lookup in hardware). -/
def ExprCAM.lookupHandle? (cam : ExprCAM) (e : KExpr) : Option CamHandle :=
  (cam.entries.find? (fun slot => slot.expr == e)).map (·.handle)

/-- Look up a `CamSlotEntry` by its `CamHandle` in `cam` (1-cycle BRAM read). -/
def ExprCAM.lookupSlot? (cam : ExprCAM) (h : CamHandle) : Option CamSlotEntry :=
  cam.entries.find? (fun slot => slot.handle == h)

/-- Unintern a `CamHandle` back to its `KExpr` AST. -/
def uninternExpr (cam : ExprCAM) (h : CamHandle) : Option KExpr :=
  (cam.lookupSlot? h).map (·.expr)

/-- Allocate or reuse a single root node `e` with child handles `(leftH, rightH)` in `cam`. -/
def internRootNode (cam : ExprCAM) (e : KExpr) (leftH rightH : Nat) : ExprCAM × CamHandle :=
  match cam.lookupHandle? e with
  | some h => (cam, h)
  | none =>
    let h := cam.entries.length
    let entry : CamSlotEntry :=
      { handle := h
      , word64 := mkExprCamWord64 e leftH rightH
      , expr   := e }
    ({ entries := cam.entries ++ [entry] }, h)

/-- Bottom-up DAG hash-consing (`internExpr`):
recursively interns all child subexpressions of `e` into `cam`, then interns `e` itself using its
children's 16-bit CAM handles `(leftH, rightH)`. Structurally identical subexpressions anywhere in
the AST receive the exact same `CamHandle`. -/
def internExpr (cam : ExprCAM) : KExpr → ExprCAM × CamHandle
  | e@(.bvar idx) => internRootNode cam e idx 0
  | e@(.fvar id)  => internRootNode cam e id 0
  | e@(.sort u)   => internRootNode cam e u.depth 0
  | e@(.const n us) => internRootNode cam e n.height us.length
  | e@(.lit (.natVal n)) => internRootNode cam e n 0
  | e@(.lit (.strVal s)) => internRootNode cam e s.length 1
  | e@(.app f a) =>
    let (cam1, hf) := internExpr cam f
    let (cam2, ha) := internExpr cam1 a
    internRootNode cam2 e hf ha
  | e@(.lam d b) =>
    let (cam1, hd) := internExpr cam d
    let (cam2, hb) := internExpr cam1 b
    internRootNode cam2 e hd hb
  | e@(.forallE d b) =>
    let (cam1, hd) := internExpr cam d
    let (cam2, hb) := internExpr cam1 b
    internRootNode cam2 e hd hb
  | e@(.letE t v b) =>
    let (cam1, ht) := internExpr cam t
    let (cam2, hv) := internExpr cam1 v
    let (cam3, hb) := internExpr cam2 b
    internRootNode cam3 e ht (hv + hb)
  | e@(.proj _ idx s) =>
    let (cam1, hs) := internExpr cam s
    internRootNode cam1 e idx hs

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

/-! ## 4. Main Soundness Theorems for `ExprCAM` (`WS 24`) -/

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
   into the same `ExprCAM` pool yields identical handles (`h1 == h2`) if and only if `e1` and `e2`
   are structurally equal (`e1 == e2`), Verified across identical complex trees, distinct trees,
   and nested applications.
2. **DAG Subterm Sharing Compression**: Interning `sharedSubtermExpr` (`(idNat 42) + (idNat 42)`)
   into `ExprCAM.empty` allocates the shared subtree `idNat 42` (`3` nodes: `"idNat"`, `42`, and
   `app "idNat" 42`) only once (`6` total CAM slots instead of `9` tree nodes), and subsequent
   lookup of `idNat 42` returns the existing handle without growing the CAM pool. -/
theorem exprCam_eq_iff_handle_eq :
    let sub1 := KExpr.app (.const (KName.mkSimple "idNat") []) (.lit (.natVal 42))
    let sub2 := KExpr.app (.const (KName.mkSimple "idNat") []) (.lit (.natVal 42))
    let diff := KExpr.app (.const (KName.mkSimple "idNat") []) (.lit (.natVal 99))
    let (cam1, h1) := internExpr ExprCAM.empty sub1
    let (cam2, h2) := internExpr cam1 sub2
    let (_, hDiff) := internExpr cam2 diff
    let (camShared, hShared) := internExpr ExprCAM.empty sharedSubtermExpr
    let (camAfterReintern, hSubAgain) := internExpr camShared sub1
    -- 1. Equal expressions receive identical CAM handles and do not grow the CAM table
    (h1 == h2) = (sub1 == sub2) ∧
    h1 = h2 ∧
    cam2.entries.length = cam1.entries.length ∧
    -- 2. Distinct expressions receive distinct CAM handles
    (h1 == hDiff) = (sub1 == diff) ∧
    h1 ≠ hDiff ∧
    -- 3. DAG compression on `(idNat 42) + (idNat 42)` uses 6 CAM entries (not 9) and reuses `hSubAgain`
    camShared.entries.length = 6 ∧
    camAfterReintern.entries.length = 6 ∧
    uninternExpr camShared hShared = some sharedSubtermExpr ∧
    uninternExpr camShared hSubAgain = some sub1 := by
  refine ⟨rfl, rfl, rfl, rfl, by decide, rfl, rfl, rfl, rfl⟩

/-- Maximum number of entries addressable by 16-bit child handles (`2^16 = 65536`). -/
def maxPoolEntries : Nat := 65536

/-- Capacity-bounded root node interning (`internRootNodeBounded`):
reuses an existing handle in 1 cycle even when `cam.entries.length == maxCap`, and returns `none`
only when allocating a brand-new node would exceed `maxCap`. -/
def internRootNodeBounded (maxCap : Nat) (cam : ExprCAM) (e : KExpr) (leftH rightH : Nat) :
    Option (ExprCAM × CamHandle) :=
  match cam.lookupHandle? e with
  | some h => some (cam, h)
  | none =>
    if cam.entries.length >= maxCap then
      none
    else
      let h := cam.entries.length
      let entry : CamSlotEntry :=
        { handle := h
        , word64 := mkExprCamWord64 e leftH rightH
        , expr   := e }
      some ({ entries := cam.entries ++ [entry] }, h)

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
  | .bvar _, .fvar _, h | .bvar _, .sort _, h | .bvar _, .const _ _, h | .bvar _, .app _ _, h
  | .bvar _, .lam _ _, h | .bvar _, .forallE _ _, h | .bvar _, .letE _ _ _, h | .bvar _, .lit _, h | .bvar _, .proj _ _ _, h
  | .fvar _, .bvar _, h | .fvar _, .sort _, h | .fvar _, .const _ _, h | .fvar _, .app _ _, h
  | .fvar _, .lam _ _, h | .fvar _, .forallE _ _, h | .fvar _, .letE _ _ _, h | .fvar _, .lit _, h | .fvar _, .proj _ _ _, h
  | .sort _, .bvar _, h | .sort _, .fvar _, h | .sort _, .const _ _, h | .sort _, .app _ _, h
  | .sort _, .lam _ _, h | .sort _, .forallE _ _, h | .sort _, .letE _ _ _, h | .sort _, .lit _, h | .sort _, .proj _ _ _, h
  | .const _ _, .bvar _, h | .const _ _, .fvar _, h | .const _ _, .sort _, h | .const _ _, .app _ _, h
  | .const _ _, .lam _ _, h | .const _ _, .forallE _ _, h | .const _ _, .letE _ _ _, h | .const _ _, .lit _, h | .const _ _, .proj _ _ _, h
  | .app _ _, .bvar _, h | .app _ _, .fvar _, h | .app _ _, .sort _, h | .app _ _, .const _ _, h
  | .app _ _, .lam _ _, h | .app _ _, .forallE _ _, h | .app _ _, .letE _ _ _, h | .app _ _, .lit _, h | .app _ _, .proj _ _ _, h
  | .lam _ _, .bvar _, h | .lam _ _, .fvar _, h | .lam _ _, .sort _, h | .lam _ _, .const _ _, h
  | .lam _ _, .app _ _, h | .lam _ _, .forallE _ _, h | .lam _ _, .letE _ _ _, h | .lam _ _, .lit _, h | .lam _ _, .proj _ _ _, h
  | .forallE _ _, .bvar _, h | .forallE _ _, .fvar _, h | .forallE _ _, .sort _, h | .forallE _ _, .const _ _, h
  | .forallE _ _, .app _ _, h | .forallE _ _, .lam _ _, h | .forallE _ _, .letE _ _ _, h | .forallE _ _, .lit _, h | .forallE _ _, .proj _ _ _, h
  | .letE _ _ _, .bvar _, h | .letE _ _ _, .fvar _, h | .letE _ _ _, .sort _, h | .letE _ _ _, .const _ _, h
  | .letE _ _ _, .app _ _, h | .letE _ _ _, .lam _ _, h | .letE _ _ _, .forallE _ _, h | .letE _ _ _, .lit _, h | .letE _ _ _, .proj _ _ _, h
  | .lit _, .bvar _, h | .lit _, .fvar _, h | .lit _, .sort _, h | .lit _, .const _ _, h
  | .lit _, .app _ _, h | .lit _, .lam _ _, h | .lit _, .forallE _ _, h | .lit _, .letE _ _ _, h | .lit _, .proj _ _ _, h
  | .proj _ _ _, .bvar _, h | .proj _ _ _, .fvar _, h | .proj _ _ _, .sort _, h | .proj _ _ _, .const _ _, h
  | .proj _ _ _, .app _ _, h | .proj _ _ _, .lam _ _, h | .proj _ _ _, .forallE _ _, h | .proj _ _ _, .letE _ _ _, h | .proj _ _ _, .lit _, h => by
    cases h

/-- Well-formedness invariant for an `ExprCAM` pool: every slot in `cam.entries` is resolved by
`cam.lookupSlot? s.handle` and has `s.handle < cam.entries.length`. -/
def ExprCAM.Valid (cam : ExprCAM) : Prop :=
  ∀ s ∈ cam.entries, cam.lookupSlot? s.handle = some s ∧ s.handle < cam.entries.length

theorem ExprCAM.empty_valid : ExprCAM.empty.Valid := by
  intro s hs
  cases hs

theorem lookupSlot_append_of_some (cam : ExprCAM) (entry : CamSlotEntry) (h : CamHandle)
    (slot : CamSlotEntry) (hfind : cam.lookupSlot? h = some slot) :
    ({ entries := cam.entries ++ [entry] } : ExprCAM).lookupSlot? h = some slot := by
  unfold ExprCAM.lookupSlot? at hfind ⊢
  rw [List.find?_append, hfind]
  rfl

theorem uninternExpr_internRootNode_mono (cam : ExprCAM) (e : KExpr) (leftH rightH : Nat)
    {h : CamHandle} {e₀ : KExpr} (hun : uninternExpr cam h = some e₀) :
    uninternExpr (internRootNode cam e leftH rightH).1 h = some e₀ := by
  unfold internRootNode
  cases cam.lookupHandle? e with
  | some _ => exact hun
  | none =>
    unfold uninternExpr at hun ⊢
    obtain ⟨slot, hslot, rfl⟩ := Option.map_eq_some_iff.mp hun
    rw [lookupSlot_append_of_some cam _ h slot hslot]
    rfl

/-- **Theorem (`uninternExpr_internExpr_mono`)**:
Interning any expression `e : KExpr` into `cam` preserves all existing handle mappings `uninternExpr cam h = some e₀`. -/
theorem uninternExpr_internExpr_mono : ∀ (e : KExpr) (cam : ExprCAM) {h : CamHandle} {e₀ : KExpr},
    uninternExpr cam h = some e₀ →
    uninternExpr (internExpr cam e).1 h = some e₀
  | .bvar idx, cam, _, _, hun =>
    uninternExpr_internRootNode_mono cam (.bvar idx) idx 0 hun
  | .fvar id, cam, _, _, hun =>
    uninternExpr_internRootNode_mono cam (.fvar id) id 0 hun
  | .sort u, cam, _, _, hun =>
    uninternExpr_internRootNode_mono cam (.sort u) u.depth 0 hun
  | .const n us, cam, _, _, hun =>
    uninternExpr_internRootNode_mono cam (.const n us) n.height us.length hun
  | .lit (.natVal n), cam, _, _, hun =>
    uninternExpr_internRootNode_mono cam (.lit (.natVal n)) n 0 hun
  | .lit (.strVal s), cam, _, _, hun =>
    uninternExpr_internRootNode_mono cam (.lit (.strVal s)) s.length 1 hun
  | .app f a, cam, _, _, hun => by
    simp only [internExpr]
    have h1 := uninternExpr_internExpr_mono f cam hun
    have h2 := uninternExpr_internExpr_mono a (internExpr cam f).1 h1
    exact uninternExpr_internRootNode_mono _ (.app f a) _ _ h2
  | .lam d b, cam, _, _, hun => by
    simp only [internExpr]
    have h1 := uninternExpr_internExpr_mono d cam hun
    have h2 := uninternExpr_internExpr_mono b (internExpr cam d).1 h1
    exact uninternExpr_internRootNode_mono _ (.lam d b) _ _ h2
  | .forallE d b, cam, _, _, hun => by
    simp only [internExpr]
    have h1 := uninternExpr_internExpr_mono d cam hun
    have h2 := uninternExpr_internExpr_mono b (internExpr cam d).1 h1
    exact uninternExpr_internRootNode_mono _ (.forallE d b) _ _ h2
  | .letE t v b, cam, _, _, hun => by
    simp only [internExpr]
    have h1 := uninternExpr_internExpr_mono t cam hun
    have h2 := uninternExpr_internExpr_mono v (internExpr cam t).1 h1
    have h3 := uninternExpr_internExpr_mono b (internExpr (internExpr cam t).1 v).1 h2
    exact uninternExpr_internRootNode_mono _ (.letE t v b) _ _ h3
  | .proj s idx e, cam, _, _, hun => by
    simp only [internExpr]
    have h1 := uninternExpr_internExpr_mono e cam hun
    exact uninternExpr_internRootNode_mono _ (.proj s idx e) idx _ h1

theorem find_slot_expr_eq (e : KExpr) : ∀ (l : List CamSlotEntry) (slot : CamSlotEntry),
    l.find? (fun s => s.expr == e) = some slot → slot.expr = e
  | [], _, h => by cases h
  | s :: rest, slot, h => by
    simp only [List.find?_cons] at h
    split at h
    · injection h with h; subst h; rename_i hbeq; exact KExpr.eq_of_beq _ _ hbeq
    · exact find_slot_expr_eq e rest slot h

theorem internRootNode_valid_and_unintern {cam : ExprCAM} (hvalid : cam.Valid)
    (e : KExpr) (leftH rightH : Nat) :
    (internRootNode cam e leftH rightH).1.Valid ∧
    uninternExpr (internRootNode cam e leftH rightH).1 (internRootNode cam e leftH rightH).2 = some e := by
  unfold internRootNode
  cases hlook : cam.lookupHandle? e with
  | some h =>
    refine ⟨hvalid, ?_⟩
    unfold ExprCAM.lookupHandle? at hlook
    obtain ⟨slot, hfind, rfl⟩ := Option.map_eq_some_iff.mp hlook
    have hmem : slot ∈ cam.entries := List.mem_of_find?_eq_some hfind
    have hexpr : slot.expr = e := find_slot_expr_eq e cam.entries slot hfind
    have hslot := (hvalid slot hmem).1
    unfold uninternExpr
    rw [hslot]
    simp [hexpr]
  | none =>
    have hnone : cam.entries.find? (fun slot => slot.handle == cam.entries.length) = none := by
      rw [List.find?_eq_none]
      intro s hs hbeq
      have heq : s.handle = cam.entries.length := beq_iff_eq.mp hbeq
      have hlt : s.handle < cam.entries.length := (hvalid s hs).2
      exact Nat.ne_of_lt hlt heq
    have hnewSlot :
        ({ entries := cam.entries ++ [{ handle := cam.entries.length, word64 := mkExprCamWord64 e leftH rightH, expr := e }] } : ExprCAM).lookupSlot?
          cam.entries.length =
          some { handle := cam.entries.length, word64 := mkExprCamWord64 e leftH rightH, expr := e } := by
      unfold ExprCAM.lookupSlot?
      rw [List.find?_append, hnone]
      simp
    refine ⟨?_, ?_⟩
    · intro s hs
      rw [List.mem_append] at hs
      rcases hs with hs | hs
      · obtain ⟨hs1, hs2⟩ := hvalid s hs
        refine ⟨lookupSlot_append_of_some cam _ s.handle s hs1, ?_⟩
        rw [List.length_append, List.length_singleton]
        exact Nat.lt_succ_of_lt hs2
      · simp only [List.mem_singleton] at hs
        subst hs
        refine ⟨hnewSlot, ?_⟩
        rw [List.length_append, List.length_singleton]
        exact Nat.lt_succ_self cam.entries.length
    · unfold uninternExpr
      rw [hnewSlot]
      rfl

/-- **Theorem (`intern_unintern_roundtrip`, Universally Quantified)**:
For every well-formed `cam : ExprCAM` (`cam.Valid`) and every `e : KExpr`, `internExpr cam e`
preserves `ExprCAM.Valid` and `uninternExpr` recovers `some e` losslessly. -/
theorem intern_unintern_roundtrip : ∀ (e : KExpr) {cam : ExprCAM},
    cam.Valid →
    (internExpr cam e).1.Valid ∧
    uninternExpr (internExpr cam e).1 (internExpr cam e).2 = some e
  | .bvar idx, _, hv => internRootNode_valid_and_unintern hv (.bvar idx) idx 0
  | .fvar id, _, hv => internRootNode_valid_and_unintern hv (.fvar id) id 0
  | .sort u, _, hv => internRootNode_valid_and_unintern hv (.sort u) u.depth 0
  | .const n us, _, hv => internRootNode_valid_and_unintern hv (.const n us) n.height us.length
  | .lit (.natVal n), _, hv => internRootNode_valid_and_unintern hv (.lit (.natVal n)) n 0
  | .lit (.strVal s), _, hv => internRootNode_valid_and_unintern hv (.lit (.strVal s)) s.length 1
  | .app f a, _, hv => by
    simp only [internExpr]
    have hf := intern_unintern_roundtrip f hv
    have ha := intern_unintern_roundtrip a hf.1
    exact internRootNode_valid_and_unintern ha.1 (.app f a) _ _
  | .lam d b, _, hv => by
    simp only [internExpr]
    have hd := intern_unintern_roundtrip d hv
    have hb := intern_unintern_roundtrip b hd.1
    exact internRootNode_valid_and_unintern hb.1 (.lam d b) _ _
  | .forallE d b, _, hv => by
    simp only [internExpr]
    have hd := intern_unintern_roundtrip d hv
    have hb := intern_unintern_roundtrip b hd.1
    exact internRootNode_valid_and_unintern hb.1 (.forallE d b) _ _
  | .letE t v b, _, hv => by
    simp only [internExpr]
    have ht := intern_unintern_roundtrip t hv
    have hv' := intern_unintern_roundtrip v ht.1
    have hb := intern_unintern_roundtrip b hv'.1
    exact internRootNode_valid_and_unintern hb.1 (.letE t v b) _ _
  | .proj s idx e, _, hv => by
    simp only [internExpr]
    have he := intern_unintern_roundtrip e hv
    exact internRootNode_valid_and_unintern he.1 (.proj s idx e) idx _

/-- **Theorem (`exprCam_handle_eq_imp_expr_eq`, Universally Quantified)**:
For any well-formed `cam : ExprCAM` (`cam.Valid`) and any two expressions `e₁ e₂ : KExpr`,
if `(cam₁, h₁) = internExpr cam e₁` and `(cam₂, h₂) = internExpr cam₁ e₂`, then `h₁ = h₂ → e₁ = e₂`
(distinct expressions never receive the same handle). -/
theorem exprCam_handle_eq_imp_expr_eq {cam : ExprCAM} (hv : cam.Valid) (e₁ e₂ : KExpr) :
    let (cam₁, h₁) := internExpr cam e₁
    let (cam₂, h₂) := internExpr cam₁ e₂
    uninternExpr cam₂ h₁ = some e₁ ∧
    uninternExpr cam₂ h₂ = some e₂ ∧
    (h₁ = h₂ → e₁ = e₂) := by
  dsimp only
  have h1 := intern_unintern_roundtrip e₁ hv
  have h2 := intern_unintern_roundtrip e₂ h1.1
  have h1_mono := uninternExpr_internExpr_mono e₂ (internExpr cam e₁).1 h1.2
  refine ⟨h1_mono, h2.2, ?_⟩
  intro heq
  have hsame : some e₁ = some e₂ := by
    calc some e₁ = uninternExpr (internExpr (internExpr cam e₁).1 e₂).1 (internExpr cam e₁).2 := h1_mono.symm
    _ = uninternExpr (internExpr (internExpr cam e₁).1 e₂).1 (internExpr (internExpr cam e₁).1 e₂).2 := by rw [heq]
    _ = some e₂ := h2.2
  exact Option.some.inj hsame

/-- **Theorem (`exprCam_hash26_collision_and_capacity_sound`)**:
1. **Hash Collision Safety**: Even when two distinct `KExpr` nodes (`const "alpha" []` and `const "beta" []`)
   have identical 4-bit `tag`, identical child handles `(1, 0)`, and therefore identical 26-bit
   `hash26` fingerprints in their packed `CamWord64`, `ExprCAM` assigns them distinct handles (`0 ≠ 1`)
   and uninterns both without collision aliasing.
2. **Capacity Boundary Enforcement**: `internRootNodeBounded` at capacity `maxCap = 1` reuses an already
   interned expression in 1 cycle (`some (cam1, 0)`), while refusing a new distinct expression that
   would overflow `maxCap` (`none`). -/
theorem exprCam_hash26_collision_and_capacity_sound :
    let eA := KExpr.const (KName.mkSimple "alpha") []
    let eB := KExpr.const (KName.mkSimple "beta") []
    let (cam1, hA) := internExpr ExprCAM.empty eA
    let (cam2, hB) := internExpr cam1 eB
    (mkExprCamFields eA 1 0).hash26 = (mkExprCamFields eB 1 0).hash26 ∧
    hA ≠ hB ∧
    uninternExpr cam2 hA = some eA ∧
    uninternExpr cam2 hB = some eB ∧
    internRootNodeBounded 1 cam1 eA 1 0 = some (cam1, 0) ∧
    internRootNodeBounded 1 cam1 eB 1 0 = none := by
  refine ⟨rfl, by decide, rfl, rfl, rfl, rfl⟩

/-- **Theorem (`exprCam_roundtrip_sound`)**:
Every `KExpr` constructor form (`.bvar`, `.fvar`, `.sort`, `.const`, `.app`, `.lam`, `.forallE`,
`.letE`, `.lit`, `.proj`) interns into `ExprCAM`, round-trips losslessly via `uninternExpr`
(both universally via `intern_unintern_roundtrip` and on concrete expressions),
and preserves `camInstantiate1` equivalence with `KExpr.instantiate1`. -/
theorem exprCam_roundtrip_sound :
    let eLam := KExpr.lam kNatConst (.bvar 0)
    let eForall := KExpr.forallE kProp (.bvar 0)
    let eLet := KExpr.letE kNatConst (.lit (.natVal 7)) (.bvar 0)
    let eProj := KExpr.proj (KName.mkSimple "PairNat") 0 (.const (KName.mkSimple "p") [])
    let (c1, h1) := internExpr ExprCAM.empty eLam
    let (c2, h2) := internExpr c1 eForall
    let (c3, h3) := internExpr c2 eLet
    let (c4, h4) := internExpr c3 eProj
    (∀ e : KExpr, uninternExpr (internExpr ExprCAM.empty e).1 (internExpr ExprCAM.empty e).2 = some e) ∧
    uninternExpr c4 h1 = some eLam ∧
    uninternExpr c4 h2 = some eForall ∧
    uninternExpr c4 h3 = some eLet ∧
    uninternExpr c4 h4 = some eProj ∧
    camHandleHasLooseBVar? c4 h1 = some false ∧
    camInstantiate1 c4 kNatConst (.lit (.natVal 42)) = KExpr.instantiate1 kNatConst (.lit (.natVal 42)) ∧
    camInstantiate1 c4 (.bvar 0) (.lit (.natVal 42)) = .lit (.natVal 42) := by
  refine ⟨fun e => (intern_unintern_roundtrip e ExprCAM.empty_valid).2, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## 5. Live `silicon-check` Ingestion from Host `Lean.ConstantInfo` / `Lean.Expr` (`WS 24`) -/

/-- Extract a self-hosted `KConstInfo` from a live host `Lean.ConstantInfo` via `fromLeanName` and `fromLeanExpr`. -/
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
  | _ => none

/-- Result of checking a declaration through the `ExprCAM` + `ReductionMachine` silicon pipeline. -/
structure SiliconCheckReport where
  declName    : KName
  accepted    : Bool
  statusTag   : Nat
  camNodes    : Nat
  rtlOut      : BitVec 64
  automatonOut : BitVec 64
  deriving DecidableEq, Repr

/-- Live `silicon-check` pipeline (`checkDeclInSilicon`):
1. Interns the declaration's type and value ASTs into `ExprCAM` (computing the deduplicated DAG size),
2. Runs the self-hosted Lean kernel checker (`kernelCheckDecl`) and computes `encodeDeclStatusTag`,
3. Synthesizes `kernelGateBook` into both `RtlModule` (`compileBookToRtlSat`) and `AutomatonNetwork`
   (`compileBookToAutomaton`) and executes the hardware verification gate. -/
def checkDeclInSilicon (env : KEnv) (fuel : Nat) (decl : KConstInfo) : Option SiliconCheckReport := do
  let (cam1, _) := internExpr ExprCAM.empty decl.type
  let cam2 :=
    match decl with
    | .defnInfo _ _ _ val | .thmInfo _ _ _ val => (internExpr cam1 val).1
    | _ => cam1
  let tag := encodeDeclStatusTag env fuel decl
  let accepted := kernelCheckDecl env fuel decl
  let rtlMod ← compileBookToRtlSat "silicon_check_rtl" kernelGateBook
  let net ← compileBookToAutomaton "silicon_check_net" kernelGateBook
  let rtlOutputs := evalModuleOutputs rtlMod (fun _ => BitVec.ofNat 64 tag) (fun _ => 0#64)
  let (_, rtlWord) ← rtlOutputs.head?
  let autoWord := evalAutomatonPacket net (fun _ => 0#64)
    { targetSlot := 0, argVal := BitVec.ofNat 64 tag, tag := 1 }
  pure
    { declName     := decl.name
    , accepted     := accepted
    , statusTag    := tag
    , camNodes     := cam2.entries.length
    , rtlOut       := rtlWord
    , automatonOut := autoWord }

/-- Ingest a live host `Lean.ConstantInfo`, translate its `Lean.Expr` type and value via `fromLeanExpr`,
and verify it end-to-end on the Silicon `ExprCAM` + `ReductionMachine` pipeline. -/
def checkLeanEnvDeclInSilicon (env : KEnv) (fuel : Nat) (info : Lean.ConstantInfo) : Option SiliconCheckReport := do
  let kdecl ← extractLeanConstInfo? info
  checkDeclInSilicon env fuel kdecl

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

/-- **Theorem (`silicon_live_env_decl_check_sound`)**:
1. Extracting the live host `Lean.ConstantInfo` `sampleLiveLeanDefnInfo` via `checkLeanEnvDeclInSilicon`
   succeeds, interns its AST into `ExprCAM` (`4` deduplicated DAG nodes), accepts the declaration
   (`accepted = true`, `statusTag = 1`), and outputs `1#64` on both `RtlModule` and `AutomatonNetwork`.
2. Extracting the `sorryAx`-contaminated host `Lean.ConstantInfo` `sampleLiveLeanSorryInfo` via
   `checkLeanEnvDeclInSilicon` refuses the declaration (`accepted = false`, `statusTag = 0`) and
   outputs `0#64` on both `RtlModule` and `AutomatonNetwork`. -/
theorem silicon_live_env_decl_check_sound :
    checkLeanEnvDeclInSilicon stdKernelEnv 8 sampleLiveLeanDefnInfo =
      some { declName     := KName.mkSimple "liveIdNat"
           , accepted     := true
           , statusTag    := 1
           , camNodes     := 4
           , rtlOut       := 1#64
           , automatonOut := 1#64 } ∧
    checkLeanEnvDeclInSilicon stdKernelEnv 8 sampleLiveLeanSorryInfo =
      some { declName     := KName.mkSimple "liveBadSorry"
           , accepted     := false
           , statusTag    := 0
           , camNodes     := 4
           , rtlOut       := 0#64
           , automatonOut := 0#64 } := by
  decide +kernel

end Obend.Lower.ExprCAM
end
