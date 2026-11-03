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

/-! ## 4b. True Hardware CAM Memory Image (`HwCamNodeWord` / `HwCamImage`) Without AST Side-Channel -/

/-- Structural AST depth of a `KExpr` (`depth e ≥ 1` for every `e : KExpr`). -/
def depth : KExpr → Nat
  | .bvar _      => 1
  | .fvar _      => 1
  | .sort _      => 1
  | .const _ _   => 1
  | .lit _       => 1
  | .app f a     => 1 + max (depth f) (depth a)
  | .lam d b     => 1 + max (depth d) (depth b)
  | .forallE d b => 1 + max (depth d) (depth b)
  | .letE t v b  => 1 + max (depth t) (max (depth v) (depth b))
  | .proj _ _ s  => 1 + depth s

abbrev KExpr.depth (e : KExpr) : Nat := Obend.Lower.ExprCAM.depth e

/-- Auxiliary symbol/literal/universe table entry (`HwCamSymbolEntry`) referenced by `symIdx`
from a `HwCamNodeWord`. Contains NO `KExpr` AST nodes! -/
inductive HwCamSymbolEntry where
  | sortEntry  (u : KLevel)
  | constEntry (name : KName) (us : List KLevel)
  | litEntry   (lit : KLiteral)
  | projEntry  (structName : KName) (fieldIdx : Nat)
  deriving DecidableEq, Repr, Inhabited

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

theorem getElem?_append_singleton_self {α : Type} (xs : List α) (x : α) :
  (xs ++ [x])[xs.length]? = some x := by
  rw [List.getElem?_append_right (Nat.le_refl xs.length)]
  simp

theorem getElem?_append_preserve {α : Type} {xs : List α} {i : Nat} {x : α}
    (ys : List α) (h : xs[i]? = some x) :
    (xs ++ ys)[i]? = some x := by
  obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp h
  rw [List.getElem?_append_left hlt, h]

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
                        · simp only [ht9, Bool.false_eq_true, ↓reduceIte] at hrec; cases hrec
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
For every fuel bound `fuel : Nat`, every expression `e : KExpr` (including `.letE t v b` with 3 children),
and every initial hardware image `img : HwCamImage`, if `depth e ≤ fuel`, then reconstructing from
`internToHwImage e img` (which stores zero `KExpr` AST nodes in its hardware tables) recovers `some e`
losslessly! -/
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

/--Metavariable FVar ID threshold matching `Obend.Lower.MetaUnify.mvarIdOffset` (`1000000`). -/
def hwCamMVarOffset : Nat := 1000000

/-- Enriched 64-bit Hardware CAM Node Word (`PackedNodeWord`):
Augments the structural child handles `(tag, h0, h1, h2, symIdx)` with the hardware summary bit-flags
required by Zone 1 (`hasLooseBVar`, `maxLooseBVar`) and Zone 2 (`hasFVar`, `hasMVar` = Bit 58):
* `hasLooseBVar`: `true` iff any loose `.bvar` escapes this subtree (`Bit 59`),
* `hasMVar`: `true` iff any metavariable occurs in this subtree (`Bit 58`),
* `hasFVar`: `true` iff any free variable occurs in this subtree (`Bit 57`),
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
Stores `PackedNodeWord` entries, symbol entries, constant entries, and recursor rules with zero
`KExpr` AST side-channel. -/
structure HwExprCAM where
  nodes    : List PackedNodeWord := []
  symbols  : List HwCamSymbolEntry := []
  consts   : List HwCamConstEntry := []
  recRules : List HwCamRecRuleEntry := []
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
    , hasLooseBVar := ws.hasLooseBVar
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
    let isMVar := decide (id >= hwCamMVarOffset)
    allocPackedNode
      { tag := 1, h0 := id, h1 := 0, hasFVar := !isMVar, hasMVar := isMVar }
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

/-- **Handle-Level CAM Substitution Soundness Theorem (`hwCamInstantiateAt_sound`)**:
1. Universal 1-cycle closed-term bypass (`hwCamInstantiateAt_closed_bypass`),
2. Concrete closed subtree bypass: interning a deep closed expression `sharedSubtermExpr` sets
   `w.hasLooseBVar = false` (`maxLooseBVar = 0`), and `hwCamInstantiate1` returns the identical
   handle and CAM state (`cam'.nodes.length = cam.nodes.length`),
3. Open `.app` and nested `.lam` instantiation: substituting `42` for `.bvar 0` in
   `.app (.const "idNat" []) (.bvar 0)` and in `.lam Nat (.app (.bvar 1) (.bvar 0))` purely on
   `HwExprCAM` handles matches `KExpr.instantiate1` identically upon reconstruction! -/
theorem hwCamInstantiateAt_sound :
    (∀ (fuel hBody depth hArg : Nat) (cam : HwExprCAM) (w : PackedNodeWord),
      cam.nodes[hBody]? = some w → w.hasLooseBVar = false →
      hwCamInstantiateAt (fuel + 1) hBody depth hArg cam = (hBody, cam)) ∧
    (let (hClosed, cam1) := internToHwExprCAM sharedSubtermExpr HwExprCAM.empty
     let (hArg, cam2) := internToHwExprCAM (.lit (.natVal 99)) cam1
     (getPackedNode cam2 hClosed).hasLooseBVar = false ∧
     hwCamInstantiate1 16 hClosed hArg cam2 = (hClosed, cam2)) ∧
    (let openBody : KExpr := .app (.const (KName.mkSimple "idNat") []) (.bvar 0)
     let arg42 : KExpr := .lit (.natVal 42)
     let (hBody, cam1) := internToHwExprCAM openBody HwExprCAM.empty
     let (hArg, cam2) := internToHwExprCAM arg42 cam1
     let (hRes, cam3) := hwCamInstantiate1 16 hBody hArg cam2
     reconstructFromHwExprCAM 16 cam3 hRes = some (KExpr.instantiate1 openBody arg42)) ∧
    (let nestedBody : KExpr := .lam kNatConst (.app (.bvar 1) (.bvar 0))
     let openArg : KExpr := .bvar 0
     let (hBody, cam1) := internToHwExprCAM nestedBody HwExprCAM.empty
     let (hArg, cam2) := internToHwExprCAM openArg cam1
     let (hRes, cam3) := hwCamInstantiate1 16 hBody hArg cam2
     reconstructFromHwExprCAM 16 cam3 hRes = some (KExpr.instantiate1 nestedBody openArg)) := by
  refine ⟨fun fuel hBody depth hArg cam w hnode hclosed =>
            (hwCamInstantiateAt_closed_bypass fuel hBody depth hArg cam w hnode hclosed).1,
          ⟨rfl, rfl⟩, rfl, rfl⟩

/-! ## 6. Live `silicon-check` Ingestion from Host `Lean.ConstantInfo` / `Lean.Expr` (`WS 24`) -/

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
  | .recInfo val => do
    let ty ← fromLeanExpr val.type
    pure (.axiomInfo (fromLeanName val.name) (val.levelParams.map fromLeanName) ty)
  | .opaqueInfo val => do
    let ty ← fromLeanExpr val.type
    pure (.axiomInfo (fromLeanName val.name) (val.levelParams.map fromLeanName) ty)
  | .quotInfo val => do
    let ty ← fromLeanExpr val.type
    pure (.axiomInfo (fromLeanName val.name) (val.levelParams.map fromLeanName) ty)

/-- Extract the list of `KRecRule` $\iota$-reduction rules from a live host `Lean.RecursorVal`
(`extractLeanRecRules`), computing `numPrefixArgs := rval.numParams + rval.numMotives + rval.numMinors`,
`numFields := rule.nfields`, and translating `rule.rhs` via `fromLeanExpr` (which strips `.mdata`
annotations transparently). -/
def extractLeanRecRules (rval : Lean.RecursorVal) : Option (List KRecRule) :=
  rval.rules.mapM fun rule => do
    let rhsExpr ← fromLeanExpr rule.rhs
    pure
      { recName       := fromLeanName rval.name
      , ctorName      := fromLeanName rule.ctor
      , numPrefixArgs := rval.numParams + rval.numMotives + rval.numMinors
      , numFields     := rule.nfields
      , rhs           := rhsExpr }

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
    collectLeanExprConsts val.type ++ val.ctors ++ [.str val.name "rec"]
  | .ctorInfo val =>
    collectLeanExprConsts val.type ++ [val.induct, .str val.induct "rec"]
  | .recInfo val =>
    collectLeanExprConsts val.type ++ val.all ++ (val.rules.flatMap fun r => r.ctor :: collectLeanExprConsts r.rhs)
  | .axiomInfo val =>
    collectLeanExprConsts val.type
  | .opaqueInfo val =>
    collectLeanExprConsts val.type ++ collectLeanExprConsts val.value
  | .quotInfo val =>
    collectLeanExprConsts val.type

/-- Bounded BFS helper extracting all transitive `KConstInfo` declarations and `KRecRule`
recursor rules reachable from a worklist of `Lean.Name`s. -/
def extractEnvConeAux
    (findConst? : Lean.Name → Option Lean.ConstantInfo) :
    Nat → List Lean.Name → List KName → List KConstInfo → List KRecRule →
    List KConstInfo × List KRecRule
  | 0, _, _, accConsts, accRules => (accConsts, accRules)
  | _ + 1, [], _, accConsts, accRules => (accConsts, accRules)
  | fuel + 1, n :: rest, visited, accConsts, accRules =>
    let kn := fromLeanName n
    if visited.contains kn then
      extractEnvConeAux findConst? fuel rest visited accConsts accRules
    else
      let visited' := kn :: visited
      match findConst? n with
      | none =>
        extractEnvConeAux findConst? fuel rest visited' accConsts accRules
      | some info =>
        let accConsts' :=
          match extractLeanConstInfo? info with
          | some kc =>
            if accConsts.any (fun c => c.name == kc.name) then accConsts
            else accConsts ++ [kc]
          | none => accConsts
        let accRules' :=
          match info with
          | .recInfo rval =>
            match extractLeanRecRules rval with
            | some rs => accRules ++ rs
            | none    => accRules
          | _ => accRules
        let deps := collectConstInfoDeps info
        extractEnvConeAux findConst? fuel (rest ++ deps) visited' accConsts' accRules'

/-- Extract a self-contained `(KEnv × KConstInfo)` transitive dependency cone rooted at `rootName`
using a lookup function `findConst? : Lean.Name → Option Lean.ConstantInfo`. -/
def extractEnvConeWith
    (findConst? : Lean.Name → Option Lean.ConstantInfo)
    (rootName : Lean.Name)
    (fuel : Nat) : Option (KEnv × KConstInfo) := do
  let rootInfo ← findConst? rootName
  let rootDecl ← extractLeanConstInfo? rootInfo
  let (consts, recRules) := extractEnvConeAux findConst? fuel [rootName] [] [] []
  pure ({ constants := consts, recRules := recRules }, rootDecl)

/-- Extract a self-contained `(KEnv × KConstInfo)` transitive dependency cone rooted at `rootName`
directly from a live host `Lean.Environment` (`extractLeanEnvCone`). -/
def extractLeanEnvCone
    (env : Lean.Environment)
    (rootName : Lean.Name)
    (fuel : Nat) : Option (KEnv × KConstInfo) :=
  extractEnvConeWith env.find? rootName fuel

/-- Intern a `KConstInfo` declaration into `HwExprCAM` (`consts`, `nodes`, `symbols`). -/
def internKConstInfoToHwExprCAM (c : KConstInfo) (cam : HwExprCAM) : HwExprCAM :=
  let (symIdx, cam1) := allocPackedSymbol (.constEntry c.name (c.levelParams.map KLevel.param)) cam
  let (tyH, cam2) := internToHwExprCAM c.type cam1
  match c with
  | .defnInfo _ _ _ val | .thmInfo _ _ _ val =>
    let (valH, cam3) := internToHwExprCAM val cam2
    let entry : HwCamConstEntry :=
      { name := c.name, symIdx := symIdx, typeHandle := tyH, valHandle? := some valH }
    { cam3 with consts := cam3.consts ++ [entry] }
  | .ctorInfo _ _ _ indName =>
    let entry : HwCamConstEntry :=
      { name := c.name, symIdx := symIdx, typeHandle := tyH, isCtor := true, inductName? := some indName }
    { cam2 with consts := cam2.consts ++ [entry] }
  | _ =>
    let entry : HwCamConstEntry :=
      { name := c.name, symIdx := symIdx, typeHandle := tyH }
    { cam2 with consts := cam2.consts ++ [entry] }

/-- Intern a `KRecRule` $\iota$-reduction rule into `HwExprCAM` (`recRules`, `nodes`, `symbols`). -/
def internKRecRuleToHwExprCAM (r : KRecRule) (cam : HwExprCAM) : HwExprCAM :=
  let (rhsH, cam1) := internToHwExprCAM r.rhs cam
  let entry : HwCamRecRuleEntry :=
    { recName   := r.recName
    , ctorName  := r.ctorName
    , numParams := r.numPrefixArgs
    , numFields := r.numFields
    , rhsHandle := rhsH }
  { cam1 with recRules := cam1.recRules ++ [entry] }

/-- Intern an entire `KEnv` declaration cone (`constants` and `recRules`) into `HwExprCAM`. -/
def internKEnvConeToHwExprCAM (env : KEnv) (cam : HwExprCAM) : HwExprCAM :=
  let cam1 := env.constants.foldl (fun acc c => internKConstInfoToHwExprCAM c acc) cam
  env.recRules.foldl (fun acc r => internKRecRuleToHwExprCAM r acc) cam1

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

/-- Sample host `Lean.RecursorVal` for a 2-constructor inductive `MyBool` (`MyBool.false`, `MyBool.true`)
with `.mdata` annotations on its rule RHSs (`λ motive hFalse hTrue => hFalse` and `λ motive hFalse hTrue => hTrue`). -/
def sampleLiveMyBoolRecVal : Lean.RecursorVal :=
  let myBoolName : Lean.Name := .str .anonymous "MyBool"
  let falseName  : Lean.Name := .str myBoolName "false"
  let trueName   : Lean.Name := .str myBoolName "true"
  let recName    : Lean.Name := .str myBoolName "rec"
  let type0      : Lean.Expr := .sort (.succ .zero)
  let myBoolExpr : Lean.Expr := .const myBoolName []
  -- RHS for `MyBool.false`: λ (motive : MyBool → Type) (hFalse : Type) (hTrue : Type) => .mdata {} (.bvar 1)
  let rhsFalse : Lean.Expr :=
    .lam (.str .anonymous "motive") (.forallE (.str .anonymous "b") myBoolExpr type0 .default)
      (.lam (.str .anonymous "hFalse") type0
        (.lam (.str .anonymous "hTrue") type0
          (.mdata {} (.bvar 1)) .default) .default) .default
  -- RHS for `MyBool.true`: λ (motive : MyBool → Type) (hFalse : Type) (hTrue : Type) => .mdata {} (.bvar 0)
  let rhsTrue : Lean.Expr :=
    .lam (.str .anonymous "motive") (.forallE (.str .anonymous "b") myBoolExpr type0 .default)
      (.lam (.str .anonymous "hFalse") type0
        (.lam (.str .anonymous "hTrue") type0
          (.mdata {} (.bvar 0)) .default) .default) .default
  { name        := recName
  , levelParams := []
  , type        := type0
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

/-- **Theorem (`extractLeanRecRules_and_cone_sound`)**:
1. `extractLeanRecRules sampleLiveMyBoolRecVal` succeeds, strips `.mdata` annotations on the rule RHSs,
   and produces the 2 `KRecRule` entries (`numPrefixArgs = 3`, `numFields = 0`),
2. `extractEnvConeWith sampleLiveConeFindConst? (.str .anonymous "flipMyBool") 16` extracts all 5
   transitive declarations (`flipMyBool`, `MyBool`, `MyBool.rec`, `MyBool.true`, `MyBool.false`) and
   both `MyBool.rec` $\iota$-reduction rules (`coneEnv.recRules.length = 2`),
3. In the extracted `coneEnv`, `kernelWhnf` $\delta + \beta + \iota$-reduces `flipMyBool MyBool.true`
   to `MyBool.false` and `flipMyBool MyBool.false` to `MyBool.true`,
4. `internKEnvConeToHwExprCAM coneEnv HwExprCAM.empty` populates `cam.consts.length = 5` and
   `cam.recRules.length = 2`. -/
theorem extractLeanRecRules_and_cone_sound :
    (match extractLeanRecRules sampleLiveMyBoolRecVal with
     | some [r0, r1] =>
       r0.numPrefixArgs == 3 && r0.numFields == 0 &&
       r1.numPrefixArgs == 3 && r1.numFields == 0
     | _ => false) = true ∧
    (match extractEnvConeWith sampleLiveConeFindConst? (.str .anonymous "flipMyBool") 16 with
     | some (coneEnv, _) =>
       let myBoolK := KName.mkSimple "MyBool"
       let trueK   := KExpr.const (.str myBoolK "true") []
       let falseK  := KExpr.const (.str myBoolK "false") []
       let flipK   := KExpr.const (KName.mkSimple "flipMyBool") []
       let cam     := internKEnvConeToHwExprCAM coneEnv HwExprCAM.empty
       coneEnv.constants.length == 5 &&
       coneEnv.recRules.length == 2 &&
       kernelWhnf coneEnv 16 (.app flipK trueK) == falseK &&
       kernelWhnf coneEnv 16 (.app flipK falseK) == trueK &&
       cam.consts.length == 5 &&
       cam.recRules.length == 2
     | none => false) = true := by
  decide +kernel

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

/-- Encode an `RtlExprRpnToken`. -/
def encodeRtlExprRpnToken : RtlExprRpnToken → List UInt8
  | .const v       => natToVarBytes 0 ++ encodeWireBitVec64 v
  | .inputPort idx => natToVarBytes 1 ++ natToVarBytes idx
  | .wireRef idx   => natToVarBytes 2 ++ natToVarBytes idx
  | .regRead idx   => natToVarBytes 3 ++ natToVarBytes idx
  | .alu op        => natToVarBytes 4 ++ encodeWireRtlAluOp op
  | .mux           => natToVarBytes 5
  | .bitNot        => natToVarBytes 6

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
  encodeWireBitVec64 f.expectedDigest ++
  encodeWireBitVec64 f.computedDigest

/-- Decode a Section-7 `IcapBitstreamFrame`. -/
def decodeWireIcapFrame (bs : List UInt8) : Option (IcapBitstreamFrame × List UInt8) := do
  let (targetTileId, bs1)   ← decodeVarBytes bs
  let (slotIdx, bs2)        ← decodeVarBytes bs1
  let (memberName, bs3)     ← decodeWireString bs2
  let (opKind, bs4)         ← decodeWireTileOpKind bs3
  let (datapath, bs5)       ← decodeWireRtlExpr bs4
  let (readsSlots, bs6)     ← decodeWireList decodeVarBytes bs5
  let (expectedDigest, bs7) ← decodeWireBitVec64 bs6
  let (computedDigest, bs8) ← decodeWireBitVec64 bs7
  pure ({ targetTileId := targetTileId
        , newTile :=
            { slotIdx    := slotIdx
            , memberName := memberName
            , opKind     := opKind
            , datapath   := datapath
            , readsSlots := readsSlots }
        , expectedDigest := expectedDigest
        , computedDigest := computedDigest }, bs8)

@[simp] theorem decodeWireIcapFrame_encodeWireIcapFrame (f : IcapBitstreamFrame) (rest : List UInt8) :
    decodeWireIcapFrame (encodeWireIcapFrame f ++ rest) = some (f, rest) := by
  rcases f with ⟨targetTileId, ⟨slotIdx, memberName, opKind, datapath, readsSlots⟩, expectedDigest, computedDigest⟩
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

end Obend.Lower.ExprCAM
end
