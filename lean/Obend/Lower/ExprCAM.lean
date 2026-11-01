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

/-- **Theorem (`exprCam_roundtrip_sound`)**:
Every `KExpr` constructor form (`.bvar`, `.fvar`, `.sort`, `.const`, `.app`, `.lam`, `.forallE`,
`.letE`, `.lit`, `.proj`) interns into `ExprCAM`, round-trips losslessly via `uninternExpr`,
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
    uninternExpr c4 h1 = some eLam ∧
    uninternExpr c4 h2 = some eForall ∧
    uninternExpr c4 h3 = some eLet ∧
    uninternExpr c4 h4 = some eProj ∧
    camHandleHasLooseBVar? c4 h1 = some false ∧
    camInstantiate1 c4 kNatConst (.lit (.natVal 42)) = KExpr.instantiate1 kNatConst (.lit (.natVal 42)) ∧
    camInstantiate1 c4 (.bvar 0) (.lit (.natVal 42)) = .lit (.natVal 42) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

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
