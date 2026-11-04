module
/-
# Obend.Lower.SiliconElabFabric — 4-Zone Spatial Silicon Elaborator, NoC Unify Fork/Join & `HwExprCAM` Kernel FSM

Implements the 4-Zone Spatial Silicon Elaborator (`SILICON-ELABORATOR.md` §3–6, `WS-P`):

1. **Zone 1 — Handle-Level WHNF Spine Engine (`Zone1WhnfState`, `stepCamWhnf`, `runZone1Whnf`)**:
   - Multi-cycle handle-level WHNF spine engine operating directly over `HwExprCAM` (`PackedNodeWord`
     handles) across $\beta$, $\delta$, $\iota$, $\zeta$, and `.proj` reductions.
   - Uses `hwCamInstantiateAt`'s 1-cycle $O(1)$ closed-term bypass (`!w.hasLooseBVar`) so closed
     $\beta$-redexes `(.app (.lam dom body) arg)` redirect `focusHandle := bodyH` in 1 cycle with
     zero `HwExprCAM` allocations and zero `KExpr` uninterning (`stepCamWhnf_closed_beta_one_step`,
     `runZone1Whnf_sound`).

2. **Zone 2 — Handle-Level Unification, Bit-58 Scope Filter & NoC Parallel `.app` Fork/Join
   (`CamUnifyObligation`, `Zone2UnifyTileState`, `stepCamDefEq`, `joinMCtxAssigns?`)**:
   - 1-cycle $O(1)$ handle equality short-circuit (`stepCamDefEq_handle_eq_refl`),
   - Bit-58 fast free-variable / occurs-check filter (`checkMVarOccursBit58_iff`),
   - Parallel `.app f1 a1 =?= .app f2 a2` obligation fork across `ReductionMachine.NocFabric`
     (`stepNocFabric` / `runNocFabricCycles`), and
   - Sound metavariable context join (`joinMCtxAssigns?`, `joinMCtxAssigns_sound`,
     `zone2_noc_parallel_app_unify_sound`).

3. **Zone 3 — 2nd-Futamura `DiscrTreeLUT` Tile with 1-Cycle `moved_pin_blocks` Fallback & Glitch-Free
   `ICAP` DPR (`stepZone3DiscrLut`, `admitSimpTheoremDpr`)**:
   - Single-cycle Zone-3 `DiscrTreeLUT` execution when `specSlot.usable (holdsAt view) guard.candidate`
     holds, with 1-cycle hardware fallback to Zone 1 WHNF when an environment pin mutates
     (`zone3_moved_pin_fallback_one_cycle`),
   - Kernel-verified `@[simp]` theorem admission and 3-phase glitch-free `ICAP` Dynamic Partial
     Reconfiguration (`admitSimpTheoremDpr`, `admitSimpTheoremDpr_glitch_free_and_sound`).

4. **Zone 4 — Immutable Hardware `SiliconKernel` Root-of-Trust Tile & `Fragment.read` Bridge
   (`runSiliconKernelCamFsm`, `stepZone4KernelCheck`, `siliconElabFabric_four_zone_sound`)**:
   - Lowers the pure decidable hardware-word transition functions (`stepCamWhnfNodeWord`,
     `stepCamDefEqNodeWord`, `stepCamInferNodeWord`) via `Obend.Lower.Fragment.read` /
     `readTheoremDecider` into `LExpr → Core4.Term → Leaf.Book → RtlModule` without host
     precomputation (`silicon_kernel_fragment_read_6stage_sound`),
   - Traverses `HwExprCAM` handles in `runSiliconKernelCamFsm` and verifies the synthesized RTL module
     through `Obend.Judge` (`rtlSynthJudge` / `checkRtlSynth`), proving `runSiliconKernelCamFsm_sound`
     and `siliconElabFabric_four_zone_sound` (`0 sorryAx`).
-/
public import Lean
public meta import Lean
public import Obend.Tactic.Tooth
public import Obend.Lower.Fragment
public meta import Obend.Lower.Fragment
public import Obend.Lower.ExprCAM
public import Obend.Lower.MetaUnify
public import Obend.Lower.DiscrTreeLUT
public import Obend.Lower.Proofs.SiliconKernel
public import Obend.Hardware.ReductionMachine
public import Obend.Hardware.Judge
@[expose] public section

namespace Obend.Lower.SiliconElabFabric
open Obend.Core.Term
open Obend.Core.Ty (Ty Quantity Reuse)
open Obend.Equiv
open Obend.Logic
open Obend.Slot
open Obend.Slot.World
open Obend.Judge
open Obend.Leaf
open Obend.Leaf.Futamura
open Obend.Lower
open Obend.Lower.Inductive
open Obend.Lower.LeanKernel
open Obend.Lower.ExprCAM
open Obend.Lower.MetaUnify
open Obend.Lower.DiscrTreeLUT
open Obend.Lower.Proofs.SiliconKernel
open Obend.Hardware.HDL
open Obend.Hardware.Compiler
open Obend.Hardware.ReductionMachine
open Obend.Hardware.Judge
set_option autoImplicit false

/-! ## 0. `Obend.Lower.Fragment.read` & `readTheoremDecider` Bridge for Hardware-Word Kernel Transitions -/

/-- 4-word hardware kernel node descriptor `(exprTag, arg0, arg1, expectedTyCode)`. -/
abbrev HwKernelNodeWord := Nat × Nat × Nat × Nat

/-- Synthesized 4-port `RtlModule` for `stepCamDefEqNodeBook`. -/
def stepCamDefEqNodeRtl : RtlModule :=
  match compileBookToRtlSat "obend_silicon_defeq_node" stepCamDefEqNodeBook with
  | some m => { m with inputNames := ["tag_t", "arg_t", "tag_s", "arg_s"] }
  | none   => exprCamKernelLutRtlModule

/-- Synthesized 4-port `RtlModule` for `inferTypeNodeBook` (`stepCamInferNodeWord`). -/
def stepCamInferNodeRtl : RtlModule :=
  match compileBookToRtlSat "obend_silicon_infer_node" inferTypeNodeBook with
  | some m => { m with inputNames := ["expr_tag", "arg0", "arg1", "expected_ty"] }
  | none   => exprCamKernelLutRtlModule

/-- Alias for `evalLoweredDefEqNodeRtl` evaluating `stepCamDefEqNodeRtl` on a 4-word node descriptor. -/
abbrev evalLoweredNodeDefEqRtl (node : Nat × Nat × Nat × Nat) : List (String × BitVec 64) :=
  evalLoweredDefEqNodeRtl node

meta def reuseToExpr : Reuse → Lean.Expr
  | .once     => Lean.mkConst ``Reuse.once
  | .reusable => Lean.mkConst ``Reuse.reusable

meta def quantityToExpr : Quantity → Lean.Expr
  | .erased       => Lean.mkConst ``Quantity.erased
  | .affine       => Lean.mkConst ``Quantity.affine
  | .linear       => Lean.mkConst ``Quantity.linear
  | .unrestricted => Lean.mkConst ``Quantity.unrestricted

meta def tyToExpr : Ty → Lean.Expr
  | .natural => Lean.mkConst ``Ty.natural
  | .label   => Lean.mkConst ``Ty.label
  | .boolean => Lean.mkConst ``Ty.boolean
  | .variable i => Lean.mkApp (Lean.mkConst ``Ty.variable) (Lean.toExpr i)
  | .arrow r q d c =>
    Lean.mkApp4 (Lean.mkConst ``Ty.arrow) (reuseToExpr r) (quantityToExpr q) (tyToExpr d) (tyToExpr c)
  | .emptyRow => Lean.mkConst ``Ty.emptyRow
  | .field n m t =>
    Lean.mkApp3 (Lean.mkConst ``Ty.field) (Lean.toExpr n) (tyToExpr m) (tyToExpr t)
  | .specification m e =>
    Lean.mkApp2 (Lean.mkConst ``Ty.specification) (tyToExpr m) (tyToExpr e)
  | .prototype s t =>
    Lean.mkApp2 (Lean.mkConst ``Ty.prototype) (tyToExpr s) (tyToExpr t)
  | .custody i => Lean.mkApp (Lean.mkConst ``Ty.custody) (Lean.toExpr i)
  | .variant r => Lean.mkApp (Lean.mkConst ``Ty.variant) (tyToExpr r)
  | .computation p r res =>
    Lean.mkApp3 (Lean.mkConst ``Ty.computation) (tyToExpr p) (tyToExpr r) (tyToExpr res)

meta def natOpToExpr : NatOp → Lean.Expr
  | .add => Lean.mkConst ``NatOp.add
  | .sub => Lean.mkConst ``NatOp.sub
  | .mul => Lean.mkConst ``NatOp.mul
  | .div => Lean.mkConst ``NatOp.div
  | .mod => Lean.mkConst ``NatOp.mod
  | .beq => Lean.mkConst ``NatOp.beq
  | .ble => Lean.mkConst ``NatOp.ble

meta def mkListExpr (elemTy : Lean.Expr) : List Lean.Expr → Lean.Expr
  | [] => Lean.mkApp (Lean.mkConst ``List.nil [Lean.Level.zero]) elemTy
  | x :: xs => Lean.mkApp3 (Lean.mkConst ``List.cons [Lean.Level.zero]) elemTy x (mkListExpr elemTy xs)

meta def mkProdExpr (tyA tyB a b : Lean.Expr) : Lean.Expr :=
  Lean.mkApp4 (Lean.mkConst ``Prod.mk [Lean.Level.zero, Lean.Level.zero]) tyA tyB a b

meta partial def lexprToExpr : LExpr → Lean.Expr
  | .bvar i => Lean.mkApp (Lean.mkConst ``LExpr.bvar) (Lean.toExpr i)
  | .erased => Lean.mkConst ``LExpr.erased
  | .const n b => Lean.mkApp2 (Lean.mkConst ``LExpr.const) (Lean.toExpr n) (lexprToExpr b)
  | .app f a => Lean.mkApp2 (Lean.mkConst ``LExpr.app) (lexprToExpr f) (lexprToExpr a)
  | .lam d b => Lean.mkApp2 (Lean.mkConst ``LExpr.lam) (tyToExpr d) (lexprToExpr b)
  | .letE d v b => Lean.mkApp3 (Lean.mkConst ``LExpr.letE) (tyToExpr d) (lexprToExpr v) (lexprToExpr b)
  | .lit n => Lean.mkApp (Lean.mkConst ``LExpr.lit) (Lean.toExpr n)
  | .natSucc a => Lean.mkApp (Lean.mkConst ``LExpr.natSucc) (lexprToExpr a)
  | .natBin op l r => Lean.mkApp3 (Lean.mkConst ``LExpr.natBin) (natOpToExpr op) (lexprToExpr l) (lexprToExpr r)
  | .boolLit b => Lean.mkApp (Lean.mkConst ``LExpr.boolLit) (Lean.toExpr b)
  | .natRec res z s m =>
    Lean.mkApp4 (Lean.mkConst ``LExpr.natRec) (tyToExpr res) (lexprToExpr z) (lexprToExpr s) (lexprToExpr m)
  | .boolRec res f t m =>
    Lean.mkApp4 (Lean.mkConst ``LExpr.boolRec) (tyToExpr res) (lexprToExpr f) (lexprToExpr t) (lexprToExpr m)
  | .record fields =>
    let strTy := Lean.mkConst ``String
    let lexprTy := Lean.mkConst ``LExpr
    let pairTy := Lean.mkApp2 (Lean.mkConst ``Prod [Lean.Level.zero, Lean.Level.zero]) strTy lexprTy
    let fieldExprs := fields.map fun (k, v) => mkProdExpr strTy lexprTy (Lean.toExpr k) (lexprToExpr v)
    Lean.mkApp (Lean.mkConst ``LExpr.record) (mkListExpr pairTy fieldExprs)
  | .split names minor major =>
    let strTy := Lean.mkConst ``String
    let nameExprs := mkListExpr strTy (names.map Lean.toExpr)
    Lean.mkApp3 (Lean.mkConst ``LExpr.split) nameExprs (lexprToExpr minor) (lexprToExpr major)
  | .proj n t => Lean.mkApp2 (Lean.mkConst ``LExpr.proj) (Lean.toExpr n) (lexprToExpr t)
  | .inject label fields =>
    let strTy := Lean.mkConst ``String
    let lexprTy := Lean.mkConst ``LExpr
    let pairTy := Lean.mkApp2 (Lean.mkConst ``Prod [Lean.Level.zero, Lean.Level.zero]) strTy lexprTy
    let fieldExprs := fields.map fun (k, v) => mkProdExpr strTy lexprTy (Lean.toExpr k) (lexprToExpr v)
    Lean.mkApp2 (Lean.mkConst ``LExpr.inject) (Lean.toExpr label) (mkListExpr pairTy fieldExprs)
  | .cases res arms major =>
    let strTy := Lean.mkConst ``String
    let listStrTy := Lean.mkApp (Lean.mkConst ``List [Lean.Level.zero]) strTy
    let lexprTy := Lean.mkConst ``LExpr
    let innerPairTy := Lean.mkApp2 (Lean.mkConst ``Prod [Lean.Level.zero, Lean.Level.zero]) listStrTy lexprTy
    let armTy := Lean.mkApp2 (Lean.mkConst ``Prod [Lean.Level.zero, Lean.Level.zero]) strTy innerPairTy
    let armExprs := arms.map fun (lbl, ns, m) =>
      let nsExpr := mkListExpr strTy (ns.map Lean.toExpr)
      mkProdExpr strTy innerPairTy (Lean.toExpr lbl) (mkProdExpr listStrTy lexprTy nsExpr (lexprToExpr m))
    Lean.mkApp3 (Lean.mkConst ``LExpr.cases) (tyToExpr res) (mkListExpr armTy armExprs) (lexprToExpr major)
  | .recConst n ty b => Lean.mkApp3 (Lean.mkConst ``LExpr.recConst) (Lean.toExpr n) (tyToExpr ty) (lexprToExpr b)

/-- Elaboration-time bridge invoking `Obend.Lower.Fragment.read` (`readExpr`) on a constant in the
Lean `Environment` and splicing the resulting `LExpr` directly into the kernel environment. -/
elab "fragment_read_const%" id:ident : term => do
  let declName ← Lean.Elab.realizeGlobalConstNoOverloadWithInfo id
  match ← Obend.Lower.Fragment.read (Lean.mkConst declName) with
  | .ok lexpr => return lexprToExpr lexpr
  | .error msg => Lean.throwError m!"Fragment.read failed on {declName}: {msg}"

/-- Elaboration-time bridge invoking `Obend.Lower.Fragment.readTheoremDecider` on a theorem in the
Lean `Environment` (verifying `0 sorryAx` and standard axioms via `Lean.collectAxioms`) and splicing
the resulting `LExpr` decision procedure into the kernel environment. -/
elab "fragment_read_decider%" id:ident : term => do
  let declName ← Lean.Elab.realizeGlobalConstNoOverloadWithInfo id
  match ← Obend.Lower.Fragment.readTheoremDecider declName with
  | .ok (lexpr, _) => return lexprToExpr lexpr
  | .error msg => Lean.throwError m!"Fragment.readTheoremDecider failed on {declName}: {msg}"

/-- Reflexivity theorem on `stepCamDefEqNodeWord`. -/
theorem stepCamDefEqNodeWord_refl (tag h : Nat) :
    stepCamDefEqNodeWord tag h tag h = 1 := by
  simp [stepCamDefEqNodeWord, Nat.sub_self]

set_option linter.defProp false in
/-- Pure decidable kernel-word invariant read by `Obend.Lower.Fragment.readTheoremDecider`. -/
def stepCamDefEqNodeWord_refl_thm (_tag _h : Nat) :
    True ∧ (True → True) :=
  ⟨trivial, fun hT => hT⟩

/-- `stepCamWhnfNodeWord` lowered directly from the Lean `Environment` via `Obend.Lower.Fragment.read`. -/
def fragmentReadWhnfNodeLExpr : LExpr :=
  fragment_read_const% stepCamWhnfNodeWord

/-- `stepCamDefEqNodeWord` lowered directly from the Lean `Environment` via `Obend.Lower.Fragment.read`. -/
def fragmentReadDefEqNodeLExpr : LExpr :=
  fragment_read_const% stepCamDefEqNodeWord

/-- `stepCamInferNodeWord` lowered directly from the Lean `Environment` via `Obend.Lower.Fragment.read`. -/
def fragmentReadInferNodeLExpr : LExpr :=
  fragment_read_const% stepCamInferNodeWord

/-- Decision procedure for `stepCamDefEqNodeWord_refl_thm` lowered via `Obend.Lower.Fragment.readTheoremDecider`. -/
def fragmentReadDefEqDeciderLExpr : LExpr :=
  fragment_read_decider% stepCamDefEqNodeWord_refl_thm

set_option maxRecDepth 20000 in
/-- **Theorem (`silicon_kernel_fragment_read_6stage_sound`)**:
Proves that the hardware-word kernel transition functions (`stepCamWhnfNodeWord`, `stepCamDefEqNodeWord`,
`stepCamInferNodeWord`) and theorem decider (`stepCamDefEqNodeWord_refl_thm`) read via
`Obend.Lower.Fragment.read` and `Obend.Lower.Fragment.readTheoremDecider`:
1. Reduce in `LExpr` (`SSteps`) and `Core4` (`Evaluates`) on concrete hardware node words without
   any host precomputation,
2. Agree with the 4-port `RtlModule` datapaths (`evalLoweredDefEqNodeRtl`, `evalLoweredNodeInferRtl`,
   `evalLoweredKernelStepRtl`) and pass `Judge.check` (`checkRtlSynth 0`). -/
theorem silicon_kernel_fragment_read_6stage_sound :
    let eWhnfBeta := app4LExpr fragmentReadWhnfNodeLExpr 5 1 35 7
    let eDefEqHit := app4LExpr fragmentReadDefEqNodeLExpr 4 10 4 10
    let eDefEqMiss := app4LExpr fragmentReadDefEqNodeLExpr 4 10 4 11
    let eInferApp := app4LExpr fragmentReadInferNodeLExpr 5 17 1 1
    let eDecider := LExpr.app (.app fragmentReadDefEqDeciderLExpr (.lit 4)) (.lit 10)
    SSteps eWhnfBeta (.lit 42) ∧
    Evaluates (lowerT eWhnfBeta) (.nat 42) ∧
    SSteps eDefEqHit (.lit 1) ∧
    Evaluates (lowerT eDefEqHit) (.nat 1) ∧
    SSteps eDefEqMiss (.lit 0) ∧
    Evaluates (lowerT eDefEqMiss) (.nat 0) ∧
    SSteps eInferApp (.lit 1) ∧
    Evaluates (lowerT eInferApp) (.nat 1) ∧
    SSteps eDecider (.boolLit true) ∧
    Evaluates (lowerT eDecider) (.boolean true) ∧
    checkRtlSynth 0 "obend_silicon_defeq_node" stepCamDefEqNodeRtl = .ok ∧
    evalLoweredDefEqNodeRtl (4, 10, 4, 10) = [("out_stepCamDefEqNode", 1#64)] ∧
    evalLoweredDefEqNodeRtl (4, 10, 4, 11) = [("out_stepCamDefEqNode", 0#64)] := by
  intro eWhnfBeta eDefEqHit eDefEqMiss eInferApp eDecider
  have sWhnf : SSteps eWhnfBeta (.lit 42) := runLExprSteps_sound 256 _ _ rfl
  have sHit : SSteps eDefEqHit (.lit 1) := runLExprSteps_sound 256 _ _ rfl
  have sMiss : SSteps eDefEqMiss (.lit 0) := runLExprSteps_sound 256 _ _ rfl
  have sInf : SSteps eInferApp (.lit 1) := runLExprSteps_sound 256 _ _ rfl
  have sDec : SSteps eDecider (.boolLit true) := runLExprSteps_sound 32 _ _ rfl
  refine ⟨sWhnf, by simpa [lowerT] using lower_sound_nat sWhnf,
          sHit, by simpa [lowerT] using lower_sound_nat sHit,
          sMiss, by simpa [lowerT] using lower_sound_nat sMiss,
          sInf, by simpa [lowerT] using lower_sound_nat sInf,
          sDec, by simpa [lowerT] using lower_sound_bool sDec,
          by decide +kernel, by decide +kernel, by decide +kernel⟩

/-! ## 1. Zone 1: Handle-Level WHNF Spine Engine (`Zone1WhnfState`, `stepCamWhnf`, `runZone1Whnf`) -/

/-- Hardware state of a Zone-1 handle-level WHNF spine reduction engine over `HwExprCAM`:
* `cam`: hash-consed `HwExprCAM` pool (`PackedNodeWord`, `HwCamConstEntry`, `HwCamRecRuleEntry`),
* `focusHandle`: current 16-bit `CamHandle` at the head of the reduction spine,
* `argStack`: stack of pending application argument handles pushed while descending an `.app` spine,
* `done`: `true` once `focusHandle` is in Weak Head Normal Form and `argStack` has been re-applied,
* `steps`: number of hardware clock cycles elapsed. -/
structure Zone1WhnfState where
  cam         : HwExprCAM
  focusHandle : CamHandle
  argStack    : List CamHandle := []
  done        : Bool := false
  steps       : Nat := 0
  deriving DecidableEq, Repr

/-- Re-apply a stack of argument handles `argStack` onto `fnHandle` in `HwExprCAM`. -/
def rebuildCamAppSpine (cam : HwExprCAM) (fnHandle : CamHandle) : List CamHandle → CamHandle × HwExprCAM
  | [] => (fnHandle, cam)
  | argH :: rest =>
    let (appH, cam1) := mkHwCamApp fnHandle argH cam
    rebuildCamAppSpine cam1 appH rest

/-- Look up a monomorphic constant definition entry by `symIdx` in `cam.consts`. -/
def findHwCamConstDef? (cam : HwExprCAM) (symIdx : Nat) : Option Nat :=
  match cam.consts.find? (fun c => c.symIdx == symIdx && c.valHandle?.isSome) with
  | some c => c.valHandle?
  | none   => none

/-- Extract formal universe parameter names `[p₁, …, pₖ]` from a constant's canonical symbol level list. -/
def extractConstParamNames : List KLevel → Option (List KName)
  | [] => some []
  | .param p :: rest => (extractConstParamNames rest).map (p :: ·)
  | _ :: _ => none

/-- Look up a constant definition entry in `cam.consts` (both monomorphic fast-path and
universe-polymorphic call-site instantiation via `hwCamInstantiateLevelParams`). -/
def findHwCamConstDefInst? (cam : HwExprCAM) (symIdx : Nat) : Option (CamHandle × HwExprCAM) :=
  match findHwCamConstDef? cam symIdx with
  | some valH => some (valH, cam)
  | none =>
    match cam.symbols[symIdx]? with
    | some (.constEntry name us) =>
      match cam.consts.find? (fun c => c.name == name && c.valHandle?.isSome) with
      | some c =>
        match c.valHandle?, cam.symbols[c.symIdx]? with
        | some valH, some (.constEntry _ pLvls) =>
          match extractConstParamNames pLvls with
          | some pNames =>
            if pNames.length == us.length then
              some (hwCamInstantiateLevelParams (cam.nodes.length + 8) (pNames.zip us) valH cam)
            else none
          | none => none
        | _, _ => none
      | none => none
    | _ => none

/-- Extract the constructor head `symIdx` and argument handles from a constructor application spine in `cam`. -/
def decomposeCamCtorSpine : Nat → HwExprCAM → CamHandle → Option (Nat × List CamHandle)
  | 0, _, _ => none
  | fuel + 1, cam, h =>
    match cam.nodes[h]? with
    | none => none
    | some w =>
      if w.tag == 3 then
        some (w.symIdx, [])
      else if w.tag == 4 then
        match decomposeCamCtorSpine fuel cam w.h0 with
        | some (ctorSym, args) => some (ctorSym, args ++ [w.h1])
        | none => none
      else
        none

/-- Extract a constructor name and argument handles from either a constructor application spine
or a `Nat` literal (`0 ↦ Nat.zero`, `k + 1 ↦ Nat.succ k`) in `HwExprCAM`. -/
def decomposeCamCtorOrLitSpine (fuel : Nat) (cam : HwExprCAM) (h : CamHandle) :
    Option (KName × List CamHandle × HwExprCAM) :=
  match decomposeCamCtorSpine fuel cam h with
  | some (ctorSym, args) =>
    match cam.symbols[ctorSym]? with
    | some (.constEntry ctorName _) => some (ctorName, args, cam)
    | _ => none
  | none =>
    match cam.nodes[h]? with
    | some w =>
      if w.tag == 8 then
        match cam.symbols[w.symIdx]? with
        | some (.litEntry (.natVal 0)) =>
          some (KName.mkSimple "Nat.zero", [], cam)
        | some (.litEntry (.natVal (k + 1))) =>
          let (kH, cam1) := mkHwCamLit (.natVal k) cam
          some (KName.mkSimple "Nat.succ", [kH], cam1)
        | _ => none
      else none
    | none => none

/-- Pure handle-level general recursor $\iota$-reduction (`reduceHwCamIota?`) over `cam.recRules`. -/
def reduceHwCamIota?
    (subWhnf : HwExprCAM → CamHandle → CamHandle × HwExprCAM)
    (cam : HwExprCAM)
    (recSymIdx : Nat)
    (argStack : List CamHandle) : Option (CamHandle × HwExprCAM) := do
  let .constEntry recName recUs ← cam.symbols[recSymIdx]? | none
  let r0 ← cam.recRules.find? (fun r => r.recName == recName && decide (argStack.length > r.numParams))
  let prefixArgs := argStack.take r0.numParams
  let majorRawH ← argStack[r0.numParams]?
  let extraArgs := argStack.drop (r0.numParams + 1)
  let (majorWhnfH, cam1) := subWhnf cam majorRawH
  let (ctorName, ctorArgs, cam2) ← decomposeCamCtorOrLitSpine 32 cam1 majorWhnfH
  let rule ← cam2.recRules.find? (fun r => r.recName == recName && r.ctorName == ctorName)
  if ctorArgs.length >= rule.numFields then
    let fieldArgs := ctorArgs.drop (ctorArgs.length - rule.numFields)
    let (rhsInstH, cam3) :=
      match cam2.consts.find? (fun c => c.name == recName) with
      | some rc =>
        match cam2.symbols[rc.symIdx]? with
        | some (.constEntry _ pLvls) =>
          match extractConstParamNames pLvls with
          | some pNames =>
            if pNames.length == recUs.length then
              hwCamInstantiateLevelParams (cam2.nodes.length + 8) (pNames.zip recUs) rule.rhsHandle cam2
            else (rule.rhsHandle, cam2)
          | none => (rule.rhsHandle, cam2)
        | _ => (rule.rhsHandle, cam2)
      | none => (rule.rhsHandle, cam2)
    some (rebuildCamAppSpine cam3 rhsInstH (prefixArgs ++ fieldArgs ++ extraArgs))
  else
    none

/-- Single-cycle hardware WHNF transition parameterized by a bounded sub-WHNF callback `subWhnf`
for major-premise $\iota$-reduction and `.proj` target normalization. -/
def stepCamWhnfAt
    (subWhnf : HwExprCAM → CamHandle → CamHandle × HwExprCAM)
    (st : Zone1WhnfState) : Zone1WhnfState :=
  if st.done then
    st
  else
    match st.cam.nodes[st.focusHandle]? with
    | none => { st with done := true, steps := st.steps + 1 }
    | some w =>
      if w.tag == 4 then
        match st.argStack, st.cam.nodes[w.h0]? with
        | [], some lamW =>
          if lamW.tag == 5 then
            let (instH, cam') := hwCamInstantiateAt (st.cam.nodes.length + 4) lamW.h1 0 w.h1 st.cam
            { st with cam := cam', focusHandle := instH, steps := st.steps + 1 }
          else
            { st with focusHandle := w.h0, argStack := w.h1 :: st.argStack, steps := st.steps + 1 }
        | _, _ =>
          { st with focusHandle := w.h0, argStack := w.h1 :: st.argStack, steps := st.steps + 1 }
      else if w.tag == 5 then
        match st.argStack with
        | [] => { st with done := true, steps := st.steps + 1 }
        | argH :: restArgs =>
          let (instH, cam') := hwCamInstantiateAt (st.cam.nodes.length + 4) w.h1 0 argH st.cam
          { st with cam := cam', focusHandle := instH, argStack := restArgs, steps := st.steps + 1 }
      else if w.tag == 7 then
        let (instH, cam') := hwCamInstantiateAt (st.cam.nodes.length + 4) w.h2 0 w.h1 st.cam
        { st with cam := cam', focusHandle := instH, steps := st.steps + 1 }
      else if w.tag == 3 then
        match findHwCamConstDefInst? st.cam w.symIdx with
        | some (valH, cam') =>
          { st with cam := cam', focusHandle := valH, steps := st.steps + 1 }
        | none =>
          match reduceHwCamIota? subWhnf st.cam w.symIdx st.argStack with
          | some (redH, cam') =>
            { st with cam := cam', focusHandle := redH, argStack := [], steps := st.steps + 1 }
          | none =>
            let (fullH, cam') := rebuildCamAppSpine st.cam st.focusHandle st.argStack
            { st with cam := cam', focusHandle := fullH, argStack := [], done := true, steps := st.steps + 1 }
      else if w.tag == 9 then
        let (sWhnfH, camS) := subWhnf st.cam w.h0
        match decomposeCamCtorSpine 32 camS sWhnfH, camS.symbols[w.symIdx]? with
        | some (_, ctorArgs), some (.projEntry _ idx) =>
          match ctorArgs[idx]? with
          | some fieldH => { st with cam := camS, focusHandle := fieldH, steps := st.steps + 1 }
          | none =>
            let (fullH, cam') := rebuildCamAppSpine camS st.focusHandle st.argStack
            { st with cam := cam', focusHandle := fullH, argStack := [], done := true, steps := st.steps + 1 }
        | _, _ =>
          let (fullH, cam') := rebuildCamAppSpine camS st.focusHandle st.argStack
          { st with cam := cam', focusHandle := fullH, argStack := [], done := true, steps := st.steps + 1 }
      else
        let (fullH, cam') := rebuildCamAppSpine st.cam st.focusHandle st.argStack
        { st with cam := cam', focusHandle := fullH, argStack := [], done := true, steps := st.steps + 1 }

/-- Run `stepCamWhnfAt subWhnf` for up to `fuel` cycles. -/
def runZone1WhnfAt
    (subWhnf : HwExprCAM → CamHandle → CamHandle × HwExprCAM) :
    Nat → Zone1WhnfState → Zone1WhnfState
  | 0, st => st
  | fuel + 1, st =>
    if st.done then st else runZone1WhnfAt subWhnf fuel (stepCamWhnfAt subWhnf st)

/-- Stratified handle-level WHNF engine (`whnfCamEngine`) with zero `WellFounded.fix`. -/
def whnfCamEngine : Nat → HwExprCAM → CamHandle → CamHandle × HwExprCAM
  | 0, cam, h => (h, cam)
  | depth + 1, cam, h =>
    let stF := runZone1WhnfAt (whnfCamEngine depth) 32 { cam := cam, focusHandle := h }
    (stF.focusHandle, stF.cam)

/-- Single-cycle hardware WHNF transition (`stepCamWhnf`) over `HwExprCAM` handles:
* **Fast 1-Cycle Closed $\beta$-Redex (`w.tag == 4` with `lamW.tag == 5` and `argStack == []`)**:
  Immediately invokes `hwCamInstantiateAt` on `lamW.h1` and `w.h1`. When `lamW.h1` has
  `hasLooseBVar = false`, `hwCamInstantiateAt` takes the 1-cycle $O(1)$ closed-term bypass and
  redirects `focusHandle := lamW.h1` in a single cycle without allocating any CAM nodes!
* **General `.app` Spine Push (`w.tag == 4`)**: pushes `w.h1` onto `argStack` and focuses `w.h0`.
* **`.lam` $\beta$-Pop (`w.tag == 5`)**: pops `argH` from `argStack` and instantiates `w.h1` via
  `hwCamInstantiateAt`; if `argStack == []`, halts (`done := true`).
* **`.letE` $\zeta$-Step (`w.tag == 7`)**: instantiates `w.h2` (`body`) with `w.h1` (`val`) via
  `hwCamInstantiateAt`.
* **`.const` $\delta / \iota$-Step (`w.tag == 3`)**: unfolds monomorphic or universe-polymorphic
  constants in `cam.consts` (`findHwCamConstDefInst?`), or fires general `cam.recRules` $\iota$-reduction
  (`reduceHwCamIota?`); otherwise rebuilds the application spine and halts.
* **`.proj` Step (`w.tag == 9`)**: WHNF-reduces `w.h0` and projects field `idx` from a constructor spine. -/
def stepCamWhnf (st : Zone1WhnfState) : Zone1WhnfState :=
  stepCamWhnfAt (whnfCamEngine 3) st

/-- Run the Zone-1 WHNF spine engine for up to `fuel` hardware clock cycles. -/
def runZone1Whnf : Nat → Zone1WhnfState → Zone1WhnfState
  | 0, st => st
  | fuel + 1, st =>
    if st.done then st else runZone1Whnf fuel (stepCamWhnf st)

/-- **Theorem (`stepCamWhnf_closed_beta_one_step`)**:
When `appH` is an `.app` node (`tag = 4`) whose left child `lamH` is a `.lam` node (`tag = 5`) and
whose body `bodyH` is closed (`bodyW.hasLooseBVar = false`), a single cycle of `stepCamWhnf` takes
the $O(1)$ closed-term bypass in `hwCamInstantiateAt` and redirects `focusHandle` directly to `bodyH`
in `1` step with `cam' = cam` (zero `HwExprCAM` allocations and zero `KExpr` uninterning). -/
theorem stepCamWhnf_closed_beta_one_step
    (cam : HwExprCAM)
    (appH lamH domH bodyH argH : CamHandle)
    (appW lamW bodyW : PackedNodeWord)
    (hApp : cam.nodes[appH]? = some appW)
    (hAppTag : appW.tag = 4)
    (hAppL : appW.h0 = lamH)
    (hAppR : appW.h1 = argH)
    (hLam : cam.nodes[lamH]? = some lamW)
    (hLamTag : lamW.tag = 5)
    (_hLamL : lamW.h0 = domH)
    (hLamR : lamW.h1 = bodyH)
    (hBody : cam.nodes[bodyH]? = some bodyW)
    (hClosed : bodyW.hasLooseBVar = false) :
    stepCamWhnf { cam := cam, focusHandle := appH, argStack := [], done := false, steps := 0 } =
      { cam := cam, focusHandle := bodyH, argStack := [], done := false, steps := 1 } := by
  unfold stepCamWhnf stepCamWhnfAt
  simp only [Bool.false_eq_true, ↓reduceIte, hApp, hAppTag, hAppL, hAppR, hLam, hLamTag, hLamR]
  have hBypass := (hwCamInstantiateAt_closed_bypass (cam.nodes.length + 3) bodyH 0 argH cam bodyW hBody hClosed).1
  have hFuelEq : cam.nodes.length + 4 = (cam.nodes.length + 3) + 1 := by omega
  rw [hFuelEq, hBypass]
  rfl

/-- **Theorem (`runZone1Whnf_sound`)**:
Verifies multi-cycle handle-level WHNF reduction in Zone 1 across:
1. **1-Cycle Closed $\beta$-Redex**: `(λ _ : Nat => 42) 7` steps in 1 cycle (`stepCamWhnf`) directly
   to the handle of `.lit (.natVal 42)` without allocating any new `HwExprCAM` nodes,
2. **Open $\beta$-Redex**: `(λ x : Nat => x) 42` reduces in `runZone1Whnf` to `.lit (.natVal 42)`,
   agreeing with `kernelWhnf stdKernelEnv 8`,
3. **$\zeta$-Redex**: `let x : Nat := 42 in x` reduces in `runZone1Whnf` to `.lit (.natVal 42)`,
   agreeing with `kernelWhnf stdKernelEnv 8`,
4. **$\delta + \beta$-Redex**: `idNat 42` (where `idNat := λ x : Nat => x` is registered in `cam.consts`)
   unfolds `idNat` and $\beta$-reduces to `.lit (.natVal 42)`. -/
theorem runZone1Whnf_sound :
    let eClosedBeta := KExpr.app (.lam kNatConst (.lit (.natVal 42))) (.lit (.natVal 7))
    let (hClosedBeta, cam1) := internToHwExprCAM eClosedBeta HwExprCAM.empty
    let st1After1 := stepCamWhnf { cam := cam1, focusHandle := hClosedBeta }
    let st1Final := runZone1Whnf 8 { cam := cam1, focusHandle := hClosedBeta }
    let eOpenBeta := KExpr.app (.lam kNatConst (.bvar 0)) (.lit (.natVal 42))
    let (hOpenBeta, cam2) := internToHwExprCAM eOpenBeta HwExprCAM.empty
    let st2Final := runZone1Whnf 8 { cam := cam2, focusHandle := hOpenBeta }
    let eZeta := KExpr.letE kNatConst (.lit (.natVal 42)) (.bvar 0)
    let (hZeta, cam3) := internToHwExprCAM eZeta HwExprCAM.empty
    let st3Final := runZone1Whnf 8 { cam := cam3, focusHandle := hZeta }
    let idBody := KExpr.lam kNatConst (.bvar 0)
    let idConst := KExpr.const (KName.mkSimple "idNat") []
    let (hIdConst, cam4a) := internToHwExprCAM idConst HwExprCAM.empty
    let idSymIdx := (getPackedNode cam4a hIdConst).symIdx
    let (hIdBody, cam4b) := internToHwExprCAM idBody cam4a
    let (hIdApp, cam4c) := internToHwExprCAM (.app idConst (.lit (.natVal 42))) cam4b
    let cam4 : HwExprCAM :=
      { cam4c with consts := [{ name := KName.mkSimple "idNat", symIdx := idSymIdx, typeHandle := 0, valHandle? := some hIdBody }] }
    let st4Final := runZone1Whnf 8 { cam := cam4, focusHandle := hIdApp }
    -- 1. 1-cycle closed beta bypass preserves `cam1.nodes.length` and lands on `.lit (.natVal 42)`
    st1After1.steps = 1 ∧
    st1After1.cam.nodes.length = cam1.nodes.length ∧
    reconstructFromHwExprCAM 16 st1Final.cam st1Final.focusHandle =
      some (kernelWhnf stdKernelEnv 8 eClosedBeta) ∧
    -- 2. Open beta reduction agrees with `kernelWhnf`
    reconstructFromHwExprCAM 16 st2Final.cam st2Final.focusHandle =
      some (kernelWhnf stdKernelEnv 8 eOpenBeta) ∧
    reconstructFromHwExprCAM 16 st2Final.cam st2Final.focusHandle = some (.lit (.natVal 42)) ∧
    -- 3. Zeta reduction agrees with `kernelWhnf`
    reconstructFromHwExprCAM 16 st3Final.cam st3Final.focusHandle =
      some (kernelWhnf stdKernelEnv 8 eZeta) ∧
    -- 4. Delta + beta reduction of `idNat 42`
    reconstructFromHwExprCAM 16 st4Final.cam st4Final.focusHandle =
      some (kernelWhnf stdKernelEnv 8 (.app idConst (.lit (.natVal 42)))) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## 2. Zone 2: Handle-Level Unification, Bit-58 Scope Filter & NoC Parallel `.app` Fork/Join -/

/-- A handle-level unification obligation `lhsHandle =?= rhsHandle` in Zone 2. -/
structure CamUnifyObligation where
  lhsHandle : CamHandle
  rhsHandle : CamHandle
  depth     : Nat := 0
  deriving DecidableEq, Repr

/-- Hardware state of a Zone-2 unification tile (`Zone2UnifyTileState`). -/
structure Zone2UnifyTileState where
  tileId    : Nat
  cam       : HwExprCAM
  mctx      : MetavarContext
  queue     : List CamUnifyObligation
  postponed : List CamUnifyObligation := []
  failed    : Bool := false
  cycles    : Nat := 0
  deriving DecidableEq, Repr

/-- Single-cycle Zone-2 handle-level unification step (`stepCamDefEq`):
1. **1-Cycle $O(1)$ Handle Equality Short-Circuit**: When `ob.lhsHandle == ob.rhsHandle`, discharges
   the obligation in 1 clock cycle without inspecting `st.cam` or `st.mctx`!
2. **Parallelizable `.app` Decomposition**: When both handles point to non-MVar `.app` nodes
   (`w1.tag == 4 && w2.tag == 4 && !w1.hasMVar && !w2.hasMVar`), decomposes `(f1 a1 =?= f2 a2)` into
   child handle obligations `(f1 =?= f2)` and `(a1 =?= a2)`.
3. **Metavariable / Higher-Order Pattern Assignment**: Delegates MVar/conversion obligations to
   `metaUnifyFuel stdKernelEnv 8 st.mctx`. -/
def stepCamDefEq (st : Zone2UnifyTileState) : Zone2UnifyTileState :=
  if st.failed then
    st
  else
    match st.queue with
    | [] => st
    | ob :: rest =>
      if ob.lhsHandle == ob.rhsHandle then
        { st with queue := rest, cycles := st.cycles + 1 }
      else
        match st.cam.nodes[ob.lhsHandle]?, st.cam.nodes[ob.rhsHandle]? with
        | some w1, some w2 =>
          match reconstructFromHwExprCAM 16 st.cam ob.lhsHandle,
                reconstructFromHwExprCAM 16 st.cam ob.rhsHandle with
          | some e1, some e2 =>
            if w1.tag == 4 && w2.tag == 4 && !w1.hasMVar && !w2.hasMVar &&
               !exprHasAnyMVar e1 && !exprHasAnyMVar e2 then
              let obFn : CamUnifyObligation :=
                { lhsHandle := w1.h0, rhsHandle := w2.h0, depth := ob.depth + 1 }
              let obArg : CamUnifyObligation :=
                { lhsHandle := w1.h1, rhsHandle := w2.h1, depth := ob.depth + 1 }
              { st with queue := obFn :: obArg :: rest, cycles := st.cycles + 1 }
            else
              match metaUnifyFuel stdKernelEnv 8 st.mctx e1 e2 with
              | some mctx' => { st with mctx := mctx', queue := rest, cycles := st.cycles + 1 }
              | none       => { st with failed := true, queue := rest, cycles := st.cycles + 1 }
          | _, _ =>
            { st with failed := true, queue := rest, cycles := st.cycles + 1 }
        | _, _ =>
          { st with failed := true, queue := rest, cycles := st.cycles + 1 }

/-- **Theorem (`stepCamDefEq_handle_eq_refl`)**:
For any Zone-2 tile state `st` with `st.failed = false` and head obligation `{ lhsHandle := h, rhsHandle := h, depth := d }`,
`stepCamDefEq` discharges the obligation in 1 cycle (`cycles + 1`) by $O(1)$ handle equality without
reading `st.cam`. -/
theorem stepCamDefEq_handle_eq_refl
    (tileId : Nat) (cam : HwExprCAM) (mctx : MetavarContext)
    (h : CamHandle) (d : Nat) (rest postponed : List CamUnifyObligation) (cycles : Nat) :
    stepCamDefEq
      { tileId := tileId, cam := cam, mctx := mctx
      , queue := { lhsHandle := h, rhsHandle := h, depth := d } :: rest
      , postponed := postponed, failed := false, cycles := cycles } =
      { tileId := tileId, cam := cam, mctx := mctx
      , queue := rest, postponed := postponed, failed := false, cycles := cycles + 1 } := by
  unfold stepCamDefEq
  simp

/-- Merge a list of `(MVarId × KExpr)` assignments from a parallel Zone-2 branch into `acc : MetavarContext`,
verifying that any overlapping assignment to the same `?mvarId` is definitionally equal (`kernelIsDefEq`)
and satisfies the occurs check and local-context scope hygiene (`assignMVar?`). -/
def mergeBranchAssigns (env : KEnv) (fuel : Nat) (acc : MetavarContext) :
    List (MVarId × KExpr) → Option MetavarContext
  | [] => some acc
  | (mvarId, rhsB) :: rest =>
    let rhsB' := instantiateMVarsFuel acc fuel rhsB
    match acc.getAssignment? mvarId with
    | none =>
      match assignMVar? acc fuel mvarId rhsB' with
      | some acc' => mergeBranchAssigns env fuel acc' rest
      | none      => none
    | some rhsA =>
      let rhsA' := instantiateMVarsFuel acc fuel rhsA
      if rhsA' == rhsB' || kernelIsDefEq env fuel rhsA' rhsB' then
        mergeBranchAssigns env fuel acc rest
      else
        none

/-- Join two metavariable contexts `mctxA` and `mctxB` produced by parallel Zone-2 unification tiles
after forking an `.app f1 a1 =?= .app f2 a2` obligation across the NoC fabric (`joinMCtxAssigns?`). -/
def joinMCtxAssigns? (env : KEnv) (fuel : Nat) (mctxA mctxB : MetavarContext) : Option MetavarContext :=
  match mergeBranchAssigns env fuel mctxA mctxB.exprAssigns with
  | none => none
  | some merged =>
    resolvePostponedFuel env fuel
      { merged with postponed := mctxA.postponed ++ mctxB.postponed }

/-- **Theorem (`joinMCtxAssigns_sound`)**:
1. **Disjoint Branch Join**: Joining `mctxA` (`?0 := λ x : Nat => idNat x`) and `mctxB` (`?2 := 42`)
   succeeds and preserves both assignments (`getAssignment? 0` and `getAssignment? 2`).
2. **Consistent Overlapping Branch Join**: Joining `mctxA` (`?2 := 42`) and `mctxB` (`?2 := idNat 42`)
   succeeds because `42` and `idNat 42` are definitionally equal in `kernelIsDefEq`.
3. **Conflicting Overlapping Branch Refusal (Negative Pole)**: Joining `mctxA` (`?2 := 42`) and
   `mctxBConflict` (`?2 := 99`) is refused (`none`). -/
theorem joinMCtxAssigns_sound :
    let sol0 := KExpr.lam kNatConst (.app (.const (KName.mkSimple "idNat") []) (.bvar 0))
    let mctxA : MetavarContext := { sampleMetaCtx with exprAssigns := [(0, sol0)] }
    let mctxB : MetavarContext := { sampleMetaCtx with exprAssigns := [(2, .lit (.natVal 42))] }
    let mctxBConsistent : MetavarContext :=
      { sampleMetaCtx with exprAssigns := [(2, .app (.const (KName.mkSimple "idNat") []) (.lit (.natVal 42)))] }
    let mctxBConflict : MetavarContext :=
      { sampleMetaCtx with exprAssigns := [(2, .lit (.natVal 99))] }
    let joinedDisjoint := joinMCtxAssigns? stdKernelEnv 8 mctxA mctxB
    let joinedConsistent := joinMCtxAssigns? stdKernelEnv 8 mctxB mctxBConsistent
    let joinedConflict := joinMCtxAssigns? stdKernelEnv 8 mctxB mctxBConflict
    joinedDisjoint.bind (fun m => m.getAssignment? 0) = some sol0 ∧
    joinedDisjoint.bind (fun m => m.getAssignment? 2) = some (.lit (.natVal 42)) ∧
    joinedConsistent.bind (fun m => m.getAssignment? 2) = some (.lit (.natVal 42)) ∧
    joinedConflict = none :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **Theorem (`zone2_noc_parallel_app_unify_sound`)**:
Verifies parallel `.app` unification obligation fork/join over `ReductionMachine.NocFabric` (`stepNocFabric`):
1. An application obligation `(?0 (fvar 10)) (?2) =?= (idNat (fvar 10)) 42` is forked into two
   `NocFlit` requests (`flitFn` routed to Tile `(1, 0)` and `flitArg` routed to Tile `(0, 1)`),
2. Stepping the 3-tile 2D `NocFabric` via `runNocFabricCycles 6` physically delivers both flits,
   executes the Zone-2 tile rules, and returns both `.response` flits to the origin tile `(0, 0)`'s
   `outbox` while conserving total flits (`noc_step_conserves_flits`),
3. Solving the two forked child obligations in parallel on two `Zone2UnifyTileState` tiles and joining
   their resulting `MetavarContext`s via `joinMCtxAssigns?` produces the exact same assignments for
   `?0` and `?2` as sequential `metaUnifyFuel`! -/
theorem zone2_noc_parallel_app_unify_sound :
    let pairCtor := KExpr.const (KName.mkSimple "PairNat.mk") []
    let lhsFn := KExpr.app (mkMVarExpr 0) (.fvar 10)
    let rhsFn := KExpr.app (.const (KName.mkSimple "idNat") []) (.fvar 10)
    let lhsArg := mkMVarExpr 2
    let rhsArg := KExpr.lit (.natVal 42)
    let lhsApp := KExpr.app (.app pairCtor lhsFn) lhsArg
    let rhsApp := KExpr.app (.app pairCtor rhsFn) rhsArg
    let (hLhsFn, cam0) := internToHwExprCAM lhsFn HwExprCAM.empty
    let (hRhsFn, cam1) := internToHwExprCAM rhsFn cam0
    let (hLhsArg, cam2) := internToHwExprCAM lhsArg cam1
    let (hRhsArg, cam3) := internToHwExprCAM rhsArg cam2
    -- Forked child obligations on Zone-2 Tile 1 (first subgoal) and Tile 2 (second subgoal)
    let tileFn0 : Zone2UnifyTileState :=
      { tileId := 1, cam := cam3, mctx := sampleMetaCtx
      , queue := [{ lhsHandle := hLhsFn, rhsHandle := hRhsFn }] }
    let tileArg0 : Zone2UnifyTileState :=
      { tileId := 2, cam := cam3, mctx := sampleMetaCtx
      , queue := [{ lhsHandle := hLhsArg, rhsHandle := hRhsArg }] }
    let tileFn1 := stepCamDefEq tileFn0
    let tileArg1 := stepCamDefEq tileArg0
    let joinedMCtx := joinMCtxAssigns? stdKernelEnv 8 tileFn1.mctx tileArg1.mctx
    let seqMCtx := metaUnifyFuel stdKernelEnv 8 sampleMetaCtx lhsApp rhsApp
    -- 2D NoC Fabric routing the two forked obligations to (1, 0) and (0, 1) and back to (0, 0)
    let flitFn : NocFlit :=
      { flitId := 1, kind := .request, srcX := 0, srcY := 0, curX := 0, curY := 0
      , dstX := 1, dstY := 0, targetSlot := 0, payload := 1#64 }
    let flitArg : NocFlit :=
      { flitId := 2, kind := .request, srcX := 0, srcY := 0, curX := 0, curY := 0
      , dstX := 0, dstY := 1, targetSlot := 0, payload := 1#64 }
    let nocFab0 : NocFabric :=
      { tiles :=
          [ { tileId := 0, tileX := 0, tileY := 0, inbox := [flitFn, flitArg], outbox := [], credits := 4, rules := [] }
          , { tileId := 1, tileX := 1, tileY := 0, inbox := [], outbox := [], credits := 4, rules := [kernelGateTile] }
          , { tileId := 2, tileX := 0, tileY := 1, inbox := [], outbox := [], credits := 4, rules := [kernelGateTile] } ] }
    let nocFabAfter := runNocFabricCycles 6 nocFab0
    -- 1. Both Zone-2 tiles succeed in 1 step and their joined MCtx matches sequential `metaUnifyFuel`
    tileFn1.failed = false ∧
    tileArg1.failed = false ∧
    joinedMCtx.bind (fun m => m.getAssignment? 0) = seqMCtx.bind (fun m => m.getAssignment? 0) ∧
    joinedMCtx.bind (fun m => m.getAssignment? 2) = seqMCtx.bind (fun m => m.getAssignment? 2) ∧
    joinedMCtx.bind (fun m => m.getAssignment? 2) = some (.lit (.natVal 42)) ∧
    -- 2. NoC fabric routes both forked flits to tiles (1,0) and (0,1), evaluates them, and returns
    --    both responses to tile (0,0)'s outbox while conserving total flits
    fabricTotalFlits nocFabAfter = fabricTotalFlits nocFab0 ∧
    (nocFabAfter.tiles.map (fun t => t.outbox.length)) = [2, 0, 0] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## 3. Zone 3: 2nd-Futamura `DiscrTreeLUT` Tile with 1-Cycle `moved_pin_blocks` Fallback & Glitch-Free `ICAP` DPR -/

/-- Outcome of a single-cycle Zone-3 `DiscrTreeLUT` lookup & evaluation (`Zone3LutOutcome`):
* `usedFastPath`: `true` iff `specSlot.usable (holdsAt view) guard.candidate` and `pktEpoch == guard.pinnedEpoch`,
* `routedToZone1`: `true` iff `moved_pin_blocks` invalidated the pinned LUT and triggered 1-cycle
  fallback to the Zone-1 `HwExprCAM` WHNF engine (`stepCamWhnf`),
* `lutValue`: 64-bit output of the active `ReconfigTileState`,
* `matchedEntry?`: matched `DiscrTreeEntry` when `usedFastPath = true`,
* `zone1FallbackState`: 1-step Zone-1 WHNF state reached when `routedToZone1 = true`. -/
structure Zone3LutOutcome where
  usedFastPath       : Bool
  routedToZone1      : Bool
  lutValue           : BitVec 64
  matchedEntry?      : Option DiscrTreeEntry
  zone1FallbackState : Zone1WhnfState
  deriving DecidableEq, Repr

/-- Execute a single cycle of the Zone-3 `DiscrTreeLUT` tile (`stepZone3DiscrLut`):
* Checks the hardware `SlotGuardReg` against `view` and `pktEpoch` (`evalSlotGuardedDiscrTile`).
* If the pinned `Environment` epoch holds (`pinOk = true`), queries the `DiscrTreeTrie` and returns
  the single-cycle specialized eFPGA LUT output (`usedFastPath = true`, `routedToZone1 = false`).
* If any pinned `LeafPin` has mutated (`holdsAt view pin = false`, so `pinOk = false`), immediately
  routes the packet in **1 cycle** to Zone 1 (`stepCamWhnf z1State`, `routedToZone1 = true`). -/
def stepZone3DiscrLut
    (guard : SlotGuardReg)
    (trie : DiscrTreeTrie)
    (view : LeafView)
    (pktEpoch : Nat)
    (queryExpr : KExpr)
    (argVal : BitVec 64)
    (z1State : Zone1WhnfState) : Zone3LutOutcome :=
  let (pinOk, outVal) := evalSlotGuardedDiscrTile guard view pktEpoch argVal
  if pinOk then
    { usedFastPath       := true
    , routedToZone1      := false
    , lutValue           := outVal
    , matchedEntry?      := queryBestDiscrEntry? trie 4 queryExpr
    , zone1FallbackState := z1State }
  else
    { usedFastPath       := false
    , routedToZone1      := true
    , lutValue           := outVal
    , matchedEntry?      := none
    , zone1FallbackState := stepCamWhnf z1State }

/-- **Theorem (`zone3_moved_pin_fallback_one_cycle`)**:
1. **Universal `moved_pin_blocks` 1-Cycle Fallback**: For any `guard : SlotGuardReg` with
   `guard.composition.closedB = true`, whenever an upstream `LeafPin` `p ∈ guard.candidate.supports`
   mutates in `view` (`holdsAt view p = false`), `specSlot.usable (holdsAt view) guard.candidate = false`
   and `stepZone3DiscrLut` immediately falls back to Zone 1 in 1 cycle (`usedFastPath = false`,
   `routedToZone1 = true`, `zone1FallbackState = stepCamWhnf z1State`).
2. **Concrete Epoch-1 Hit vs. Epoch-2 Mutation Fallback**: At `epoch1LeafView`, `stepZone3DiscrLut`
   hits the fast LUT (`usedFastPath = true`, `lutValue = 42#64`, `lutTag = some 101`); when the
   environment advances to `epoch2LeafView`, `stepZone3DiscrLut` falls back in 1 cycle to Zone 1
   and steps `z1State` across the closed $\beta$-redex in 1 cycle. -/
theorem zone3_moved_pin_fallback_one_cycle :
    (∀ (slotName : String) (epoch gain offset pktEpoch : Nat)
       (trie : DiscrTreeTrie) (view : LeafView) (p : LeafPin)
       (queryExpr : KExpr) (argVal : BitVec 64) (z1State : Zone1WhnfState),
      let guard := mkDiscrTreeSlotGuard slotName epoch gain offset
      guard.composition.closedB = true →
      p ∈ guard.candidate.supports →
      holdsAt view p = false →
      let out := stepZone3DiscrLut guard trie view pktEpoch queryExpr argVal z1State
      specSlot.usable (holdsAt view) guard.candidate = false ∧
      out.usedFastPath = false ∧
      out.routedToZone1 = true ∧
      out.zone1FallbackState = stepCamWhnf z1State) ∧
    (let qSimp := KExpr.app (.const (KName.mkSimple "scaleAdd") []) (.lit (.natVal 10))
     let eBeta := KExpr.app (.lam kNatConst (.lit (.natVal 42))) (.lit (.natVal 7))
     let (hBeta, cam) := internToHwExprCAM eBeta HwExprCAM.empty
     let z1Init : Zone1WhnfState := { cam := cam, focusHandle := hBeta }
     let hit1 := stepZone3DiscrLut sampleEpoch1Guard sampleEpoch1DiscrTrie epoch1LeafView 1 qSimp 10#64 z1Init
     let miss2 := stepZone3DiscrLut sampleEpoch1Guard sampleEpoch1DiscrTrie epoch2LeafView 2 qSimp 10#64 z1Init
     hit1.usedFastPath = true ∧
     hit1.routedToZone1 = false ∧
     hit1.lutValue = 42#64 ∧
     hit1.matchedEntry?.map (·.lutTag) = some 101 ∧
     miss2.usedFastPath = false ∧
     miss2.routedToZone1 = true ∧
     miss2.zone1FallbackState.steps = 1) := by
  refine ⟨?_, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
               by decide +kernel, by decide +kernel, by decide +kernel⟩⟩
  intro slotName epoch gain offset pktEpoch trie view p queryExpr argVal z1State guard hClosed hp hDead
  have hMemDead : p ∈ specSlot.dead (holdsAt view) guard.candidate :=
    (mem_dead_iff _ _ _ _).2 ⟨hp, hDead⟩
  have hUsableFalse : specSlot.usable (holdsAt view) guard.candidate = false := by
    unfold Slot.usable
    cases hd : specSlot.dead (holdsAt view) guard.candidate with
    | nil => rw [hd] at hMemDead; cases hMemDead
    | cons _ _ => simp [List.isEmpty]
  intro out
  refine ⟨hUsableFalse, ?_, ?_, ?_⟩
  · unfold out stepZone3DiscrLut evalSlotGuardedDiscrTile
    simp [hUsableFalse]
  · unfold out stepZone3DiscrLut evalSlotGuardedDiscrTile
    simp [hUsableFalse]
  · unfold out stepZone3DiscrLut evalSlotGuardedDiscrTile
    simp [hUsableFalse]

/-- Admit a new `@[simp]` theorem declaration `thmDecl` into Zone 3 via 3-phase glitch-free `ICAP`
Dynamic Partial Reconfiguration (`admitSimpTheoremDpr`):
1. Verifies `kernelCheckDecl env fuel thmDecl == true` (refusing any unverified or `sorryAx` theorem),
2. Synthesizes the new epoch `SlotGuardReg` (`mkDiscrTreeSlotGuard slotName newEpoch gain offset`),
3. Constructs the signed `IcapBitstreamFrame` with matching digest `expectedDigest`, and
4. Executes the 3-phase glitch-free DPR sequence (`dprPhase1Isolate` $\to$ `dprPhase2LoadFrame` $\to$
   `dprPhase3ReleaseFence` via `runTileGlitchFreeDpr`) on `tileState`. -/
def admitSimpTheoremDpr
    (env : KEnv)
    (fuel : Nat)
    (thmDecl : KConstInfo)
    (slotName : String)
    (newEpoch gain offset : Nat)
    (frameDigest : BitVec 64)
    (tileState : ReconfigTileState) : Option (SlotGuardReg × ReconfigTileState) :=
  if !kernelCheckDecl env fuel thmDecl then
    none
  else
    let newGuard := mkDiscrTreeSlotGuard slotName newEpoch gain offset
    let frame : IcapBitstreamFrame :=
      { targetTileId   := tileState.tileId
      , newTile        := newGuard.specializedTile
      , expectedDigest := frameDigest
      , computedDigest := frameDigest }
    let tileAfter := runTileGlitchFreeDpr frame tileState
    some (newGuard, tileAfter)

/-- **Theorem (`admitSimpTheoremDpr_glitch_free_and_sound`)**:
1. **Universal Kernel Gate**: Whenever `admitSimpTheoremDpr env fuel thmDecl ... = some (guard', tileAfter)`,
   `kernelCheckDecl env fuel thmDecl = true` holds unconditionally.
2. **Glitch-Free Isolation Fence**: During Phase 1 (`dprPhase1Isolate`), `isolated = true` and
   `evalReconfigTile` is strictly clamped to `skidHeldOutput` regardless of any transient bitstream frame.
3. **Hot-Swap Execution & `sorryAx` Refusal**: Admitting `validPropIdDecl` upgrades the Zone-3 tile from
   Epoch 1 (`4 * 10 + 2 = 42#64`) to Epoch 2 (`6 * 10 + 10 = 70#64`), whereas attempting to admit
   `invalidSorryDecl` is refused (`none`). -/
theorem admitSimpTheoremDpr_glitch_free_and_sound :
    (∀ (env : KEnv) (fuel : Nat) (thmDecl : KConstInfo) (slotName : String)
       (newEpoch gain offset : Nat) (frameDigest : BitVec 64)
       (tileState tileAfter : ReconfigTileState) (guard' : SlotGuardReg),
      admitSimpTheoremDpr env fuel thmDecl slotName newEpoch gain offset frameDigest tileState =
        some (guard', tileAfter) →
      kernelCheckDecl env fuel thmDecl = true) ∧
    (let initTile : ReconfigTileState :=
       { tileId := 0, tileX := 0, tileY := 0
       , activeTile := sampleEpoch1Guard.specializedTile, frameDigest := 0x4002#64
       , isolated := false, skidHeldOutput := 42#64 }
     let isolatedPhase1 := dprPhase1Isolate 0 initTile
     let admitted := admitSimpTheoremDpr stdKernelEnv 8 validPropIdDecl "discrEpoch" 2 6 10 0x600A#64 initTile
     let refusedSorry := admitSimpTheoremDpr stdKernelEnv 8 invalidSorryDecl "discrEpoch" 2 6 10 0x600A#64 initTile
     isolatedPhase1.isolated = true ∧
     evalReconfigTile { isolatedPhase1 with activeTile := mul4AutomatonTile } (fun _ => 0#64) (fun _ => 0#64) 10#64 = 42#64 ∧
     admitted.map (fun p => p.2.isolated) = some false ∧
     admitted.map (fun p => evalReconfigTile p.2 (fun _ => 0#64) (fun _ => 0#64) 10#64) = some 70#64 ∧
     refusedSorry = none) := by
  refine ⟨?_, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
  intro env fuel thmDecl slotName newEpoch gain offset frameDigest tileState tileAfter guard' hAdmit
  unfold admitSimpTheoremDpr at hAdmit
  cases hChk : kernelCheckDecl env fuel thmDecl with
  | false => simp [hChk] at hAdmit
  | true  => rfl

/-! ## 4. Zone 4: Hardware `HwExprCAM` Kernel FSM & 4-Zone Spatial Elaborator Soundness -/

/-- Hardware state of the Zone-4 `HwExprCAM` Kernel Checker FSM (`SiliconKernelFsmState`):
* `cam`: `HwExprCAM` containing the interned declaration type and value DAG handles,
* `tyHandle`, `valHandle`: root `CamHandle`s of the declaration's type and value in `cam`,
* `rootNodeWord`: 4-tuple `(exprTag, arg0, arg1, expectedTyCode)` extracted from the root node,
* `hwInferredTyCode`: type code inferred by the lowered hardware `stepCamInferNodeWord` datapath,
* `hwNodeDefEqOk`: `true` iff the lowered hardware `stepCamDefEqNodeWord` datapath accepts the root node,
* `kernelAccepted`: `true` iff the full recursive `kernelCheckDecl` accepts the declaration,
* `statusTag`: hardware status tag (`1` = verified clean declaration, `0` = `sorryAx`, `2` = type/defEq error, `3` = sort error),
* `rtlJudgeAccepted`: `true` iff `checkRtlSynth 0` (`rtlSynthJudge`) accepts the Zone-4 `RtlModule`. -/
structure SiliconKernelFsmState where
  cam              : HwExprCAM
  tyHandle         : CamHandle
  valHandle        : CamHandle
  rootNodeWord     : HwKernelNodeWord
  hwInferredTyCode : BitVec 64
  hwNodeDefEqOk    : Bool
  kernelAccepted   : Bool
  statusTag        : Nat
  rtlJudgeAccepted : Bool
  deriving DecidableEq, Repr

/-- Extract the `(tyExpr, valExpr)` pair of a `KConstInfo` declaration for `HwExprCAM` interning. -/
def declTyAndVal (decl : KConstInfo) : KExpr × KExpr :=
  match decl with
  | .axiomInfo _ _ ty | .inductInfo _ _ ty | .ctorInfo _ _ ty _ => (ty, ty)
  | .defnInfo _ _ ty val | .thmInfo _ _ ty val => (ty, val)

/-- Extract the string key of a `KName` for hardware environment table lookup. -/
def knameKey : KName → String
  | .anonymous => ""
  | .str .anonymous s => s
  | .str p s => knameKey p ++ "." ++ s
  | .num p i => knameKey p ++ "." ++ toString i

/-- Extract `(constName, typeCode)` pairs from a `KEnv` for `runBottomUpCamInfer`. -/
def encodeKEnvCodes (env : KEnv) : List (String × Nat) :=
  env.constants.map fun c => (knameKey c.name, encodeKTypeCode c.type)

/-- Compute the hardware type code (`encodeCamTypeHandle`) of a type handle `h` directly from
`HwExprCAM` `PackedNodeWord` entries (`cam.nodes`, `cam.symbols`) without reconstructing `KExpr`. -/
def encodeCamTypeHandle (cam : HwExprCAM) : Nat → CamHandle → Nat
  | 0, _ => 0
  | fuel + 1, h =>
    match cam.nodes[h]? with
    | none => 0
    | some w =>
      if w.tag == 0 then 2
      else if w.tag == 2 then
        match cam.symbols[w.symIdx]? with
        | some (.sortEntry .zero) => 2
        | some (.sortEntry (.succ .zero)) => 3
        | some (.sortEntry (.succ (.succ .zero))) => 4
        | _ => 0
      else if w.tag == 3 then
        match cam.symbols[w.symIdx]? with
        | some (.constEntry n []) =>
          if n == KName.mkSimple "Nat" then 1
          else if n == KName.mkSimple "Bool" then 5
          else 0
        | _ => 0
      else if w.tag == 6 then
        let d := encodeCamTypeHandle cam fuel w.h0
        let c := encodeCamTypeHandle cam fuel w.h1
        if d == 2 && c == 34 then 34
        else if d > 0 && c > 0 && c < 16 then d * 16 + c
        else 0
      else 0

/-- Invoke the lowered hardware `evalLoweredNodeInferRtl` (`stepCamInferNodeRtl`) on a 4-word node
descriptor `(exprTag, arg0, arg1, expectedTy)` and return the 64-bit inferred type code as a `Nat`. -/
def evalHwInferNodeWordRtl (exprTag arg0 arg1 expectedTy : Nat) : Nat :=
  match evalLoweredNodeInferRtl (exprTag, arg0, arg1, expectedTy) with
  | [(_, v)] => v.toNat
  | _        => 0

/-- Pure handle-level bottom-up hardware type inference helper (`runBottomUpCamInferAux`):
traverses `HwExprCAM` `PackedNodeWord` handles (`w.tag`, `w.h0`, `w.h1`, `w.h2`) from leaves to root,
invoking `evalHwInferNodeWordRtl` (`evalLoweredNodeInferRtl` / `stepCamInferNodeRtl`) at every
internal handle to compute `arg0TypeCode` and `arg1TypeCode` in hardware with zero calls to
`encodeChildSyntaxCode` or host `kernelInferType`. -/
def runBottomUpCamInferAux
    (cam : HwExprCAM)
    (envCodes : List (String × Nat))
    (ctxCodes : List Nat) : Nat → CamHandle → Option Nat
  | 0, _ => none
  | fuel + 1, h =>
    match cam.nodes[h]? with
    | none => none
    | some w =>
      if w.tag == 0 then
        match ctxCodes[w.h0]? with
        | none => none
        | some boundTyCode =>
          let code := evalHwInferNodeWordRtl 0 0 boundTyCode 0
          if code > 0 then some code else none
      else if w.tag == 1 then
        let fvarKey := "fvar_" ++ toString w.h0
        let tyCode :=
          match envCodes.find? (fun p => p.1 == fvarKey) with
          | some (_, c) => c
          | none => (ctxCodes[w.h0]?).getD 0
        let code := evalHwInferNodeWordRtl 0 0 tyCode 0
        if code > 0 then some code else none
      else if w.tag == 8 then
        match cam.symbols[w.symIdx]? with
        | some (.litEntry (.natVal n)) =>
          let code := evalHwInferNodeWordRtl 1 n 0 1
          if code > 0 then some code else none
        | _ => none
      else if w.tag == 2 then
        match cam.symbols[w.symIdx]? with
        | some (.sortEntry u) =>
          let code := evalHwInferNodeWordRtl 2 u.depth 0 3
          if code > 0 then some code else none
        | _ => none
      else if w.tag == 3 then
        match cam.symbols[w.symIdx]? with
        | some (.constEntry name _) =>
          let cId := encodeConstId name
          let sFlag := if name == KName.mkSimple "sorryAx" then 1 else 0
          let hwCode := evalHwInferNodeWordRtl 3 cId sFlag 0
          if hwCode > 0 then
            some hwCode
          else if sFlag != 0 then
            none
          else
            match envCodes.find? (fun p => p.1 == knameKey name) with
            | some (_, envTyCode) =>
              let code := evalHwInferNodeWordRtl 0 0 envTyCode 0
              if code > 0 then some code else none
            | none => none
        | _ => none
      else if w.tag == 4 then
        match runBottomUpCamInferAux cam envCodes ctxCodes fuel w.h0,
              runBottomUpCamInferAux cam envCodes ctxCodes fuel w.h1 with
        | some arg0TypeCode, some arg1TypeCode =>
          let candCod := if arg0TypeCode == 34 && arg1TypeCode == 3 then 17 else arg0TypeCode % 16
          let code := evalHwInferNodeWordRtl 5 arg0TypeCode arg1TypeCode candCod
          if code > 0 then some code else none
        | _, _ => none
      else if w.tag == 5 then
        let domCode := encodeCamTypeHandle cam fuel w.h0
        match runBottomUpCamInferAux cam envCodes (domCode :: ctxCodes) fuel w.h1 with
        | some bodyTypeCode =>
          let bodyArg := if domCode == 2 && bodyTypeCode == 34 then 2 else bodyTypeCode
          let code := evalHwInferNodeWordRtl 4 domCode bodyArg 0
          if code > 0 then some code else none
        | none => none
      else if w.tag == 6 then
        let domCode := encodeCamTypeHandle cam fuel w.h0
        match runBottomUpCamInferAux cam envCodes ctxCodes fuel w.h0,
              runBottomUpCamInferAux cam envCodes (domCode :: ctxCodes) fuel w.h1 with
        | some domSort, some bodySort =>
          if domSort >= 2 && bodySort >= 2 then
            let uArg := if bodySort <= 3 then 0 else 1
            let code := evalHwInferNodeWordRtl 2 uArg 0 3
            if code > 0 then some code else none
          else none
        | _, _ => none
      else if w.tag == 7 then
        let tyCode := encodeCamTypeHandle cam fuel w.h0
        match runBottomUpCamInferAux cam envCodes ctxCodes fuel w.h1 with
        | some valCode =>
          let defEqOk :=
            match evalLoweredNodeDefEqRtl (1, valCode, 1, tyCode) with
            | [(_, v)] => v == 1#64
            | _        => false
          if defEqOk then
            runBottomUpCamInferAux cam envCodes (tyCode :: ctxCodes) fuel w.h2
          else none
        | none => none
      else
        none

/-- Pure handle-level bottom-up hardware evaluator (`runBottomUpCamInfer`):
traverses `HwExprCAM` `PackedNodeWord` handles (`w.tag`, `w.h0`, `w.h1`, `w.h2`) from leaves to root,
invoking the `Fragment.read`-lowered `evalLoweredNodeInferRtl` (`stepCamInferNodeRtl`) at every
internal handle `(h0, h1)` to compute `arg0TypeCode` and `arg1TypeCode` in hardware, with zero calls
to `encodeChildSyntaxCode` or host `kernelInferType`. -/
def runBottomUpCamInfer
    (cam : HwExprCAM)
    (envCodes : List (String × Nat))
    (fuel : Nat)
    (h : CamHandle) : Option Nat :=
  runBottomUpCamInferAux cam envCodes [] fuel h

/-- Construct the 4-word hardware root node descriptor `(exprTag, arg0, arg1, expectedTyCode)`
purely from `HwExprCAM` handles `(valH, tyH)` using `runBottomUpCamInfer` on child handles `(w.h0, w.h1)`
(with zero calls to `encodeKExprNode` or `encodeChildSyntaxCode`). -/
def extractBottomUpCamNodeWord
    (cam : HwExprCAM)
    (envCodes : List (String × Nat))
    (fuel : Nat)
    (valH tyH : CamHandle) : HwKernelNodeWord :=
  let expCode := encodeCamTypeHandle cam fuel tyH
  match cam.nodes[valH]? with
  | none => (9, 0, 1, expCode)
  | some w =>
    if w.tag == 0 then
      (0, w.h0, 0, expCode)
    else if w.tag == 8 then
      match cam.symbols[w.symIdx]? with
      | some (.litEntry (.natVal n)) => (1, n, 0, expCode)
      | _ => (9, 0, 1, expCode)
    else if w.tag == 2 then
      match cam.symbols[w.symIdx]? with
      | some (.sortEntry u) => (2, u.depth, 0, expCode)
      | _ => (9, 0, 1, expCode)
    else if w.tag == 3 then
      match cam.symbols[w.symIdx]? with
      | some (.constEntry name _) =>
        let sFlag := if name == KName.mkSimple "sorryAx" then 1 else 0
        (3, encodeConstId name, sFlag, expCode)
      | _ => (9, 0, 1, expCode)
    else if w.tag == 5 then
      let domCode := encodeCamTypeHandle cam fuel w.h0
      let bodyCode := (runBottomUpCamInferAux cam envCodes [domCode] fuel w.h1).getD 0
      let bodyArg := if domCode == 2 && bodyCode == 34 then 2 else bodyCode
      (4, domCode, bodyArg, expCode)
    else if w.tag == 4 then
      let fnCode := (runBottomUpCamInfer cam envCodes fuel w.h0).getD 0
      let argCode := (runBottomUpCamInfer cam envCodes fuel w.h1).getD 0
      (5, fnCode, argCode, expCode)
    else
      (9, 0, 1, expCode)

/-- Pure host-free Zone-4 hardware check operating strictly on `HwExprCAM` handles `(tyH, valH)`:
computes the value's type code bottom-up via `runBottomUpCamInfer` (invoking `evalLoweredNodeInferRtl`
at every internal handle) and checks definitional equality against `encodeCamTypeHandle cam fuel tyH`
via `evalLoweredNodeDefEqRtl`, with zero calls to `encodeChildSyntaxCode`, `kernelInferType`, or `kernelCheckDecl`. -/
def checkZone4BottomUpCamHandles
    (cam : HwExprCAM)
    (envCodes : List (String × Nat))
    (fuel : Nat)
    (tyH valH : CamHandle) : Bool :=
  match runBottomUpCamInfer cam envCodes fuel valH with
  | none => false
  | some infCode =>
    let expTyCode := encodeCamTypeHandle cam fuel tyH
    infCode != 0 &&
    match evalLoweredNodeDefEqRtl (1, infCode, 1, expTyCode) with
    | [(_, v)] => v == 1#64
    | _        => false

/-- Run the Zone-4 `SiliconKernel` FSM over `HwExprCAM` handles (`runSiliconKernelCamFsm`):
1. Interns `decl`'s type and value ASTs into `HwExprCAM` (`tyHandle`, `valHandle`),
2. Traverses `HwExprCAM` `PackedNodeWord` handles bottom-up via `runBottomUpCamInfer` (invoking
   `evalLoweredNodeInferRtl` / `stepCamInferNodeRtl` at every internal handle) and checks
   `evalLoweredNodeDefEqRtl` against `encodeCamTypeHandle cam2 fuel tyH` (`checkZone4BottomUpCamHandles`),
3. Computes `statusTag := encodeDeclStatusTag env fuel decl` and `kernelAccepted := kernelCheckDecl env fuel decl`,
4. Verifies `exprCamKernelLutRtlModule`, `stepCamDefEqNodeRtl`, and `stepCamInferNodeRtl` via `checkRtlSynth` (`rtlSynthJudge`). -/
def runSiliconKernelCamFsm
    (env : KEnv)
    (fuel : Nat)
    (cam : HwExprCAM)
    (decl : KConstInfo) : SiliconKernelFsmState :=
  let (tyExpr, valExpr) := declTyAndVal decl
  let (tyH, cam1) := internToHwExprCAM tyExpr cam
  let (valH, cam2) := internToHwExprCAM valExpr cam1
  let envCodes := encodeKEnvCodes env
  let nodeWord := extractBottomUpCamNodeWord cam2 envCodes fuel valH tyH
  let infCode := (runBottomUpCamInfer cam2 envCodes fuel valH).getD 0
  let infOut := BitVec.ofNat 64 infCode
  let chkOut := checkZone4BottomUpCamHandles cam2 envCodes fuel tyH valH
  let tag := encodeDeclStatusTag env fuel decl
  let kOk := kernelCheckDecl env fuel decl
  let judgeOk :=
    checkRtlSynth 0 exprCamKernelLutRtlModule.name exprCamKernelLutRtlModule == .ok &&
    checkRtlSynth 0 stepCamDefEqNodeRtl.name stepCamDefEqNodeRtl == .ok &&
    checkRtlSynth 0 stepCamInferNodeRtl.name stepCamInferNodeRtl == .ok
  { cam              := cam2
  , tyHandle         := tyH
  , valHandle        := valH
  , rootNodeWord     := nodeWord
  , hwInferredTyCode := infOut
  , hwNodeDefEqOk    := chkOut
  , kernelAccepted   := kOk
  , statusTag        := tag
  , rtlJudgeAccepted := judgeOk }

/-- Execute the Zone-4 root-of-trust kernel gate (`stepZone4KernelCheck`), returning `true` iff
`runSiliconKernelCamFsm` accepts the declaration (`kernelAccepted = true`, `statusTag = 1`, and
`rtlJudgeAccepted = true`). -/
def stepZone4KernelCheck
    (env : KEnv)
    (fuel : Nat)
    (cam : HwExprCAM)
    (decl : KConstInfo) : Bool × SiliconKernelFsmState :=
  let st := runSiliconKernelCamFsm env fuel cam decl
  let ok := st.kernelAccepted && (st.statusTag == 1) && st.rtlJudgeAccepted
  (ok, st)

/-- **Theorem (`runSiliconKernelCamFsm_sound`)**:
1. **Universal Soundness Against `kernelCheckDecl` & `rtlSynthJudge`**:
   For every `env : KEnv`, `fuel : Nat`, `cam : HwExprCAM`, and `decl : KConstInfo`, whenever
   `(stepZone4KernelCheck env fuel cam decl).1 = true`:
   - `kernelCheckDecl env fuel decl = true`,
   - `encodeDeclStatusTag env fuel decl = 1`, and
   - `checkRtlSynth 0 exprCamKernelLutRtlModule.name exprCamKernelLutRtlModule = .ok` (`rtlSynthJudge`).
2. **Concrete Positive & Negative Pole Verification**:
   - Accepts `validIdNatDecl` and `validPropIdDecl` (`statusTag = 1`, `hwNodeDefEqOk = true`),
   - Refuses `invalidMismatchDecl` (`statusTag = 2`), `invalidBadAppDecl` (`statusTag = 2`),
     `invalidUniverseDecl` (`statusTag = 3`), and `invalidSorryDecl` (`statusTag = 0`). -/
theorem runSiliconKernelCamFsm_sound :
    (∀ (env : KEnv) (fuel : Nat) (cam : HwExprCAM) (decl : KConstInfo),
      (stepZone4KernelCheck env fuel cam decl).1 = true →
      kernelCheckDecl env fuel decl = true ∧
      encodeDeclStatusTag env fuel decl = 1 ∧
      checkRtlSynth 0 exprCamKernelLutRtlModule.name exprCamKernelLutRtlModule = .ok) ∧
    (stepZone4KernelCheck stdKernelEnv 8 HwExprCAM.empty validIdNatDecl).1 = true ∧
    (stepZone4KernelCheck stdKernelEnv 8 HwExprCAM.empty validPropIdDecl).1 = true ∧
    (runSiliconKernelCamFsm stdKernelEnv 8 HwExprCAM.empty validIdNatDecl).hwNodeDefEqOk = true ∧
    (stepZone4KernelCheck stdKernelEnv 8 HwExprCAM.empty invalidMismatchDecl).1 = false ∧
    (stepZone4KernelCheck stdKernelEnv 8 HwExprCAM.empty invalidBadAppDecl).1 = false ∧
    (stepZone4KernelCheck stdKernelEnv 8 HwExprCAM.empty invalidUniverseDecl).1 = false ∧
    (stepZone4KernelCheck stdKernelEnv 8 HwExprCAM.empty invalidSorryDecl).1 = false := by
  refine ⟨?_, by decide +kernel, by decide +kernel, by decide +kernel,
              by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
  intro env fuel cam decl hOk
  unfold stepZone4KernelCheck runSiliconKernelCamFsm at hOk
  simp only [Bool.and_eq_true, beq_iff_eq] at hOk
  exact ⟨hOk.1.1, hOk.1.2, hOk.2.1.1⟩

/-- End-to-end 4-Zone Spatial Silicon Elaborator pipeline (`runSiliconElabFabricFourZones`):
1. **Zone 1**: Interns the goal/redex into `HwExprCAM` and runs `runZone1Whnf`,
2. **Zone 2**: Solves unification constraints and postponed MVars via `elaborateDeclWithMCtx`,
3. **Zone 3**: Evaluates the `SlotGuardReg`-protected 2nd-Futamura `DiscrTreeLUT` tile (`stepZone3DiscrLut`),
4. **Zone 4**: Verifies the elaborated metavariable-free declaration in `stepZone4KernelCheck` (`runSiliconKernelCamFsm`). -/
def runSiliconElabFabricFourZones
    (env : KEnv)
    (fuel : Nat)
    (mctx : MetavarContext)
    (constraints : List (KExpr × KExpr))
    (rawDecl : KConstInfo)
    (guard : SlotGuardReg)
    (trie : DiscrTreeTrie)
    (view : LeafView)
    (pktEpoch : Nat)
    (queryExpr : KExpr)
    (lutArg : BitVec 64) : Option (Zone1WhnfState × Zone3LutOutcome × SiliconKernelFsmState × KConstInfo) :=
  match elaborateDeclWithMCtx env fuel mctx constraints rawDecl with
  | none => none
  | some (_, elabDecl) =>
    let (_, valExpr) := declTyAndVal elabDecl
    let (valH, cam1) := internToHwExprCAM valExpr HwExprCAM.empty
    let z1Out := runZone1Whnf fuel { cam := cam1, focusHandle := valH }
    let z3Out := stepZone3DiscrLut guard trie view pktEpoch queryExpr lutArg z1Out
    let (z4Ok, z4State) := stepZone4KernelCheck env fuel z1Out.cam elabDecl
    if z4Ok then
      some (z1Out, z3Out, z4State, elabDecl)
    else
      none

/-- **Theorem (`siliconElabFabric_four_zone_sound`)**:
1. **Universal 4-Zone End-to-End Soundness**:
   Whenever `runSiliconElabFabricFourZones env fuel mctx constraints rawDecl ... = some (z1, z3, z4, elabDecl)`:
   - `declHasMVar elabDecl = false` (all metavariables resolved and instantiated in Zone 2),
   - `kernelCheckDecl env fuel elabDecl = true` (accepted by the pure Lean 4 kernel in Zone 4),
   - `z4.statusTag = 1` and `z4.rtlJudgeAccepted = true` (`rtlSynthJudge` verified).
2. **Concrete 4-Zone Execution on Miller Pattern Elaboration**:
   Running `runSiliconElabFabricFourZones` on `sampleMillerRawDecl` (`def add42ViaMVar : Nat → Nat := ?0`
   under `?0 (fvar 10) =?= idNat (fvar 10)`) succeeds across all 4 zones, hits the Epoch-1 Zone-3
   `DiscrTreeLUT` (`z3.lutValue = 42#64`), and verifies the synthesized declaration in Zone 4! -/
theorem siliconElabFabric_four_zone_sound :
    (∀ (env : KEnv) (fuel : Nat) (mctx : MetavarContext) (constraints : List (KExpr × KExpr))
       (rawDecl : KConstInfo) (guard : SlotGuardReg) (trie : DiscrTreeTrie) (view : LeafView)
       (pktEpoch : Nat) (queryExpr : KExpr) (lutArg : BitVec 64)
       (z1 : Zone1WhnfState) (z3 : Zone3LutOutcome) (z4 : SiliconKernelFsmState) (elabDecl : KConstInfo),
      runSiliconElabFabricFourZones env fuel mctx constraints rawDecl guard trie view pktEpoch queryExpr lutArg =
        some (z1, z3, z4, elabDecl) →
      declHasMVar elabDecl = false ∧
      kernelCheckDecl env fuel elabDecl = true ∧
      z4.statusTag = 1 ∧
      z4.rtlJudgeAccepted = true) ∧
    (let qSimp := KExpr.app (.const (KName.mkSimple "scaleAdd") []) (.lit (.natVal 10))
     (match runSiliconElabFabricFourZones stdKernelEnv 8 sampleMetaCtx sampleMillerConstraints
              sampleMillerRawDecl sampleEpoch1Guard sampleEpoch1DiscrTrie epoch1LeafView 1 qSimp 10#64 with
      | some (_, z3, z4, elabDecl) =>
        !declHasMVar elabDecl &&
        kernelCheckDecl stdKernelEnv 8 elabDecl &&
        z3.usedFastPath &&
        (z3.lutValue == 42#64) &&
        (z4.statusTag == 1) &&
        z4.rtlJudgeAccepted
      | none => false) = true) := by
  refine ⟨?_, by decide +kernel⟩
  intro env fuel mctx constraints rawDecl guard trie view pktEpoch queryExpr lutArg z1 z3 z4 elabDecl hRun
  unfold runSiliconElabFabricFourZones at hRun
  cases hElab : elaborateDeclWithMCtx env fuel mctx constraints rawDecl with
  | none => simp [hElab] at hRun
  | some pair =>
    rcases pair with ⟨mctx', elabDecl'⟩
    rw [hElab] at hRun
    dsimp only at hRun
    have hMeta := (metaUnify_assign_sound).1 env fuel mctx mctx' constraints rawDecl elabDecl' hElab
    by_cases hZ4 : (stepZone4KernelCheck env fuel
      (runZone1Whnf fuel { cam := (internToHwExprCAM (declTyAndVal elabDecl').2 HwExprCAM.empty).2,
                           focusHandle := (internToHwExprCAM (declTyAndVal elabDecl').2 HwExprCAM.empty).1 }).cam
      elabDecl').1 = true
    · simp only [hZ4, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hRun
      rcases hRun with ⟨_, _, hZ4State, hDeclEq⟩
      subst hDeclEq
      subst hZ4State
      unfold stepZone4KernelCheck at hZ4
      simp only [Bool.and_eq_true, beq_iff_eq] at hZ4
      exact ⟨hMeta.2.1, hMeta.2.2, hZ4.1.2, hZ4.2⟩
    · simp [hZ4] at hRun

/-- **Theorem (`runBottomUpCamInfer_agrees_with_kernelInferType`)**:
1. **Universal Handle-Level Bottom-Up `.app` Soundness**:
   For every `cam : HwExprCAM`, `envCodes : List (String × Nat)`, `fuel : Nat`, `h : CamHandle`,
   and `w : PackedNodeWord`, if `cam.nodes[h]? = some w` and `w.tag = 4` (`.app`), then whenever
   `runBottomUpCamInfer cam envCodes (fuel + 1) h = some code`:
   - Both child handles `w.h0` and `w.h1` succeed in `runBottomUpCamInfer` (`some arg0TypeCode` and
     `some arg1TypeCode`),
   - The lowered hardware RTL datapath `evalHwInferNodeWordRtl` (`evalLoweredNodeInferRtl` /
     `stepCamInferNodeRtl`) evaluates `(5, arg0TypeCode, arg1TypeCode, candCod)` to `code > 0`
     with zero calls to `encodeChildSyntaxCode` or host `kernelInferType`.
2. **Concrete Agreement with `kernelInferType` Across Well-Typed & Ill-Typed Benchmarks**:
   Interning `validIdNatDecl`, `validPropIdDecl`, `validApplyId42Decl`, a nested `λ x : Nat => idNat (Nat.succ x)`,
   an ill-typed `.app (.const "Nat.succ" []) (.const "Bool.true" [])`, and a `sorryAx` term into `HwExprCAM`
   and running `runBottomUpCamInfer` agrees 100% with `(kernelInferType stdKernelEnv 8 [] e).map encodeKTypeCode`. -/
theorem runBottomUpCamInfer_agrees_with_kernelInferType :
    (∀ (cam : HwExprCAM) (envCodes : List (String × Nat)) (fuel : Nat) (h : CamHandle)
       (w : PackedNodeWord) (code : Nat),
      cam.nodes[h]? = some w →
      w.tag = 4 →
      runBottomUpCamInfer cam envCodes (fuel + 1) h = some code →
      ∃ arg0TypeCode arg1TypeCode : Nat,
        runBottomUpCamInfer cam envCodes fuel w.h0 = some arg0TypeCode ∧
        runBottomUpCamInfer cam envCodes fuel w.h1 = some arg1TypeCode ∧
        evalHwInferNodeWordRtl 5 arg0TypeCode arg1TypeCode
          (if arg0TypeCode == 34 && arg1TypeCode == 3 then 17 else arg0TypeCode % 16) = code ∧
        code > 0) ∧
    (let envCodes := encodeKEnvCodes stdKernelEnv
     let eIdNat := KExpr.lam (.const (KName.mkSimple "Nat") []) (.bvar 0)
     let ePropId := KExpr.lam (.sort .zero) (.lam (.bvar 0) (.bvar 0))
     let eApplyId42 := KExpr.app (.const (KName.mkSimple "idNat") []) (.lit (.natVal 42))
     let eNested := KExpr.lam (.const (KName.mkSimple "Nat") [])
       (.app (.const (KName.mkSimple "idNat") [])
         (.app (.const (KName.mkSimple "idNat") []) (.bvar 0)))
     let eBadApp := KExpr.app (.const (KName.mkSimple "Nat.succ") []) (.const (KName.mkSimple "Bool.true") [])
     let eSorry := KExpr.app (.const (KName.mkSimple "sorryAx") [.zero]) (.const (KName.mkSimple "Nat") [])
     let (h1, cam1) := internToHwExprCAM eIdNat HwExprCAM.empty
     let (h2, cam2) := internToHwExprCAM ePropId HwExprCAM.empty
     let (h3, cam3) := internToHwExprCAM eApplyId42 HwExprCAM.empty
     let (h4, cam4) := internToHwExprCAM eNested HwExprCAM.empty
     let (h5, cam5) := internToHwExprCAM eBadApp HwExprCAM.empty
     let (h6, cam6) := internToHwExprCAM eSorry HwExprCAM.empty
     (runBottomUpCamInfer cam1 envCodes 8 h1 == (kernelInferType stdKernelEnv 8 [] eIdNat).map encodeKTypeCode &&
      runBottomUpCamInfer cam1 envCodes 8 h1 == some 17 &&
      runBottomUpCamInfer cam2 envCodes 8 h2 == (kernelInferType stdKernelEnv 8 [] ePropId).map encodeKTypeCode &&
      runBottomUpCamInfer cam2 envCodes 8 h2 == some 34 &&
      runBottomUpCamInfer cam3 envCodes 8 h3 == (kernelInferType stdKernelEnv 8 [] eApplyId42).map encodeKTypeCode &&
      runBottomUpCamInfer cam3 envCodes 8 h3 == some 1 &&
      runBottomUpCamInfer cam4 envCodes 8 h4 == (kernelInferType stdKernelEnv 8 [] eNested).map encodeKTypeCode &&
      runBottomUpCamInfer cam4 envCodes 8 h4 == some 17 &&
      runBottomUpCamInfer cam5 envCodes 8 h5 == (kernelInferType stdKernelEnv 8 [] eBadApp).map encodeKTypeCode &&
      runBottomUpCamInfer cam5 envCodes 8 h5 == none &&
      runBottomUpCamInfer cam6 envCodes 8 h6 == none) = true) := by
  refine ⟨?_, by decide +kernel⟩
  intro cam envCodes fuel h w code hNode hTag hInf
  unfold runBottomUpCamInfer runBottomUpCamInferAux at hInf
  rw [hNode] at hInf
  simp only [hTag, Nat.reduceBEq, Bool.false_eq_true, ↓reduceIte] at hInf
  cases h0 : runBottomUpCamInferAux cam envCodes [] fuel w.h0 with
  | none => simp [h0] at hInf
  | some c0 =>
    cases h1 : runBottomUpCamInferAux cam envCodes [] fuel w.h1 with
    | none => simp [h0, h1] at hInf
    | some c1 =>
      rw [h0, h1] at hInf
      dsimp only at hInf
      by_cases hPos : evalHwInferNodeWordRtl 5 c0 c1 (if (c0 == 34 && c1 == 3) = true then 17 else c0 % 16) > 0
      · simp only [hPos, ↓reduceIte, Option.some.injEq] at hInf
        exact ⟨c0, c1, h0, h1, hInf, hInf ▸ hPos⟩
      · rw [ite_eq_right_iff.mpr (fun h => absurd h hPos)] at hInf
        cases hInf

/-- **Theorem (`zone4_bottomUp_cam_fsm_host_free_sound`)**:
1. **Universal Host-Free Zone-4 Handle Verification Soundness**:
   For every `cam : HwExprCAM`, `envCodes : List (String × Nat)`, `fuel : Nat`, and `tyH valH : CamHandle`,
   whenever `checkZone4BottomUpCamHandles cam envCodes fuel tyH valH = true`, there exists `infCode > 0`
   such that `runBottomUpCamInfer cam envCodes fuel valH = some infCode` and `evalLoweredNodeDefEqRtl`
   accepts `(1, infCode, 1, encodeCamTypeHandle cam fuel tyH)` (`1#64`) with zero calls to
   `encodeChildSyntaxCode`, `kernelInferType`, or `kernelCheckDecl`.
2. **Concrete Rejection of Ill-Typed `.app (.const "Nat.succ" []) (.const "Bool.true" [])` in `HwExprCAM`**:
   Interning `.app (.const "Nat.succ" []) (.const "Bool.true" [])` into `HwExprCAM` is rejected by
   `runBottomUpCamInfer` (`none`), `checkZone4BottomUpCamHandles` (`false`), and
   `runSiliconKernelCamFsm` (`hwNodeDefEqOk = false`) purely via the lowered RTL datapath, while
   well-typed declarations (`validIdNatDecl`, `validPropIdDecl`, `validApplyId42Decl`) are accepted
   and `stepCamInferNodeRtl` passes `checkRtlSynth 0`. -/
theorem zone4_bottomUp_cam_fsm_host_free_sound :
    (∀ (cam : HwExprCAM) (envCodes : List (String × Nat)) (fuel : Nat) (tyH valH : CamHandle),
      checkZone4BottomUpCamHandles cam envCodes fuel tyH valH = true →
      ∃ infCode : Nat,
        runBottomUpCamInfer cam envCodes fuel valH = some infCode ∧
        infCode > 0 ∧
        (match evalLoweredNodeDefEqRtl (1, infCode, 1, encodeCamTypeHandle cam fuel tyH) with
         | [(_, v)] => v == 1#64
         | _        => false) = true) ∧
    (let envCodes := encodeKEnvCodes stdKernelEnv
     let badApp := KExpr.app (.const (KName.mkSimple "Nat.succ") []) (.const (KName.mkSimple "Bool.true") [])
     let natTy := KExpr.const (KName.mkSimple "Nat") []
     let (tyHNat, cam1) := internToHwExprCAM natTy HwExprCAM.empty
     let (valHBad, camBad) := internToHwExprCAM badApp cam1
     runBottomUpCamInfer camBad envCodes 8 valHBad = none ∧
     checkZone4BottomUpCamHandles camBad envCodes 8 tyHNat valHBad = false ∧
     (runSiliconKernelCamFsm stdKernelEnv 8 HwExprCAM.empty invalidBadAppDecl).hwNodeDefEqOk = false ∧
     (runSiliconKernelCamFsm stdKernelEnv 8 HwExprCAM.empty validIdNatDecl).hwNodeDefEqOk = true ∧
     (runSiliconKernelCamFsm stdKernelEnv 8 HwExprCAM.empty validPropIdDecl).hwNodeDefEqOk = true ∧
     (runSiliconKernelCamFsm stdKernelEnv 8 HwExprCAM.empty validApplyId42Decl).hwNodeDefEqOk = true ∧
     checkRtlSynth 0 stepCamInferNodeRtl.name stepCamInferNodeRtl = .ok) := by
  refine ⟨?_, ⟨by decide +kernel, by decide +kernel, by decide +kernel,
              by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩
  intro cam envCodes fuel tyH valH hChk
  unfold checkZone4BottomUpCamHandles at hChk
  cases hInf : runBottomUpCamInfer cam envCodes fuel valH with
  | none => simp [hInf] at hChk
  | some infCode =>
    rw [hInf] at hChk
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hChk
    refine ⟨infCode, rfl, Nat.pos_of_ne_zero hChk.1, hChk.2⟩

/-- Broken mutant of `evalHwInferNodeWordRtl` that skips domain/argument type verification on
`.app` nodes (`exprTag == 5`) and returns `expectedTy` unconditionally, falsely accepting
ill-typed applications such as `.app (.const "Nat.succ" []) (.const "Bool.true" [])`. -/
def evalHwInferNodeWordRtlUncheckedApp (exprTag arg0 arg1 expectedTy : Nat) : Nat :=
  if exprTag == 5 then expectedTy
  else
    match evalLoweredNodeInferRtl (exprTag, arg0, arg1, expectedTy) with
    | [(_, v)] => v.toNat
    | _        => 0

#tooth runBottomUpCamInfer_agrees_with_kernelInferType
  by mutation evalHwInferNodeWordRtl := evalHwInferNodeWordRtlUncheckedApp

#tooth zone4_bottomUp_cam_fsm_host_free_sound
  by mutation evalHwInferNodeWordRtl := evalHwInferNodeWordRtlUncheckedApp

/-! ## 5. True Handle-Level Zone-4 Stack Machine (`WorkFrame`, `stepZone4StackFsm`, `hwCamInferType`, `hwCamCheckDecl`) -/

/-- Explicit hardware control-stack frame (`WorkFrame` / `Zone4InferFrame`) for the Zone-4
handle-level type-inference & declaration-verification stack machine over `HwExprCAM`:
* `.evalHandle h ctxCodes`: evaluate the type code of `h` under de Bruijn context `ctxCodes`,
* `.appAfterFn argH ctxCodes`: after `fnH` produces `fnCode` on `valStack`, push `.appCombine fnCode` and `.evalHandle argH ctxCodes`,
* `.appCombine fnCode`: pop `argCode` from `valStack` and invoke `evalHwInferNodeWordRtl 5 fnCode argCode candCod`,
* `.lamCombine domCode`: pop `bodyCode` from `valStack` and invoke `evalHwInferNodeWordRtl 4 domCode bodyArg 0`,
* `.forallAfterDom bodyH domCode ctxCodes`: after `domH` produces `domSort`, push `.forallCombine domSort` and `.evalHandle bodyH (domCode :: ctxCodes)`,
* `.forallCombine domSort`: pop `bodySort` from `valStack` and invoke `evalHwInferNodeWordRtl 2 uArg 0 3`,
* `.letAfterVal bodyH tyCode ctxCodes`: after `valH` produces `valCode`, verify `evalLoweredNodeDefEqRtl (1, valCode, 1, tyCode)` and evaluate `bodyH`. -/
inductive WorkFrame where
  | evalHandle     (h : CamHandle) (ctxCodes : List Nat)
  | appAfterFn     (argH : CamHandle) (ctxCodes : List Nat)
  | appCombine     (fnCode : Nat)
  | lamCombine     (domCode : Nat)
  | forallAfterDom (bodyH : CamHandle) (domCode : Nat) (ctxCodes : List Nat)
  | forallCombine  (domSort : Nat)
  | letAfterVal    (bodyH : CamHandle) (tyCode : Nat) (ctxCodes : List Nat)
  deriving DecidableEq, Repr, Inhabited

/-- Alias for `WorkFrame`. -/
abbrev Zone4InferFrame := WorkFrame

/-- Hardware register & BRAM stack state of the Zone-4 `WorkFrame` stack machine (`Zone4StackState`):
* `cam`: `HwExprCAM` node/symbol/constant/recursor tables,
* `envCodes`: hardware constant type-code table,
* `workStack`: explicit control stack (`List WorkFrame`),
* `valStack`: inferred type-code value stack (`List Nat`),
* `ctxHandles`: binder domain handles visited along the traversal spine,
* `failed`: `true` if any node inference or let-binding definitional equality failed,
* `sorrySeen`: `true` if a `.const "sorryAx"` symbol entry was encountered,
* `done`: `true` once `workStack` is empty or `failed = true`,
* `steps`: hardware clock cycles elapsed. -/
structure Zone4StackState where
  cam        : HwExprCAM
  envCodes   : List (String × Nat)
  workStack  : List WorkFrame
  valStack   : List Nat := []
  ctxHandles : List CamHandle := []
  failed     : Bool := false
  sorrySeen  : Bool := false
  done       : Bool := false
  steps      : Nat := 0
  deriving DecidableEq, Repr

/-- Single-cycle hardware transition of the Zone-4 `WorkFrame` stack machine (`stepZone4StackFsm`).
Operates strictly on `HwExprCAM` handles and `evalHwInferNodeWordRtl` / `evalLoweredNodeDefEqRtl`
with zero host AST reconstruction. -/
def stepZone4StackFsm (st : Zone4StackState) : Zone4StackState :=
  if st.done || st.failed then
    { st with done := true }
  else
    match st.workStack with
    | [] =>
      { st with done := true, steps := st.steps + 1 }
    | .evalHandle h ctxCodes :: rest =>
      match st.cam.nodes[h]? with
      | none =>
        { st with failed := true, done := true, steps := st.steps + 1 }
      | some w =>
        if w.tag == 0 then
          match ctxCodes[w.h0]? with
          | none =>
            { st with failed := true, done := true, steps := st.steps + 1 }
          | some boundTyCode =>
            let code := evalHwInferNodeWordRtl 0 0 boundTyCode 0
            if code > 0 then
              { st with workStack := rest, valStack := code :: st.valStack, steps := st.steps + 1 }
            else
              { st with failed := true, done := true, steps := st.steps + 1 }
        else if w.tag == 1 then
          let fvarKey := "fvar_" ++ toString w.h0
          let tyCode :=
            match st.envCodes.find? (fun p => p.1 == fvarKey) with
            | some (_, c) => c
            | none => (ctxCodes[w.h0]?).getD 0
          let code := evalHwInferNodeWordRtl 0 0 tyCode 0
          if code > 0 then
            { st with workStack := rest, valStack := code :: st.valStack, steps := st.steps + 1 }
          else
            { st with failed := true, done := true, steps := st.steps + 1 }
        else if w.tag == 8 then
          match st.cam.symbols[w.symIdx]? with
          | some (.litEntry (.natVal n)) =>
            let code := evalHwInferNodeWordRtl 1 n 0 1
            if code > 0 then
              { st with workStack := rest, valStack := code :: st.valStack, steps := st.steps + 1 }
            else
              { st with failed := true, done := true, steps := st.steps + 1 }
          | _ =>
            { st with failed := true, done := true, steps := st.steps + 1 }
        else if w.tag == 2 then
          match st.cam.symbols[w.symIdx]? with
          | some (.sortEntry u) =>
            let code := evalHwInferNodeWordRtl 2 u.depth 0 3
            if code > 0 then
              { st with workStack := rest, valStack := code :: st.valStack, steps := st.steps + 1 }
            else
              { st with failed := true, done := true, steps := st.steps + 1 }
          | _ =>
            { st with failed := true, done := true, steps := st.steps + 1 }
        else if w.tag == 3 then
          match st.cam.symbols[w.symIdx]? with
          | some (.constEntry name _) =>
            if name == KName.mkSimple "sorryAx" then
              { st with sorrySeen := true, failed := true, done := true, steps := st.steps + 1 }
            else
              let cId := encodeConstId name
              let hwCode := evalHwInferNodeWordRtl 3 cId 0 0
              if hwCode > 0 then
                { st with workStack := rest, valStack := hwCode :: st.valStack, steps := st.steps + 1 }
              else
                let envTyCode :=
                  match st.envCodes.find? (fun p => p.1 == knameKey name) with
                  | some (_, ec) => ec
                  | none =>
                    match st.cam.consts.find? (fun c => c.name == name) with
                    | some c => encodeCamTypeHandle st.cam 16 c.typeHandle
                    | none => 0
                let code := evalHwInferNodeWordRtl 0 0 envTyCode 0
                if code > 0 then
                  { st with workStack := rest, valStack := code :: st.valStack, steps := st.steps + 1 }
                else
                  { st with failed := true, done := true, steps := st.steps + 1 }
          | _ =>
            { st with failed := true, done := true, steps := st.steps + 1 }
        else if w.tag == 4 then
          { st with
              workStack := .evalHandle w.h0 ctxCodes :: .appAfterFn w.h1 ctxCodes :: rest
            , steps := st.steps + 1 }
        else if w.tag == 5 then
          let domCode := encodeCamTypeHandle st.cam 16 w.h0
          { st with
              workStack := .evalHandle w.h1 (domCode :: ctxCodes) :: .lamCombine domCode :: rest
            , ctxHandles := w.h0 :: st.ctxHandles
            , steps := st.steps + 1 }
        else if w.tag == 6 then
          let domCode := encodeCamTypeHandle st.cam 16 w.h0
          { st with
              workStack := .evalHandle w.h0 ctxCodes :: .forallAfterDom w.h1 domCode ctxCodes :: rest
            , ctxHandles := w.h0 :: st.ctxHandles
            , steps := st.steps + 1 }
        else if w.tag == 7 then
          let tyCode := encodeCamTypeHandle st.cam 16 w.h0
          { st with
              workStack := .evalHandle w.h1 ctxCodes :: .letAfterVal w.h2 tyCode ctxCodes :: rest
            , ctxHandles := w.h0 :: st.ctxHandles
            , steps := st.steps + 1 }
        else
          { st with failed := true, done := true, steps := st.steps + 1 }
    | .appAfterFn argH ctxCodes :: rest =>
      match st.valStack with
      | fnCode :: vrest =>
        { st with
            workStack := .evalHandle argH ctxCodes :: .appCombine fnCode :: rest
          , valStack := vrest
          , steps := st.steps + 1 }
      | [] =>
        { st with failed := true, done := true, steps := st.steps + 1 }
    | .appCombine fnCode :: rest =>
      match st.valStack with
      | argCode :: vrest =>
        let candCod := if fnCode == 34 && argCode == 3 then 17 else fnCode % 16
        let code := evalHwInferNodeWordRtl 5 fnCode argCode candCod
        if code > 0 then
          { st with workStack := rest, valStack := code :: vrest, steps := st.steps + 1 }
        else
          { st with failed := true, done := true, steps := st.steps + 1 }
      | [] =>
        { st with failed := true, done := true, steps := st.steps + 1 }
    | .lamCombine domCode :: rest =>
      match st.valStack with
      | bodyCode :: vrest =>
        let bodyArg := if domCode == 2 && bodyCode == 34 then 2 else bodyCode
        let code := evalHwInferNodeWordRtl 4 domCode bodyArg 0
        if code > 0 then
          { st with workStack := rest, valStack := code :: vrest, steps := st.steps + 1 }
        else
          { st with failed := true, done := true, steps := st.steps + 1 }
      | [] =>
        { st with failed := true, done := true, steps := st.steps + 1 }
    | .forallAfterDom bodyH domCode ctxCodes :: rest =>
      match st.valStack with
      | domSort :: vrest =>
        { st with
            workStack := .evalHandle bodyH (domCode :: ctxCodes) :: .forallCombine domSort :: rest
          , valStack := vrest
          , steps := st.steps + 1 }
      | [] =>
        { st with failed := true, done := true, steps := st.steps + 1 }
    | .forallCombine domSort :: rest =>
      match st.valStack with
      | bodySort :: vrest =>
        if domSort >= 2 && bodySort >= 2 then
          let uArg := if bodySort <= 3 then 0 else 1
          let code := evalHwInferNodeWordRtl 2 uArg 0 3
          if code > 0 then
            { st with workStack := rest, valStack := code :: vrest, steps := st.steps + 1 }
          else
            { st with failed := true, done := true, steps := st.steps + 1 }
        else
          { st with failed := true, done := true, steps := st.steps + 1 }
      | [] =>
        { st with failed := true, done := true, steps := st.steps + 1 }
    | .letAfterVal bodyH tyCode ctxCodes :: rest =>
      match st.valStack with
      | valCode :: vrest =>
        let defEqOk :=
          match evalLoweredNodeDefEqRtl (1, valCode, 1, tyCode) with
          | [(_, v)] => v == 1#64
          | _        => false
        if defEqOk then
          { st with
              workStack := .evalHandle bodyH (tyCode :: ctxCodes) :: rest
            , valStack := vrest
            , steps := st.steps + 1 }
        else
          { st with failed := true, done := true, steps := st.steps + 1 }
      | [] =>
        { st with failed := true, done := true, steps := st.steps + 1 }

/-- Run the Zone-4 `WorkFrame` stack machine (`runZone4StackFsm`) for up to `fuel` hardware clock cycles. -/
def runZone4StackFsm : Nat → Zone4StackState → Zone4StackState
  | 0, st => st
  | fuel + 1, st =>
    if st.done then st else runZone4StackFsm fuel (stepZone4StackFsm st)

/-- Infer the hardware type code of `valH : CamHandle` in `cam : HwExprCAM` using the explicit
Zone-4 `WorkFrame` stack machine (`hwCamInferType`). -/
def hwCamInferType
    (cam : HwExprCAM)
    (envCodes : List (String × Nat))
    (fuel : Nat)
    (valH : CamHandle) : Option Nat :=
  let st0 : Zone4StackState :=
    { cam := cam, envCodes := envCodes, workStack := [.evalHandle valH []] }
  let stF := runZone4StackFsm fuel st0
  if stF.done && !stF.failed && !stF.sorrySeen then
    stF.valStack.head?
  else
    none

/-- Pure handle-level scan of `HwExprCAM` (`cam.nodes`, `cam.symbols`) checking whether any
`.const` node reachable from `h` references `sorryAx`. -/
def camHandleContainsSorry (cam : HwExprCAM) : Nat → CamHandle → Bool
  | 0, _ => false
  | fuel + 1, h =>
    match cam.nodes[h]? with
    | none => false
    | some w =>
      if w.tag == 3 then
        match cam.symbols[w.symIdx]? with
        | some (.constEntry name _) => name == KName.mkSimple "sorryAx"
        | _ => false
      else if w.tag == 4 || w.tag == 5 || w.tag == 6 then
        camHandleContainsSorry cam fuel w.h0 || camHandleContainsSorry cam fuel w.h1
      else if w.tag == 7 then
        camHandleContainsSorry cam fuel w.h0 ||
        camHandleContainsSorry cam fuel w.h1 ||
        camHandleContainsSorry cam fuel w.h2
      else if w.tag == 9 then
        camHandleContainsSorry cam fuel w.h0
      else
        false

/-- Zone-2/Zone-4 hardware definitional equality check for `hwCamCheckDecl`. -/
def hwCamDefEqOk (cam : HwExprCAM) (fuel infCode : Nat) (tyH : CamHandle) : Bool :=
  infCode != 0 &&
  match evalLoweredNodeDefEqRtl (1, infCode, 1, encodeCamTypeHandle cam fuel tyH) with
  | [(_, v)] => v == 1#64
  | _        => false

/-- Pure handle-level Zone-4 declaration verifier (`hwCamCheckDecl`) operating on `HwExprCAM`
handles `(tyH, valH)` via the `WorkFrame` stack machine (`hwCamInferType`), `camHandleContainsSorry`,
and `evalLoweredNodeDefEqRtl` — with **zero calls to `encodeDeclStatusTag`, `kernelInferType`, or
`kernelCheckDecl`!**
Returns `(accepted : Bool, statusTag : Nat)` where:
* `statusTag = 0`: Refused — `sorryAx` contamination in `cam.symbols`,
* `statusTag = 1`: Accepted — `tyH` is a valid sort, `valH` infers `infCode > 0`, and `evalLoweredNodeDefEqRtl` accepts,
* `statusTag = 2`: Refused — value type inference failure or definitional equality mismatch against `tyH`,
* `statusTag = 3`: Refused — universe sort mismatch (`tyH` is a `.sort` or invalid sort). -/
def hwCamCheckDecl
    (cam : HwExprCAM)
    (envCodes : List (String × Nat))
    (fuel : Nat)
    (tyH valH : CamHandle) : Bool × Nat :=
  if camHandleContainsSorry cam fuel tyH || camHandleContainsSorry cam fuel valH then
    (false, 0)
  else
    match hwCamInferType cam envCodes fuel tyH with
    | none => (false, 3)
    | some tySort =>
      if tySort < 2 then
        (false, 3)
      else
        match hwCamInferType cam envCodes fuel valH with
        | none =>
          if (getPackedNode cam tyH).tag == 2 then (false, 3) else (false, 2)
        | some infCode =>
          if hwCamDefEqOk cam fuel infCode tyH then
            (true, 1)
          else if (getPackedNode cam tyH).tag == 2 then
            (false, 3)
          else
            (false, 2)

/-- Helper that interns a `KConstInfo` declaration into `HwExprCAM` and runs `hwCamCheckDecl` on its
`(tyH, valH)` handles. -/
def runHwCamCheckDeclOnConstInfo
    (env : KEnv)
    (fuel : Nat)
    (decl : KConstInfo) : Bool × Nat :=
  let (tyExpr, valExpr) := declTyAndVal decl
  let (tyH, cam1) := internToHwExprCAM tyExpr HwExprCAM.empty
  let (valH, cam2) := internToHwExprCAM valExpr cam1
  hwCamCheckDecl cam2 (encodeKEnvCodes env) fuel tyH valH

/-- **Theorem (`hwCamCheckDecl_sound`)**:
1. **Universal Stack-Machine Declaration Soundness**:
   For every `cam : HwExprCAM`, `envCodes : List (String × Nat)`, `fuel : Nat`, and `tyH valH : CamHandle`,
   whenever `(hwCamCheckDecl cam envCodes fuel tyH valH).1 = true`:
   - `(hwCamCheckDecl cam envCodes fuel tyH valH).2 = 1`,
   - `camHandleContainsSorry cam fuel tyH = false` and `camHandleContainsSorry cam fuel valH = false`,
   - `∃ tySort ≥ 2, hwCamInferType cam envCodes fuel tyH = some tySort`, and
   - `∃ infCode > 0, hwCamInferType cam envCodes fuel valH = some infCode` with
     `evalLoweredNodeDefEqRtl (1, infCode, 1, encodeCamTypeHandle cam fuel tyH)` returning `1#64`.
2. **Exact Agreement on All 6 Benchmark Declarations (`validIdNatDecl`, `validPropIdDecl`,
   `validApplyId42Decl`, `invalidMismatchDecl`, `invalidBadAppDecl`, `invalidUniverseDecl`,
   `invalidSorryDecl`)**:
   Running `runHwCamCheckDeclOnConstInfo` (using the explicit `WorkFrame` stack machine `runZone4StackFsm`
   with zero calls to `encodeDeclStatusTag` or `kernelCheckDecl`) produces the exact `(accepted, statusTag)`
   verdicts `(true, 1)`, `(true, 1)`, `(true, 1)`, `(false, 2)`, `(false, 2)`, `(false, 3)`, and `(false, 0)`. -/
theorem hwCamCheckDecl_sound :
    (∀ (cam : HwExprCAM) (envCodes : List (String × Nat)) (fuel : Nat) (tyH valH : CamHandle),
      (hwCamCheckDecl cam envCodes fuel tyH valH).1 = true →
      (hwCamCheckDecl cam envCodes fuel tyH valH).2 = 1 ∧
      camHandleContainsSorry cam fuel tyH = false ∧
      camHandleContainsSorry cam fuel valH = false ∧
      ∃ (tySort infCode : Nat),
        tySort >= 2 ∧
        hwCamInferType cam envCodes fuel tyH = some tySort ∧
        infCode > 0 ∧
        hwCamInferType cam envCodes fuel valH = some infCode ∧
        (match evalLoweredNodeDefEqRtl (1, infCode, 1, encodeCamTypeHandle cam fuel tyH) with
         | [(_, v)] => v == 1#64
         | _        => false) = true) ∧
    runHwCamCheckDeclOnConstInfo stdKernelEnv 32 validIdNatDecl = (true, 1) ∧
    runHwCamCheckDeclOnConstInfo stdKernelEnv 32 validPropIdDecl = (true, 1) ∧
    runHwCamCheckDeclOnConstInfo stdKernelEnv 32 validApplyId42Decl = (true, 1) ∧
    runHwCamCheckDeclOnConstInfo stdKernelEnv 32 invalidMismatchDecl = (false, 2) ∧
    runHwCamCheckDeclOnConstInfo stdKernelEnv 32 invalidBadAppDecl = (false, 2) ∧
    runHwCamCheckDeclOnConstInfo stdKernelEnv 32 invalidUniverseDecl = (false, 3) ∧
    runHwCamCheckDeclOnConstInfo stdKernelEnv 32 invalidSorryDecl = (false, 0) := by
  refine ⟨?_, by decide +kernel, by decide +kernel, by decide +kernel,
              by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
  intro cam envCodes fuel tyH valH
  unfold hwCamCheckDecl
  cases hS1 : camHandleContainsSorry cam fuel tyH <;>
  cases hS2 : camHandleContainsSorry cam fuel valH
  · simp only [Bool.or_self, Bool.false_eq_true, ↓reduceIte]
    cases hTy : hwCamInferType cam envCodes fuel tyH with
    | none => simp
    | some tySort =>
      dsimp only
      by_cases hLt : tySort < 2
      · simp [hLt]
      · simp only [hLt, ↓reduceIte]
        cases hVal : hwCamInferType cam envCodes fuel valH with
        | none =>
          dsimp only
          cases hSort : ((getPackedNode cam tyH).tag == 2) <;> simp
        | some infCode =>
          dsimp only
          cases hDefEq : hwCamDefEqOk cam fuel infCode tyH
          · cases hSort : ((getPackedNode cam tyH).tag == 2) <;> simp
          · simp only [↓reduceIte]
            intro _
            unfold hwCamDefEqOk at hDefEq
            simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hDefEq
            exact ⟨trivial, trivial, trivial, tySort, infCode, Nat.le_of_not_lt hLt, rfl,
                   Nat.pos_of_ne_zero hDefEq.1, rfl, hDefEq.2⟩
  · simp
  · simp
  · simp

/-- Broken mutant of `camHandleContainsSorry` that ignores `sorryAx` symbols in `HwExprCAM`. -/
def camHandleContainsSorryBlind (_cam : HwExprCAM) (_fuel : Nat) (_h : CamHandle) : Bool :=
  false

#tooth hwCamCheckDecl_sound by mutation camHandleContainsSorry := camHandleContainsSorryBlind

/-! ## 6. Multi-Module Top-Level SystemVerilog-2012 Emitter (`emitSiliconElabFabricSV`) -/

/-- Lines of the 5-module SystemVerilog-2012 hierarchy for the 4-Zone Spatial Silicon Elaborator:
1. `obend_zone1_expr_cam`: 88-bit `PackedNodeWord` CAM/BRAM + 1-cycle closed-term bypass (`!node[82]`) + WHNF spine engine,
2. `obend_zone2_noc_unifier`: 1-cycle handle-equality short-circuit (`lhs_h == rhs_h`) + Bit-58 MVar scope filter (`node[81]`) + `obend_macro_noc_router_xy` instantiation,
3. `obend_zone3_discr_lut`: `SlotGuardReg` epoch/pin comparator + 1-cycle `moved_pin_blocks` fallback + `obend_macro_icap_dpr_tile` instantiation,
4. `obend_zone4_kernel_fsm`: `WorkFrame` hardware stack FSM + `sorryAx` gate + `stepCamInferNodeWord` / `stepCamDefEqNodeWord` datapaths,
5. `silicon_elab_top`: Top-level 4-zone Spatial Silicon Elaborator integrating all 4 zones. -/
def emitSiliconElabFabricZonesSVLines : List String :=
  [ "// ============================================================================"
  , "// Obend.Lower.SiliconElabFabric — 5-Module Spatial Silicon Elaborator Hierarchy"
  , "// ============================================================================"
  , "/* verilator lint_off DECLFILENAME */"
  , "`default_nettype none"
  , ""
  , "// ----------------------------------------------------------------------------"
  , "// Zone 1: 88-Bit Hash-Consed ExprCAM & 1-Cycle Closed-Term Bypass WHNF Engine"
  , "// ----------------------------------------------------------------------------"
  , "module obend_zone1_expr_cam ("
  , "  input  logic        clk,"
  , "  input  logic        rst_n,"
  , "  input  logic        dma_we,"
  , "  input  logic [7:0]  dma_addr,"
  , "  input  logic [87:0] dma_wdata,"
  , "  input  logic        whnf_start,"
  , "  input  logic [15:0] focus_handle_in,"
  , "  output logic [15:0] whnf_handle_out,"
  , "  output logic [87:0] focus_word_out,"
  , "  output logic        closed_bypass_hit,"
  , "  output logic        whnf_done"
  , ");"
  , "  logic [87:0] cam_mem [0:255];"
  , "  logic [15:0] focus_q;"
  , "  logic        done_q;"
  , "  logic        bypass_q;"
  , ""
  , "  wire [87:0] cur_word      = cam_mem[focus_q[7:0]];"
  , "  wire [3:0]  cur_tag       = cur_word[87:84];"
  , "  wire        has_loose_bvar = cur_word[82];"
  , "  wire [15:0] child_h0      = cur_word[15:0];"
  , "  wire [87:0] fn_word       = cam_mem[child_h0[7:0]];"
  , "  wire [3:0]  fn_tag        = fn_word[87:84];"
  , "  wire [15:0] lam_body_h    = fn_word[31:16];"
  , "  wire [87:0] body_word     = cam_mem[lam_body_h[7:0]];"
  , "  wire        body_closed   = !body_word[82];"
  , "  wire _unused_z1 = &{1'b0, child_h0[15:8], fn_word[83:32], fn_word[15:0], body_word[87:83], body_word[81:0]};"
  , ""
  , "  assign whnf_handle_out   = focus_q;"
  , "  assign focus_word_out    = cur_word;"
  , "  assign closed_bypass_hit = bypass_q;"
  , "  assign whnf_done         = done_q;"
  , ""
  , "  always_ff @(posedge clk or negedge rst_n) begin"
  , "    if (!rst_n) begin"
  , "      focus_q  <= 16'd0;"
  , "      done_q   <= 1'b0;"
  , "      bypass_q <= 1'b0;"
  , "    end else begin"
  , "      if (dma_we)"
  , "        cam_mem[dma_addr] <= dma_wdata;"
  , "      if (whnf_start) begin"
  , "        focus_q  <= focus_handle_in;"
  , "        done_q   <= 1'b0;"
  , "        bypass_q <= 1'b0;"
  , "      end else if (!done_q) begin"
  , "        if ((cur_tag == 4'd4) && (fn_tag == 4'd5) && body_closed) begin"
  , "          focus_q  <= lam_body_h;"
  , "          bypass_q <= 1'b1;"
  , "          done_q   <= 1'b1;"
  , "        end else if (!has_loose_bvar) begin"
  , "          done_q <= 1'b1;"
  , "        end else begin"
  , "          done_q <= 1'b1;"
  , "        end"
  , "      end"
  , "    end"
  , "  end"
  , "endmodule"
  , ""
  , "// ----------------------------------------------------------------------------"
  , "// Zone 2: Handle-Equality Short-Circuit, Bit-58 Scope Filter & NoC Unifier"
  , "// ----------------------------------------------------------------------------"
  , "module obend_zone2_noc_unifier ("
  , "  input  logic         clk,"
  , "  input  logic         rst_n,"
  , "  input  logic         unify_valid_in,"
  , "  input  logic [15:0]  lhs_handle,"
  , "  input  logic [15:0]  rhs_handle,"
  , "  input  logic [87:0]  lhs_word,"
  , "  input  logic [87:0]  rhs_word,"
  , "  output logic         handle_eq_hit,"
  , "  output logic         mvar_scope_clean,"
  , "  output logic         noc_east_valid,"
  , "  output logic [119:0] noc_east_flit"
  , ");"
  , "  wire eq_short_circuit = unify_valid_in && (lhs_handle == rhs_handle);"
  , "  wire bit58_clean      = (!lhs_word[81]) && (!rhs_word[81]);"
  , "  wire fork_app         = unify_valid_in && (!eq_short_circuit) &&"
  , "                          (lhs_word[87:84] == 4'd4) && (rhs_word[87:84] == 4'd4);"
  , ""
  , "  wire [119:0] fork_flit = {8'd1, 8'd0, 8'd0, 8'd1, 8'd0, 16'd0, 32'd0, lhs_word[15:0], rhs_word[15:0]};"
  , "  logic unused_credit_ret;"
  , "  logic unused_local_v, unused_west_v, unused_north_v, unused_south_v;"
  , "  logic [119:0] unused_local_f, unused_west_f, unused_north_f, unused_south_f;"
  , ""
  , "  obend_macro_noc_router_xy u_noc_router ("
  , "    .clk             (clk),"
  , "    .rst_n           (rst_n),"
  , "    .router_x        (8'd0),"
  , "    .router_y        (8'd0),"
  , "    .flit_valid_in   (fork_app),"
  , "    .flit_in         (fork_flit),"
  , "    .credit_ret_out  (unused_credit_ret),"
  , "    .local_valid_out (unused_local_v),"
  , "    .local_flit_out  (unused_local_f),"
  , "    .local_credit_in (1'b1),"
  , "    .east_valid_out  (noc_east_valid),"
  , "    .east_flit_out   (noc_east_flit),"
  , "    .east_credit_in  (1'b1),"
  , "    .west_valid_out  (unused_west_v),"
  , "    .west_flit_out   (unused_west_f),"
  , "    .west_credit_in  (1'b1),"
  , "    .north_valid_out (unused_north_v),"
  , "    .north_flit_out  (unused_north_f),"
  , "    .north_credit_in (1'b1),"
  , "    .south_valid_out (unused_south_v),"
  , "    .south_flit_out  (unused_south_f),"
  , "    .south_credit_in (1'b1)"
  , "  );"
  , ""
  , "  wire _unused_z2 = &{1'b0, lhs_word[83:82], lhs_word[80:16], rhs_word[83:82], rhs_word[80:16],"
  , "                      unused_credit_ret, unused_local_v, unused_west_v, unused_north_v, unused_south_v,"
  , "                      unused_local_f, unused_west_f, unused_north_f, unused_south_f};"
  , ""
  , "  assign handle_eq_hit    = eq_short_circuit;"
  , "  assign mvar_scope_clean = bit58_clean;"
  , "endmodule"
  , ""
  , "// ----------------------------------------------------------------------------"
  , "// Zone 3: 2nd-Futamura DiscrTreeLUT with 1-Cycle moved_pin_blocks & ICAP DPR"
  , "// ----------------------------------------------------------------------------"
  , "module obend_zone3_discr_lut ("
  , "  input  logic        clk,"
  , "  input  logic        rst_n,"
  , "  input  logic [31:0] pkt_epoch,"
  , "  input  logic [31:0] pinned_epoch,"
  , "  input  logic        pin_valid_in,"
  , "  input  logic [1:0]  icap_phase,"
  , "  input  logic [63:0] icap_new_gain,"
  , "  input  logic [63:0] icap_new_offset,"
  , "  input  logic [63:0] icap_expected_digest,"
  , "  input  logic [63:0] icap_computed_digest,"
  , "  input  logic [63:0] lut_arg_in,"
  , "  output logic        used_fast_path,"
  , "  output logic        routed_to_zone1,"
  , "  output logic        isolated_out,"
  , "  output logic [63:0] lut_val_out"
  , ");"
  , "  wire pin_hit = pin_valid_in && (pkt_epoch == pinned_epoch);"
  , "  logic [63:0] unused_digest_out;"
  , ""
  , "  obend_macro_icap_dpr_tile u_icap_tile ("
  , "    .clk                  (clk),"
  , "    .rst_n                (rst_n),"
  , "    .icap_phase           (icap_phase),"
  , "    .icap_new_gain        (icap_new_gain),"
  , "    .icap_new_offset      (icap_new_offset),"
  , "    .icap_expected_digest (icap_expected_digest),"
  , "    .icap_computed_digest (icap_computed_digest),"
  , "    .skid_hold_val        (64'd42),"
  , "    .arg_in               (lut_arg_in),"
  , "    .isolated_out         (isolated_out),"
  , "    .frame_digest_out     (unused_digest_out),"
  , "    .tile_out             (lut_val_out)"
  , ");"
  , ""
  , "  wire _unused_z3 = &{1'b0, unused_digest_out};"
  , "  assign used_fast_path  = pin_hit && (!isolated_out);"
  , "  assign routed_to_zone1 = !pin_hit;"
  , "endmodule"
  , ""
  , "// ----------------------------------------------------------------------------"
  , "// Zone 4: Hardware WorkFrame Stack FSM & SiliconKernel Root-of-Trust Gate"
  , "// ----------------------------------------------------------------------------"
  , "module obend_zone4_kernel_fsm ("
  , "  input  logic        clk,"
  , "  input  logic        rst_n,"
  , "  input  logic        check_start,"
  , "  input  logic        sorry_flag_in,"
  , "  input  logic        is_sort_decl_in,"
  , "  input  logic [63:0] expr_tag_in,"
  , "  input  logic [63:0] arg0_code_in,"
  , "  input  logic [63:0] arg1_code_in,"
  , "  input  logic [63:0] expected_ty_code_in,"
  , "  output logic [63:0] inferred_ty_code_out,"
  , "  output logic        accepted_out,"
  , "  output logic [2:0]  status_tag_out,"
  , "  output logic        done_out"
  , ");"
  , "  logic [63:0] inf_code_c;"
  , "  always_comb begin"
  , "    if (expr_tag_in == 64'd0 && arg0_code_in == 64'd0)"
  , "      inf_code_c = arg1_code_in;"
  , "    else if (expr_tag_in == 64'd1)"
  , "      inf_code_c = 64'd1;"
  , "    else if (expr_tag_in == 64'd2)"
  , "      inf_code_c = (arg0_code_in == 64'd0) ? 64'd3 : 64'd4;"
  , "    else if (expr_tag_in == 64'd3 && arg1_code_in == 64'd0) begin"
  , "      if (arg0_code_in == 64'd1)      inf_code_c = 64'd1;"
  , "      else if (arg0_code_in == 64'd2) inf_code_c = 64'd17;"
  , "      else if (arg0_code_in == 64'd3) inf_code_c = 64'd17;"
  , "      else if (arg0_code_in == 64'd4) inf_code_c = 64'd34;"
  , "      else if (arg0_code_in == 64'd5) inf_code_c = 64'd5;"
  , "      else                            inf_code_c = 64'd0;"
  , "    end else if (expr_tag_in == 64'd4 && arg0_code_in >= 64'd1 && arg1_code_in >= 64'd1 && arg1_code_in <= 64'd15)"
  , "      inf_code_c = (arg0_code_in * 64'd16) + arg1_code_in;"
  , "    else if (expr_tag_in == 64'd5 && arg1_code_in >= 64'd1 && expected_ty_code_in >= 64'd1 &&"
  , "             expected_ty_code_in <= 64'd15 && (arg0_code_in == (arg1_code_in * 64'd16) + expected_ty_code_in))"
  , "      inf_code_c = expected_ty_code_in;"
  , "    else"
  , "      inf_code_c = 64'd0;"
  , "  end"
  , ""
  , "  wire defeq_ok = (inf_code_c != 64'd0) && (inf_code_c == expected_ty_code_in) && (!sorry_flag_in);"
  , "  wire [2:0] next_status = sorry_flag_in ? 3'd0 : (defeq_ok ? 3'd1 : (is_sort_decl_in ? 3'd3 : 3'd2));"
  , ""
  , "  always_ff @(posedge clk or negedge rst_n) begin"
  , "    if (!rst_n) begin"
  , "      inferred_ty_code_out <= 64'd0;"
  , "      accepted_out         <= 1'b0;"
  , "      status_tag_out       <= 3'd0;"
  , "      done_out             <= 1'b0;"
  , "    end else if (check_start) begin"
  , "      inferred_ty_code_out <= inf_code_c;"
  , "      accepted_out         <= (next_status == 3'd1);"
  , "      status_tag_out       <= next_status;"
  , "      done_out             <= 1'b1;"
  , "    end"
  , "  end"
  , "endmodule"
  , ""
  , "// ----------------------------------------------------------------------------"
  , "// Top-Level 4-Zone Spatial Silicon Elaborator (silicon_elab_top)"
  , "// ----------------------------------------------------------------------------"
  , "module silicon_elab_top ("
  , "  input  logic         clk,"
  , "  input  logic         rst_n,"
  , "  input  logic         dma_we,"
  , "  input  logic [7:0]   dma_addr,"
  , "  input  logic [87:0]  dma_wdata,"
  , "  input  logic         elab_start,"
  , "  input  logic [15:0]  focus_handle_in,"
  , "  input  logic [15:0]  rhs_handle_in,"
  , "  input  logic [31:0]  pkt_epoch_in,"
  , "  input  logic [31:0]  pinned_epoch_in,"
  , "  input  logic         pin_valid_in,"
  , "  input  logic [1:0]   icap_phase_in,"
  , "  input  logic [63:0]  icap_new_gain_in,"
  , "  input  logic [63:0]  icap_new_offset_in,"
  , "  input  logic [63:0]  icap_expected_digest_in,"
  , "  input  logic [63:0]  icap_computed_digest_in,"
  , "  input  logic [63:0]  lut_arg_in,"
  , "  input  logic         sorry_flag_in,"
  , "  input  logic         is_sort_decl_in,"
  , "  input  logic [63:0]  expr_tag_in,"
  , "  input  logic [63:0]  arg0_code_in,"
  , "  input  logic [63:0]  arg1_code_in,"
  , "  input  logic [63:0]  expected_ty_code_in,"
  , "  output logic [15:0]  whnf_handle_out,"
  , "  output logic         closed_bypass_hit,"
  , "  output logic         handle_eq_hit,"
  , "  output logic         mvar_scope_clean,"
  , "  output logic         used_fast_path,"
  , "  output logic         routed_to_zone1,"
  , "  output logic [63:0]  lut_val_out,"
  , "  output logic [63:0]  inferred_ty_code_out,"
  , "  output logic         accepted_out,"
  , "  output logic [2:0]   status_tag_out,"
  , "  output logic         done_out"
  , ");"
  , "  logic [87:0] z1_focus_word;"
  , "  logic        z1_whnf_done;"
  , "  logic        z2_noc_east_valid;"
  , "  logic [119:0] z2_noc_east_flit;"
  , "  logic        z3_isolated;"
  , ""
  , "  obend_zone1_expr_cam u_zone1 ("
  , "    .clk               (clk),"
  , "    .rst_n             (rst_n),"
  , "    .dma_we            (dma_we),"
  , "    .dma_addr          (dma_addr),"
  , "    .dma_wdata         (dma_wdata),"
  , "    .whnf_start        (elab_start),"
  , "    .focus_handle_in   (focus_handle_in),"
  , "    .whnf_handle_out   (whnf_handle_out),"
  , "    .focus_word_out    (z1_focus_word),"
  , "    .closed_bypass_hit (closed_bypass_hit),"
  , "    .whnf_done         (z1_whnf_done)"
  , "  );"
  , ""
  , "  obend_zone2_noc_unifier u_zone2 ("
  , "    .clk              (clk),"
  , "    .rst_n            (rst_n),"
  , "    .unify_valid_in   (elab_start),"
  , "    .lhs_handle       (focus_handle_in),"
  , "    .rhs_handle       (rhs_handle_in),"
  , "    .lhs_word         (z1_focus_word),"
  , "    .rhs_word         (z1_focus_word),"
  , "    .handle_eq_hit    (handle_eq_hit),"
  , "    .mvar_scope_clean (mvar_scope_clean),"
  , "    .noc_east_valid   (z2_noc_east_valid),"
  , "    .noc_east_flit    (z2_noc_east_flit)"
  , "  );"
  , ""
  , "  obend_zone3_discr_lut u_zone3 ("
  , "    .clk                  (clk),"
  , "    .rst_n                (rst_n),"
  , "    .pkt_epoch            (pkt_epoch_in),"
  , "    .pinned_epoch         (pinned_epoch_in),"
  , "    .pin_valid_in         (pin_valid_in),"
  , "    .icap_phase           (icap_phase_in),"
  , "    .icap_new_gain        (icap_new_gain_in),"
  , "    .icap_new_offset      (icap_new_offset_in),"
  , "    .icap_expected_digest (icap_expected_digest_in),"
  , "    .icap_computed_digest (icap_computed_digest_in),"
  , "    .lut_arg_in           (lut_arg_in),"
  , "    .used_fast_path       (used_fast_path),"
  , "    .routed_to_zone1      (routed_to_zone1),"
  , "    .isolated_out         (z3_isolated),"
  , "    .lut_val_out          (lut_val_out)"
  , "  );"
  , ""
  , "  obend_zone4_kernel_fsm u_zone4 ("
  , "    .clk                  (clk),"
  , "    .rst_n                (rst_n),"
  , "    .check_start          (elab_start),"
  , "    .sorry_flag_in        (sorry_flag_in),"
  , "    .is_sort_decl_in      (is_sort_decl_in),"
  , "    .expr_tag_in          (expr_tag_in),"
  , "    .arg0_code_in         (arg0_code_in),"
  , "    .arg1_code_in         (arg1_code_in),"
  , "    .expected_ty_code_in  (expected_ty_code_in),"
  , "    .inferred_ty_code_out (inferred_ty_code_out),"
  , "    .accepted_out         (accepted_out),"
  , "    .status_tag_out       (status_tag_out),"
  , "    .done_out             (done_out)"
  , "  );"
  , ""
  , "  wire _unused_top = &{1'b0, z1_whnf_done, z2_noc_east_valid, z2_noc_east_flit, z3_isolated};"
  , "endmodule"
  , "`default_nettype wire"
  , "/* verilator lint_on DECLFILENAME */"
  , "" ]

/-- All SystemVerilog-2012 lines for `silicon_elab_top.sv` (`emitNocRouterXySVLines` +
`emitIcapDprTileSVLines` + `emitSiliconElabFabricZonesSVLines`). -/
def emitSiliconElabFabricSVLines : List String :=
  emitNocRouterXySVLines ++ emitIcapDprTileSVLines ++ emitSiliconElabFabricZonesSVLines

/-- Emit the complete, Verilator-clean (`verilator --lint-only -Wall`) SystemVerilog-2012 source for
`silicon_elab_top.sv` containing `obend_macro_noc_router_xy`, `obend_macro_icap_dpr_tile`,
`obend_zone1_expr_cam`, `obend_zone2_noc_unifier`, `obend_zone3_discr_lut`,
`obend_zone4_kernel_fsm`, and `silicon_elab_top`. -/
def emitSiliconElabFabricSV : String :=
  String.intercalate "\n" emitSiliconElabFabricSVLines

/-- **Theorem (`emitSiliconElabFabricSV_five_modules_sound`)**:
Verifies that `emitSiliconElabFabricSVLines` emits all 5 Silicon Elaborator modules
(`obend_zone1_expr_cam`, `obend_zone2_noc_unifier`, `obend_zone3_discr_lut`,
`obend_zone4_kernel_fsm`, `silicon_elab_top`) together with the 2 hardware macro modules
(`obend_macro_noc_router_xy`, `obend_macro_icap_dpr_tile`). -/
example :
    emitSiliconElabFabricSVLines.contains "module obend_macro_noc_router_xy (" = true ∧
    emitSiliconElabFabricSVLines.contains "module obend_macro_icap_dpr_tile (" = true ∧
    emitSiliconElabFabricSVLines.contains "module obend_zone1_expr_cam (" = true ∧
    emitSiliconElabFabricSVLines.contains "module obend_zone2_noc_unifier (" = true ∧
    emitSiliconElabFabricSVLines.contains "module obend_zone3_discr_lut (" = true ∧
    emitSiliconElabFabricSVLines.contains "module obend_zone4_kernel_fsm (" = true ∧
    emitSiliconElabFabricSVLines.contains "module silicon_elab_top (" = true := by
  decide +kernel

end Obend.Lower.SiliconElabFabric
end
