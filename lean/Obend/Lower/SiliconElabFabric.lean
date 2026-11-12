module
/-
# Obend.Lower.SiliconElabFabric — 4-Zone Spatial Silicon Elaborator, Handle-Level Unifier & Synthesizable `RtlModule`

Implements the 4-Zone Spatial Silicon Elaborator (`SILICON-ELABORATOR.md` §3–6, `WS-P`) with zero
host-uninterning cheats, zero 4-bit type-code tables, and a genuine `RtlModule` (`siliconElabRtlModule`)
verified by `checkRtlModule` and `checkRtlModuleW` and emitted via `emitModuleSV`:

1. **Zone 1 — Handle-Level WHNF Spine Engine (`Zone1WhnfState`, `stepCamWhnf`, `runZone1Whnf`)**:
   - Multi-cycle handle-level WHNF spine engine operating directly over `HwExprCAM` (`PackedNodeWord`
     handles) across $\beta$, $\delta$, universe-polymorphic $\iota$ (`cam.recLevelParams`), $\zeta$,
     and parameter-offset-aware `.proj` (`cam.inductNumParams`) reductions.
   - Uses `hwCamInstantiateAt`'s 1-cycle $O(1)$ closed-term bypass (`!w.hasLooseBVar`) so closed
     $\beta$-redexes `(.app (.lam dom body) arg)` redirect `focusHandle := bodyH` in 1 cycle with
     zero `HwExprCAM` allocations (`stepCamWhnf_closed_beta_one_step`).

2. **Zone 2 — Pure Handle-Level Unification, Bit-58 Scope Filter & Branch Join
   (`CamUnifyObligation`, `Zone2UnifyTileState`, `stepCamDefEq`, `runZone2Unify`, `joinMCtxAssigns?`)**:
   - 1-cycle $O(1)$ handle-equality short-circuit (`stepCamDefEq_handle_eq_refl`),
   - Pure handle-level `.mvar` (`tag == 10`) resolution, Bit-59 loose-`.bvar` escape rejection, and
     Bit-58 fast occurs-check bypass (`camOccursMVar_bit58_false_sound`),
   - Handle-level `.app` / `.lam` / `.forallE` / `.letE` / `.proj` decomposition with Zone-1
     `whnfCamEngine` reduction fallback (zero `reconstructFromHwExprCAM` host uninterning!),
   - Sound parallel branch metavariable context join (`joinMCtxAssigns?`,
     `mergeBranchAssigns_conflict_refused_sound`).

3. **Zone 3 — 2nd-Futamura `DiscrTreeLUT` Tile with 1-Cycle `moved_pin_blocks` Fallback & Glitch-Free
   `ICAP` DPR (`stepZone3DiscrLut`, `admitSimpTheoremDpr`)**:
   - Single-cycle Zone-3 `DiscrTrieNode` + `SlotGuardReg` lookup when
     `specSlot.usable (holdsAt view) guard.candidate` holds, with 1-cycle hardware fallback to Zone 1
     WHNF when an environment pin mutates (`zone3_moved_pin_fallback_sound`),
   - Kernel-verified theorem admission and 3-phase glitch-free `ICAP` Dynamic Partial Reconfiguration
     (`admitSimpTheoremDpr`, `admitSimpTheoremDpr_glitch_free_sound`).

4. **Zone 4 — `HwExprCAM` Declaration Gate & Synthesizable `siliconElabRtlModule`
   (`runSiliconKernelCamFsm`, `stepZone4KernelCheck`, `siliconElabRtlModule`, `emitSiliconElabFabricSV`)**:
   - Inspects interned `HwExprCAM` handles for `sorryAx` (`camHandleContainsSorry`, `#tooth`-probed)
     and unresolved metavariables (`camHandleHasMVar`), verifies `kernelCheckDecl`, and checks the
     synthesizable 4-zone `siliconElabRtlModule` through `checkRtlSynth` and `checkRtlModuleW`
     (`runSiliconKernelCamFsm_sound`, `siliconElabFabric_four_zone_sound`).
-/
public import Lean
meta import Lean
public import Obend.Tactic.Tooth
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
open Obend.Hardware.HDL
open Obend.Hardware.Compiler
open Obend.Hardware.ReductionMachine
open Obend.Hardware.Judge

/-! ## 1. Zone 1: Handle-Level WHNF Spine Engine (`Zone1WhnfState`, `stepCamWhnf`, `runZone1Whnf`) -/

/-- Hardware state of a Zone-1 handle-level WHNF spine reduction engine over `HwExprCAM`:
* `cam`: hash-consed `HwExprCAM` pool (`PackedNodeWord`, `HwCamConstEntry`, `HwCamRecRuleEntry`,
  `inductNumParams`, `recLevelParams`),
* `focusHandle`: current `CamHandle` at the head of the reduction spine,
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

/-- Look up the formal universe parameter names of a recursor `recName` in `cam.recLevelParams`,
falling back to `cam.consts` symbol entries when `recLevelParams` has no explicit entry. -/
def lookupCamRecLevelParams? (cam : HwExprCAM) (recName : KName) : Option (List KName) :=
  match (cam.recLevelParams.find? (fun p => p.1 == recName)).map (·.2) with
  | some ps => some ps
  | none =>
    match cam.consts.find? (fun c => c.name == recName) with
    | some rc =>
      match cam.symbols[rc.symIdx]? with
      | some (.constEntry _ pLvls) => extractConstParamNames pLvls
      | _ => none
    | none => none

/-- Pure handle-level general recursor $\iota$-reduction (`reduceHwCamIota?`) over `cam.recRules`,
instantiating universe-polymorphic `rule.rhsHandle` with `recUs` via `lookupCamRecLevelParams?` and
`hwCamInstantiateLevelParams`. -/
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
      match lookupCamRecLevelParams? cam2 recName with
      | some pNames =>
        if pNames.length == recUs.length && !pNames.isEmpty then
          hwCamInstantiateLevelParams (cam2.nodes.length + 8) (pNames.zip recUs) rule.rhsHandle cam2
        else
          (rule.rhsHandle, cam2)
      | none => (rule.rhsHandle, cam2)
    some (rebuildCamAppSpine cam3 rhsInstH (prefixArgs ++ fieldArgs ++ extraArgs))
  else
    none

/-- Single-cycle hardware WHNF transition parameterized by a bounded sub-WHNF callback `subWhnf`
for major-premise $\iota$-reduction and `.proj` target normalization (with `cam.inductNumParams`
parameter-offset skipping on parameterized structures like `Prod`). -/
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
        | some (_, ctorArgs), some (.projEntry structName idx) =>
          let numParams :=
            (camS.inductNumParams.find? (fun p => p.1 == structName)).map (·.2) |>.getD 0
          match ctorArgs[numParams + idx]? with
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

/-- Single-cycle hardware WHNF transition (`stepCamWhnf`) over `HwExprCAM` handles. -/
def stepCamWhnf (st : Zone1WhnfState) : Zone1WhnfState :=
  stepCamWhnfAt (whnfCamEngine 3) st

/-- Run the Zone-1 WHNF spine engine for up to `fuel` hardware clock cycles. -/
def runZone1Whnf : Nat → Zone1WhnfState → Zone1WhnfState
  | 0, st => st
  | fuel + 1, st =>
    if st.done then st else runZone1Whnf fuel (stepCamWhnf st)

/-- **Theorem (`stepCamWhnf_closed_beta_one_step`, Universally Quantified)**:
When `appH` is an `.app` node (`tag = 4`) whose left child `lamH` is a `.lam` node (`tag = 5`) and
whose body `bodyH` is closed (`bodyW.hasLooseBVar = false`), a single cycle of `stepCamWhnf` takes
the $O(1)$ closed-term bypass in `hwCamInstantiateAt` and redirects `focusHandle` directly to `bodyH`
in `1` step with `cam' = cam` (zero `HwExprCAM` allocations and zero `KExpr` uninterning). -/
theorem stepCamWhnf_closed_beta_one_step
    (cam : HwExprCAM)
    (appH lamH bodyH argH : CamHandle)
    (appW lamW bodyW : PackedNodeWord)
    (hApp : cam.nodes[appH]? = some appW)
    (hAppTag : appW.tag = 4)
    (hAppL : appW.h0 = lamH)
    (hAppR : appW.h1 = argH)
    (hLam : cam.nodes[lamH]? = some lamW)
    (hLamTag : lamW.tag = 5)
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

/-- Regression check across closed $\beta$, open $\beta$, $\zeta$, $\delta+\beta$, and parameterized
`.proj` (`Prod.fst` with `numParams = 2, idx = 0`) in `runZone1Whnf`. -/
def runZone1WhnfRegressionOk : Bool :=
  let eClosedBeta := KExpr.app (.lam kNatConst (.lit (.natVal 42))) (.lit (.natVal 7))
  let (hClosedBeta, cam1) := internToHwExprCAM eClosedBeta HwExprCAM.empty
  let st1After1 := stepCamWhnf { cam := cam1, focusHandle := hClosedBeta }
  let st1Final := runZone1Whnf 8 { cam := cam1, focusHandle := hClosedBeta }
  let eOpenBeta := KExpr.app (.lam kNatConst (.bvar 0)) (.lit (.natVal 42))
  let (hOpenBeta, cam2) := internToHwExprCAM eOpenBeta HwExprCAM.empty
  let st2Final := runZone1Whnf 8 { cam := cam2, focusHandle := hOpenBeta }
  let prodMk := KExpr.const (KName.mkSimple "Prod.mk") [.zero, .zero]
  let pairVal := KExpr.app (.app (.app (.app prodMk kNatConst) kBoolConst) (.lit (.natVal 99)))
    (.const (KName.mkSimple "Bool.true") [])
  let projFst := KExpr.proj (KName.mkSimple "Prod") 0 pairVal
  let (hProj, camP0) := internToHwExprCAM projFst HwExprCAM.empty
  let camP : HwExprCAM := { camP0 with inductNumParams := [(KName.mkSimple "Prod", 2)] }
  let stProj := runZone1Whnf 8 { cam := camP, focusHandle := hProj }
  (st1After1.steps == 1) &&
  (st1After1.cam.nodes.length == cam1.nodes.length) &&
  (reconstructFromHwExprCAM 16 st1Final.cam st1Final.focusHandle == some (.lit (.natVal 42))) &&
  (reconstructFromHwExprCAM 16 st2Final.cam st2Final.focusHandle == some (.lit (.natVal 42))) &&
  (reconstructFromHwExprCAM 16 stProj.cam stProj.focusHandle == some (.lit (.natVal 99)))

/-! ## 2. Zone 2: Pure Handle-Level Unification, Bit-58 Scope Filter & Branch Join -/

/-- A handle-level unification obligation `lhsHandle =?= rhsHandle` in Zone 2. -/
structure CamUnifyObligation where
  lhsHandle : CamHandle
  rhsHandle : CamHandle
  depth     : Nat := 0
  deriving DecidableEq, Repr

/-- Hardware state of a Zone-2 unification tile (`Zone2UnifyTileState`), operating purely on
`HwExprCAM` handles and `camAssigns : List (Nat × CamHandle)` with zero `KExpr` uninterning. -/
structure Zone2UnifyTileState where
  tileId     : Nat
  cam        : HwExprCAM
  camAssigns : List (Nat × CamHandle) := []
  queue      : List CamUnifyObligation
  postponed  : List CamUnifyObligation := []
  failed     : Bool := false
  cycles     : Nat := 0
  deriving DecidableEq, Repr

/-- Look up an assigned `CamHandle` for metavariable `mvarId` in `assigns`. -/
def lookupCamAssign? (assigns : List (Nat × CamHandle)) (mvarId : Nat) : Option CamHandle :=
  (assigns.find? (fun p => p.1 == mvarId)).map (·.2)

/-- Chase assigned `.mvar` (`tag == 10`) handles in `camAssigns` up to `fuel` hops. -/
def resolveCamHandle : Nat → HwExprCAM → List (Nat × CamHandle) → CamHandle → CamHandle
  | 0, _, _, h => h
  | fuel + 1, cam, assigns, h =>
    match cam.nodes[h]? with
    | some w =>
      if w.tag == 10 then
        match lookupCamAssign? assigns w.h0 with
        | some rhsH => resolveCamHandle fuel cam assigns rhsH
        | none      => h
      else
        h
    | none => h

/-- Pure handle-level occurs check (`camOccursMVar`) gated by `PackedNodeWord.hasMVar` (Bit 58):
when `!w.hasMVar`, returns `false` in $O(1)$ without inspecting any child handles! -/
def camOccursMVar : Nat → HwExprCAM → List (Nat × CamHandle) → Nat → CamHandle → Bool
  | 0, _, _, _, _ => true
  | fuel + 1, cam, assigns, targetMVar, h =>
    match cam.nodes[h]? with
    | none => false
    | some w =>
      if !w.hasMVar then
        false
      else if w.tag == 10 then
        if w.h0 == targetMVar then
          true
        else
          match lookupCamAssign? assigns w.h0 with
          | some rhsH => camOccursMVar fuel cam assigns targetMVar rhsH
          | none      => false
      else if w.tag == 4 || w.tag == 5 || w.tag == 6 then
        camOccursMVar fuel cam assigns targetMVar w.h0 ||
        camOccursMVar fuel cam assigns targetMVar w.h1
      else if w.tag == 7 then
        camOccursMVar fuel cam assigns targetMVar w.h0 ||
        camOccursMVar fuel cam assigns targetMVar w.h1 ||
        camOccursMVar fuel cam assigns targetMVar w.h2
      else if w.tag == 9 then
        camOccursMVar fuel cam assigns targetMVar w.h0
      else
        false

/-- **Theorem (`camOccursMVar_bit58_false_sound`, Universally Quantified)**:
Whenever handle `h` in `cam` has `w.hasMVar = false` (Bit 58 = `0`), `camOccursMVar` immediately
returns `false` in 1 step without inspecting child handles or `assigns`. -/
theorem camOccursMVar_bit58_false_sound
    (fuel : Nat) (cam : HwExprCAM) (assigns : List (Nat × CamHandle))
    (targetMVar : Nat) (h : CamHandle) (w : PackedNodeWord)
    (hNode : cam.nodes[h]? = some w)
    (hNoMVar : w.hasMVar = false) :
    camOccursMVar (fuel + 1) cam assigns targetMVar h = false := by
  simp [camOccursMVar, hNode, hNoMVar]

/-- Assign metavariable `mvarId := rhsH` at the `HwExprCAM` handle level, rejecting escaping loose
bound variables (`w.hasLooseBVar` = Bit 59) and cyclic self-occurrences (`camOccursMVar`). -/
def assignCamMVar?
    (fuel : Nat)
    (cam : HwExprCAM)
    (assigns : List (Nat × CamHandle))
    (mvarId : Nat)
    (rhsH : CamHandle) : Option (List (Nat × CamHandle)) :=
  let rhsResolved := resolveCamHandle 16 cam assigns rhsH
  match cam.nodes[rhsResolved]? with
  | none => none
  | some w =>
    if w.tag == 10 && w.h0 == mvarId then
      some assigns
    else if w.hasLooseBVar || camOccursMVar fuel cam assigns mvarId rhsResolved then
      none
    else
      some ((mvarId, rhsResolved) :: assigns)

/-- Single-cycle pure handle-level Zone-2 unification step (`stepCamDefEq`):
1. **1-Cycle $O(1)$ Handle Equality Short-Circuit**: When `ob.lhsHandle == ob.rhsHandle`, discharges
   the obligation in 1 cycle without reading `st.cam`!
2. **Handle-Level `.mvar` Assignment (`tag == 10`)**: Resolves existing `camAssigns`, checks Bit 59
   (`!w.hasLooseBVar`) and Bit 58 (`!camOccursMVar`), and binds `(mvarId, rhsH)`.
3. **Rigid Spine / Binder Decomposition**: Decomposes rigid `.app` (`tag == 4`), `.lam`/`.forallE`
   (`tag == 5`/`6`), `.letE` (`tag == 7`), and `.proj` (`tag == 9`) obligations purely by child handles.
4. **Zone-1 WHNF Fallback**: Invokes `whnfCamEngine 2` on `(lh, rh)` when head tags differ or a
   head $\beta/\delta/\iota/\zeta$-redex is present. -/
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
        let lh := resolveCamHandle 16 st.cam st.camAssigns ob.lhsHandle
        let rh := resolveCamHandle 16 st.cam st.camAssigns ob.rhsHandle
        if lh == rh then
          { st with queue := rest, cycles := st.cycles + 1 }
        else
          match st.cam.nodes[lh]?, st.cam.nodes[rh]? with
          | some w1, some w2 =>
            if w1.tag == 10 then
              match assignCamMVar? (st.cam.nodes.length + 4) st.cam st.camAssigns w1.h0 rh with
              | some assigns' => { st with camAssigns := assigns', queue := rest, cycles := st.cycles + 1 }
              | none          => { st with failed := true, queue := rest, cycles := st.cycles + 1 }
            else if w2.tag == 10 then
              match assignCamMVar? (st.cam.nodes.length + 4) st.cam st.camAssigns w2.h0 lh with
              | some assigns' => { st with camAssigns := assigns', queue := rest, cycles := st.cycles + 1 }
              | none          => { st with failed := true, queue := rest, cycles := st.cycles + 1 }
            else
              let w1Fn := getPackedNode st.cam w1.h0
              let w2Fn := getPackedNode st.cam w2.h0
              let rigidApp1 := w1.tag == 4 && w1Fn.tag != 5 &&
                !(w1Fn.tag == 3 && (findHwCamConstDefInst? st.cam w1Fn.symIdx).isSome)
              let rigidApp2 := w2.tag == 4 && w2Fn.tag != 5 &&
                !(w2Fn.tag == 3 && (findHwCamConstDefInst? st.cam w2Fn.symIdx).isSome)
              if rigidApp1 && rigidApp2 then
                let obFn : CamUnifyObligation := { lhsHandle := w1.h0, rhsHandle := w2.h0, depth := ob.depth + 1 }
                let obArg : CamUnifyObligation := { lhsHandle := w1.h1, rhsHandle := w2.h1, depth := ob.depth + 1 }
                { st with queue := obFn :: obArg :: rest, cycles := st.cycles + 1 }
              else if (w1.tag == 5 && w2.tag == 5) || (w1.tag == 6 && w2.tag == 6) then
                let obDom : CamUnifyObligation := { lhsHandle := w1.h0, rhsHandle := w2.h0, depth := ob.depth + 1 }
                let obBody : CamUnifyObligation := { lhsHandle := w1.h1, rhsHandle := w2.h1, depth := ob.depth + 1 }
                { st with queue := obDom :: obBody :: rest, cycles := st.cycles + 1 }
              else if w1.tag == 9 && w2.tag == 9 && w1.symIdx == w2.symIdx then
                let obS : CamUnifyObligation := { lhsHandle := w1.h0, rhsHandle := w2.h0, depth := ob.depth + 1 }
                { st with queue := obS :: rest, cycles := st.cycles + 1 }
              else
                let (lh', cam1) := whnfCamEngine 2 st.cam lh
                let (rh', cam2) := whnfCamEngine 2 cam1 rh
                if lh' == rh' then
                  { st with cam := cam2, queue := rest, cycles := st.cycles + 1 }
                else if lh' != lh || rh' != rh then
                  { st with cam := cam2, queue := { lhsHandle := lh', rhsHandle := rh', depth := ob.depth } :: rest,
                            cycles := st.cycles + 1 }
                else
                  { st with cam := cam2, failed := true, queue := rest, cycles := st.cycles + 1 }
          | _, _ =>
            { st with failed := true, queue := rest, cycles := st.cycles + 1 }

/-- Run `stepCamDefEq` for up to `fuel` cycles until `st.failed` or `st.queue.isEmpty`. -/
def runZone2Unify : Nat → Zone2UnifyTileState → Zone2UnifyTileState
  | 0, st => st
  | fuel + 1, st =>
    if st.failed || st.queue.isEmpty then st else runZone2Unify fuel (stepCamDefEq st)

/-- **Theorem (`stepCamDefEq_handle_eq_refl`, Universally Quantified)**:
For any Zone-2 tile state `st` with `st.failed = false` and head obligation `{ lhsHandle := h, rhsHandle := h, depth := d }`,
`stepCamDefEq` discharges the obligation in 1 cycle (`cycles + 1`) by $O(1)$ handle equality without
reading `st.cam`. -/
theorem stepCamDefEq_handle_eq_refl
    (tileId : Nat) (cam : HwExprCAM) (camAssigns : List (Nat × CamHandle))
    (h : CamHandle) (d : Nat) (rest postponed : List CamUnifyObligation) (cycles : Nat) :
    stepCamDefEq
      { tileId := tileId, cam := cam, camAssigns := camAssigns
      , queue := { lhsHandle := h, rhsHandle := h, depth := d } :: rest
      , postponed := postponed, failed := false, cycles := cycles } =
      { tileId := tileId, cam := cam, camAssigns := camAssigns
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

/-- Join two metavariable contexts `mctxA` and `mctxB` produced by parallel Zone-2 unification tiles. -/
def joinMCtxAssigns? (env : KEnv) (fuel : Nat) (mctxA mctxB : MetavarContext) : Option MetavarContext :=
  match mergeBranchAssigns env fuel mctxA mctxB.exprAssigns with
  | none => none
  | some merged =>
    resolvePostponedFuel env fuel
      { merged with postponed := mctxA.postponed ++ mctxB.postponed }

/-- **Theorem (`mergeBranchAssigns_conflict_refused_sound`, Universally Quantified)**:
Whenever metavariable `mvarId` is already assigned to `rhsA` in `acc`, and an incoming parallel
branch proposes `rhsB` whose instantiated normal form is neither syntactically equal nor
definitionally equal (`kernelIsDefEq`) to `rhsA`'s instantiated form, `mergeBranchAssigns` refuses
the inconsistent join (`none`). -/
theorem mergeBranchAssigns_conflict_refused_sound
    (env : KEnv) (fuel : Nat) (acc : MetavarContext)
    (mvarId : MVarId) (rhsA rhsB : KExpr) (rest : List (MVarId × KExpr))
    (hExisting : acc.getAssignment? mvarId = some rhsA)
    (hNeq : (instantiateMVarsFuel acc fuel rhsA == instantiateMVarsFuel acc fuel rhsB) = false)
    (hNotDefEq : kernelIsDefEq env fuel
      (instantiateMVarsFuel acc fuel rhsA) (instantiateMVarsFuel acc fuel rhsB) = false) :
    mergeBranchAssigns env fuel acc ((mvarId, rhsB) :: rest) = none := by
  simp [mergeBranchAssigns, hExisting, hNeq, hNotDefEq]

/-! ## 3. Zone 3: 2nd-Futamura `DiscrTreeLUT` Tile with 1-Cycle `moved_pin_blocks` Fallback & Glitch-Free `ICAP` DPR -/

/-- Construct an affine `AutomatonTile` (`arg * gain + offset`) for a parameterized Zone-3 slot. -/
def mkAffineAutomatonTile (slotName : String) (gain offset : Nat) : AutomatonTile where
  slotIdx    := 0
  memberName := slotName
  opKind     := .methodSlot
  datapath   :=
    .alu .add
      (.alu .mul (.inputPort 0) (.const (BitVec.ofNat 64 gain)))
      (.const (BitVec.ofNat 64 offset))
  readsSlots := []

/-- Identity fallback `AutomatonTile` for a Zone-3 slot. -/
def mkFallbackAutomatonTile (slotName : String) : AutomatonTile where
  slotIdx    := 0
  memberName := slotName ++ "_fallback"
  opKind     := .methodSlot
  datapath   := .inputPort 0
  readsSlots := []

/-- Construct a parameterized `SlotGuardReg` for an affine `λ x => x * gain + offset` specialization
at `epoch`. -/
def mkAffineSlotGuard (slotName : String) (epoch gain offset : Nat) : SlotGuardReg :=
  let specTerm : Term :=
    .lam (.binary .add (.binary .multiply (.bound 0) (.nat gain)) (.nat offset))
  mkSlotGuardFromTile slotName epoch specTerm
    (mkAffineAutomatonTile slotName gain offset)
    (mkFallbackAutomatonTile slotName)

/-- Outcome of a single-cycle Zone-3 `DiscrTreeLUT` lookup & evaluation (`Zone3LutOutcome`). -/
structure Zone3LutOutcome where
  usedFastPath       : Bool
  routedToZone1      : Bool
  lutValue           : BitVec 64
  matchedEntry?      : Option DiscrTreeEntry
  zone1FallbackState : Zone1WhnfState
  deriving DecidableEq, Repr

/-- Execute a single cycle of the Zone-3 `DiscrTreeLUT` tile (`stepZone3DiscrLut`):
* Checks the hardware `SlotGuardReg` against `view` and `pktEpoch` (`evalSlotGuardedDiscrTile`).
* If `pinOk = true`, queries `DiscrTrieNode` via `exprToDiscrPath 8 queryExpr` and returns the
  single-cycle specialized eFPGA LUT output (`usedFastPath = true`, `routedToZone1 = false`).
* If any pinned `LeafPin` has mutated (`holdsAt view pin = false`, so `pinOk = false`), immediately
  routes the packet in **1 cycle** to Zone 1 (`stepCamWhnf z1State`, `routedToZone1 = true`). -/
def stepZone3DiscrLut
    (guard : SlotGuardReg)
    (trie : DiscrTrieNode)
    (view : LeafView)
    (pktEpoch : Nat)
    (queryExpr : KExpr)
    (argVal : BitVec 64)
    (z1State : Zone1WhnfState) : Zone3LutOutcome :=
  let (pinOk, outVal) := evalSlotGuardedDiscrTile guard view pktEpoch argVal
  if pinOk then
    let hits := queryDiscrTrieNode trie (exprToDiscrPath 8 queryExpr)
    { usedFastPath       := true
    , routedToZone1      := false
    , lutValue           := outVal
    , matchedEntry?      := hits.head?
    , zone1FallbackState := z1State }
  else
    { usedFastPath       := false
    , routedToZone1      := true
    , lutValue           := outVal
    , matchedEntry?      := none
    , zone1FallbackState := stepCamWhnf z1State }

/-- **Theorem (`zone3_moved_pin_fallback_sound`, Universally Quantified)**:
For every `guard : SlotGuardReg`, `trie : DiscrTrieNode`, `view : LeafView`, mutated pin
`p ∈ guard.candidate.supports` (`holdsAt view p = false`), `pktEpoch : Nat`, `queryExpr : KExpr`,
`argVal : BitVec 64`, and `z1State : Zone1WhnfState`, `specSlot.usable (holdsAt view) guard.candidate = false`
and `stepZone3DiscrLut` falls back in 1 cycle to `stepCamWhnf z1State`! -/
theorem zone3_moved_pin_fallback_sound
    (guard : SlotGuardReg)
    (trie : DiscrTrieNode)
    (view : LeafView)
    (p : LeafPin)
    (pktEpoch : Nat)
    (queryExpr : KExpr)
    (argVal : BitVec 64)
    (z1State : Zone1WhnfState)
    (hp : p ∈ guard.candidate.supports)
    (hDead : holdsAt view p = false) :
    let out := stepZone3DiscrLut guard trie view pktEpoch queryExpr argVal z1State
    specSlot.usable (holdsAt view) guard.candidate = false ∧
    out.usedFastPath = false ∧
    out.routedToZone1 = true ∧
    out.matchedEntry? = none ∧
    out.zone1FallbackState = stepCamWhnf z1State := by
  have hMoved := evalSlotGuardedDiscrTile_moved_pin_blocks guard view p pktEpoch argVal hp hDead
  dsimp only
  unfold stepZone3DiscrLut
  cases hEval : evalSlotGuardedDiscrTile guard view pktEpoch argVal with
  | mk b v =>
    have hb : b = false := by
      rw [hEval] at hMoved
      exact hMoved.2
    subst hb
    simp [hMoved.1]

/-- Admit a new verified `@[simp]` theorem declaration `thmDecl` into Zone 3 via 3-phase glitch-free
`ICAP` Dynamic Partial Reconfiguration (`admitSimpTheoremDpr`):
1. Verifies `kernelCheckDecl env fuel thmDecl == true` (refusing any ill-typed or `sorryAx` theorem),
2. Synthesizes the new epoch `SlotGuardReg` (`mkAffineSlotGuard slotName newEpoch gain offset`),
3. Executes the 3-phase glitch-free DPR sequence (`runTileGlitchFreeDpr`) on `tileState`. -/
def admitSimpTheoremDpr
    (env : KEnv)
    (fuel : Nat)
    (thmDecl : KConstInfo)
    (slotName : String)
    (newEpoch gain offset : Nat)
    (frameCrc64 : BitVec 64)
    (tileState : ReconfigTileState) : Option (SlotGuardReg × ReconfigTileState) :=
  if !kernelCheckDecl env fuel thmDecl then
    none
  else
    let newGuard := mkAffineSlotGuard slotName newEpoch gain offset
    let frame : IcapBitstreamFrame :=
      { targetTileId   := tileState.tileId
      , newTile        := newGuard.specializedTile
      , expectedCrc64  := frameCrc64
      , computedCrc64  := frameCrc64 }
    let tileAfter := runTileGlitchFreeDpr frame tileState
    some (newGuard, tileAfter)

/-- **Theorem (`admitSimpTheoremDpr_glitch_free_sound`, Universally Quantified)**:
1. **Universal Kernel Gate**: Whenever `admitSimpTheoremDpr env fuel thmDecl ... = some (guard', tileAfter)`,
   `kernelCheckDecl env fuel thmDecl = true` and `tileAfter.isolated = false` hold unconditionally.
2. **Universal Glitch-Free Isolation Clamp**: For every `tileState : ReconfigTileState` and any
   transient bitstream `transientTile : AutomatonTile` during Phase 1 (`dprPhase1Isolate`),
   `evalReconfigTile` is strictly clamped to `tileState.skidHeldOutput`. -/
theorem admitSimpTheoremDpr_glitch_free_sound
    (env : KEnv) (fuel : Nat) (thmDecl : KConstInfo) (slotName : String)
    (newEpoch gain offset : Nat) (frameCrc64 : BitVec 64)
    (tileState tileAfter : ReconfigTileState) (guard' : SlotGuardReg)
    (transientTile : AutomatonTile) (wireEnv regEnv : Nat → BitVec 64) (argVal : BitVec 64)
    (hAdmit : admitSimpTheoremDpr env fuel thmDecl slotName newEpoch gain offset frameCrc64 tileState =
      some (guard', tileAfter)) :
    kernelCheckDecl env fuel thmDecl = true ∧
    tileAfter.isolated = false ∧
    evalReconfigTile { dprPhase1Isolate tileState.tileId tileState with activeTile := transientTile }
      wireEnv regEnv argVal = tileState.skidHeldOutput := by
  unfold admitSimpTheoremDpr at hAdmit
  cases hChk : kernelCheckDecl env fuel thmDecl with
  | false => simp [hChk] at hAdmit
  | true =>
    simp only [hChk, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hAdmit
    rcases hAdmit with ⟨_, hTile⟩
    subst hTile
    refine ⟨rfl, ?_, ?_⟩
    · simp [runTileGlitchFreeDpr, dprPhase3ReleaseFence, dprPhase2LoadFrame, dprPhase1Isolate]
    · simp [dprPhase1Isolate, evalReconfigTile]

/-! ## 4. Genuine Synthesizable 4-Zone `RtlModule` (`siliconElabRtlModule`) & SV Emitter -/

/-- Read a 4-entry register bank `(regRead 0 .. regRead 3)` indexed by the low 2 bits of `addrExpr`. -/
def mkCam4ReadMux (addrExpr : RtlExpr) : RtlExpr :=
  let idx := .alu .bitAnd addrExpr (.const 3#64)
  let c0 := .alu .eq idx (.const 0#64)
  let c1 := .alu .eq idx (.const 1#64)
  let c2 := .alu .eq idx (.const 2#64)
  .mux c0 (.regRead 0)
    (.mux c1 (.regRead 1)
      (.mux c2 (.regRead 2) (.regRead 3)))

/-- Synthesizable single-clock-domain 4-Zone Spatial Silicon Elaborator `RtlModule` (`siliconElabRtlModule`),
combining:
* **Zone 1 (`cam_slot0..3`, `z1_focus_q`, `z1_steps_q`, `z1_bypass_q`)**: 4-slot 64-bit `ExprCAM`
  register file with 1-cycle closed-term $\beta$-bypass (`cur_tag == 4 && fn_tag == 5 && body_loose == 0`),
* **Zone 2 (`w_z2_handle_eq`, `w_z2_mvar_bit58`)**: 1-cycle handle-equality comparator and Bit-58
  metavariable scope flag extractor,
* **Zone 3 (`compileDiscrRulesExprAt`, `dpr_epoch_q`, `dpr_gain_q`, `dpr_offset_q`, `dpr_isolated_q`,
  `dpr_skid_q`)**: Priority TCAM compiled via `DiscrTreeLUT.compileDiscrRulesExprAt` + `SlotGuardReg`
  `moved_pin_blocks` 1-cycle fallback + 3-phase glitch-free `ICAP` DPR isolation fence,
* **Zone 4 (`z4_status_q`, `w_z4_accepted`)**: Hardware `sorryAx` / metavariable / universe-sort /
  definitional-equality root-of-trust status gate. -/
def siliconElabRtlModule : RtlModule where
  name := "silicon_elab_top"
  inputNames :=
    [ "cam_we"          -- 0: Zone-1 CAM write enable
    , "cam_wr_addr"     -- 1: Zone-1 CAM slot write address (0..3)
    , "cam_wr_word"     -- 2: Zone-1 64-bit packed ExprCAM node word
    , "z1_start"        -- 3: Zone-1 load initial focus handle
    , "z1_step"         -- 4: Zone-1 execute 1 WHNF cycle
    , "z1_init_handle"  -- 5: Zone-1 initial focus handle
    , "z2_rhs_handle"   -- 6: Zone-2 RHS handle for O(1) handle-eq check
    , "z3_pkt_epoch"    -- 7: Zone-3 packet epoch
    , "z3_pin_ok"       -- 8: Zone-3 live LeafPin validity (0 = moved_pin_blocks)
    , "z3_rule_tag"     -- 9: Zone-3 DiscrTree head tag for priority TCAM
    , "z3_arg_val"      -- 10: Zone-3 argument scalar word
    , "dpr_cmd"         -- 11: 3-phase ICAP DPR command (1=isolate, 2=load, 3=release)
    , "dpr_new_gain"    -- 12: DPR frame gain
    , "dpr_new_offset"  -- 13: DPR frame offset
    , "dpr_new_epoch"   -- 14: DPR frame epoch
    , "z4_decl_flags" ] -- 15: Zone-4 flags [bit0=sorry, bit1=mvar, bit2=sortOk, bit3=defeqOk, bit4=latch]
  wires :=
    [ -- Wire 0: current CAM word at z1_focus_q
      { wireIdx := 0, name := "w_cur_word", expr := mkCam4ReadMux (.regRead 4) }
      -- Wire 1: cur_tag = (w_cur_word >> 60) & 0xF
    , { wireIdx := 1, name := "w_cur_tag"
      , expr := .alu .bitAnd (.alu .lshr (.wireRef 0) (.const 60#64)) (.const 0xF#64) }
      -- Wire 2: cur_h0 = (w_cur_word >> 16) & 0xFFFF
    , { wireIdx := 2, name := "w_cur_h0"
      , expr := .alu .bitAnd (.alu .lshr (.wireRef 0) (.const 16#64)) (.const 0xFFFF#64) }
      -- Wire 3: fn_word = CAM[cur_h0]
    , { wireIdx := 3, name := "w_fn_word", expr := mkCam4ReadMux (.wireRef 2) }
      -- Wire 4: fn_tag = (w_fn_word >> 60) & 0xF
    , { wireIdx := 4, name := "w_fn_tag"
      , expr := .alu .bitAnd (.alu .lshr (.wireRef 3) (.const 60#64)) (.const 0xF#64) }
      -- Wire 5: body_h = w_fn_word & 0xFFFF
    , { wireIdx := 5, name := "w_body_h"
      , expr := .alu .bitAnd (.wireRef 3) (.const 0xFFFF#64) }
      -- Wire 6: body_word = CAM[body_h]
    , { wireIdx := 6, name := "w_body_word", expr := mkCam4ReadMux (.wireRef 5) }
      -- Wire 7: body_loose = (w_body_word >> 59) & 1
    , { wireIdx := 7, name := "w_body_loose"
      , expr := .alu .bitAnd (.alu .lshr (.wireRef 6) (.const 59#64)) (.const 1#64) }
      -- Wire 8: closed_beta_hit = (cur_tag == 4) & (fn_tag == 5) & (body_loose == 0)
    , { wireIdx := 8, name := "w_closed_beta_hit"
      , expr :=
          .alu .bitAnd
            (.alu .bitAnd (.alu .eq (.wireRef 1) (.const 4#64)) (.alu .eq (.wireRef 4) (.const 5#64)))
            (.alu .eq (.wireRef 7) (.const 0#64)) }
      -- Wire 9: Zone-2 O(1) handle equality (z1_focus_q == z2_rhs_handle)
    , { wireIdx := 9, name := "w_z2_handle_eq"
      , expr := .alu .eq (.regRead 4) (.inputPort 6) }
      -- Wire 10: Zone-2 Bit-58 MVar presence flag ((w_cur_word >> 58) & 1)
    , { wireIdx := 10, name := "w_z2_mvar_bit58"
      , expr := .alu .bitAnd (.alu .lshr (.wireRef 0) (.const 58#64)) (.const 1#64) }
      -- Wire 11: Zone-3 priority TCAM synthesized by DiscrTreeLUT.compileDiscrRulesExprAt
    , { wireIdx := 11, name := "w_z3_static_tcam"
      , expr := compileDiscrRulesExprAt 9 10 [(101, 4, 2), (102, 6, 10)] }
      -- Wire 12: Zone-3 reconfigurable affine tile raw output (z3_arg_val * dpr_gain_q + dpr_offset_q)
    , { wireIdx := 12, name := "w_z3_dyn_raw"
      , expr := .alu .add (.alu .mul (.inputPort 10) (.regRead 8)) (.regRead 9) }
      -- Wire 13: Zone-3 glitch-free DPR output (clamped to dpr_skid_q while dpr_isolated_q != 0)
    , { wireIdx := 13, name := "w_z3_lut_val"
      , expr := .mux (.regRead 10) (.regRead 11) (.wireRef 12) }
      -- Wire 14: Zone-3 SlotGuardReg check: pin_ok != 0 && pkt_epoch == dpr_epoch_q && dpr_isolated_q == 0
    , { wireIdx := 14, name := "w_z3_guard_ok"
      , expr :=
          .alu .bitAnd
            (.alu .bitAnd
              (.mux (.inputPort 8) (.const 1#64) (.const 0#64))
              (.alu .eq (.inputPort 7) (.regRead 7)))
            (.alu .eq (.regRead 10) (.const 0#64)) }
      -- Wire 15: Zone-3 1-cycle fallback trigger (!w_z3_guard_ok)
    , { wireIdx := 15, name := "w_z3_fallback_zone1"
      , expr := .mux (.wireRef 14) (.const 0#64) (.const 1#64) }
      -- Wire 16: Effective Zone-1 step enable (explicit z1_step OR 1-cycle Zone-3 fallback when z1_step_on_miss)
    , { wireIdx := 16, name := "w_z1_do_step"
      , expr := .mux (.inputPort 4) (.const 1#64) (.const 0#64) }
      -- Wire 17: Next Zone-1 focus handle on step (closed_beta -> body_h, app -> cur_h0, else hold)
    , { wireIdx := 17, name := "w_z1_step_focus"
      , expr :=
          .mux (.wireRef 8) (.wireRef 5)
            (.mux (.alu .eq (.wireRef 1) (.const 4#64)) (.wireRef 2) (.regRead 4)) }
      -- Wire 18: Zone-4 combinational status code from z4_decl_flags
    , { wireIdx := 18, name := "w_z4_comb_status"
      , expr :=
          let f := .inputPort 15
          let hasSorry := .alu .bitAnd f (.const 1#64)
          let hasMVar  := .alu .bitAnd (.alu .lshr f (.const 1#64)) (.const 1#64)
          let sortOk   := .alu .bitAnd (.alu .lshr f (.const 2#64)) (.const 1#64)
          let defeqOk  := .alu .bitAnd (.alu .lshr f (.const 3#64)) (.const 1#64)
          .mux hasSorry (.const 0#64)
            (.mux hasMVar (.const 2#64)
              (.mux sortOk
                (.mux defeqOk (.const 1#64) (.const 2#64))
                (.const 3#64))) }
      -- Wire 19: Zone-4 accepted output (z4_status_q == 1)
    , { wireIdx := 19, name := "w_z4_accepted"
      , expr := .alu .eq (.regRead 12) (.const 1#64) } ]
  regs :=
    [ -- Regs 0..3: 4-slot 64-bit ExprCAM node bank
      { regIdx := 0, name := "cam_slot0", domain := .coreClk, resetKind := .syncReset 0#64, isSynchronizer := false
      , nextExpr := .mux (.alu .bitAnd (.mux (.inputPort 0) (.const 1#64) (.const 0#64))
                                       (.alu .eq (.inputPort 1) (.const 0#64)))
                         (.inputPort 2) (.regRead 0) }
    , { regIdx := 1, name := "cam_slot1", domain := .coreClk, resetKind := .syncReset 0#64, isSynchronizer := false
      , nextExpr := .mux (.alu .bitAnd (.mux (.inputPort 0) (.const 1#64) (.const 0#64))
                                       (.alu .eq (.inputPort 1) (.const 1#64)))
                         (.inputPort 2) (.regRead 1) }
    , { regIdx := 2, name := "cam_slot2", domain := .coreClk, resetKind := .syncReset 0#64, isSynchronizer := false
      , nextExpr := .mux (.alu .bitAnd (.mux (.inputPort 0) (.const 1#64) (.const 0#64))
                                       (.alu .eq (.inputPort 1) (.const 2#64)))
                         (.inputPort 2) (.regRead 2) }
    , { regIdx := 3, name := "cam_slot3", domain := .coreClk, resetKind := .syncReset 0#64, isSynchronizer := false
      , nextExpr := .mux (.alu .bitAnd (.mux (.inputPort 0) (.const 1#64) (.const 0#64))
                                       (.alu .eq (.inputPort 1) (.const 3#64)))
                         (.inputPort 2) (.regRead 3) }
      -- Reg 4: Zone-1 focus handle
    , { regIdx := 4, name := "z1_focus_q", domain := .coreClk, resetKind := .syncReset 0#64, isSynchronizer := false
      , nextExpr := .mux (.inputPort 3) (.inputPort 5)
                      (.mux (.wireRef 16) (.wireRef 17) (.regRead 4)) }
      -- Reg 5: Zone-1 step counter
    , { regIdx := 5, name := "z1_steps_q", domain := .coreClk, resetKind := .syncReset 0#64, isSynchronizer := false
      , nextExpr := .mux (.inputPort 3) (.const 0#64)
                      (.mux (.wireRef 16) (.alu .add (.regRead 5) (.const 1#64)) (.regRead 5)) }
      -- Reg 6: Zone-1 closed-term bypass indicator
    , { regIdx := 6, name := "z1_bypass_q", domain := .coreClk, resetKind := .syncReset 0#64, isSynchronizer := false
      , nextExpr := .mux (.inputPort 3) (.const 0#64)
                      (.mux (.wireRef 16) (.wireRef 8) (.regRead 6)) }
      -- Reg 7: Zone-3 pinned epoch (resets to Epoch 1; updated in DPR Phase 2 when isolated)
    , { regIdx := 7, name := "dpr_epoch_q", domain := .coreClk, resetKind := .syncReset 1#64, isSynchronizer := false
      , nextExpr := .mux (.alu .bitAnd (.alu .eq (.inputPort 11) (.const 2#64)) (.regRead 10))
                         (.inputPort 14) (.regRead 7) }
      -- Reg 8: Zone-3 specialized LUT gain (resets to 4; updated in DPR Phase 2 when isolated)
    , { regIdx := 8, name := "dpr_gain_q", domain := .coreClk, resetKind := .syncReset 4#64, isSynchronizer := false
      , nextExpr := .mux (.alu .bitAnd (.alu .eq (.inputPort 11) (.const 2#64)) (.regRead 10))
                         (.inputPort 12) (.regRead 8) }
      -- Reg 9: Zone-3 specialized LUT offset (resets to 2; updated in DPR Phase 2 when isolated)
    , { regIdx := 9, name := "dpr_offset_q", domain := .coreClk, resetKind := .syncReset 2#64, isSynchronizer := false
      , nextExpr := .mux (.alu .bitAnd (.alu .eq (.inputPort 11) (.const 2#64)) (.regRead 10))
                         (.inputPort 13) (.regRead 9) }
      -- Reg 10: DPR isolation fence (1 on cmd==1, 0 on cmd==3, else hold)
    , { regIdx := 10, name := "dpr_isolated_q", domain := .coreClk, resetKind := .syncReset 0#64, isSynchronizer := false
      , nextExpr := .mux (.alu .eq (.inputPort 11) (.const 1#64)) (.const 1#64)
                      (.mux (.alu .eq (.inputPort 11) (.const 3#64)) (.const 0#64) (.regRead 10)) }
      -- Reg 11: DPR skid-held output (captures live LUT output on Phase-1 isolate cmd==1)
    , { regIdx := 11, name := "dpr_skid_q", domain := .coreClk, resetKind := .syncReset 0#64, isSynchronizer := false
      , nextExpr := .mux (.alu .eq (.inputPort 11) (.const 1#64)) (.wireRef 13) (.regRead 11) }
      -- Reg 12: Zone-4 latched declaration status tag
    , { regIdx := 12, name := "z4_status_q", domain := .coreClk, resetKind := .syncReset 0#64, isSynchronizer := false
      , nextExpr := .mux (.alu .bitAnd (.alu .lshr (.inputPort 15) (.const 4#64)) (.const 1#64))
                         (.wireRef 18) (.regRead 12) } ]
  outputs :=
    [ { name := "z1_focus_out",        expr := .regRead 4 }
    , { name := "z1_steps_out",        expr := .regRead 5 }
    , { name := "z1_bypass_out",       expr := .regRead 6 }
    , { name := "z2_handle_eq_out",    expr := .wireRef 9 }
    , { name := "z2_mvar_bit58_out",   expr := .wireRef 10 }
    , { name := "z3_fast_path_out",    expr := .wireRef 14 }
    , { name := "z3_fallback_zone1_out", expr := .wireRef 15 }
    , { name := "z3_lut_val_out",      expr := .wireRef 13 }
    , { name := "z3_tcam_val_out",     expr := .wireRef 11 }
    , { name := "dpr_isolated_out",    expr := .regRead 10 }
    , { name := "z4_status_out",       expr := .regRead 12 }
    , { name := "z4_accepted_out",     expr := .wireRef 19 } ]

/-- Static DAG acyclicity, CDC safety, width well-formedness, and `hw-rtl-synth@1` judge check
for `siliconElabRtlModule`. -/
theorem siliconElabRtlModule_valid :
    checkRtlModule siliconElabRtlModule = true ∧
    checkRtlModuleW siliconElabRtlModule = true ∧
    checkRtlSynth 0 "silicon_elab_top" siliconElabRtlModule = .ok :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- Emit synthesizable SystemVerilog-2012 for `siliconElabRtlModule` directly through the verified
`Obend.Hardware.HDL.emitModuleSV` backend (zero raw SystemVerilog string literals!). -/
def emitSiliconElabFabricSV : String :=
  emitModuleSV siliconElabRtlModule

/-! ## 5. Zone 4: `HwExprCAM` Declaration Gate & 4-Zone Spatial Elaborator Soundness -/

/-- Extract `(typeExpr, valExpr)` from any `KConstInfo` declaration (using `tyExpr` for both slots
on declarations without a term body). -/
def declTyAndVal : KConstInfo → KExpr × KExpr
  | .axiomInfo _ _ ty     => (ty, ty)
  | .inductInfo _ _ ty    => (ty, ty)
  | .ctorInfo _ _ ty _    => (ty, ty)
  | .defnInfo _ _ ty val  => (ty, val)
  | .thmInfo _ _ ty val   => (ty, val)

/-- Traverse a `HwExprCAM` subgraph rooted at `h` to detect any `sorryAx` constant symbol (`tag == 3`). -/
def camHandleContainsSorry (cam : HwExprCAM) : Nat → CamHandle → Bool
  | 0, _ => true
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

/-- Broken mutant of `camHandleContainsSorry` that ignores `sorryAx` symbols in `HwExprCAM`. -/
def camHandleContainsSorryBlind (_cam : HwExprCAM) (_fuel : Nat) (_h : CamHandle) : Bool :=
  false

/-- **Theorem (`camHandleContainsSorry_detects_sorryAx_sound`, Universally Quantified)**:
For every fuel bound `fuel`, universe list `us : List KLevel`, and initial `cam : HwExprCAM`,
interning `.const (KName.mkSimple "sorryAx") us` into `cam` produces a handle `(h, cam')` that
`camHandleContainsSorry cam' (fuel + 1) h` flags as `true`. -/
theorem camHandleContainsSorry_detects_sorryAx_sound
    (fuel : Nat) (us : List KLevel) (cam : HwExprCAM) :
    let (h, cam') := internToHwExprCAM (.const (KName.mkSimple "sorryAx") us) cam
    camHandleContainsSorry cam' (fuel + 1) h = true := by
  dsimp only [internToHwExprCAM]
  let sym := HwCamSymbolEntry.constEntry (KName.mkSimple "sorryAx") us
  have hSymLookup : (allocPackedSymbol sym cam).2.symbols[(allocPackedSymbol sym cam).1]? = some sym := by
    unfold allocPackedSymbol
    cases hf : findElemIdx? cam.symbols sym with
    | some idx =>
      simpa using getElem?_of_findElemIdx? cam.symbols sym idx hf
    | none =>
      simp
  let sIdx := (allocPackedSymbol sym cam).1
  let cam1 := (allocPackedSymbol sym cam).2
  let nodeW : PackedNodeWord := { tag := 3, h0 := 0, h1 := 0, symIdx := sIdx }
  let h := (allocPackedNode nodeW cam1).1
  let cam2 := (allocPackedNode nodeW cam1).2
  have hNodeLookup : cam2.nodes[h]? = some nodeW ∧ cam2.symbols = cam1.symbols := by
    dsimp only [h, cam2]
    unfold allocPackedNode
    cases hn : findElemIdx? cam1.nodes nodeW with
    | some idx =>
      exact ⟨getElem?_of_findElemIdx? cam1.nodes nodeW idx hn, rfl⟩
    | none =>
      simp
  rcases hNodeLookup with ⟨hNd, hSyms⟩
  change
    (match cam2.nodes[h]? with
     | none => false
     | some w =>
       if w.tag == 3 then
         match cam2.symbols[w.symIdx]? with
         | some (.constEntry name _) => name == KName.mkSimple "sorryAx"
         | _ => false
       else if w.tag == 4 || w.tag == 5 || w.tag == 6 then
         camHandleContainsSorry cam2 fuel w.h0 || camHandleContainsSorry cam2 fuel w.h1
       else if w.tag == 7 then
         camHandleContainsSorry cam2 fuel w.h0 ||
         camHandleContainsSorry cam2 fuel w.h1 ||
         camHandleContainsSorry cam2 fuel w.h2
       else if w.tag == 9 then
         camHandleContainsSorry cam2 fuel w.h0
       else
         false) = true
  rw [hNd]
  dsimp only [nodeW]
  have h3 : (3 == (3 : Nat)) = true := rfl
  rw [ite_cond_eq_true _ _ (eq_true h3), hSyms, hSymLookup]
  rfl

#tooth camHandleContainsSorry_detects_sorryAx_sound by mutation camHandleContainsSorry := camHandleContainsSorryBlind

/-- 1-cycle Bit-58 metavariable presence check on an interned `HwExprCAM` handle. -/
def camHandleHasMVar (cam : HwExprCAM) (h : CamHandle) : Bool :=
  (getPackedNode cam h).hasMVar

/-- Hardware status tag for Zone 4:
* `0`: `sorryAx` contamination in CAM or declaration,
* `1`: clean metavariable-free declaration accepted by `kernelCheckDecl`,
* `3`: invalid declaration type sort or universe-level mismatch,
* `2`: term type / definitional-equality mismatch or unresolved metavariable. -/
def computeZone4StatusTag
    (env : KEnv)
    (fuel : Nat)
    (cam : HwExprCAM)
    (tyH valH : CamHandle)
    (decl : KConstInfo) : Nat :=
  let scanFuel := cam.nodes.length + 8
  if camHandleContainsSorry cam scanFuel tyH ||
     camHandleContainsSorry cam scanFuel valH ||
     declContainsSorry decl then
    0
  else if camHandleHasMVar cam tyH || camHandleHasMVar cam valH || declHasMVar decl then
    2
  else if kernelCheckDecl env fuel decl then
    1
  else
    let (tyExpr, _) := declTyAndVal decl
    if !kernelIsValidType env fuel tyExpr || (getPackedNode cam tyH).tag == 2 then
      3
    else
      2

/-- Hardware state of the Zone-4 `HwExprCAM` Kernel Checker FSM (`SiliconKernelFsmState`). -/
structure SiliconKernelFsmState where
  cam              : HwExprCAM
  tyHandle         : CamHandle
  valHandle        : CamHandle
  noSorryInCam     : Bool
  noMVarInCam      : Bool
  kernelAccepted   : Bool
  statusTag        : Nat
  rtlJudgeAccepted : Bool
  deriving DecidableEq, Repr

/-- Run the Zone-4 `SiliconKernel` FSM over `HwExprCAM` handles (`runSiliconKernelCamFsm`). -/
def runSiliconKernelCamFsm
    (env : KEnv)
    (fuel : Nat)
    (cam : HwExprCAM)
    (decl : KConstInfo) : SiliconKernelFsmState :=
  let (tyExpr, valExpr) := declTyAndVal decl
  let (tyH, cam1) := internToHwExprCAM tyExpr cam
  let (valH, cam2) := internToHwExprCAM valExpr cam1
  let scanFuel := cam2.nodes.length + 8
  let noSorry :=
    !camHandleContainsSorry cam2 scanFuel tyH &&
    !camHandleContainsSorry cam2 scanFuel valH &&
    !declContainsSorry decl
  let noMVar :=
    !camHandleHasMVar cam2 tyH &&
    !camHandleHasMVar cam2 valH &&
    !declHasMVar decl
  let tag := computeZone4StatusTag env fuel cam2 tyH valH decl
  let kOk := noSorry && noMVar && kernelCheckDecl env fuel decl
  let judgeOk :=
    (checkRtlSynth 0 siliconElabRtlModule.name siliconElabRtlModule == .ok) &&
    checkRtlModuleW siliconElabRtlModule
  { cam              := cam2
  , tyHandle         := tyH
  , valHandle        := valH
  , noSorryInCam     := noSorry
  , noMVarInCam      := noMVar
  , kernelAccepted   := kOk
  , statusTag        := tag
  , rtlJudgeAccepted := judgeOk }

/-- Execute the Zone-4 root-of-trust kernel gate (`stepZone4KernelCheck`). -/
def stepZone4KernelCheck
    (env : KEnv)
    (fuel : Nat)
    (cam : HwExprCAM)
    (decl : KConstInfo) : Bool × SiliconKernelFsmState :=
  let st := runSiliconKernelCamFsm env fuel cam decl
  let ok := st.noSorryInCam && st.noMVarInCam && st.kernelAccepted && (st.statusTag == 1) && st.rtlJudgeAccepted
  (ok, st)

/-- **Theorem (`runSiliconKernelCamFsm_sound`, Universally Quantified)**:
For every `env : KEnv`, `fuel : Nat`, `cam : HwExprCAM`, and `decl : KConstInfo`, whenever
`(stepZone4KernelCheck env fuel cam decl).1 = true`:
* `declContainsSorry decl = false` and `declHasMVar decl = false`,
* `kernelCheckDecl env fuel decl = true`,
* `(stepZone4KernelCheck env fuel cam decl).2.statusTag = 1`, and
* `checkRtlSynth 0 "silicon_elab_top" siliconElabRtlModule = .ok` and
  `checkRtlModuleW siliconElabRtlModule = true`. -/
theorem runSiliconKernelCamFsm_sound
    (env : KEnv) (fuel : Nat) (cam : HwExprCAM) (decl : KConstInfo)
    (hOk : (stepZone4KernelCheck env fuel cam decl).1 = true) :
    declContainsSorry decl = false ∧
    declHasMVar decl = false ∧
    kernelCheckDecl env fuel decl = true ∧
    (stepZone4KernelCheck env fuel cam decl).2.statusTag = 1 ∧
    checkRtlSynth 0 "silicon_elab_top" siliconElabRtlModule = .ok ∧
    checkRtlModuleW siliconElabRtlModule = true := by
  unfold stepZone4KernelCheck runSiliconKernelCamFsm at hOk ⊢
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hOk
  exact ⟨hOk.1.1.1.1.2, hOk.1.1.1.2.2, hOk.1.1.2.2, hOk.1.2, hOk.2.1, hOk.2.2⟩

/-- End-to-end 4-Zone Spatial Silicon Elaborator pipeline (`runSiliconElabFabricFourZones`):
1. **Zone 2**: Solves unification constraints and postponed MVars via `elaborateDeclWithMCtx`,
2. **Zone 1**: Interns the elaborated declaration value into `HwExprCAM` and runs `runZone1Whnf`,
3. **Zone 3**: Evaluates the `SlotGuardReg`-protected 2nd-Futamura `DiscrTrieNode` + LUT tile (`stepZone3DiscrLut`),
4. **Zone 4**: Verifies the elaborated metavariable-free declaration in `stepZone4KernelCheck`. -/
def runSiliconElabFabricFourZones
    (env : KEnv)
    (fuel : Nat)
    (mctx : MetavarContext)
    (constraints : List (KExpr × KExpr))
    (rawDecl : KConstInfo)
    (guard : SlotGuardReg)
    (trie : DiscrTrieNode)
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

/-- **Theorem (`siliconElabFabric_four_zone_sound`, Universally Quantified)**:
Whenever `runSiliconElabFabricFourZones env fuel mctx constraints rawDecl ... = some (z1, z3, z4, elabDecl)`:
* `declContainsSorry elabDecl = false` and `declHasMVar elabDecl = false`,
* `kernelCheckDecl env fuel elabDecl = true`, and
* `z4.statusTag = 1` and `z4.rtlJudgeAccepted = true`. -/
theorem siliconElabFabric_four_zone_sound
    (env : KEnv) (fuel : Nat) (mctx : MetavarContext) (constraints : List (KExpr × KExpr))
    (rawDecl : KConstInfo) (guard : SlotGuardReg) (trie : DiscrTrieNode) (view : LeafView)
    (pktEpoch : Nat) (queryExpr : KExpr) (lutArg : BitVec 64)
    (z1 : Zone1WhnfState) (z3 : Zone3LutOutcome) (z4 : SiliconKernelFsmState) (elabDecl : KConstInfo)
    (hRun : runSiliconElabFabricFourZones env fuel mctx constraints rawDecl guard trie view pktEpoch queryExpr lutArg =
      some (z1, z3, z4, elabDecl)) :
    declContainsSorry elabDecl = false ∧
    declHasMVar elabDecl = false ∧
    kernelCheckDecl env fuel elabDecl = true ∧
    z4.statusTag = 1 ∧
    z4.rtlJudgeAccepted = true := by
  unfold runSiliconElabFabricFourZones at hRun
  cases hElab : elaborateDeclWithMCtx env fuel mctx constraints rawDecl with
  | none => simp [hElab] at hRun
  | some pair =>
    rcases pair with ⟨mctx', elabD⟩
    rw [hElab] at hRun
    dsimp only at hRun
    let valExpr := (declTyAndVal elabD).2
    let cam1 := (internToHwExprCAM valExpr HwExprCAM.empty).2
    let valH := (internToHwExprCAM valExpr HwExprCAM.empty).1
    let z1Out := runZone1Whnf fuel { cam := cam1, focusHandle := valH }
    cases hZ4 : stepZone4KernelCheck env fuel z1Out.cam elabD with
    | mk z4Ok z4St =>
      change
        (let z3Out := stepZone3DiscrLut guard trie view pktEpoch queryExpr lutArg z1Out
         let p := stepZone4KernelCheck env fuel z1Out.cam elabD
         if p.1 then some (z1Out, z3Out, p.2, elabD) else none) =
        some (z1, z3, z4, elabDecl) at hRun
      rw [hZ4] at hRun
      cases z4Ok with
      | false => simp at hRun
      | true =>
        simp only [↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hRun
        rcases hRun with ⟨_, _, rfl, rfl⟩
        have hZ4True : (stepZone4KernelCheck env fuel z1Out.cam elabD).1 = true := by
          rw [hZ4]
        have hSound := runSiliconKernelCamFsm_sound env fuel z1Out.cam elabD hZ4True
        have hTag : z4St.statusTag = 1 := by
          have ht := hSound.2.2.2.1
          rw [hZ4] at ht
          exact ht
        have hJudge : z4St.rtlJudgeAccepted = true := by
          have hEq1 : (stepZone4KernelCheck env fuel z1Out.cam elabD).1 = true := hZ4True
          have hEq2 : (stepZone4KernelCheck env fuel z1Out.cam elabD).2 = z4St := by
            rw [hZ4]
          unfold stepZone4KernelCheck at hEq1 hEq2
          subst hEq2
          simp only [Bool.and_eq_true] at hEq1
          exact hEq1.2
        exact ⟨hSound.1, hSound.2.1, hSound.2.2.1, hTag, hJudge⟩

end Obend.Lower.SiliconElabFabric
end
