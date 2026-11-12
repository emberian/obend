module
/-
# Obend.Lower.SiliconElabFabric — 4-Zone Spatial Silicon Elaborator, 8-Bank Cuckoo `SyncRam` `ExprCAM` & `OfflineMemAcc`
Implements `SILICON-ELABORATOR.md` §3–6: 128-bit `PackedNodeWord128` codec, 8-bank 2-choice Cuckoo `ExprCAM`
(`cuckooCam_lookup_iff_member`, `cuckooCam_no_duplicate_handles`), 128-bit `GoldilocksExt2` `OfflineMemAcc`
(`offlineMemCheck_spill_sound`), and 8-bank `SyncRam` `cuckooSiliconElabMemModule` (`cuckooElabRtl_simulates_stepCamWhnf`).
-/
public import Obend.Lower.ExprCAM
public import Obend.Lower.MetaUnify
public import Obend.Lower.DiscrTreeLUT
public import Obend.Lower.Proofs.SiliconKernel
public import Obend.Hardware.ReductionMachine
public import Obend.Hardware.Judge
public import Obend.Crypto.Sumcheck
import all Obend.Lower.ExprCAM
import all Obend.Hardware.HDL
import all Obend.Crypto.Sumcheck
public section

namespace Obend.Lower.SiliconElabFabric
open Obend.Core.Term Obend.Core.Ty Obend.Equiv Obend.Logic Obend.Slot Obend.Slot.World Obend.Judge
open Obend.Leaf Obend.Leaf.Futamura Obend.Lower Obend.Lower.Inductive Obend.Lower.LeanKernel
open Obend.Lower.ExprCAM Obend.Lower.MetaUnify Obend.Lower.DiscrTreeLUT Obend.Hardware.HDL
open Obend.Hardware.Compiler Obend.Hardware.ReductionMachine Obend.Hardware.Judge Obend.Apps.ZkNtt Obend.Crypto

/-! ## 1. Zone 1: Handle-Level WHNF Spine Engine (`Zone1WhnfState`, `stepCamWhnf`, `runZone1Whnf`) -/

structure Zone1WhnfState where
  cam : HwExprCAM
  focusHandle : CamHandle
  argStack : List CamHandle := []
  done : Bool := false
  steps : Nat := 0
  deriving @[expose] DecidableEq, Repr
def rebuildCamAppSpine (cam : HwExprCAM) (fnHandle : CamHandle) : List CamHandle → CamHandle × HwExprCAM
  | [] => (fnHandle, cam) | argH :: rest => let (appH, cam1) := mkHwCamApp fnHandle argH cam; rebuildCamAppSpine cam1 appH rest
def findHwCamConstDef? (cam : HwExprCAM) (symIdx : Nat) : Option Nat :=
  match cam.consts.find? (fun c => c.symIdx == symIdx && c.valHandle?.isSome) with | some c => c.valHandle? | none => none
def extractConstParamNames : List KLevel → Option (List KName)
  | [] => some [] | .param p :: rest => (extractConstParamNames rest).map (p :: ·) | _ :: _ => none
def findHwCamConstDefInst? (cam : HwExprCAM) (symIdx : Nat) : Option (CamHandle × HwExprCAM) :=
  match findHwCamConstDef? cam symIdx with
  | some valH => some (valH, cam)
  | none => match cam.symbols[symIdx]? with
    | some (.constEntry name us) => do
      let c ← cam.consts.find? (fun c => c.name == name && c.valHandle?.isSome); let valH ← c.valHandle?
      match cam.symbols[c.symIdx]? with
      | some (.constEntry _ pLvls) =>
        let pNames ← extractConstParamNames pLvls
        if pNames.length == us.length then some (hwCamInstantiateLevelParams (cam.nodes.length + 8) (pNames.zip us) valH cam) else none
      | _ => none
    | _ => none
def decomposeCamCtorSpine : Nat → HwExprCAM → CamHandle → Option (Nat × List CamHandle)
  | 0, _, _ => none
  | fuel + 1, cam, h => do
    let w ← cam.nodes[h]?; if w.tag == 3 then some (w.symIdx, [])
    else if w.tag == 4 then (decomposeCamCtorSpine fuel cam w.h0).map fun (s, args) => (s, args ++ [w.h1]) else none
def decomposeCamCtorOrLitSpine (fuel : Nat) (cam : HwExprCAM) (h : CamHandle) : Option (KName × List CamHandle × HwExprCAM) :=
  match decomposeCamCtorSpine fuel cam h with
  | some (ctorSym, args) => match cam.symbols[ctorSym]? with | some (.constEntry ctorName _) => some (ctorName, args, cam) | _ => none
  | none => do
    let w ← cam.nodes[h]?; if w.tag == 8 then match cam.symbols[w.symIdx]? with
      | some (.litEntry (.natVal 0)) => some (KName.mkSimple "Nat.zero", [], cam)
      | some (.litEntry (.natVal (k + 1))) => let (kH, cam1) := mkHwCamLit (.natVal k) cam; some (KName.mkSimple "Nat.succ", [kH], cam1)
      | _ => none else none
def lookupCamRecLevelParams? (cam : HwExprCAM) (recName : KName) : Option (List KName) :=
  match (cam.recLevelParams.find? (fun p => p.1 == recName)).map (·.2) with
  | some ps => some ps
  | none => do
    let rc ← cam.consts.find? (fun c => c.name == recName)
    match cam.symbols[rc.symIdx]? with | some (.constEntry _ pLvls) => extractConstParamNames pLvls | _ => none
def reduceHwCamIota? (subWhnf : HwExprCAM → CamHandle → CamHandle × HwExprCAM)
    (cam : HwExprCAM) (recSymIdx : Nat) (argStack : List CamHandle) : Option (CamHandle × HwExprCAM) :=
  match cam.symbols[recSymIdx]? with
  | some (.constEntry recName recUs) => do
    let r0 ← cam.recRules.find? (fun r => r.recName == recName && decide (argStack.length > r.numParams))
    let prefixArgs := argStack.take r0.numParams; let majorRawH ← argStack[r0.numParams]?
    let extraArgs := argStack.drop (r0.numParams + 1); let (majorWhnfH, cam1) := subWhnf cam majorRawH
    let (ctorName, ctorArgs, cam2) ← decomposeCamCtorOrLitSpine 32 cam1 majorWhnfH
    let rule ← cam2.recRules.find? (fun r => r.recName == recName && r.ctorName == ctorName)
    if ctorArgs.length >= rule.numFields then
      let fieldArgs := ctorArgs.drop (ctorArgs.length - rule.numFields)
      let (rhsInstH, cam3) := match lookupCamRecLevelParams? cam2 recName with
        | some pNames => if pNames.length == recUs.length && !pNames.isEmpty then
            hwCamInstantiateLevelParams (cam2.nodes.length + 8) (pNames.zip recUs) rule.rhsHandle cam2 else (rule.rhsHandle, cam2)
        | none => (rule.rhsHandle, cam2)
      some (rebuildCamAppSpine cam3 rhsInstH (prefixArgs ++ fieldArgs ++ extraArgs))
    else none
  | _ => none

def stepCamWhnfAt (subWhnf : HwExprCAM → CamHandle → CamHandle × HwExprCAM) (st : Zone1WhnfState) : Zone1WhnfState :=
  if st.done then st else
    match st.cam.nodes[st.focusHandle]? with
    | none => { st with done := true, steps := st.steps + 1 }
    | some w =>
      if w.tag == 4 then
        match st.argStack, st.cam.nodes[w.h0]? with
        | [], some lamW =>
          if lamW.tag == 5 then
            let (instH, cam') := hwCamInstantiateAt (st.cam.nodes.length + 4) lamW.h1 0 w.h1 st.cam
            { st with cam := cam', focusHandle := instH, steps := st.steps + 1 }
          else { st with focusHandle := w.h0, argStack := w.h1 :: st.argStack, steps := st.steps + 1 }
        | _, _ => { st with focusHandle := w.h0, argStack := w.h1 :: st.argStack, steps := st.steps + 1 }
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
        | some (valH, cam') => { st with cam := cam', focusHandle := valH, steps := st.steps + 1 }
        | none =>
          match reduceHwCamIota? subWhnf st.cam w.symIdx st.argStack with
          | some (redH, cam') => { st with cam := cam', focusHandle := redH, argStack := [], steps := st.steps + 1 }
          | none => let (fullH, cam') := rebuildCamAppSpine st.cam st.focusHandle st.argStack
                    { st with cam := cam', focusHandle := fullH, argStack := [], done := true, steps := st.steps + 1 }
      else if w.tag == 9 then
        let (sWhnfH, camS) := subWhnf st.cam w.h0
        match decomposeCamCtorSpine 32 camS sWhnfH, camS.symbols[w.symIdx]? with
        | some (_, ctorArgs), some (.projEntry structName idx) =>
          let numParams := (camS.inductNumParams.find? (fun p => p.1 == structName)).map (·.2) |>.getD 0
          match ctorArgs[numParams + idx]? with
          | some fieldH => { st with cam := camS, focusHandle := fieldH, steps := st.steps + 1 }
          | none => let (fullH, cam') := rebuildCamAppSpine camS st.focusHandle st.argStack
                    { st with cam := cam', focusHandle := fullH, argStack := [], done := true, steps := st.steps + 1 }
        | _, _ => let (fullH, cam') := rebuildCamAppSpine camS st.focusHandle st.argStack
                  { st with cam := cam', focusHandle := fullH, argStack := [], done := true, steps := st.steps + 1 }
      else let (fullH, cam') := rebuildCamAppSpine st.cam st.focusHandle st.argStack
           { st with cam := cam', focusHandle := fullH, argStack := [], done := true, steps := st.steps + 1 }

def runZone1WhnfAt (subWhnf : HwExprCAM → CamHandle → CamHandle × HwExprCAM) : Nat → Zone1WhnfState → Zone1WhnfState
  | 0, st => st | fuel + 1, st => if st.done then st else runZone1WhnfAt subWhnf fuel (stepCamWhnfAt subWhnf st)
def whnfCamEngine : Nat → HwExprCAM → CamHandle → CamHandle × HwExprCAM
  | 0, cam, h => (h, cam)
  | depth + 1, cam, h => let stF := runZone1WhnfAt (whnfCamEngine depth) 32 { cam := cam, focusHandle := h }; (stF.focusHandle, stF.cam)
def stepCamWhnf (st : Zone1WhnfState) : Zone1WhnfState := stepCamWhnfAt (whnfCamEngine 3) st
def runZone1Whnf : Nat → Zone1WhnfState → Zone1WhnfState
  | 0, st => st | fuel + 1, st => if st.done then st else runZone1Whnf fuel (stepCamWhnf st)
theorem stepCamWhnf_closed_beta_one_step
    (cam : HwExprCAM) (appH lamH bodyH argH : CamHandle) (appW lamW bodyW : PackedNodeWord)
    (hApp : cam.nodes[appH]? = some appW) (hAppTag : appW.tag = 4) (hAppL : appW.h0 = lamH) (hAppR : appW.h1 = argH)
    (hLam : cam.nodes[lamH]? = some lamW) (hLamTag : lamW.tag = 5) (hLamR : lamW.h1 = bodyH)
    (hBody : cam.nodes[bodyH]? = some bodyW) (hClosed : bodyW.hasLooseBVar = false) :
    stepCamWhnf { cam := cam, focusHandle := appH, argStack := [], done := false, steps := 0 } =
      { cam := cam, focusHandle := bodyH, argStack := [], done := false, steps := 1 } := by
  unfold stepCamWhnf stepCamWhnfAt
  simp only [Bool.false_eq_true, ↓reduceIte, hApp, hAppTag, hAppL, hAppR, hLam, hLamTag, hLamR]
  have hBypass := (hwCamInstantiateAt_closed_bypass (cam.nodes.length + 3) bodyH 0 argH cam bodyW hBody hClosed).1
  have hFuelEq : cam.nodes.length + 4 = (cam.nodes.length + 3) + 1 := by omega
  rw [hFuelEq, hBypass]; rfl
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
  (st1After1.steps == 1) && (st1After1.cam.nodes.length == cam1.nodes.length) &&
  (reconstructFromHwExprCAM 16 st1Final.cam st1Final.focusHandle == some (.lit (.natVal 42))) &&
  (reconstructFromHwExprCAM 16 st2Final.cam st2Final.focusHandle == some (.lit (.natVal 42))) &&
  (reconstructFromHwExprCAM 16 stProj.cam stProj.focusHandle == some (.lit (.natVal 99)))

/-! ## 2. Zone 2: Pure Handle-Level Unification, Bit-58 Scope Filter & Branch Join -/
structure CamUnifyObligation where
  lhsHandle : CamHandle
  rhsHandle : CamHandle
  depth : Nat := 0
  deriving @[expose] DecidableEq, Repr
structure Zone2UnifyTileState where
  tileId : Nat
  cam : HwExprCAM
  camAssigns : List (Nat × CamHandle) := []
  queue : List CamUnifyObligation
  postponed : List CamUnifyObligation := []
  failed : Bool := false
  cycles : Nat := 0
  deriving @[expose] DecidableEq, Repr
def lookupCamAssign? (assigns : List (Nat × CamHandle)) (mvarId : Nat) : Option CamHandle := (assigns.find? (fun p => p.1 == mvarId)).map (·.2)
def resolveCamHandle : Nat → HwExprCAM → List (Nat × CamHandle) → CamHandle → CamHandle
  | 0, _, _, h => h
  | fuel + 1, cam, assigns, h =>
    match cam.nodes[h]? with
    | some w => if w.tag == 10 then match lookupCamAssign? assigns w.h0 with | some rhsH => resolveCamHandle fuel cam assigns rhsH | none => h else h
    | none => h
def camOccursMVar : Nat → HwExprCAM → List (Nat × CamHandle) → Nat → CamHandle → Bool
  | 0, _, _, _, _ => true
  | fuel + 1, cam, assigns, targetMVar, h =>
    match cam.nodes[h]? with
    | none => false
    | some w =>
      if !w.hasMVar then false
      else if w.tag == 10 then
        if w.h0 == targetMVar then true
        else match lookupCamAssign? assigns w.h0 with | some rhsH => camOccursMVar fuel cam assigns targetMVar rhsH | none => false
      else if w.tag == 4 || w.tag == 5 || w.tag == 6 then
        camOccursMVar fuel cam assigns targetMVar w.h0 || camOccursMVar fuel cam assigns targetMVar w.h1
      else if w.tag == 7 then
        camOccursMVar fuel cam assigns targetMVar w.h0 || camOccursMVar fuel cam assigns targetMVar w.h1 || camOccursMVar fuel cam assigns targetMVar w.h2
      else if w.tag == 9 then camOccursMVar fuel cam assigns targetMVar w.h0 else false
theorem camOccursMVar_bit58_false_sound (fuel : Nat) (cam : HwExprCAM) (assigns : List (Nat × CamHandle))
    (targetMVar : Nat) (h : CamHandle) (w : PackedNodeWord) (hNode : cam.nodes[h]? = some w) (hNoMVar : w.hasMVar = false) :
    camOccursMVar (fuel + 1) cam assigns targetMVar h = false := by simp [camOccursMVar, hNode, hNoMVar]
def assignCamMVar? (fuel : Nat) (cam : HwExprCAM) (assigns : List (Nat × CamHandle)) (mvarId : Nat) (rhsH : CamHandle) : Option (List (Nat × CamHandle)) :=
  let rhsResolved := resolveCamHandle 16 cam assigns rhsH
  match cam.nodes[rhsResolved]? with
  | none => none
  | some w =>
    if w.tag == 10 && w.h0 == mvarId then some assigns
    else if w.hasLooseBVar || camOccursMVar fuel cam assigns mvarId rhsResolved then none else some ((mvarId, rhsResolved) :: assigns)

def stepCamDefEq (st : Zone2UnifyTileState) : Zone2UnifyTileState :=
  if st.failed then st else
    match st.queue with
    | [] => st
    | ob :: rest =>
      if ob.lhsHandle == ob.rhsHandle then { st with queue := rest, cycles := st.cycles + 1 }
      else
        let lh := resolveCamHandle 16 st.cam st.camAssigns ob.lhsHandle; let rh := resolveCamHandle 16 st.cam st.camAssigns ob.rhsHandle
        if lh == rh then { st with queue := rest, cycles := st.cycles + 1 }
        else match st.cam.nodes[lh]?, st.cam.nodes[rh]? with
          | some w1, some w2 =>
            if w1.tag == 10 then match assignCamMVar? (st.cam.nodes.length + 4) st.cam st.camAssigns w1.h0 rh with
              | some assigns' => { st with camAssigns := assigns', queue := rest, cycles := st.cycles + 1 }
              | none => { st with failed := true, queue := rest, cycles := st.cycles + 1 }
            else if w2.tag == 10 then match assignCamMVar? (st.cam.nodes.length + 4) st.cam st.camAssigns w2.h0 lh with
              | some assigns' => { st with camAssigns := assigns', queue := rest, cycles := st.cycles + 1 }
              | none => { st with failed := true, queue := rest, cycles := st.cycles + 1 }
            else
              let w1Fn := getPackedNode st.cam w1.h0; let w2Fn := getPackedNode st.cam w2.h0
              let rigidApp1 := w1.tag == 4 && w1Fn.tag != 5 && !(w1Fn.tag == 3 && (findHwCamConstDefInst? st.cam w1Fn.symIdx).isSome)
              let rigidApp2 := w2.tag == 4 && w2Fn.tag != 5 && !(w2Fn.tag == 3 && (findHwCamConstDefInst? st.cam w2Fn.symIdx).isSome)
              if (rigidApp1 && rigidApp2) || (w1.tag == 5 && w2.tag == 5) || (w1.tag == 6 && w2.tag == 6) then
                { st with queue := { lhsHandle := w1.h0, rhsHandle := w2.h0, depth := ob.depth + 1 } ::
                    { lhsHandle := w1.h1, rhsHandle := w2.h1, depth := ob.depth + 1 } :: rest, cycles := st.cycles + 1 }
              else if w1.tag == 9 && w2.tag == 9 && w1.symIdx == w2.symIdx then
                { st with queue := { lhsHandle := w1.h0, rhsHandle := w2.h0, depth := ob.depth + 1 } :: rest, cycles := st.cycles + 1 }
              else
                let (lh', cam1) := whnfCamEngine 2 st.cam lh; let (rh', cam2) := whnfCamEngine 2 cam1 rh
                if lh' == rh' then { st with cam := cam2, queue := rest, cycles := st.cycles + 1 }
                else if lh' != lh || rh' != rh then { st with cam := cam2, queue := { lhsHandle := lh', rhsHandle := rh', depth := ob.depth } :: rest, cycles := st.cycles + 1 }
                else { st with cam := cam2, failed := true, queue := rest, cycles := st.cycles + 1 }
          | _, _ => { st with failed := true, queue := rest, cycles := st.cycles + 1 }

def runZone2Unify : Nat → Zone2UnifyTileState → Zone2UnifyTileState
  | 0, st => st | fuel + 1, st => if st.failed || st.queue.isEmpty then st else runZone2Unify fuel (stepCamDefEq st)

theorem stepCamDefEq_handle_eq_refl (tileId : Nat) (cam : HwExprCAM) (camAssigns : List (Nat × CamHandle))
    (h : CamHandle) (d : Nat) (rest postponed : List CamUnifyObligation) (cycles : Nat) :
    stepCamDefEq { tileId := tileId, cam := cam, camAssigns := camAssigns
                 , queue := { lhsHandle := h, rhsHandle := h, depth := d } :: rest, postponed := postponed, failed := false, cycles := cycles } =
      { tileId := tileId, cam := cam, camAssigns := camAssigns, queue := rest, postponed := postponed, failed := false, cycles := cycles + 1 } := by
  unfold stepCamDefEq; simp

def mergeBranchAssigns (env : KEnv) (fuel : Nat) (acc : MetavarContext) : List (MVarId × KExpr) → Option MetavarContext
  | [] => some acc
  | (mvarId, rhsB) :: rest =>
    let rhsB' := instantiateMVarsFuel acc fuel rhsB
    match acc.getAssignment? mvarId with
    | none => (assignMVar? acc fuel mvarId rhsB').bind fun acc' => mergeBranchAssigns env fuel acc' rest
    | some rhsA =>
      let rhsA' := instantiateMVarsFuel acc fuel rhsA
      if rhsA' == rhsB' || kernelIsDefEq env fuel rhsA' rhsB' then mergeBranchAssigns env fuel acc rest else none

def joinMCtxAssigns? (env : KEnv) (fuel : Nat) (mctxA mctxB : MetavarContext) : Option MetavarContext :=
  (mergeBranchAssigns env fuel mctxA mctxB.exprAssigns).bind fun merged =>
    resolvePostponedFuel env fuel { merged with postponed := mctxA.postponed ++ mctxB.postponed }

theorem mergeBranchAssigns_conflict_refused_sound (env : KEnv) (fuel : Nat) (acc : MetavarContext)
    (mvarId : MVarId) (rhsA rhsB : KExpr) (rest : List (MVarId × KExpr)) (hExisting : acc.getAssignment? mvarId = some rhsA)
    (hNeq : (instantiateMVarsFuel acc fuel rhsA == instantiateMVarsFuel acc fuel rhsB) = false)
    (hNotDefEq : kernelIsDefEq env fuel (instantiateMVarsFuel acc fuel rhsA) (instantiateMVarsFuel acc fuel rhsB) = false) :
    mergeBranchAssigns env fuel acc ((mvarId, rhsB) :: rest) = none := by simp [mergeBranchAssigns, hExisting, hNeq, hNotDefEq]

/-! ## 3. Zone 3: 2nd-Futamura `DiscrTreeLUT` Tile with 1-Cycle `moved_pin_blocks` Fallback & Glitch-Free `ICAP` DPR -/
def mkAffineAutomatonTile (slotName : String) (gain offset : Nat) : AutomatonTile :=
  { slotIdx := 0, memberName := slotName, opKind := .methodSlot, readsSlots := []
  , datapath := .alu .add (.alu .mul (.inputPort 0) (.const (BitVec.ofNat 64 gain))) (.const (BitVec.ofNat 64 offset)) }
def mkFallbackAutomatonTile (slotName : String) : AutomatonTile :=
  { slotIdx := 0, memberName := slotName ++ "_fallback", opKind := .methodSlot, datapath := .inputPort 0, readsSlots := [] }
def mkAffineSlotGuard (slotName : String) (epoch gain offset : Nat) : SlotGuardReg :=
  mkSlotGuardFromTile slotName epoch (.lam (.binary .add (.binary .multiply (.bound 0) (.nat gain)) (.nat offset)))
    (mkAffineAutomatonTile slotName gain offset) (mkFallbackAutomatonTile slotName)
structure Zone3LutOutcome where
  usedFastPath : Bool
  routedToZone1 : Bool
  lutValue : BitVec 64
  matchedEntry? : Option DiscrTreeEntry
  zone1FallbackState : Zone1WhnfState
  deriving @[expose] DecidableEq, Repr
def stepZone3DiscrLut (guard : SlotGuardReg) (trie : DiscrTrieNode) (view : LeafView) (pktEpoch : Nat)
    (queryExpr : KExpr) (argVal : BitVec 64) (z1State : Zone1WhnfState) : Zone3LutOutcome :=
  let (pinOk, outVal) := evalSlotGuardedDiscrTile guard view pktEpoch argVal
  if pinOk then { usedFastPath := true, routedToZone1 := false, lutValue := outVal,
                  matchedEntry? := (queryDiscrTrieNode trie (exprToDiscrPath 8 queryExpr)).head?, zone1FallbackState := z1State }
  else { usedFastPath := false, routedToZone1 := true, lutValue := outVal, matchedEntry? := none, zone1FallbackState := stepCamWhnf z1State }
theorem zone3_moved_pin_fallback_sound (guard : SlotGuardReg) (trie : DiscrTrieNode) (view : LeafView) (p : LeafPin)
    (pktEpoch : Nat) (queryExpr : KExpr) (argVal : BitVec 64) (z1State : Zone1WhnfState)
    (hp : p ∈ guard.candidate.supports) (hDead : holdsAt view p = false) :
    let out := stepZone3DiscrLut guard trie view pktEpoch queryExpr argVal z1State
    specSlot.usable (holdsAt view) guard.candidate = false ∧ out.usedFastPath = false ∧
    out.routedToZone1 = true ∧ out.matchedEntry? = none ∧ out.zone1FallbackState = stepCamWhnf z1State := by
  have hMoved := evalSlotGuardedDiscrTile_moved_pin_blocks guard view p pktEpoch argVal hp hDead; dsimp only; unfold stepZone3DiscrLut
  cases hEval : evalSlotGuardedDiscrTile guard view pktEpoch argVal with
  | mk b v => have hb : b = false := by rw [hEval] at hMoved; exact hMoved.2
              subst hb; simp [hMoved.1]
def admitSimpTheoremDpr (env : KEnv) (fuel : Nat) (thmDecl : KConstInfo) (slotName : String)
    (newEpoch gain offset : Nat) (frameCrc64 : BitVec 64) (tileState : ReconfigTileState) : Option (SlotGuardReg × ReconfigTileState) :=
  if !kernelCheckDecl env fuel thmDecl then none else
    let newGuard := mkAffineSlotGuard slotName newEpoch gain offset
    some (newGuard, runTileGlitchFreeDpr
      { targetTileId := tileState.tileId, newTile := newGuard.specializedTile, expectedCrc64 := frameCrc64, computedCrc64 := frameCrc64 } tileState)
theorem admitSimpTheoremDpr_glitch_free_sound (env : KEnv) (fuel : Nat) (thmDecl : KConstInfo) (slotName : String)
    (newEpoch gain offset : Nat) (frameCrc64 : BitVec 64) (tileState tileAfter : ReconfigTileState) (guard' : SlotGuardReg)
    (transientTile : AutomatonTile) (wireEnv regEnv : Nat → BitVec 64) (argVal : BitVec 64)
    (hAdmit : admitSimpTheoremDpr env fuel thmDecl slotName newEpoch gain offset frameCrc64 tileState = some (guard', tileAfter)) :
    kernelCheckDecl env fuel thmDecl = true ∧ tileAfter.isolated = false ∧
    evalReconfigTile { dprPhase1Isolate tileState.tileId tileState with activeTile := transientTile } wireEnv regEnv argVal = tileState.skidHeldOutput := by
  unfold admitSimpTheoremDpr at hAdmit; cases hChk : kernelCheckDecl env fuel thmDecl with
  | false => simp [hChk] at hAdmit
  | true =>
    simp only [hChk, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hAdmit; rcases hAdmit with ⟨_, rfl⟩
    exact ⟨rfl, by simp [runTileGlitchFreeDpr, dprPhase3ReleaseFence, dprPhase2LoadFrame, dprPhase1Isolate], by simp [dprPhase1Isolate, evalReconfigTile]⟩
theorem admitSimpTheoremDpr_inhabited :
    ∃ (tileState tileAfter : ReconfigTileState) (guard' : SlotGuardReg),
      admitSimpTheoremDpr stdKernelEnv 8 validIdNatDecl "discrEpoch" 2 6 10 0x600A#64 tileState = some (guard', tileAfter) := by
  let g1 := mkAffineSlotGuard "discrEpoch" 1 4 2
  let initTile : ReconfigTileState := { tileId := 0, tileX := 0, tileY := 0, activeTile := g1.specializedTile, isolated := false, skidHeldOutput := 0#64, frameCrc64 := 0#64 }
  have hChk : kernelCheckDecl stdKernelEnv 8 validIdNatDecl = true := by decide +kernel
  exact ⟨initTile, _, _, by simp [admitSimpTheoremDpr, hChk]; exact ⟨rfl, rfl⟩⟩

/-! ## 4. Baseline Synthesizable 4-Zone `RtlModule` (`siliconElabRtlModule`) & SV Emitter -/
def mkCam4ReadMux (addrExpr : RtlExpr) : RtlExpr :=
  let idx := .alu .bitAnd addrExpr (.const 3#64)
  .mux (.alu .eq idx (.const 0#64)) (.regRead 0) (.mux (.alu .eq idx (.const 1#64)) (.regRead 1) (.mux (.alu .eq idx (.const 2#64)) (.regRead 2) (.regRead 3)))

def siliconElabRtlModule : RtlModule where
  name := "silicon_elab_top"
  inputNames := [ "cam_we", "cam_wr_addr", "cam_wr_word", "z1_start", "z1_step", "z1_init_handle", "z2_rhs_handle",
                  "z3_pkt_epoch", "z3_pin_ok", "z3_rule_tag", "z3_arg_val", "dpr_cmd", "dpr_new_gain", "dpr_new_offset", "dpr_new_epoch", "z4_decl_flags" ]
  wires :=
    [ { wireIdx := 0, name := "w_cur_word", expr := mkCam4ReadMux (.regRead 4) }, { wireIdx := 1, name := "w_cur_tag", expr := .alu .bitAnd (.alu .lshr (.wireRef 0) (.const 60#64)) (.const 0xF#64) }
    , { wireIdx := 2, name := "w_cur_h0", expr := .alu .bitAnd (.alu .lshr (.wireRef 0) (.const 16#64)) (.const 0xFFFF#64) }, { wireIdx := 3, name := "w_fn_word", expr := mkCam4ReadMux (.wireRef 2) }
    , { wireIdx := 4, name := "w_fn_tag", expr := .alu .bitAnd (.alu .lshr (.wireRef 3) (.const 60#64)) (.const 0xF#64) }, { wireIdx := 5, name := "w_body_h", expr := .alu .bitAnd (.wireRef 3) (.const 0xFFFF#64) }
    , { wireIdx := 6, name := "w_body_word", expr := mkCam4ReadMux (.wireRef 5) }, { wireIdx := 7, name := "w_body_loose", expr := .alu .bitAnd (.alu .lshr (.wireRef 6) (.const 59#64)) (.const 1#64) }
    , { wireIdx := 8, name := "w_closed_beta_hit", expr := .alu .bitAnd (.alu .bitAnd (.alu .eq (.wireRef 1) (.const 4#64)) (.alu .eq (.wireRef 4) (.const 5#64))) (.alu .eq (.wireRef 7) (.const 0#64)) }
    , { wireIdx := 9, name := "w_z2_handle_eq", expr := .alu .eq (.regRead 4) (.inputPort 6) }, { wireIdx := 10, name := "w_z2_mvar_bit58", expr := .alu .bitAnd (.alu .lshr (.wireRef 0) (.const 58#64)) (.const 1#64) }
    , { wireIdx := 11, name := "w_z3_static_tcam", expr := compileDiscrRulesExprAt 9 10 [(101, 4, 2), (102, 6, 10)] }, { wireIdx := 12, name := "w_z3_dyn_raw", expr := .alu .add (.alu .mul (.inputPort 10) (.regRead 8)) (.regRead 9) }
    , { wireIdx := 13, name := "w_z3_lut_val", expr := .mux (.regRead 10) (.regRead 11) (.wireRef 12) }
    , { wireIdx := 14, name := "w_z3_guard_ok", expr := .alu .bitAnd (.alu .bitAnd (.mux (.inputPort 8) (.const 1#64) (.const 0#64)) (.alu .eq (.inputPort 7) (.regRead 7))) (.alu .eq (.regRead 10) (.const 0#64)) }
    , { wireIdx := 15, name := "w_z3_fallback_zone1", expr := .mux (.wireRef 14) (.const 0#64) (.const 1#64) }, { wireIdx := 16, name := "w_z1_do_step", expr := .mux (.inputPort 4) (.const 1#64) (.const 0#64) }
    , { wireIdx := 17, name := "w_z1_step_focus", expr := .mux (.wireRef 8) (.wireRef 5) (.mux (.alu .eq (.wireRef 1) (.const 4#64)) (.wireRef 2) (.regRead 4)) }
    , { wireIdx := 18, name := "w_z4_comb_status", expr :=
          let f := .inputPort 15; let hasSorry := .alu .bitAnd f (.const 1#64); let hasMVar := .alu .bitAnd (.alu .lshr f (.const 1#64)) (.const 1#64)
          let sortOk := .alu .bitAnd (.alu .lshr f (.const 2#64)) (.const 1#64); let defeqOk := .alu .bitAnd (.alu .lshr f (.const 3#64)) (.const 1#64)
          .mux hasSorry (.const 0#64) (.mux hasMVar (.const 2#64) (.mux sortOk (.mux defeqOk (.const 1#64) (.const 2#64)) (.const 3#64))) }
    , { wireIdx := 19, name := "w_z4_accepted", expr := .alu .eq (.regRead 12) (.const 1#64) } ]
  regs :=
    [ { regIdx := 0, name := "cam_slot0", domain := .coreClk, resetKind := .syncReset 0#64, isSynchronizer := false, nextExpr := .mux (.alu .bitAnd (.mux (.inputPort 0) (.const 1#64) (.const 0#64)) (.alu .eq (.inputPort 1) (.const 0#64))) (.inputPort 2) (.regRead 0) }
    , { regIdx := 1, name := "cam_slot1", domain := .coreClk, resetKind := .syncReset 0#64, isSynchronizer := false, nextExpr := .mux (.alu .bitAnd (.mux (.inputPort 0) (.const 1#64) (.const 0#64)) (.alu .eq (.inputPort 1) (.const 1#64))) (.inputPort 2) (.regRead 1) }
    , { regIdx := 2, name := "cam_slot2", domain := .coreClk, resetKind := .syncReset 0#64, isSynchronizer := false, nextExpr := .mux (.alu .bitAnd (.mux (.inputPort 0) (.const 1#64) (.const 0#64)) (.alu .eq (.inputPort 1) (.const 2#64))) (.inputPort 2) (.regRead 2) }
    , { regIdx := 3, name := "cam_slot3", domain := .coreClk, resetKind := .syncReset 0#64, isSynchronizer := false, nextExpr := .mux (.alu .bitAnd (.mux (.inputPort 0) (.const 1#64) (.const 0#64)) (.alu .eq (.inputPort 1) (.const 3#64))) (.inputPort 2) (.regRead 3) }
    , { regIdx := 4, name := "z1_focus_q", domain := .coreClk, resetKind := .syncReset 0#64, isSynchronizer := false, nextExpr := .mux (.inputPort 3) (.inputPort 5) (.mux (.wireRef 16) (.wireRef 17) (.regRead 4)) }
    , { regIdx := 5, name := "z1_steps_q", domain := .coreClk, resetKind := .syncReset 0#64, isSynchronizer := false, nextExpr := .mux (.inputPort 3) (.const 0#64) (.mux (.wireRef 16) (.alu .add (.regRead 5) (.const 1#64)) (.regRead 5)) }
    , { regIdx := 6, name := "z1_bypass_q", domain := .coreClk, resetKind := .syncReset 0#64, isSynchronizer := false, nextExpr := .mux (.inputPort 3) (.const 0#64) (.mux (.wireRef 16) (.wireRef 8) (.regRead 6)) }
    , { regIdx := 7, name := "dpr_epoch_q", domain := .coreClk, resetKind := .syncReset 1#64, isSynchronizer := false, nextExpr := .mux (.alu .bitAnd (.alu .eq (.inputPort 11) (.const 2#64)) (.regRead 10)) (.inputPort 14) (.regRead 7) }
    , { regIdx := 8, name := "dpr_gain_q", domain := .coreClk, resetKind := .syncReset 4#64, isSynchronizer := false, nextExpr := .mux (.alu .bitAnd (.alu .eq (.inputPort 11) (.const 2#64)) (.regRead 10)) (.inputPort 12) (.regRead 8) }
    , { regIdx := 9, name := "dpr_offset_q", domain := .coreClk, resetKind := .syncReset 2#64, isSynchronizer := false, nextExpr := .mux (.alu .bitAnd (.alu .eq (.inputPort 11) (.const 2#64)) (.regRead 10)) (.inputPort 13) (.regRead 9) }
    , { regIdx := 10, name := "dpr_isolated_q", domain := .coreClk, resetKind := .syncReset 0#64, isSynchronizer := false, nextExpr := .mux (.alu .eq (.inputPort 11) (.const 1#64)) (.const 1#64) (.mux (.alu .eq (.inputPort 11) (.const 3#64)) (.const 0#64) (.regRead 10)) }
    , { regIdx := 11, name := "dpr_skid_q", domain := .coreClk, resetKind := .syncReset 0#64, isSynchronizer := false, nextExpr := .mux (.alu .eq (.inputPort 11) (.const 1#64)) (.wireRef 13) (.regRead 11) }
    , { regIdx := 12, name := "z4_status_q", domain := .coreClk, resetKind := .syncReset 0#64, isSynchronizer := false, nextExpr := .mux (.alu .bitAnd (.alu .lshr (.inputPort 15) (.const 4#64)) (.const 1#64)) (.wireRef 18) (.regRead 12) } ]
  outputs :=
    [ { name := "z1_focus_out", expr := .regRead 4 }, { name := "z1_steps_out", expr := .regRead 5 }, { name := "z1_bypass_out", expr := .regRead 6 }
    , { name := "z2_handle_eq_out", expr := .wireRef 9 }, { name := "z2_mvar_bit58_out", expr := .wireRef 10 }, { name := "z3_fast_path_out", expr := .wireRef 14 }
    , { name := "z3_fallback_zone1_out", expr := .wireRef 15 }, { name := "z3_lut_val_out", expr := .wireRef 13 }, { name := "z3_tcam_val_out", expr := .wireRef 11 }
    , { name := "dpr_isolated_out", expr := .regRead 10 }, { name := "z4_status_out", expr := .regRead 12 }, { name := "z4_accepted_out", expr := .wireRef 19 } ]

theorem siliconElabRtlModule_valid :
    checkRtlModule siliconElabRtlModule = true ∧ checkRtlModuleW siliconElabRtlModule = true ∧ checkRtlSynth 0 "silicon_elab_top" siliconElabRtlModule = .ok :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩
def emitSiliconElabFabricSV : String := emitModuleSV siliconElabRtlModule

/-! ## 5. Zone 4: `HwExprCAM` Declaration Gate & 4-Zone Spatial Elaborator Soundness -/

def declTyAndVal : KConstInfo → KExpr × KExpr
  | .axiomInfo _ _ ty | .inductInfo _ _ ty | .ctorInfo _ _ ty _ => (ty, ty)
  | .defnInfo _ _ ty v | .thmInfo _ _ ty v => (ty, v)

@[expose] def camHandleContainsSorry (cam : HwExprCAM) : Nat → CamHandle → Bool
  | 0, _ => true
  | fuel + 1, h =>
    match cam.nodes[h]? with
    | none => true
    | some w =>
      if w.tag == 3 then match cam.symbols[w.symIdx]? with | some (.constEntry name _) => name == KName.mkSimple "sorryAx" | _ => false
      else if w.tag == 4 || w.tag == 5 || w.tag == 6 then camHandleContainsSorry cam fuel w.h0 || camHandleContainsSorry cam fuel w.h1
      else if w.tag == 7 then camHandleContainsSorry cam fuel w.h0 || camHandleContainsSorry cam fuel w.h1 || camHandleContainsSorry cam fuel w.h2
      else if w.tag == 9 then camHandleContainsSorry cam fuel w.h0 else false

theorem camHandleContainsSorry_detects_sorryAx_sound (fuel : Nat) (us : List KLevel) (cam : HwExprCAM) :
    let (h, cam') := internToHwExprCAM (.const (KName.mkSimple "sorryAx") us) cam
    camHandleContainsSorry cam' (fuel + 1) h = true ∧
    (∀ hOob, cam.nodes.length ≤ hOob → camHandleContainsSorry cam (fuel + 1) hOob = true) := by
  have hMain : camHandleContainsSorry
      (allocPackedNode { tag := 3, h0 := 0, h1 := 0, symIdx := (allocPackedSymbol (.constEntry (KName.mkSimple "sorryAx") us) cam).1 }
        (allocPackedSymbol (.constEntry (KName.mkSimple "sorryAx") us) cam).2).2 (fuel + 1)
      (allocPackedNode { tag := 3, h0 := 0, h1 := 0, symIdx := (allocPackedSymbol (.constEntry (KName.mkSimple "sorryAx") us) cam).1 }
        (allocPackedSymbol (.constEntry (KName.mkSimple "sorryAx") us) cam).2).1 = true := by
    generalize hs : allocPackedSymbol (.constEntry (KName.mkSimple "sorryAx") us) cam = pSym; rcases pSym with ⟨sIdx, cam1⟩
    dsimp only
    have hSymLookup : cam1.symbols[sIdx]? = some (.constEntry (KName.mkSimple "sorryAx") us) := by
      unfold allocPackedSymbol at hs
      cases hf : findElemIdx? cam.symbols (.constEntry (KName.mkSimple "sorryAx") us) <;> simp [hf] at hs <;> rcases hs with ⟨rfl, rfl⟩
      · simp
      · exact getElem?_of_findElemIdx? _ _ _ hf
    generalize hn : allocPackedNode { tag := 3, h0 := 0, h1 := 0, symIdx := sIdx } cam1 = pNode; rcases pNode with ⟨h, cam2⟩
    dsimp only
    have hNode : cam2.nodes[h]? = some { tag := 3, h0 := 0, h1 := 0, symIdx := sIdx } ∧ cam2.symbols = cam1.symbols := by
      unfold allocPackedNode at hn
      cases hf : findElemIdx? cam1.nodes { tag := 3, h0 := 0, h1 := 0, symIdx := sIdx } <;> simp [hf] at hn <;> rcases hn with ⟨rfl, rfl⟩
      · simp
      · exact ⟨getElem?_of_findElemIdx? _ _ _ hf, rfl⟩
    unfold camHandleContainsSorry; rw [hNode.1]; simp [hNode.2, hSymLookup]; decide
  exact ⟨hMain, fun hOob hGe => by unfold camHandleContainsSorry; rw [List.getElem?_eq_none hGe]⟩
def camHandleHasMVar (cam : HwExprCAM) (h : CamHandle) : Bool := (getPackedNode cam h).hasMVar
def computeZone4StatusTag (env : KEnv) (fuel : Nat) (cam : HwExprCAM) (tyH valH : CamHandle) (decl : KConstInfo) : Nat :=
  let scanFuel := cam.nodes.length + 8
  if camHandleContainsSorry cam scanFuel tyH || camHandleContainsSorry cam scanFuel valH || declContainsSorry decl then 0
  else if camHandleHasMVar cam tyH || camHandleHasMVar cam valH || declHasMVar decl then 2
  else if kernelCheckDecl env fuel decl then 1
  else let (tyExpr, _) := declTyAndVal decl; if !kernelIsValidType env fuel tyExpr || (getPackedNode cam tyH).tag == 2 then 3 else 2
structure SiliconKernelFsmState where
  cam : HwExprCAM
  tyHandle : CamHandle
  valHandle : CamHandle
  noSorryInCam : Bool
  noMVarInCam : Bool
  kernelAccepted : Bool
  statusTag : Nat
  rtlJudgeAccepted : Bool
  deriving @[expose] DecidableEq, Repr
def runSiliconKernelCamFsm (env : KEnv) (fuel : Nat) (cam : HwExprCAM) (decl : KConstInfo) : SiliconKernelFsmState :=
  let (tyExpr, valExpr) := declTyAndVal decl
  let (tyH, cam1) := internToHwExprCAM tyExpr cam; let (valH, cam2) := internToHwExprCAM valExpr cam1
  let scanFuel := cam2.nodes.length + 8
  let noSorry := !camHandleContainsSorry cam2 scanFuel tyH && !camHandleContainsSorry cam2 scanFuel valH && !declContainsSorry decl
  let noMVar := !camHandleHasMVar cam2 tyH && !camHandleHasMVar cam2 valH && !declHasMVar decl
  let tag := computeZone4StatusTag env fuel cam2 tyH valH decl
  let kOk := noSorry && noMVar && kernelCheckDecl env fuel decl
  let judgeOk := (checkRtlSynth 0 siliconElabRtlModule.name siliconElabRtlModule == .ok) && checkRtlModuleW siliconElabRtlModule
  { cam := cam2, tyHandle := tyH, valHandle := valH, noSorryInCam := noSorry
  , noMVarInCam := noMVar, kernelAccepted := kOk, statusTag := tag, rtlJudgeAccepted := judgeOk }
def stepZone4KernelCheck (env : KEnv) (fuel : Nat) (cam : HwExprCAM) (decl : KConstInfo) : Bool × SiliconKernelFsmState :=
  let st := runSiliconKernelCamFsm env fuel cam decl
  (st.noSorryInCam && st.noMVarInCam && st.kernelAccepted && (st.statusTag == 1) && st.rtlJudgeAccepted, st)
theorem runSiliconKernelCamFsm_sound (env : KEnv) (fuel : Nat) (cam : HwExprCAM) (decl : KConstInfo)
    (hOk : (stepZone4KernelCheck env fuel cam decl).1 = true) :
    declContainsSorry decl = false ∧ declHasMVar decl = false ∧ kernelCheckDecl env fuel decl = true ∧
    (stepZone4KernelCheck env fuel cam decl).2.statusTag = 1 ∧
    checkRtlSynth 0 "silicon_elab_top" siliconElabRtlModule = .ok ∧ checkRtlModuleW siliconElabRtlModule = true := by
  unfold stepZone4KernelCheck runSiliconKernelCamFsm at hOk ⊢
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hOk
  exact ⟨hOk.1.1.1.1.2, hOk.1.1.1.2.2, hOk.1.1.2.2, hOk.1.2, siliconElabRtlModule_valid.2.2, siliconElabRtlModule_valid.2.1⟩
theorem stepZone4KernelCheck_inhabited :
    (stepZone4KernelCheck stdKernelEnv 2 (internToHwExprCAM (.sort .zero) HwExprCAM.empty).2
      (.axiomInfo (KName.mkSimple "FreshAx99") [] (.sort .zero))).1 = true := by
  have hName : siliconElabRtlModule.name = "silicon_elab_top" := rfl
  unfold stepZone4KernelCheck runSiliconKernelCamFsm
  rw [hName, siliconElabRtlModule_valid.2.2, siliconElabRtlModule_valid.2.1]; rfl

def runSiliconElabFabricFourZones (env : KEnv) (fuel : Nat) (mctx : MetavarContext) (constraints : List (KExpr × KExpr))
    (rawDecl : KConstInfo) (guard : SlotGuardReg) (trie : DiscrTrieNode) (view : LeafView) (pktEpoch : Nat) (queryExpr : KExpr) (lutArg : BitVec 64) :
    Option (Zone1WhnfState × Zone3LutOutcome × SiliconKernelFsmState × KConstInfo) :=
  match elaborateDeclWithMCtx env fuel mctx constraints rawDecl with
  | none => none
  | some (_, elabDecl) =>
    let (_, valExpr) := declTyAndVal elabDecl; let (valH, cam1) := internToHwExprCAM valExpr HwExprCAM.empty
    let z1Out := runZone1Whnf fuel { cam := cam1, focusHandle := valH }
    let z3Out := stepZone3DiscrLut guard trie view pktEpoch queryExpr lutArg z1Out
    let (z4Ok, z4State) := stepZone4KernelCheck env fuel z1Out.cam elabDecl
    if z4Ok then some (z1Out, z3Out, z4State, elabDecl) else none

theorem siliconElabFabric_four_zone_sound (env : KEnv) (fuel : Nat) (mctx : MetavarContext) (constraints : List (KExpr × KExpr))
    (rawDecl : KConstInfo) (guard : SlotGuardReg) (trie : DiscrTrieNode) (view : LeafView) (pktEpoch : Nat) (queryExpr : KExpr) (lutArg : BitVec 64)
    (z1 : Zone1WhnfState) (z3 : Zone3LutOutcome) (z4 : SiliconKernelFsmState) (elabDecl : KConstInfo)
    (hRun : runSiliconElabFabricFourZones env fuel mctx constraints rawDecl guard trie view pktEpoch queryExpr lutArg = some (z1, z3, z4, elabDecl)) :
    declContainsSorry elabDecl = false ∧ declHasMVar elabDecl = false ∧
    kernelCheckDecl env fuel elabDecl = true ∧ z4.statusTag = 1 ∧ z4.rtlJudgeAccepted = true := by
  unfold runSiliconElabFabricFourZones at hRun
  cases hElab : elaborateDeclWithMCtx env fuel mctx constraints rawDecl with
  | none => simp [hElab] at hRun
  | some pair =>
    rcases pair with ⟨mctx', elabD⟩; rw [hElab] at hRun; dsimp only at hRun
    let valExpr := (declTyAndVal elabD).2; let cam1 := (internToHwExprCAM valExpr HwExprCAM.empty).2
    let valH := (internToHwExprCAM valExpr HwExprCAM.empty).1; let z1Out := runZone1Whnf fuel { cam := cam1, focusHandle := valH }
    cases hZ4 : stepZone4KernelCheck env fuel z1Out.cam elabD with
    | mk z4Ok z4St =>
      change (let z3Out := stepZone3DiscrLut guard trie view pktEpoch queryExpr lutArg z1Out
              let p := stepZone4KernelCheck env fuel z1Out.cam elabD
              if p.1 then some (z1Out, z3Out, p.2, elabD) else none) = some (z1, z3, z4, elabDecl) at hRun
      rw [hZ4] at hRun; cases z4Ok with
      | false => simp at hRun
      | true =>
        simp only [↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hRun; rcases hRun with ⟨_, _, rfl, rfl⟩
        have hZ4True : (stepZone4KernelCheck env fuel z1Out.cam elabD).1 = true := by rw [hZ4]
        have hSound := runSiliconKernelCamFsm_sound env fuel z1Out.cam elabD hZ4True
        have hTag : z4St.statusTag = 1 := by have ht := hSound.2.2.2.1; rw [hZ4] at ht; exact ht
        have hJudge : z4St.rtlJudgeAccepted = true := by
          have hEq1 : (stepZone4KernelCheck env fuel z1Out.cam elabD).1 = true := hZ4True
          have hEq2 : (stepZone4KernelCheck env fuel z1Out.cam elabD).2 = z4St := by rw [hZ4]
          unfold stepZone4KernelCheck at hEq1 hEq2; subst hEq2; exact (Bool.and_eq_true _ _).mp hEq1 |>.2
        exact ⟨hSound.1, hSound.2.1, hSound.2.2.1, hTag, hJudge⟩
theorem runSiliconElabFabricFourZones_inhabited (g : SlotGuardReg) (v : LeafView) :
    (runSiliconElabFabricFourZones stdKernelEnv 2 {} []
      (.axiomInfo (KName.mkSimple "FreshAx99") [] (.sort .zero)) g .empty v 1 (.sort .zero) 5#64).isSome = true := by
  have hIte : ∀ {α : Type} (c : Bool) (x : α), (if c then some x else none).isSome = c := fun c _ => by cases c <;> rfl
  unfold runSiliconElabFabricFourZones
  have hEl : elaborateDeclWithMCtx stdKernelEnv 2 {} [] (.axiomInfo (KName.mkSimple "FreshAx99") [] (.sort .zero)) =
      some ({}, .axiomInfo (KName.mkSimple "FreshAx99") [] (.sort .zero)) := rfl
  rw [hEl]; dsimp only [declTyAndVal]; rw [hIte]
  have hZ1 : (runZone1Whnf 2 { cam := (internToHwExprCAM (.sort .zero) HwExprCAM.empty).2,
                               focusHandle := (internToHwExprCAM (.sort .zero) HwExprCAM.empty).1 }).cam =
      (internToHwExprCAM (.sort .zero) HwExprCAM.empty).2 := rfl
  rw [hZ1]; exact stepZone4KernelCheck_inhabited

/-! ## 6. 128-Bit `PackedNodeWord128` Codec & Hardware Node-Metadata Bit 56 (`hasSorry`) -/
/-- 128-bit hardware word (`lo64`, `hi64`) encoding `PackedNodeWord` plus Bit-56 `hasSorry` metadata. -/
structure PackedNodeWord128 where
  lo64 : BitVec 64
  hi64 : BitVec 64
  deriving @[expose] DecidableEq, Repr
def packNodeWord128 (w : PackedNodeWord) (hasSorry : Bool) (handleId : Nat := 0) : PackedNodeWord128 :=
  let bSorry := if hasSorry then 1 else 0; let bFVar := if w.hasFVar then 1 else 0
  let bMVar  := if w.hasMVar then 1 else 0; let bLoose := if w.hasLooseBVar then 1 else 0
  let loNat := (w.h1 % 65536) + 65536 * (w.h0 % 65536) + 4294967296 * (w.symIdx % 65536) +
    72057594037927936 * bSorry + 144115188075855872 * bFVar +
    288230376151711744 * bMVar + 576460752303423488 * bLoose + 1152921504606846976 * (w.tag % 16)
  let hiNat := (w.h2 % 65536) + 65536 * (w.maxLooseBVar % 65536) + 4294967296 * (handleId % 4294967296)
  { lo64 := BitVec.ofNat 64 loNat, hi64 := BitVec.ofNat 64 hiNat }

def packNodeWord9Checked? (w : PackedNodeWord) (hasSorry : Bool) (handleId : Nat := 0) : Option (BitVec 64) :=
  if w.tag < 16 && w.tag != 7 && w.h0 < 512 && w.h1 < 512 && w.symIdx < 65536 && handleId < 512 then
    some (packNodeWord128 w hasSorry handleId).lo64
  else none

def unpackNodeWord128 (p : PackedNodeWord128) : PackedNodeWord × Bool × Nat :=
  let lo := p.lo64.toNat; let hi := p.hi64.toNat
  ( { tag := (lo / 1152921504606846976) % 16, h0 := (lo / 65536) % 65536, h1 := lo % 65536
    , h2 := hi % 65536, symIdx := (lo / 4294967296) % 65536
    , hasLooseBVar := ((lo / 576460752303423488) % 2) == 1, hasFVar := ((lo / 144115188075855872) % 2) == 1
    , hasMVar := ((lo / 288230376151711744) % 2) == 1, maxLooseBVar := (hi / 65536) % 65536 }
  , ((lo / 72057594037927936) % 2) == 1, (hi / 4294967296) % 4294967296 )

theorem unpack_pack_nodeWord128 (w : PackedNodeWord) (hasSorry : Bool) (handleId : Nat)
    (hTag : w.tag < 16) (hH0 : w.h0 < 65536) (hH1 : w.h1 < 65536) (hH2 : w.h2 < 65536)
    (hSym : w.symIdx < 65536) (hMax : w.maxLooseBVar < 65536) (hHid : handleId < 4294967296) :
    unpackNodeWord128 (packNodeWord128 w hasSorry handleId) = (w, hasSorry, handleId) := by
  cases w with | mk tag h0 h1 h2 symIdx hasLooseBVar hasFVar hasMVar maxLooseBVar =>
    dsimp only at hTag hH0 hH1 hH2 hSym hMax; unfold unpackNodeWord128 packNodeWord128; simp only [BitVec.toNat_ofNat]
    generalize hbS : (if hasSorry then 1 else 0) = bS; generalize hbL : (if hasLooseBVar then 1 else 0) = bL
    generalize hbF : (if hasFVar then 1 else 0) = bF; generalize hbM : (if hasMVar then 1 else 0) = bM
    have hS2 : bS < 2 ∧ (bS == 1) = hasSorry := by subst hbS; cases hasSorry <;> decide
    have hL2 : bL < 2 ∧ (bL == 1) = hasLooseBVar := by subst hbL; cases hasLooseBVar <;> decide
    have hF2 : bF < 2 ∧ (bF == 1) = hasFVar := by subst hbF; cases hasFVar <;> decide
    have hM2 : bM < 2 ∧ (bM == 1) = hasMVar := by subst hbM; cases hasMVar <;> decide
    rw [← hS2.2, ← hL2.2, ← hF2.2, ← hM2.2]
    have := hS2.1; have := hL2.1; have := hF2.1; have := hM2.1
    simp only [Prod.mk.injEq, PackedNodeWord.mk.injEq]; refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩ <;>
      first | omega | (congr 1; omega)

theorem packLo64_slices (w : PackedNodeWord) (hasSorry : Bool) (hid : Nat)
    (hTag : w.tag < 16) (hH0 : w.h0 < 512) (hH1 : w.h1 < 512) :
    let lo := (packNodeWord128 w hasSorry hid).lo64
    (lo >>> 60) &&& 0xF#64 = BitVec.ofNat 64 w.tag ∧
    (lo >>> 59) &&& 1#64 = (if w.hasLooseBVar then 1#64 else 0#64) ∧
    (lo >>> 58) &&& 1#64 = (if w.hasMVar then 1#64 else 0#64) ∧
    (lo >>> 56) &&& 1#64 = (if hasSorry then 1#64 else 0#64) ∧
    (lo >>> 16) &&& 0x1FF#64 = BitVec.ofNat 64 w.h0 ∧ lo &&& 0x1FF#64 = BitVec.ofNat 64 w.h1 := by
  dsimp only [packNodeWord128]
  generalize hbS : (if hasSorry then 1 else 0) = bS; generalize hbL : (if w.hasLooseBVar then 1 else 0) = bL
  generalize hbF : (if w.hasFVar then 1 else 0) = bF; generalize hbM : (if w.hasMVar then 1 else 0) = bM
  have hS : bS < 2 ∧ BitVec.ofNat 64 bS = (if hasSorry then 1#64 else 0#64) := by subst hbS; cases hasSorry <;> decide
  have hL : bL < 2 ∧ BitVec.ofNat 64 bL = (if w.hasLooseBVar then 1#64 else 0#64) := by subst hbL; cases w.hasLooseBVar <;> decide
  have hF : bF < 2 := by subst hbF; cases w.hasFVar <;> decide
  have hM : bM < 2 ∧ BitVec.ofNat 64 bM = (if w.hasMVar then 1#64 else 0#64) := by subst hbM; cases w.hasMVar <;> decide
  rw [← hL.2, ← hM.2, ← hS.2]; have := hS.1; have := hL.1; have := hM.1
  have h15 : (0xF#64).toNat = 2 ^ 4 - 1 := rfl; have h1 : (1#64).toNat = 2 ^ 1 - 1 := rfl; have h9 : (0x1FF#64).toNat = 2 ^ 9 - 1 := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals (apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, h15, h1, h9, Nat.and_two_pow_sub_one_eq_mod]; omega)

/-! ## 7. 8-Bank 2-Choice Cuckoo-Hashed `ExprCAM` (`CuckooExprCAM`, `cuckooLookup?`, `cuckooInsert`) -/
structure CuckooSlot where
  key      : PackedNodeWord
  hasSorry : Bool := false
  handle   : CamHandle
  deriving @[expose] DecidableEq, Repr
structure CuckooExprCAM where
  bankDepth  : Nat := 64
  nextHandle : Nat := 0
  slots      : Array (Option CuckooSlot)
  deriving @[expose] DecidableEq, Repr
def CuckooExprCAM.empty (bankDepth : Nat := 64) : CuckooExprCAM :=
  { bankDepth := bankDepth, nextHandle := 0, slots := Array.replicate (8 * bankDepth) none }
def cuckooRawHash0 (k : PackedNodeWord) : Nat :=
  2654435761 * k.tag + 40503 * k.h0 + 65537 * k.h1 + 257 * k.h2 + 131071 * k.symIdx

def cuckooRawHash1 (k : PackedNodeWord) : Nat :=
  97 + 2246822519 * k.tag + 1140071481 * k.h0 + 3266489917 * k.h1 + 668265263 * k.h2 + 374761393 * k.symIdx

def cuckooLoc0 (bankDepth : Nat) (k : PackedNodeWord) : Nat × Nat := let h := cuckooRawHash0 k; (h % 4, (h / 4) % bankDepth)
def cuckooLoc1 (bankDepth : Nat) (k : PackedNodeWord) : Nat × Nat := let h := cuckooRawHash1 k; (4 + h % 4, (h / 4) % bankDepth)
theorem cuckooLoc_bounds {d : Nat} (hd : 0 < d) (k : PackedNodeWord) :
    (cuckooLoc0 d k).1 < 4 ∧ (cuckooLoc0 d k).2 < d ∧
    4 ≤ (cuckooLoc1 d k).1 ∧ (cuckooLoc1 d k).1 < 8 ∧ (cuckooLoc1 d k).2 < d ∧ cuckooLoc0 d k ≠ cuckooLoc1 d k := by
  unfold cuckooLoc0 cuckooLoc1; dsimp only
  refine ⟨by omega, Nat.mod_lt _ hd, by omega, by omega, Nat.mod_lt _ hd, fun hEq => ?_⟩
  have h1 := congrArg Prod.fst hEq; dsimp only at h1; omega
def CuckooExprCAM.readBankSlot (cam : CuckooExprCAM) (b r : Nat) : Option CuckooSlot := cam.slots.getD (b * cam.bankDepth + r) none
def CuckooExprCAM.writeBankSlot (cam : CuckooExprCAM) (b r : Nat) (s : CuckooSlot) : CuckooExprCAM :=
  { cam with slots := cam.slots.set! (b * cam.bankDepth + r) (some s) }
def cuckooProbeSlot? (s? : Option CuckooSlot) (k : PackedNodeWord) : Option CuckooSlot :=
  match s? with | some s => if s.key == k then some s else none | none => none
def cuckooLookupSlot? (cam : CuckooExprCAM) (k : PackedNodeWord) : Option CuckooSlot :=
  (cuckooProbeSlot? (cam.readBankSlot (cuckooLoc0 cam.bankDepth k).1 (cuckooLoc0 cam.bankDepth k).2) k).or
    (cuckooProbeSlot? (cam.readBankSlot (cuckooLoc1 cam.bankDepth k).1 (cuckooLoc1 cam.bankDepth k).2) k)
def cuckooLookup? (cam : CuckooExprCAM) (k : PackedNodeWord) : Option CamHandle := (cuckooLookupSlot? cam k).map (fun s : CuckooSlot => s.handle)
def cuckooChooseLoc (useChoice1 : Bool) (d : Nat) (k : PackedNodeWord) : Nat × Nat := if useChoice1 then cuckooLoc1 d k else cuckooLoc0 d k
def cuckooEvictLoop : Nat → Bool → CuckooSlot → CuckooExprCAM → CuckooExprCAM × Option CuckooSlot
  | 0 => fun _ curSlot cam => (cam, some curSlot)
  | kicks + 1 => fun useChoice1 curSlot cam =>
    let loc := cuckooChooseLoc useChoice1 cam.bankDepth curSlot.key
    match cam.readBankSlot loc.1 loc.2 with
    | none => (cam.writeBankSlot loc.1 loc.2 curSlot, none)
    | some victim => cuckooEvictLoop kicks (!useChoice1) victim (cam.writeBankSlot loc.1 loc.2 curSlot)
def cuckooInsertMissAux (maxKicks : Nat) (k : PackedNodeWord) (newSlot : CuckooSlot) (camAlloc : CuckooExprCAM) :
    Option CuckooSlot → Option CuckooSlot → CamHandle × CuckooExprCAM × Option CuckooSlot
  | none, _ => (newSlot.handle, camAlloc.writeBankSlot (cuckooLoc0 camAlloc.bankDepth k).1 (cuckooLoc0 camAlloc.bankDepth k).2 newSlot, none)
  | some _, none => (newSlot.handle, camAlloc.writeBankSlot (cuckooLoc1 camAlloc.bankDepth k).1 (cuckooLoc1 camAlloc.bankDepth k).2 newSlot, none)
  | some _, some _ => let ev := cuckooEvictLoop maxKicks false newSlot camAlloc; (newSlot.handle, ev.1, ev.2)
def cuckooTaintKeySorry (cam : CuckooExprCAM) (k : PackedNodeWord) : CuckooExprCAM :=
  match cuckooProbeSlot? (cam.readBankSlot (cuckooLoc0 cam.bankDepth k).1 (cuckooLoc0 cam.bankDepth k).2) k with
  | some s0 => cam.writeBankSlot (cuckooLoc0 cam.bankDepth k).1 (cuckooLoc0 cam.bankDepth k).2 { s0 with hasSorry := true }
  | none => match cuckooProbeSlot? (cam.readBankSlot (cuckooLoc1 cam.bankDepth k).1 (cuckooLoc1 cam.bankDepth k).2) k with
    | some s1 => cam.writeBankSlot (cuckooLoc1 cam.bankDepth k).1 (cuckooLoc1 cam.bankDepth k).2 { s1 with hasSorry := true } | none => cam
def cuckooInsertAux (maxKicks : Nat) (k : PackedNodeWord) (hasSorry : Bool) (cam : CuckooExprCAM) :
    Option CamHandle → CamHandle × CuckooExprCAM × Option CuckooSlot
  | some existingH => (existingH, if hasSorry then cuckooTaintKeySorry cam k else cam, none)
  | none =>
    let newSlot : CuckooSlot := { key := k, hasSorry := hasSorry, handle := cam.nextHandle }
    let camAlloc : CuckooExprCAM := { cam with nextHandle := cam.nextHandle + 1 }
    cuckooInsertMissAux maxKicks k newSlot camAlloc
      (camAlloc.readBankSlot (cuckooLoc0 cam.bankDepth k).1 (cuckooLoc0 cam.bankDepth k).2)
      (camAlloc.readBankSlot (cuckooLoc1 cam.bankDepth k).1 (cuckooLoc1 cam.bankDepth k).2)
def cuckooInsert (maxKicks : Nat) (k : PackedNodeWord) (hasSorry : Bool) (cam : CuckooExprCAM) :
    CamHandle × CuckooExprCAM × Option CuckooSlot := cuckooInsertAux maxKicks k hasSorry cam (cuckooLookup? cam k)
def CuckooMember (cam : CuckooExprCAM) (k : PackedNodeWord) (h : CamHandle) : Prop :=
  ∃ b r s, b < 8 ∧ r < cam.bankDepth ∧ cam.readBankSlot b r = some s ∧ s.key = k ∧ s.handle = h

structure CuckooCamWF (cam : CuckooExprCAM) : Prop where
  depthPos   : 0 < cam.bankDepth
  slotsSize  : cam.slots.size = 8 * cam.bankDepth
  validPlace : ∀ b r s, b < 8 → r < cam.bankDepth → cam.readBankSlot b r = some s →
    (b, r) = cuckooLoc0 cam.bankDepth s.key ∨ (b, r) = cuckooLoc1 cam.bankDepth s.key
  handleLt   : ∀ b r s, b < 8 → r < cam.bankDepth → cam.readBankSlot b r = some s → s.handle < cam.nextHandle
  noDup      : ∀ b₁ r₁ s₁ b₂ r₂ s₂, b₁ < 8 → r₁ < cam.bankDepth → b₂ < 8 → r₂ < cam.bankDepth →
    cam.readBankSlot b₁ r₁ = some s₁ → cam.readBankSlot b₂ r₂ = some s₂ →
    (b₁, r₁) ≠ (b₂, r₂) → s₁.key ≠ s₂.key ∧ s₁.handle ≠ s₂.handle

private theorem bankIdx_lt {d b r : Nat} (hb : b < 8) (hr : r < d) : b * d + r < 8 * d := by
  have hmul : b * d ≤ 7 * d := Nat.mul_le_mul_right d (by omega); omega
private theorem bankIdx_eq_iff {d b₁ r₁ b₂ r₂ : Nat} (hr₁ : r₁ < d) (hr₂ : r₂ < d) :
    b₁ * d + r₁ = b₂ * d + r₂ ↔ (b₁, r₁) = (b₂, r₂) := by
  constructor
  · intro h
    by_cases hlt : b₁ < b₂
    · have hm := Nat.mul_le_mul_right d hlt; rw [Nat.succ_mul] at hm; omega
    · by_cases hgt : b₂ < b₁
      · have hm := Nat.mul_le_mul_right d hgt; rw [Nat.succ_mul] at hm; omega
      · have hb : b₁ = b₂ := by omega
        subst hb; exact Prod.ext rfl (by omega)
  · intro h; cases h; rfl
private theorem ifTrue {α : Type _} {c : Prop} [inst : Decidable c] {a b : α} (h : c) : @ite α c inst a b = a := by
  cases inst with | isTrue _ => rfl | isFalse hn => exact absurd h hn
private theorem ifFalse {α : Type _} {c : Prop} [inst : Decidable c] {a b : α} (hn : ¬c) : @ite α c inst a b = b := by
  cases inst with | isTrue h => exact absurd h hn | isFalse _ => rfl
private theorem none_ne_some {α : Type _} {x : α} (h : (none : Option α) = some x) : False := by cases h
private theorem some_ne_none {α : Type _} {x : α} (h : some x = (none : Option α)) : False := by cases h
private theorem readBankSlot_writeBankSlot (cam : CuckooExprCAM) (hSz : cam.slots.size = 8 * cam.bankDepth)
    {b r b' r' : Nat} (hb : b < 8) (hr : r < cam.bankDepth) (hr' : r' < cam.bankDepth) (s : CuckooSlot) :
    (cam.writeBankSlot b r s).readBankSlot b' r' = if (b', r') = (b, r) then some s else cam.readBankSlot b' r' := by
  have hj : b * cam.bankDepth + r < cam.slots.size := by rw [hSz]; exact bankIdx_lt hb hr
  change (cam.slots.set! (b * cam.bankDepth + r) (some s)).getD (b' * cam.bankDepth + r') none = _
  rw [array_getD_set! cam.slots (b * cam.bankDepth + r) (b' * cam.bankDepth + r') (some s) none hj]
  by_cases heq : (b', r') = (b, r)
  · rw [ifTrue ((bankIdx_eq_iff hr' hr).mpr heq), ifTrue heq]
  · rw [ifFalse (fun h => heq ((bankIdx_eq_iff hr' hr).mp h)), ifFalse heq]; rfl
private theorem cuckooProbeSlot_eq_some {s? : Option CuckooSlot} {k : PackedNodeWord} {s : CuckooSlot} :
    cuckooProbeSlot? s? k = some s ↔ s? = some s ∧ s.key = k := by
  cases s? with
  | none => exact ⟨fun h => (none_ne_some h).elim, fun ⟨h, _⟩ => (none_ne_some h).elim⟩
  | some s' =>
    change (if (s'.key == k) = true then some s' else none) = some s ↔ some s' = some s ∧ s.key = k
    by_cases hk : (s'.key == k) = true
    · rw [ifTrue hk]; exact ⟨fun h => ⟨h, (Option.some.inj h) ▸ of_decide_eq_true hk⟩, fun ⟨h, _⟩ => h⟩
    · rw [ifFalse hk]; exact ⟨fun h => (none_ne_some h).elim, fun ⟨h, hkeq⟩ => absurd (decide_eq_true ((Option.some.inj h) ▸ hkeq)) hk⟩
private theorem cuckooProbeSlot_eq_none {s? : Option CuckooSlot} {k : PackedNodeWord} :
    cuckooProbeSlot? s? k = none ↔ ∀ s, s? = some s → s.key ≠ k := by
  cases s? with
  | none => exact ⟨fun _ _ h => (none_ne_some h).elim, fun _ => rfl⟩
  | some s' =>
    change (if (s'.key == k) = true then some s' else none) = none ↔ ∀ s, some s' = some s → s.key ≠ k
    by_cases hk : (s'.key == k) = true
    · rw [ifTrue hk]; exact ⟨fun h => (some_ne_none h).elim, fun H => absurd (of_decide_eq_true hk) (H s' rfl)⟩
    · rw [ifFalse hk]; exact ⟨fun _ s hs hkeq => hk (decide_eq_true ((Option.some.inj hs) ▸ hkeq)), fun _ => rfl⟩
private theorem option_or_map_eq_some {α β : Type} (f : α → β) (o₁ o₂ : Option α) (y : β) :
    ((o₁.or o₂).map f = some y) ↔ (∃ a, o₁ = some a ∧ f a = y) ∨ (o₁ = none ∧ ∃ a, o₂ = some a ∧ f a = y) := by
  cases o₁ <;> cases o₂ <;> simp [Option.or]

/-- **1-Cycle Dual-Bank Cuckoo Lookup Soundness & Completeness (`cuckooCam_lookup_iff_member`)**. -/
theorem cuckooCam_lookup_iff_member (cam : CuckooExprCAM) (k : PackedNodeWord) (h : CamHandle)
    (hWF : CuckooCamWF cam) : cuckooLookup? cam k = some h ↔ CuckooMember cam k h := by
  obtain ⟨hb0_4, hb0r0_d, _, hb1_lt, hb1r1_d, hLocNe⟩ := cuckooLoc_bounds hWF.depthPos k
  have hb0_lt : (cuckooLoc0 cam.bankDepth k).1 < 8 := by omega
  unfold cuckooLookup? cuckooLookupSlot?; rw [option_or_map_eq_some]; constructor
  · rintro (⟨s0, hP0, hH0⟩ | ⟨_, s1, hP1, hH1⟩)
    · obtain ⟨hR0, hK0⟩ := cuckooProbeSlot_eq_some.mp hP0; exact ⟨_, _, s0, hb0_lt, hb0r0_d, hR0, hK0, hH0⟩
    · obtain ⟨hR1, hK1⟩ := cuckooProbeSlot_eq_some.mp hP1; exact ⟨_, _, s1, hb1_lt, hb1r1_d, hR1, hK1, hH1⟩
  · rintro ⟨b, r, s, hb, hr, hRead, rfl, rfl⟩
    rcases hWF.validPlace b r s hb hr hRead with hP0 | hP1
    · have hbEq : b = (cuckooLoc0 cam.bankDepth s.key).1 := congrArg Prod.fst hP0
      have hrEq : r = (cuckooLoc0 cam.bankDepth s.key).2 := congrArg Prod.snd hP0
      subst hbEq hrEq; exact Or.inl ⟨s, cuckooProbeSlot_eq_some.mpr ⟨hRead, rfl⟩, rfl⟩
    · have hbEq : b = (cuckooLoc1 cam.bankDepth s.key).1 := congrArg Prod.fst hP1
      have hrEq : r = (cuckooLoc1 cam.bankDepth s.key).2 := congrArg Prod.snd hP1
      subst hbEq hrEq; refine Or.inr ⟨cuckooProbeSlot_eq_none.mpr fun s0 hR0 => ?_, s, cuckooProbeSlot_eq_some.mpr ⟨hRead, rfl⟩, rfl⟩
      exact (hWF.noDup _ _ s0 _ _ s hb0_lt hb0r0_d hb1_lt hb1r1_d hR0 hRead hLocNe).1

theorem cuckooEmpty_wf {d : Nat} (hd : 0 < d) : CuckooCamWF (CuckooExprCAM.empty d) := by
  refine ⟨hd, by simp only [CuckooExprCAM.empty, Array.size_replicate], ?_, ?_, ?_⟩
  · intro b r s _ _ hRd; unfold CuckooExprCAM.empty CuckooExprCAM.readBankSlot at hRd; rw [array_getD_replicate] at hRd; exact (none_ne_some hRd).elim
  · intro b r s _ _ hRd; unfold CuckooExprCAM.empty CuckooExprCAM.readBankSlot at hRd; rw [array_getD_replicate] at hRd; exact (none_ne_some hRd).elim
  · intro b r s _ _ _ _ _ _ _ hRd _ _; unfold CuckooExprCAM.empty CuckooExprCAM.readBankSlot at hRd; rw [array_getD_replicate] at hRd; exact (none_ne_some hRd).elim

private theorem writeBankSlot_preserves_wf (cam : CuckooExprCAM) (hWF : CuckooCamWF cam)
    {b r : Nat} (hb : b < 8) (hr : r < cam.bankDepth) (s : CuckooSlot)
    (hPlace : (b, r) = cuckooLoc0 cam.bankDepth s.key ∨ (b, r) = cuckooLoc1 cam.bankDepth s.key) (hLt : s.handle < cam.nextHandle)
    (hFresh : ∀ b' r' s', b' < 8 → r' < cam.bankDepth → (b', r') ≠ (b, r) →
      cam.readBankSlot b' r' = some s' → s'.key ≠ s.key ∧ s'.handle ≠ s.handle) :
    CuckooCamWF (cam.writeBankSlot b r s) := by
  refine ⟨hWF.depthPos, by simp only [CuckooExprCAM.writeBankSlot, Array.size_set!, hWF.slotsSize], ?_, ?_, ?_⟩
  · intro b' r' s' hb' hr' hRd; rw [readBankSlot_writeBankSlot cam hWF.slotsSize hb hr hr' s] at hRd
    by_cases heq : (b', r') = (b, r)
    · rw [ifTrue heq] at hRd; have hs := Option.some.inj hRd; subst hs; rw [heq]; exact hPlace
    · rw [ifFalse heq] at hRd; exact hWF.validPlace b' r' s' hb' hr' hRd
  · intro b' r' s' hb' hr' hRd; rw [readBankSlot_writeBankSlot cam hWF.slotsSize hb hr hr' s] at hRd
    by_cases heq : (b', r') = (b, r)
    · rw [ifTrue heq] at hRd; have hs := Option.some.inj hRd; subst hs; exact hLt
    · rw [ifFalse heq] at hRd; exact hWF.handleLt b' r' s' hb' hr' hRd
  · intro b₁ r₁ s₁ b₂ r₂ s₂ hb₁ hr₁ hb₂ hr₂ hRd₁ hRd₂ hNe
    rw [readBankSlot_writeBankSlot cam hWF.slotsSize hb hr hr₁ s] at hRd₁
    rw [readBankSlot_writeBankSlot cam hWF.slotsSize hb hr hr₂ s] at hRd₂
    by_cases h1 : (b₁, r₁) = (b, r)
    · rw [ifTrue h1] at hRd₁; have hs := Option.some.inj hRd₁; subst hs
      have h2 : (b₂, r₂) ≠ (b, r) := fun he => hNe (h1.trans he.symm)
      rw [ifFalse h2] at hRd₂; have hf := hFresh b₂ r₂ s₂ hb₂ hr₂ h2 hRd₂; exact ⟨hf.1.symm, hf.2.symm⟩
    · rw [ifFalse h1] at hRd₁
      by_cases h2 : (b₂, r₂) = (b, r)
      · rw [ifTrue h2] at hRd₂; have hs := Option.some.inj hRd₂; subst hs; exact hFresh b₁ r₁ s₁ hb₁ hr₁ h1 hRd₁
      · rw [ifFalse h2] at hRd₂; exact hWF.noDup b₁ r₁ s₁ b₂ r₂ s₂ hb₁ hr₁ hb₂ hr₂ hRd₁ hRd₂ hNe

private theorem cuckooChooseLoc_bounds (u : Bool) {d : Nat} (hd : 0 < d) (k : PackedNodeWord) :
    (cuckooChooseLoc u d k).1 < 8 ∧ (cuckooChooseLoc u d k).2 < d ∧
    (((cuckooChooseLoc u d k).1, (cuckooChooseLoc u d k).2) = cuckooLoc0 d k ∨
     ((cuckooChooseLoc u d k).1, (cuckooChooseLoc u d k).2) = cuckooLoc1 d k) := by
  obtain ⟨hb0, hr0, _, hb1, hr1, _⟩ := cuckooLoc_bounds hd k; cases u
  · exact ⟨by change (cuckooLoc0 d k).1 < 8; omega, hr0, Or.inl (Prod.ext rfl rfl)⟩
  · exact ⟨hb1, hr1, Or.inr (Prod.ext rfl rfl)⟩
private theorem cuckooEvictStep_wf (kicks : Nat)
    (ih : ∀ (u : Bool) (c : CuckooSlot) (m : CuckooExprCAM), CuckooCamWF m → c.handle < m.nextHandle →
      (∀ b r s, b < 8 → r < m.bankDepth → m.readBankSlot b r = some s → s.key ≠ c.key ∧ s.handle ≠ c.handle) → CuckooCamWF (cuckooEvictLoop kicks u c m).1)
    (u : Bool) (cur : CuckooSlot) (cam : CuckooExprCAM) (b r : Nat) (hb : b < 8) (hr : r < cam.bankDepth)
    (hPl : (b, r) = cuckooLoc0 cam.bankDepth cur.key ∨ (b, r) = cuckooLoc1 cam.bankDepth cur.key)
    (hWF : CuckooCamWF cam) (hLt : cur.handle < cam.nextHandle)
    (hDisj : ∀ b' r' s', b' < 8 → r' < cam.bankDepth → cam.readBankSlot b' r' = some s' → s'.key ≠ cur.key ∧ s'.handle ≠ cur.handle)
    (old? : Option CuckooSlot) (hOld : cam.readBankSlot b r = old?) :
    CuckooCamWF (match old? with | none => (cam.writeBankSlot b r cur, none) | some victim => cuckooEvictLoop kicks (!u) victim (cam.writeBankSlot b r cur)).1 := by
  have hWF' := writeBankSlot_preserves_wf cam hWF hb hr cur hPl hLt (fun b' r' s' hb' hr' _ hRd => hDisj b' r' s' hb' hr' hRd)
  cases old? with
  | none => exact hWF'
  | some victim =>
    apply ih (!u) victim (cam.writeBankSlot b r cur) hWF' (hWF.handleLt b r victim hb hr hOld)
    intro b' r' s' hb' hr' hRd; rw [readBankSlot_writeBankSlot cam hWF.slotsSize hb hr hr' cur] at hRd
    by_cases heq : (b', r') = (b, r)
    · rw [ifTrue heq] at hRd; have hs := Option.some.inj hRd; subst hs; have hvc := hDisj b r victim hb hr hOld; exact ⟨hvc.1.symm, hvc.2.symm⟩
    · rw [ifFalse heq] at hRd; exact hWF.noDup b' r' s' b r victim hb' hr' hb hr hRd hOld heq
private theorem cuckooEvictLoop_preserves_wf (kicks : Nat) :
    ∀ (u : Bool) (cur : CuckooSlot) (cam : CuckooExprCAM), CuckooCamWF cam → cur.handle < cam.nextHandle →
      (∀ b' r' s', b' < 8 → r' < cam.bankDepth → cam.readBankSlot b' r' = some s' → s'.key ≠ cur.key ∧ s'.handle ≠ cur.handle) →
      CuckooCamWF (cuckooEvictLoop kicks u cur cam).1 := by
  induction kicks with
  | zero => intro _ _ _ hWF _ _; exact hWF
  | succ kicks ih =>
    intro u cur cam hWF hLt hDisj; obtain ⟨hb, hr, hPl⟩ := cuckooChooseLoc_bounds u hWF.depthPos cur.key
    exact cuckooEvictStep_wf kicks ih u cur cam _ _ hb hr hPl hWF hLt hDisj _ rfl
private theorem cuckooInsertMissAux_wf (m : Nat) (k : PackedNodeWord) (ns : CuckooSlot) (ca : CuckooExprCAM)
    (hKey : ns.key = k) (hWF : CuckooCamWF ca) (hLt : ns.handle < ca.nextHandle)
    (hDisj : ∀ b r s, b < 8 → r < ca.bankDepth → ca.readBankSlot b r = some s → s.key ≠ k ∧ s.handle ≠ ns.handle) :
    ∀ (o0 o1 : Option CuckooSlot), CuckooCamWF (cuckooInsertMissAux m k ns ca o0 o1).2.1
  | none, _ =>
    have ⟨_, hr0, _, _, _, _⟩ := cuckooLoc_bounds hWF.depthPos k
    writeBankSlot_preserves_wf ca hWF (by have ⟨hb0, _, _, _, _, _⟩ := cuckooLoc_bounds hWF.depthPos k; omega) hr0 ns
      (Or.inl (hKey ▸ Prod.ext rfl rfl)) hLt (fun b r s hb hr _ hRd => by rw [hKey]; exact hDisj b r s hb hr hRd)
  | some _, none =>
    have ⟨_, _, _, hb1, hr1, _⟩ := cuckooLoc_bounds hWF.depthPos k
    writeBankSlot_preserves_wf ca hWF hb1 hr1 ns (Or.inr (hKey ▸ Prod.ext rfl rfl)) hLt (fun b r s hb hr _ hRd => by rw [hKey]; exact hDisj b r s hb hr hRd)
  | some _, some _ => cuckooEvictLoop_preserves_wf m false ns ca hWF hLt (fun b r s hb hr hRd => by rw [hKey]; exact hDisj b r s hb hr hRd)
private theorem cuckooTaintKeySorry_wf (cam : CuckooExprCAM) (k : PackedNodeWord) (hWF : CuckooCamWF cam) : CuckooCamWF (cuckooTaintKeySorry cam k) := by
  obtain ⟨hb0_4, hr0, _, hb1, hr1, _⟩ := cuckooLoc_bounds hWF.depthPos k; have hb0 : (cuckooLoc0 cam.bankDepth k).1 < 8 := by omega
  unfold cuckooTaintKeySorry
  cases hp0 : cuckooProbeSlot? (cam.readBankSlot (cuckooLoc0 cam.bankDepth k).1 (cuckooLoc0 cam.bankDepth k).2) k with
  | some s0 =>
    obtain ⟨hRd0, hK0⟩ := cuckooProbeSlot_eq_some.mp hp0
    exact writeBankSlot_preserves_wf cam hWF hb0 hr0 { s0 with hasSorry := true } (Or.inl (hK0 ▸ Prod.ext rfl rfl))
      (hWF.handleLt _ _ s0 hb0 hr0 hRd0) (fun b' r' s' hb' hr' hNe hRd' => hWF.noDup _ _ s' _ _ s0 hb' hr' hb0 hr0 hRd' hRd0 hNe)
  | none =>
    cases hp1 : cuckooProbeSlot? (cam.readBankSlot (cuckooLoc1 cam.bankDepth k).1 (cuckooLoc1 cam.bankDepth k).2) k with
    | some s1 =>
      obtain ⟨hRd1, hK1⟩ := cuckooProbeSlot_eq_some.mp hp1
      exact writeBankSlot_preserves_wf cam hWF hb1 hr1 { s1 with hasSorry := true } (Or.inr (hK1 ▸ Prod.ext rfl rfl))
        (hWF.handleLt _ _ s1 hb1 hr1 hRd1) (fun b' r' s' hb' hr' hNe hRd' => hWF.noDup _ _ s' _ _ s1 hb' hr' hb1 hr1 hRd' hRd1 hNe)
    | none => exact hWF
private theorem cuckooInsertAux_wf (m : Nat) (k : PackedNodeWord) (s : Bool) (cam : CuckooExprCAM) (hWF : CuckooCamWF cam) :
    ∀ (lk : Option CamHandle), cuckooLookup? cam k = lk → CuckooCamWF (cuckooInsertAux m k s cam lk).2.1
  | some _, _ => by unfold cuckooInsertAux; cases s <;> simp [hWF, cuckooTaintKeySorry_wf]
  | none, hLook =>
    let ca : CuckooExprCAM := { cam with nextHandle := cam.nextHandle + 1 }; let ns : CuckooSlot := { key := k, hasSorry := s, handle := cam.nextHandle }
    cuckooInsertMissAux_wf m k ns ca rfl
      ⟨hWF.depthPos, hWF.slotsSize, hWF.validPlace, fun b r sl hb hr hRd => Nat.lt_trans (hWF.handleLt b r sl hb hr hRd) (Nat.lt_succ_self _), hWF.noDup⟩
      (Nat.lt_succ_self _)
      (fun b r sl hb hr hRd => ⟨fun hKEq => (none_ne_some (hLook.symm.trans ((cuckooCam_lookup_iff_member cam k sl.handle hWF).mpr ⟨b, r, sl, hb, hr, hRd, hKEq, rfl⟩))).elim,
        Nat.ne_of_lt (hWF.handleLt b r sl hb hr hRd)⟩) _ _
private theorem cuckooTaintKeySorry_lookup (cam : CuckooExprCAM) (k : PackedNodeWord) (hOld : CamHandle)
    (hWF : CuckooCamWF cam) (hMem : CuckooMember cam k hOld) :
    ∃ s', cuckooLookupSlot? (cuckooTaintKeySorry cam k) k = some s' ∧ s'.handle = hOld ∧ s'.hasSorry = true := by
  obtain ⟨hb0_4, hr0, _, hb1, hr1, hLocNe⟩ := cuckooLoc_bounds hWF.depthPos k; have hb0 : (cuckooLoc0 cam.bankDepth k).1 < 8 := by omega
  rcases hMem with ⟨b, r, s, hb, hr, hRd, rfl, rfl⟩; rcases hWF.validPlace b r s hb hr hRd with hP0 | hP1
  · have hbE := congrArg Prod.fst hP0; have hrE := congrArg Prod.snd hP0; subst hbE hrE
    have hp0 := cuckooProbeSlot_eq_some.mpr ⟨hRd, (rfl : s.key = s.key)⟩; unfold cuckooTaintKeySorry; rw [hp0]; dsimp only
    unfold cuckooLookupSlot?
    have hWr : (cam.writeBankSlot (cuckooLoc0 cam.bankDepth s.key).1 (cuckooLoc0 cam.bankDepth s.key).2 { s with hasSorry := true }).readBankSlot
        (cuckooLoc0 cam.bankDepth s.key).1 (cuckooLoc0 cam.bankDepth s.key).2 = some { s with hasSorry := true } := by
      rw [readBankSlot_writeBankSlot cam hWF.slotsSize hb0 hr0 hr0, ifTrue rfl]
    have hPr0 : cuckooProbeSlot? ((cam.writeBankSlot (cuckooLoc0 cam.bankDepth s.key).1 (cuckooLoc0 cam.bankDepth s.key).2 { s with hasSorry := true }).readBankSlot
        (cuckooLoc0 cam.bankDepth s.key).1 (cuckooLoc0 cam.bankDepth s.key).2) s.key = some { s with hasSorry := true } :=
      cuckooProbeSlot_eq_some.mpr ⟨hWr, rfl⟩
    exact ⟨{ s with hasSorry := true }, by
      change (cuckooProbeSlot? ((cam.writeBankSlot (cuckooLoc0 cam.bankDepth s.key).1 (cuckooLoc0 cam.bankDepth s.key).2 { s with hasSorry := true }).readBankSlot
          (cuckooLoc0 cam.bankDepth s.key).1 (cuckooLoc0 cam.bankDepth s.key).2) s.key).or
        (cuckooProbeSlot? ((cam.writeBankSlot (cuckooLoc0 cam.bankDepth s.key).1 (cuckooLoc0 cam.bankDepth s.key).2 { s with hasSorry := true }).readBankSlot
          (cuckooLoc1 cam.bankDepth s.key).1 (cuckooLoc1 cam.bankDepth s.key).2) s.key) = _
      rw [hPr0]; rfl, rfl, rfl⟩
  · have hbE := congrArg Prod.fst hP1; have hrE := congrArg Prod.snd hP1; subst hbE hrE
    have hp0 : cuckooProbeSlot? (cam.readBankSlot (cuckooLoc0 cam.bankDepth s.key).1 (cuckooLoc0 cam.bankDepth s.key).2) s.key = none :=
      cuckooProbeSlot_eq_none.mpr fun s0 hRd0 => (hWF.noDup _ _ s0 _ _ s hb0 hr0 hb1 hr1 hRd0 hRd hLocNe).1
    have hp1 := cuckooProbeSlot_eq_some.mpr ⟨hRd, (rfl : s.key = s.key)⟩; unfold cuckooTaintKeySorry; rw [hp0, hp1]; dsimp only
    unfold cuckooLookupSlot?
    have hWr0 : (cam.writeBankSlot (cuckooLoc1 cam.bankDepth s.key).1 (cuckooLoc1 cam.bankDepth s.key).2 { s with hasSorry := true }).readBankSlot
        (cuckooLoc0 cam.bankDepth s.key).1 (cuckooLoc0 cam.bankDepth s.key).2 =
        cam.readBankSlot (cuckooLoc0 cam.bankDepth s.key).1 (cuckooLoc0 cam.bankDepth s.key).2 := by
      rw [readBankSlot_writeBankSlot cam hWF.slotsSize hb1 hr1 hr0, ifFalse hLocNe]
    have hWr1 : (cam.writeBankSlot (cuckooLoc1 cam.bankDepth s.key).1 (cuckooLoc1 cam.bankDepth s.key).2 { s with hasSorry := true }).readBankSlot
        (cuckooLoc1 cam.bankDepth s.key).1 (cuckooLoc1 cam.bankDepth s.key).2 = some { s with hasSorry := true } := by
      rw [readBankSlot_writeBankSlot cam hWF.slotsSize hb1 hr1 hr1, ifTrue rfl]
    have hPr1 : cuckooProbeSlot? ((cam.writeBankSlot (cuckooLoc1 cam.bankDepth s.key).1 (cuckooLoc1 cam.bankDepth s.key).2 { s with hasSorry := true }).readBankSlot
        (cuckooLoc1 cam.bankDepth s.key).1 (cuckooLoc1 cam.bankDepth s.key).2) s.key = some { s with hasSorry := true } :=
      cuckooProbeSlot_eq_some.mpr ⟨hWr1, rfl⟩
    exact ⟨{ s with hasSorry := true }, by
      change (cuckooProbeSlot? ((cam.writeBankSlot (cuckooLoc1 cam.bankDepth s.key).1 (cuckooLoc1 cam.bankDepth s.key).2 { s with hasSorry := true }).readBankSlot
          (cuckooLoc0 cam.bankDepth s.key).1 (cuckooLoc0 cam.bankDepth s.key).2) s.key).or
        (cuckooProbeSlot? ((cam.writeBankSlot (cuckooLoc1 cam.bankDepth s.key).1 (cuckooLoc1 cam.bankDepth s.key).2 { s with hasSorry := true }).readBankSlot
          (cuckooLoc1 cam.bankDepth s.key).1 (cuckooLoc1 cam.bankDepth s.key).2) s.key) = _
      rw [hWr0, hp0, hPr1]; rfl, rfl, rfl⟩
/-- **Cuckoo Insertion Well-Formedness, Conservative `hasSorry` Dedup & No-Duplicate-Handles (`cuckooCam_no_duplicate_handles`)**. -/
theorem cuckooCam_no_duplicate_handles
    (maxKicks : Nat) (k : PackedNodeWord) (hasSorry : Bool) (cam : CuckooExprCAM) (hWF : CuckooCamWF cam) :
    let res := cuckooInsert maxKicks k hasSorry cam
    CuckooCamWF res.2.1 ∧
    (∀ b₁ r₁ s₁ b₂ r₂ s₂, b₁ < 8 → r₁ < res.2.1.bankDepth → b₂ < 8 → r₂ < res.2.1.bankDepth →
      res.2.1.readBankSlot b₁ r₁ = some s₁ → res.2.1.readBankSlot b₂ r₂ = some s₂ → (b₁, r₁) ≠ (b₂, r₂) → s₁.key ≠ s₂.key ∧ s₁.handle ≠ s₂.handle) ∧
    (∀ hOld, CuckooMember cam k hOld → res.1 = hOld ∧ res.2.2 = none ∧ (hasSorry = false → res.2.1 = cam) ∧
      (hasSorry = true → ∃ s', cuckooLookupSlot? res.2.1 k = some s' ∧ s'.handle = hOld ∧ s'.hasSorry = true)) := by
  have hPres : CuckooCamWF (cuckooInsert maxKicks k hasSorry cam).2.1 := cuckooInsertAux_wf maxKicks k hasSorry cam hWF _ rfl
  refine ⟨hPres, hPres.noDup, fun hOld hMem => ?_⟩
  have hLk : cuckooLookup? cam k = some hOld := (cuckooCam_lookup_iff_member cam k hOld hWF).mpr hMem
  unfold cuckooInsert; rw [hLk]; unfold cuckooInsertAux
  exact ⟨rfl, rfl, fun hF => by simp [hF], fun hT => by simp only [hT, ↓reduceIte]; exact cuckooTaintKeySorry_lookup cam k hOld hWF hMem⟩
theorem cuckooCam_wf_inhabited : ∃ (cam : CuckooExprCAM) (k : PackedNodeWord) (h : CamHandle), CuckooCamWF cam ∧ CuckooMember cam k h := by
  let k0 : PackedNodeWord := { tag := 0, h0 := 0, h1 := 0 }; let s0 : CuckooSlot := { key := k0, hasSorry := false, handle := 0 }
  let ca : CuckooExprCAM := { CuckooExprCAM.empty 1 with nextHandle := 1 }; have hE := cuckooEmpty_wf (d := 1) (by decide)
  have hEmptyRd : ∀ b r sl, ca.readBankSlot b r = some sl → False := fun b r sl hRd =>
    none_ne_some (by change (Array.replicate 8 none).getD (b * 1 + r) none = some sl at hRd; rwa [array_getD_replicate] at hRd)
  have hWFCa : CuckooCamWF ca := ⟨hE.depthPos, hE.slotsSize, hE.validPlace, fun b r sl _ _ hRd => (hEmptyRd b r sl hRd).elim, hE.noDup⟩
  have hWF1 : CuckooCamWF (ca.writeBankSlot 0 0 s0) := writeBankSlot_preserves_wf ca hWFCa (by decide) (by decide) s0
    (Or.inl (by simp [ca, CuckooExprCAM.empty, s0, k0, cuckooLoc0, cuckooRawHash0])) (by decide) (fun b r sl _ _ _ hRd => (hEmptyRd b r sl hRd).elim)
  have hMem : (ca.writeBankSlot 0 0 s0).readBankSlot 0 0 = some s0 := by
    rw [readBankSlot_writeBankSlot ca hWFCa.slotsSize (by decide) (by decide) (by decide) s0, ifTrue rfl]
  exact ⟨ca.writeBankSlot 0 0 s0, k0, 0, hWF1, 0, 0, s0, by decide, by decide, hMem, rfl, rfl⟩
/-! ## 8. 128-Bit `GoldilocksExt2` Permutation-Product Spill Authenticator (`OfflineMemAcc`) -/
structure SpillTuple where
  addr : UInt32
  word : PackedNodeWord128
  timestamp : UInt64
  deriving @[expose] DecidableEq, Repr
def encodeSpillLimbs (t : SpillTuple) : List Goldilocks :=
  let lo := t.word.lo64.toNat; let hi := t.word.hi64.toNat; let ts := t.timestamp.toNat
  [ Goldilocks.ofNat (lo % 72057594037927936), Goldilocks.ofNat (hi % 72057594037927936), Goldilocks.ofNat (ts % 72057594037927936)
  , Goldilocks.ofNat (t.addr.toNat + 4294967296 * (lo / 72057594037927936) + 1099511627776 * (hi / 72057594037927936) + 281474976710656 * (ts / 72057594037927936)) ]
theorem encodeSpillLimbs_injective {t₁ t₂ : SpillTuple} (hEq : encodeSpillLimbs t₁ = encodeSpillLimbs t₂) : t₁ = t₂ := by
  rcases t₁ with ⟨⟨a1⟩, ⟨lo1, hi1⟩, ⟨ts1⟩⟩; rcases t₂ with ⟨⟨a2⟩, ⟨lo2, hi2⟩, ⟨ts2⟩⟩
  unfold encodeSpillLimbs at hEq; simp only [List.cons.injEq, and_true] at hEq
  have hv0 := congrArg Goldilocks.val hEq.1; have hv1 := congrArg Goldilocks.val hEq.2.1
  have hv2 := congrArg Goldilocks.val hEq.2.2.1; have hv3 := congrArg Goldilocks.val hEq.2.2.2
  simp only [Goldilocks.ofNat, UInt32.toNat, UInt64.toNat] at hv0 hv1 hv2 hv3
  have hp : goldilocksPrime = 18446744069414584321 := rfl; rw [hp] at hv0 hv1 hv2 hv3
  have := a1.isLt; have := a2.isLt; have := lo1.isLt; have := lo2.isLt; have := hi1.isLt; have := hi2.isLt; have := ts1.isLt; have := ts2.isLt
  have modP : ∀ {x : Nat}, x < 18446744069414584321 → x % 18446744069414584321 = x := fun h => Nat.mod_eq_of_lt h
  rw [modP (by omega), modP (by omega)] at hv0 hv1 hv2 hv3
  have ha : a1 = a2 := BitVec.eq_of_toNat_eq (by omega); have hlo : lo1 = lo2 := BitVec.eq_of_toNat_eq (by omega)
  have hhi : hi1 = hi2 := BitVec.eq_of_toNat_eq (by omega); have hts : ts1 = ts2 := BitVec.eq_of_toNat_eq (by omega)
  subst ha hlo hhi hts; rfl

def spillPolyCoeffs (t : SpillTuple) : List GoldilocksExt2 := (encodeSpillLimbs t).map GoldilocksExt2.ofBase
def compressSpillTuple (α : GoldilocksExt2) (t : SpillTuple) : GoldilocksExt2 := RoundPoly.evalCoeffs (spillPolyCoeffs t) α
def grandProd {R : Type} [CommRingOps R] (γ : R) : List R → R
  | [] => CommRingOps.one | t :: ts => CommRingOps.mul (CommRingOps.sub γ t) (grandProd γ ts)

/-- Hardware accumulator state for authenticated external HBM2 DAG spills over `GoldilocksExt2`. -/
structure OfflineMemAcc where
  gamma : GoldilocksExt2
  alpha : GoldilocksExt2
  wProd : GoldilocksExt2 := CommRingOps.one
  rProd : GoldilocksExt2 := CommRingOps.one
  writeCount : Nat := 0
  readCount : Nat := 0
  deriving @[expose] DecidableEq, Repr
def recordSpillWrite (acc : OfflineMemAcc) (t : SpillTuple) : OfflineMemAcc :=
  { acc with wProd := CommRingOps.mul acc.wProd (CommRingOps.sub acc.gamma (compressSpillTuple acc.alpha t)), writeCount := acc.writeCount + 1 }
def recordSpillRead (acc : OfflineMemAcc) (t : SpillTuple) : OfflineMemAcc :=
  { acc with rProd := CommRingOps.mul acc.rProd (CommRingOps.sub acc.gamma (compressSpillTuple acc.alpha t)), readCount := acc.readCount + 1 }
def runOfflineMemTrace (γ α : GoldilocksExt2) (writes reads : List SpillTuple) : OfflineMemAcc :=
  reads.foldl recordSpillRead (writes.foldl recordSpillWrite { gamma := γ, alpha := α })

private theorem foldl_write_gen (step : GoldilocksExt2 → GoldilocksExt2 → GoldilocksExt2 → SpillTuple → GoldilocksExt2) :
    ∀ (l : List SpillTuple) (acc : OfflineMemAcc),
      (l.foldl (fun s t => { s with wProd := step s.gamma s.alpha s.wProd t, writeCount := s.writeCount + 1 }) acc).wProd =
        l.foldl (fun p t => step acc.gamma acc.alpha p t) acc.wProd ∧
      (l.foldl (fun s t => { s with wProd := step s.gamma s.alpha s.wProd t, writeCount := s.writeCount + 1 }) acc).rProd = acc.rProd ∧
      (l.foldl (fun s t => { s with wProd := step s.gamma s.alpha s.wProd t, writeCount := s.writeCount + 1 }) acc).gamma = acc.gamma ∧
      (l.foldl (fun s t => { s with wProd := step s.gamma s.alpha s.wProd t, writeCount := s.writeCount + 1 }) acc).alpha = acc.alpha
  | [], _ => ⟨rfl, rfl, rfl, rfl⟩ | _ :: rest, _ => foldl_write_gen step rest _
private theorem foldl_read_gen (step : GoldilocksExt2 → GoldilocksExt2 → GoldilocksExt2 → SpillTuple → GoldilocksExt2) :
    ∀ (l : List SpillTuple) (acc : OfflineMemAcc),
      (l.foldl (fun s t => { s with rProd := step s.gamma s.alpha s.rProd t, readCount := s.readCount + 1 }) acc).rProd =
        l.foldl (fun p t => step acc.gamma acc.alpha p t) acc.rProd ∧
      (l.foldl (fun s t => { s with rProd := step s.gamma s.alpha s.rProd t, readCount := s.readCount + 1 }) acc).wProd = acc.wProd
  | [], _ => ⟨rfl, rfl⟩ | _ :: rest, _ => foldl_read_gen step rest _
private theorem foldl_mul_sub_eq {R α : Type} [LawfulCommRing R] (γ : R) (f : α → R) :
    ∀ (l : List α) (acc : R), l.foldl (fun p t => CommRingOps.mul p (CommRingOps.sub γ (f t))) acc = CommRingOps.mul acc (grandProd γ (l.map f))
  | [], acc => (LawfulCommRing.mul_one acc).symm
  | t :: rest, acc => (foldl_mul_sub_eq γ f rest _).trans (LawfulCommRing.mul_assoc acc (CommRingOps.sub γ (f t)) (grandProd γ (rest.map f)))

theorem runOfflineMemTrace_prods (γ α : GoldilocksExt2) (ws rs : List SpillTuple) :
    (runOfflineMemTrace γ α ws rs).wProd = grandProd γ (ws.map (compressSpillTuple α)) ∧
    (runOfflineMemTrace γ α ws rs).rProd = grandProd γ (rs.map (compressSpillTuple α)) := by
  let step (g a p : GoldilocksExt2) (t : SpillTuple) := CommRingOps.mul p (CommRingOps.sub g (compressSpillTuple a t))
  obtain ⟨hw, hr0, hg, ha⟩ := foldl_write_gen step ws { gamma := γ, alpha := α }
  obtain ⟨hr, hwKeep⟩ := foldl_read_gen step rs (ws.foldl recordSpillWrite { gamma := γ, alpha := α })
  have hg' : (ws.foldl recordSpillWrite { gamma := γ, alpha := α }).gamma = γ := hg
  have ha' : (ws.foldl recordSpillWrite { gamma := γ, alpha := α }).alpha = α := ha
  have hr0' : (ws.foldl recordSpillWrite { gamma := γ, alpha := α }).rProd = CommRingOps.one := hr0
  refine ⟨hwKeep.trans (hw.trans ((foldl_mul_sub_eq γ (compressSpillTuple α) ws CommRingOps.one).trans (LawfulCommRing.one_mul _))), hr.trans ?_⟩
  rw [hg', ha', hr0']; exact (foldl_mul_sub_eq γ (compressSpillTuple α) rs CommRingOps.one).trans (LawfulCommRing.one_mul _)

theorem grandProd_perm_invariant {R : Type} [LawfulCommRing R] (γ : R) {xs ys : List R} (hPerm : xs.Perm ys) : grandProd γ xs = grandProd γ ys := by
  induction hPerm with
  | nil => rfl | cons x _ ih => simp only [grandProd, ih] | trans _ _ ih1 ih2 => exact ih1.trans ih2
  | swap x y l => simp only [grandProd]; rw [← LawfulCommRing.mul_assoc, LawfulCommRing.mul_comm (CommRingOps.sub γ y), LawfulCommRing.mul_assoc]
private theorem perm_map_local {α β : Type} (f : α → β) {xs ys : List α} (h : xs.Perm ys) : (xs.map f).Perm (ys.map f) := by
  induction h with | nil => exact .nil | cons x _ ih => exact .cons (f x) ih | swap x y l => exact .swap (f x) (f y) (l.map f) | trans _ _ i1 i2 => exact i1.trans i2

theorem offlineMemCheck_perm_complete (γ α : GoldilocksExt2) (writeLog readLog : List SpillTuple) (hPerm : writeLog.Perm readLog) :
    (runOfflineMemTrace γ α writeLog readLog).wProd = (runOfflineMemTrace γ α writeLog readLog).rProd := by
  obtain ⟨hW, hR⟩ := runOfflineMemTrace_prods γ α writeLog readLog; rw [hW, hR]
  exact grandProd_perm_invariant γ (perm_map_local (compressSpillTuple α) hPerm)

private theorem sub_eq_zero_iff_ring {R : Type} [LawfulCommRing R] {a b : R} : CommRingOps.sub a b = CommRingOps.zero ↔ a = b :=
  ⟨fun h => by have h1 := congrArg (CommRingOps.add · b) h; rwa [LawfulCommRing.zero_add, LawfulCommRing.sub_eq_add_neg, LawfulCommRing.add_assoc, LawfulCommRing.add_left_neg, LawfulCommRing.add_zero] at h1,
   fun h => h ▸ LawfulCommRing.sub_self a⟩
private theorem exists_evalCoeffs_nz_poly {R : Type} [LawfulCommRing R] [DecidableEq R] [NoZeroDivisors R]
    (p1 p2 p3 : R) (hNd : [p1, p2, p3].Nodup) (hp1Nz : p1 ≠ CommRingOps.zero) (hp2Nz : p2 ≠ CommRingOps.zero) (hp3Nz : p3 ≠ CommRingOps.zero) (cs : List R) :
    cs.length ≤ 4 → (∃ c ∈ cs, c ≠ CommRingOps.zero) → ∃ x₀ : R, RoundPoly.evalCoeffs cs x₀ ≠ CommRingOps.zero := by
  induction cs with
  | nil => rintro _ ⟨_, h, _⟩; nomatch h
  | cons c₀ tl ih =>
    rintro hlen ⟨c, hcMem, hcNz⟩
    if hc₀ : c₀ = CommRingOps.zero then
      subst hc₀; obtain ⟨x₁, hx₁⟩ := ih (by simp at hlen; omega) (by cases hcMem with | head => exact (hcNz rfl).elim | tail _ ht => exact ⟨c, ht, hcNz⟩)
      have hMulNz : ∀ {p : R}, p ≠ CommRingOps.zero → RoundPoly.evalCoeffs tl p ≠ CommRingOps.zero →
          RoundPoly.evalCoeffs (CommRingOps.zero :: tl) p ≠ CommRingOps.zero := fun hp hEv hZ => by
        simp only [RoundPoly.evalCoeffs, LawfulCommRing.zero_add] at hZ; exact (NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero hZ).elim hp hEv
      by_cases hp1 : RoundPoly.evalCoeffs tl p1 = CommRingOps.zero
      · by_cases hp2 : RoundPoly.evalCoeffs tl p2 = CommRingOps.zero
        · by_cases hp3 : RoundPoly.evalCoeffs tl p3 = CommRingOps.zero
          · have hB := RoundPoly.roots_nodup_length_le 2 tl [p1, p2, p3] hNd (by simp at hlen; omega) ⟨x₁, hx₁⟩
            simp only [List.filter, hp1, hp2, hp3, decide_true, List.length_cons, List.length_nil] at hB; omega
          · exact ⟨p3, hMulNz hp3Nz hp3⟩
        · exact ⟨p2, hMulNz hp2Nz hp2⟩
      · exact ⟨p1, hMulNz hp1Nz hp1⟩
    else refine ⟨CommRingOps.zero, ?_⟩; simpa [RoundPoly.evalCoeffs, LawfulCommRing.zero_mul, LawfulCommRing.add_zero] using hc₀

private def monicFromRoots {R : Type} [CommRingOps R] : List R → List R
  | [] => [CommRingOps.one] | a :: ts => let cs := monicFromRoots ts; RoundPoly.subCoeffs (CommRingOps.zero :: cs) (cs.map (CommRingOps.mul a))
private theorem monicFromRoots_length {R : Type} [CommRingOps R] : ∀ (ts : List R), (monicFromRoots ts).length = ts.length + 1
  | [] => rfl | _ :: ts => by simp [monicFromRoots, RoundPoly.subCoeffs_length, monicFromRoots_length ts]
private theorem evalCoeffs_map_mul {R : Type} [LawfulCommRing R] (a x : R) :
    ∀ (cs : List R), RoundPoly.evalCoeffs (cs.map (CommRingOps.mul a)) x = CommRingOps.mul a (RoundPoly.evalCoeffs cs x)
  | [] => (LawfulCommRing.mul_zero a).symm
  | _ :: cs => by simp only [List.map_cons, RoundPoly.evalCoeffs, evalCoeffs_map_mul a x cs]; rw [LawfulCommRing.left_distrib, ← LawfulCommRing.mul_assoc x a, LawfulCommRing.mul_comm x a, LawfulCommRing.mul_assoc]
private theorem evalCoeffs_monicFromRoots {R : Type} [LawfulCommRing R] : ∀ (ts : List R) (γ : R), RoundPoly.evalCoeffs (monicFromRoots ts) γ = grandProd γ ts
  | [], _ => by simp [monicFromRoots, grandProd, RoundPoly.evalCoeffs, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
  | a :: ts, γ => by simp only [monicFromRoots, grandProd, RoundPoly.evalCoeffs_sub, RoundPoly.evalCoeffs, LawfulCommRing.zero_add, evalCoeffs_map_mul, evalCoeffs_monicFromRoots ts γ]; exact (LawfulCommRing.sub_mul γ a (grandProd γ ts)).symm
private theorem grandProd_ne_zero_of_not_mem {R : Type} [LawfulCommRing R] [NoZeroDivisors R]
    (h10 : (CommRingOps.one : R) ≠ CommRingOps.zero) {a : R} : ∀ {ts : List R}, a ∉ ts → grandProd a ts ≠ CommRingOps.zero
  | [], _ => h10
  | _ :: _, hnm => fun hZ => (NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero hZ).elim (fun h1 => hnm (sub_eq_zero_iff_ring.mp h1 ▸ .head _)) (grandProd_ne_zero_of_not_mem h10 fun hm => hnm (.tail _ hm))
private def eraseTag {R : Type} [DecidableEq R] (v : R) : List R → List R
  | [] => [] | y :: ys => if y = v then ys else y :: eraseTag v ys
private theorem eraseTag_spec {R : Type} [DecidableEq R] [LawfulCommRing R] {v : R} :
    ∀ {ys : List R}, v ∈ ys → (v :: eraseTag v ys).Perm ys ∧ (eraseTag v ys).length + 1 = ys.length ∧
      (∀ γ, grandProd γ ys = CommRingOps.mul (CommRingOps.sub γ v) (grandProd γ (eraseTag v ys)))
  | [], h => nomatch h
  | y :: ys, h => by
    dsimp only [eraseTag]; if hy : y = v then subst hy; exact ⟨by simp, by simp, fun _ => by simp [grandProd]⟩
    else
      simp only [hy, ↓reduceIte, List.length_cons, grandProd]
      obtain ⟨hp, hlen, hgp⟩ := eraseTag_spec (by cases h with | head => exact False.elim (hy rfl) | tail _ ht => exact ht)
      refine ⟨(List.Perm.swap y v _).trans (List.Perm.cons y hp), by omega, fun γ => ?_⟩
      rw [hgp γ, ← LawfulCommRing.mul_assoc, LawfulCommRing.mul_comm (CommRingOps.sub γ y), LawfulCommRing.mul_assoc]
private theorem nodup_eraseTag {R : Type} [DecidableEq R] {v : R} :
    ∀ {S : List R}, S.Nodup → (eraseTag v S).Nodup ∧ (∀ x ∈ eraseTag v S, x ≠ v ∧ x ∈ S)
  | [], _ => ⟨.nil, fun _ h => nomatch h⟩
  | y :: _, .cons hrel hnd => by
    dsimp only [eraseTag]; if hy : y = v then subst hy; simp only [↓reduceIte]; exact ⟨hnd, fun x hx => ⟨fun hEq => hrel x hx hEq.symm, .tail _ hx⟩⟩
    else
      simp only [hy, ↓reduceIte]; obtain ⟨hnd', hsub⟩ := nodup_eraseTag hnd
      refine ⟨.cons (fun b hb => hrel b (hsub b hb).2) hnd', fun x hx => ?_⟩
      cases hx with | head => exact ⟨hy, .head _⟩ | tail _ ht => exact ⟨(hsub x ht).1, .tail _ (hsub x ht).2⟩
private theorem filter_len_le_eraseTag {R : Type} [DecidableEq R] (v : R) (p : R → Bool) :
    ∀ (S : List R), (S.filter p).length ≤ ((eraseTag v S).filter p).length + 1
  | [] => by simp [eraseTag]
  | y :: ys => by
    dsimp only [eraseTag]; if hy : y = v then simp only [hy, ↓reduceIte, List.filter]; cases p v <;> simp <;> omega
    else have ih := filter_len_le_eraseTag v p ys; simp only [hy, ↓reduceIte, List.filter]; cases p y <;> simp <;> omega
private theorem filter_le_of_imp_on {α : Type} {p q : α → Bool} :
    ∀ (S : List α), (∀ x ∈ S, p x = true → q x = true) → (S.filter p).length ≤ (S.filter q).length
  | [], _ => Nat.le_refl 0
  | x :: xs, himp => by
    simp only [List.filter]; have ih := filter_le_of_imp_on xs (fun y hy => himp y (.tail _ hy))
    cases hp : p x; · cases q x <;> simp <;> omega
    · rw [himp x (.head _) hp]; simp; omega
private theorem grandProd_roots_of_witness {R : Type} [DecidableEq R] [LawfulCommRing R] [NoZeroDivisors R]
    {ws rs S : List R} (hNodup : S.Nodup) (hWit : ∃ x₀, grandProd x₀ ws ≠ grandProd x₀ rs) :
    (S.filter (fun γ => decide (grandProd γ ws = grandProd γ rs))).length ≤ Nat.max ws.length rs.length := by
  obtain ⟨x₀, hx₀⟩ := hWit; let diff := RoundPoly.subCoeffs (monicFromRoots ws) (monicFromRoots rs)
  have hLen : diff.length ≤ Nat.max ws.length rs.length + 1 := by simp [diff, RoundPoly.subCoeffs_length, monicFromRoots_length, Nat.succ_max_succ]
  have hNz : RoundPoly.evalCoeffs diff x₀ ≠ CommRingOps.zero := by
    rw [RoundPoly.evalCoeffs_sub, evalCoeffs_monicFromRoots, evalCoeffs_monicFromRoots]; exact fun hZ => hx₀ (sub_eq_zero_iff_ring.mp hZ)
  have hB := RoundPoly.roots_nodup_length_le (Nat.max ws.length rs.length) diff S hNodup hLen ⟨x₀, hNz⟩
  refine Nat.le_trans (filter_le_of_imp_on S fun γ _ hEq => ?_) hB; rw [decide_eq_true_eq] at hEq ⊢
  rw [RoundPoly.evalCoeffs_sub, evalCoeffs_monicFromRoots, evalCoeffs_monicFromRoots, hEq, LawfulCommRing.sub_self]
private theorem grandProd_roots_le_poly {R : Type} [DecidableEq R] [LawfulCommRing R] [NoZeroDivisors R]
    (h10 : (CommRingOps.one : R) ≠ CommRingOps.zero) (ws : List R) :
    ∀ (rs S : List R), S.Nodup → ¬ ws.Perm rs → (S.filter (fun γ => decide (grandProd γ ws = grandProd γ rs))).length ≤ Nat.max ws.length rs.length := by
  induction ws with
  | nil =>
    intro rs S hNd hNP
    cases rs with
    | nil => exact False.elim (hNP .nil)
    | cons b _ => exact grandProd_roots_of_witness hNd ⟨b, fun hEq => by simp only [grandProd, LawfulCommRing.sub_self, LawfulCommRing.zero_mul] at hEq; exact h10 hEq⟩
  | cons a ws ih =>
    intro rs S hNd hNP; by_cases hMem : a ∈ rs
    · obtain ⟨hPermR, hLenR, hGpR⟩ := eraseTag_spec hMem; obtain ⟨hNd', hSub'⟩ := nodup_eraseTag hNd
      have hRec := ih (eraseTag a rs) (eraseTag a S) hNd' (fun hp => hNP ((List.Perm.cons a hp).trans hPermR))
      have hImp : ((eraseTag a S).filter (fun γ => decide (grandProd γ (a :: ws) = grandProd γ rs))).length ≤
          ((eraseTag a S).filter (fun γ => decide (grandProd γ ws = grandProd γ (eraseTag a rs)))).length := by
        apply filter_le_of_imp_on; intro γ hγ hEq; rw [decide_eq_true_eq] at hEq ⊢; rw [grandProd, hGpR γ] at hEq
        have hSubZ : CommRingOps.mul (CommRingOps.sub γ a) (CommRingOps.sub (grandProd γ ws) (grandProd γ (eraseTag a rs))) = CommRingOps.zero := by
          rw [LawfulCommRing.mul_sub, hEq, LawfulCommRing.sub_self]
        rcases NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero hSubZ with hZa | hZw
        · exact False.elim ((hSub' γ hγ).1 (sub_eq_zero_iff_ring.mp hZa))
        · exact sub_eq_zero_iff_ring.mp hZw
      have hStep := filter_len_le_eraseTag a (fun γ => decide (grandProd γ (a :: ws) = grandProd γ rs)) S
      rw [← hLenR, List.length_cons]; simp only [Nat.max_def] at hRec ⊢; split at hRec <;> split <;> omega
    · exact grandProd_roots_of_witness hNd ⟨a, fun hEq => by simp only [grandProd, LawfulCommRing.sub_self, LawfulCommRing.zero_mul] at hEq; exact grandProd_ne_zero_of_not_mem h10 hMem hEq.symm⟩

private theorem subCoeffs_ofBase_nz :
    ∀ {xs ys : List Goldilocks}, xs.length = ys.length → xs ≠ ys →
      ∃ c ∈ RoundPoly.subCoeffs (xs.map GoldilocksExt2.ofBase) (ys.map GoldilocksExt2.ofBase), c ≠ CommRingOps.zero
  | [], [], _, hNe => False.elim (hNe rfl)
  | x :: xs, y :: ys, hLen, hNe => by
    simp only [List.map, RoundPoly.subCoeffs]
    by_cases hxy : CommRingOps.sub (GoldilocksExt2.ofBase x) (GoldilocksExt2.ofBase y) = CommRingOps.zero
    · have exy : x = y := by simpa [GoldilocksExt2.ofBase] using congrArg GoldilocksExt2.c0 (sub_eq_zero_iff_ring.mp hxy)
      subst exy; obtain ⟨c, hc, hcz⟩ := subCoeffs_ofBase_nz (Nat.succ.inj hLen) (fun htl => hNe (congrArg (x :: ·) htl)); exact ⟨c, .tail _ hc, hcz⟩
    · exact ⟨_, .head _, hxy⟩
theorem grandProd_roots_le (ws rs S : List GoldilocksExt2) (hNd : S.Nodup) (hNP : ¬ ws.Perm rs) :
    (S.filter (fun γ => decide (grandProd γ ws = grandProd γ rs))).length ≤ Nat.max ws.length rs.length :=
  grandProd_roots_le_poly (by decide) ws rs S hNd hNP
theorem offlineMemCheck_spill_sound
    (t₁ t₂ : SpillTuple) (hNe : t₁ ≠ t₂) (α : GoldilocksExt2) (writeLog readLog : List SpillTuple)
    (hNotTagPerm : ¬ (writeLog.map (compressSpillTuple α)).Perm (readLog.map (compressSpillTuple α)))
    (S_α S_γ : List GoldilocksExt2) (hNdα : S_α.Nodup) (hNdγ : S_γ.Nodup) :
    (S_α.filter (fun r => decide (compressSpillTuple r t₁ = compressSpillTuple r t₂))).length ≤ 3 ∧
    (S_γ.filter (fun γ => decide ((runOfflineMemTrace γ α writeLog readLog).wProd =
      (runOfflineMemTrace γ α writeLog readLog).rProd))).length ≤ Nat.max writeLog.length readLog.length ∧ 2 ^ 127 < goldilocksPrime ^ 2 := by
  refine ⟨?_, ?_, goldilocksExt2_card_gt_two_pow_126 127 (Nat.le_refl 127)⟩
  · let diff := RoundPoly.subCoeffs (spillPolyCoeffs t₁) (spillPolyCoeffs t₂)
    have hDiffNz : ∃ c ∈ diff, c ≠ CommRingOps.zero := subCoeffs_ofBase_nz rfl (fun hEq => hNe (encodeSpillLimbs_injective hEq))
    have hLen : diff.length ≤ 3 + 1 := by simp only [diff, RoundPoly.subCoeffs_length]; exact Nat.le_refl 4
    have hWit := exists_evalCoeffs_nz_poly (GoldilocksExt2.ofBase (Goldilocks.ofNat 1))
      (GoldilocksExt2.ofBase (Goldilocks.ofNat 2)) (GoldilocksExt2.ofBase (Goldilocks.ofNat 3)) (by decide) (by decide) (by decide) (by decide) diff hLen hDiffNz
    have hB := RoundPoly.roots_nodup_length_le 3 diff S_α hNdα hLen hWit
    refine Nat.le_trans (filter_le_of_imp_on S_α fun r _ hEq => ?_) hB; rw [decide_eq_true_eq] at hEq ⊢
    change RoundPoly.evalCoeffs (spillPolyCoeffs t₁) r = RoundPoly.evalCoeffs (spillPolyCoeffs t₂) r at hEq; rw [RoundPoly.evalCoeffs_sub, hEq, LawfulCommRing.sub_self]
  · have hEqF : (fun γ => decide ((runOfflineMemTrace γ α writeLog readLog).wProd = (runOfflineMemTrace γ α writeLog readLog).rProd)) =
        (fun γ => decide (grandProd γ (writeLog.map (compressSpillTuple α)) = grandProd γ (readLog.map (compressSpillTuple α)))) := by
      funext γ; rw [(runOfflineMemTrace_prods γ α writeLog readLog).1, (runOfflineMemTrace_prods γ α writeLog readLog).2]
    rw [hEqF]; simpa only [List.length_map] using grandProd_roots_le (writeLog.map (compressSpillTuple α)) (readLog.map (compressSpillTuple α)) S_γ hNdγ hNotTagPerm
theorem offlineMemCheck_inhabited :
    ∃ (t₁ t₂ : SpillTuple) (γ α : GoldilocksExt2), t₁ ≠ t₂ ∧
      (runOfflineMemTrace γ α [t₁, t₂] [t₂, t₁]).wProd = (runOfflineMemTrace γ α [t₁, t₂] [t₂, t₁]).rProd ∧
      (runOfflineMemTrace γ α [t₁, t₂] [t₁, t₁]).wProd ≠ (runOfflineMemTrace γ α [t₁, t₂] [t₁, t₁]).rProd :=
  ⟨{ addr := 0, word := { lo64 := 0#64, hi64 := 0#64 }, timestamp := 0 }, { addr := 0, word := { lo64 := 1#64, hi64 := 0#64 }, timestamp := 0 },
   GoldilocksExt2.ofBase (Goldilocks.ofNat 1), GoldilocksExt2.ofBase (Goldilocks.ofNat 7), by decide, offlineMemCheck_perm_complete _ _ _ _ (.swap _ _ .nil), by decide⟩
/-! ## 9. Synthesizable 8-Bank `SyncRam` `cuckooSiliconElabMemModule` & Cycle-Accurate `stepCamWhnf` Simulation -/
def mkBank8ReadMux (selExpr : RtlExpr) : RtlExpr :=
  let idx := .alu .bitAnd selExpr (.const 7#64)
  .mux (.alu .eq idx (.const 0#64)) (.regRead 10) (.mux (.alu .eq idx (.const 1#64)) (.regRead 11)
    (.mux (.alu .eq idx (.const 2#64)) (.regRead 12) (.mux (.alu .eq idx (.const 3#64)) (.regRead 13)
    (.mux (.alu .eq idx (.const 4#64)) (.regRead 14) (.mux (.alu .eq idx (.const 5#64)) (.regRead 15) (.mux (.alu .eq idx (.const 6#64)) (.regRead 16) (.regRead 17)))))))
def cuckooSiliconElabMemModule : RtlMemModule where
  core := {
    name := "cuckoo_silicon_elab_top"
    inputNames := [ "ram_we", "ram_wsel", "ram_waddr", "ram_wdata", "z1_start", "z1_step_en", "z1_init_handle", "z4_ctrl" ]
    inputWidths := [ 1, 3, 6, 64, 1, 1, 9, 3 ]
    wires :=
      let hwReady := .alu .bitAnd (.alu .bitAnd (.mux (.regRead 5) (.const 1#64) (.const 0#64)) (.alu .eq (.regRead 1) (.const 0#64))) (.alu .eq (.inputPort 0) (.const 0#64))
      [ { wireIdx := 0, name := "w_ram_word", width := 64, expr := mkBank8ReadMux (.regRead 2) }
      , { wireIdx := 1, name := "w_ram_tag", width := 4, expr := .alu .bitAnd (.alu .lshr (.wireRef 0) (.const 60#64)) (.const 0xF#64) }
      , { wireIdx := 2, name := "w_ram_h0", width := 9, expr := .alu .bitAnd (.alu .lshr (.wireRef 0) (.const 16#64)) (.const 0x1FF#64) }
      , { wireIdx := 3, name := "w_ram_h1", width := 9, expr := .alu .bitAnd (.wireRef 0) (.const 0x1FF#64) }
      , { wireIdx := 4, name := "w_ram_loose", width := 1, expr := .alu .bitAnd (.alu .lshr (.wireRef 0) (.const 59#64)) (.const 1#64) }
      , { wireIdx := 5, name := "w_ram_mvar", width := 1, expr := .alu .bitAnd (.alu .lshr (.wireRef 0) (.const 58#64)) (.const 1#64) }
      , { wireIdx := 6, name := "w_ram_sorry", width := 1, expr := .alu .bitAnd (.alu .lshr (.wireRef 0) (.const 56#64)) (.const 1#64) }
      , { wireIdx := 7, name := "w_req_handle", width := 9, expr := .mux (.alu .eq (.regRead 1) (.const 1#64)) (.wireRef 2) (.mux (.alu .eq (.regRead 1) (.const 2#64)) (.wireRef 3) (.regRead 0)) }
      , { wireIdx := 8, name := "w_req_bank", width := 3, expr := .alu .bitAnd (.alu .lshr (.wireRef 7) (.const 6#64)) (.const 7#64) }
      , { wireIdx := 9, name := "w_req_row", width := 6, expr := .alu .bitAnd (.wireRef 7) (.const 0x3F#64) }
      , { wireIdx := 10, name := "w_in_read_phase", width := 1, expr := .alu .bitAnd (.inputPort 5) (.mux (.regRead 1) (.const 1#64) (.const 0#64)) }
      , { wireIdx := 11, name := "w_eff_sorry", width := 1, expr := .alu .bitOr (.regRead 7) (.alu .bitAnd (.wireRef 10) (.wireRef 6)) }
      , { wireIdx := 12, name := "w_eff_mvar", width := 1, expr := .alu .bitOr (.regRead 8) (.alu .bitAnd (.wireRef 10) (.wireRef 5)) }
      , { wireIdx := 13, name := "w_z4_comb_status", width := 2
        , expr := .mux (.wireRef 11) (.const 0#64) (.mux (.wireRef 12) (.const 2#64)
            (.mux (.alu .bitAnd (.inputPort 7) (.const 1#64))
              (.mux (.alu .bitAnd (.alu .bitAnd (.alu .lshr (.inputPort 7) (.const 1#64)) (.const 1#64)) hwReady) (.const 1#64) (.const 2#64)) (.const 3#64))) }
      , { wireIdx := 14, name := "w_z4_accepted", width := 1, expr := .alu .eq (.regRead 9) (.const 1#64) } ]
    regs :=
      let macroDone := .alu .bitOr (.alu .eq (.regRead 1) (.const 3#64))
        (.alu .bitOr (.alu .bitAnd (.alu .eq (.regRead 1) (.const 1#64)) (.mux (.alu .eq (.wireRef 1) (.const 4#64)) (.const 0#64) (.const 1#64)))
                     (.alu .bitAnd (.alu .eq (.regRead 1) (.const 2#64)) (.mux (.alu .eq (.wireRef 1) (.const 5#64)) (.const 0#64) (.const 1#64))))
      let satIncSteps := .mux (.alu .eq (.regRead 5) (.const 0xFFFF#64)) (.const 0xFFFF#64) (.alu .bitAnd (.alu .add (.regRead 5) (.const 1#64)) (.const 0xFFFF#64))
      [ { regIdx := 0, name := "z1_focus_q", domain := .coreClk, resetKind := .syncReset 0#64, isSynchronizer := false, width := 9
        , nextExpr :=
            let stepFocus := .mux (.alu .eq (.regRead 1) (.const 2#64)) (.mux (.alu .eq (.wireRef 1) (.const 5#64)) (.regRead 0) (.regRead 3))
              (.mux (.alu .eq (.regRead 1) (.const 3#64)) (.mux (.alu .eq (.wireRef 4) (.const 0#64)) (.regRead 4) (.regRead 3)) (.regRead 0))
            .mux (.inputPort 4) (.inputPort 6) (.mux (.inputPort 5) stepFocus (.regRead 0)) }
      , { regIdx := 1, name := "whnf_phase_q", domain := .coreClk, resetKind := .syncReset 0#64, isSynchronizer := false, width := 2
        , nextExpr :=
            let nextPh := .mux (.alu .eq (.regRead 1) (.const 0#64)) (.const 1#64)
              (.mux (.alu .eq (.regRead 1) (.const 1#64)) (.mux (.alu .eq (.wireRef 1) (.const 4#64)) (.const 2#64) (.const 0#64))
              (.mux (.alu .eq (.regRead 1) (.const 2#64)) (.mux (.alu .eq (.wireRef 1) (.const 5#64)) (.const 3#64) (.const 0#64)) (.const 0#64)))
            .mux (.inputPort 4) (.const 0#64) (.mux (.inputPort 5) nextPh (.regRead 1)) }
      , { regIdx := 2, name := "bank_sel_q", domain := .coreClk, resetKind := .syncReset 0#64, isSynchronizer := false, width := 3, nextExpr := .mux (.inputPort 4) (.const 0#64) (.mux (.inputPort 5) (.wireRef 8) (.regRead 2)) }
      , { regIdx := 3, name := "cur_h0_q", domain := .coreClk, resetKind := .syncReset 0#64, isSynchronizer := false, width := 9, nextExpr := .mux (.inputPort 4) (.const 0#64) (.mux (.alu .bitAnd (.inputPort 5) (.alu .eq (.regRead 1) (.const 1#64))) (.wireRef 2) (.regRead 3)) }
      , { regIdx := 4, name := "body_h_q", domain := .coreClk, resetKind := .syncReset 0#64, isSynchronizer := false, width := 9, nextExpr := .mux (.inputPort 4) (.const 0#64) (.mux (.alu .bitAnd (.inputPort 5) (.alu .eq (.regRead 1) (.const 2#64))) (.wireRef 3) (.regRead 4)) }
      , { regIdx := 5, name := "z1_steps_q", domain := .coreClk, resetKind := .syncReset 0#64, isSynchronizer := false, width := 16, nextExpr := .mux (.alu .bitAnd (.inputPort 5) macroDone) satIncSteps (.regRead 5) }
      , { regIdx := 6, name := "z1_bypass_q", domain := .coreClk, resetKind := .syncReset 0#64, isSynchronizer := false, width := 1, nextExpr := .mux (.inputPort 4) (.const 0#64) (.mux (.alu .bitAnd (.inputPort 5) (.alu .eq (.regRead 1) (.const 3#64))) (.alu .eq (.wireRef 4) (.const 0#64)) (.regRead 6)) }
      , { regIdx := 7, name := "acc_sorry_q", domain := .coreClk, resetKind := .syncReset 0#64, isSynchronizer := false, width := 1, nextExpr := .wireRef 11 }
      , { regIdx := 8, name := "acc_mvar_q", domain := .coreClk, resetKind := .syncReset 0#64, isSynchronizer := false, width := 1, nextExpr := .wireRef 12 }
      , { regIdx := 9, name := "z4_status_q", domain := .coreClk, resetKind := .syncReset 0#64, isSynchronizer := false, width := 2, nextExpr := .mux (.inputPort 4) (.const 0#64) (.mux (.alu .bitAnd (.alu .lshr (.inputPort 7) (.const 2#64)) (.const 1#64)) (.wireRef 13) (.regRead 9)) } ]
    outputs :=
      [ { name := "z1_focus_out", expr := .regRead 0, width := 9 }, { name := "whnf_phase_out", expr := .regRead 1, width := 2 }
      , { name := "z1_steps_out", expr := .regRead 5, width := 16 }, { name := "z1_bypass_out", expr := .regRead 6, width := 1 }
      , { name := "acc_sorry_out", expr := .regRead 7, width := 1 }, { name := "acc_mvar_out", expr := .regRead 8, width := 1 }
      , { name := "z4_status_out", expr := .regRead 9, width := 2 }, { name := "z4_accepted_out", expr := .wireRef 14, width := 1 } ] }
  rams := [(0, "cuckoo_bank0", "cuckoo_rdata0"), (1, "cuckoo_bank1", "cuckoo_rdata1"),
           (2, "cuckoo_bank2", "cuckoo_rdata2"), (3, "cuckoo_bank3", "cuckoo_rdata3"),
           (4, "cuckoo_bank4", "cuckoo_rdata4"), (5, "cuckoo_bank5", "cuckoo_rdata5"),
           (6, "cuckoo_bank6", "cuckoo_rdata6"), (7, "cuckoo_bank7", "cuckoo_rdata7")].map fun (b, nm, rnm) =>
    { ramIdx := b, name := nm, rdataName := rnm, domain := .coreClk, style := .bram, mode := .readFirst
    , addrWidth := 6, dataWidth := 64, readAddrExpr := .wireRef 9, writeAddrExpr := .inputPort 2, writeDataExpr := .inputPort 3
    , writeEnExpr := .alu .bitAnd (.alu .bitAnd (.inputPort 0) (.alu .eq (.inputPort 1) (.const (BitVec.ofNat 64 b))))
        (.alu .bitAnd (.alu .eq (.regRead 1) (.const 0#64)) (.alu .eq (.regRead 5) (.const 0#64))) }

def emitCuckooSiliconElabSV : String := emitMemModuleSV cuckooSiliconElabMemModule
theorem cuckooSiliconElabMemModule_valid :
    checkRtlMemModule cuckooSiliconElabMemModule = true ∧ checkRtlMemModuleW cuckooSiliconElabMemModule = true :=
  ⟨by decide +kernel, by decide +kernel⟩
def cuckooIdleStepInputs : Nat → BitVec 64 := fun i => if i == 5 then 1#64 else 0#64

private theorem handle_bank_row {h : Nat} (hh : h < 512) :
    ((BitVec.ofNat 64 h >>> 6) &&& 7#64) = BitVec.ofNat 64 (h / 64) ∧
    truncToWidth 6 (BitVec.ofNat 64 h &&& 0x3F#64) = BitVec.ofNat 64 (h % 64) ∧ h / 64 < 8 := by
  refine ⟨?_, ?_, by omega⟩
  · apply BitVec.eq_of_toNat_eq; have h7 : (7#64).toNat = 2 ^ 3 - 1 := rfl
    simp only [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, h7, Nat.and_two_pow_sub_one_eq_mod]; omega
  · apply BitVec.eq_of_toNat_eq; have h63 : (0x3F#64).toNat = 2 ^ 6 - 1 := rfl; have hm : (BitVec.allOnes 64 >>> (64 - 6)).toNat = 2 ^ 6 - 1 := rfl
    simp only [truncToWidth, BitVec.toNat_and, BitVec.toNat_ofNat, h63, hm, Nat.and_two_pow_sub_one_eq_mod]; omega

private theorem evalBank8ReadMux_eq {regs : Nat → BitVec 64} {b : Nat} (hb : b < 8) (hSel : regs 2 = BitVec.ofNat 64 b) :
    evalRtlExpr cuckooIdleStepInputs (fun _ => 0#64) regs (mkBank8ReadMux (.regRead 2)) = regs (10 + b) := by
  rw [mkBank8ReadMux]; simp only [evalRtlExpr, evalAluOp, hSel]
  rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨ b = 5 ∨ b = 6 ∨ b = 7) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

private theorem cuckooIdle_mems_eq (st : MemState) :
    (stepMemModule cuckooSiliconElabMemModule false cuckooIdleStepInputs st).mems = st.mems := by
  dsimp only [stepMemModule, cuckooSiliconElabMemModule, stepSyncRamArray, List.map, List.foldl]
  simp only [cuckooIdleStepInputs, evalRtlExpr, evalAluOp, truncToWidth]
  funext k; by_cases h0 : k = 0 <;> by_cases h1 : k = 1 <;> by_cases h2 : k = 2 <;> by_cases h3 : k = 3 <;>
    by_cases h4 : k = 4 <;> by_cases h5 : k = 5 <;> by_cases h6 : k = 6 <;> by_cases h7 : k = 7 <;> simp_all

private def cuckooHwReadyVal (ins regs : Nat → BitVec 64) : BitVec 64 :=
  ((if regs 5 != 0#64 then 1#64 else 0#64) &&& (if regs 1 == 0#64 then 1#64 else 0#64)) &&&
    (if ins 0 == 0#64 then 1#64 else 0#64)

private def cuckooWireFnWith (ins regs : Nat → BitVec 64) (w0 : BitVec 64) : Nat → BitVec 64 :=
  let w1 := (w0 >>> 60) &&& 0xF#64; let w2 := (w0 >>> 16) &&& 0x1FF#64; let w3 := w0 &&& 0x1FF#64
  let w4 := (w0 >>> 59) &&& 1#64; let w5 := (w0 >>> 58) &&& 1#64; let w6 := (w0 >>> 56) &&& 1#64
  let w7 := if (if regs 1 == 1#64 then 1#64 else 0#64) != 0#64 then w2
            else if (if regs 1 == 2#64 then 1#64 else 0#64) != 0#64 then w3 else regs 0
  let w8 := (w7 >>> 6) &&& 7#64; let w9 := w7 &&& 0x3F#64
  let w10 := ins 5 &&& (if regs 1 != 0#64 then 1#64 else 0#64)
  let w11 := regs 7 ||| (w10 &&& w6); let w12 := regs 8 ||| (w10 &&& w5)
  let w13 := if w11 != 0#64 then 0#64 else if w12 != 0#64 then 2#64
             else if (ins 7 &&& 1#64) != 0#64 then
               (if (((ins 7 >>> 1) &&& 1#64) &&& cuckooHwReadyVal ins regs) != 0#64 then 1#64 else 2#64)
             else 3#64
  let w14 := if regs 9 == 1#64 then 1#64 else 0#64
  fun i => if i == 14 then w14 else if i == 13 then w13 else if i == 12 then w12 else if i == 11 then w11
    else if i == 10 then w10 else if i == 9 then w9 else if i == 8 then w8 else if i == 7 then w7
    else if i == 6 then w6 else if i == 5 then w5 else if i == 4 then w4 else if i == 3 then w3
    else if i == 2 then w2 else if i == 1 then w1 else if i == 0 then w0 else 0#64

private theorem wire_foldl_step (ins regs env : Nat → BitVec 64) (a : WireAssign) (rest : List WireAssign)
    (v : BitVec 64) (hv : evalRtlExpr ins env regs a.expr = v) :
    List.foldl (fun e (w : WireAssign) => fun i => if i == w.wireIdx then evalRtlExpr ins e regs w.expr else e i) env (a :: rest) =
    List.foldl (fun e (w : WireAssign) => fun i => if i == w.wireIdx then evalRtlExpr ins e regs w.expr else e i)
      (fun i => if i == a.wireIdx then v else env i) rest := by simp only [List.foldl_cons, hv]

private theorem cuckooWireTable_eq (ins regs : Nat → BitVec 64) :
    evalWireTable ins regs cuckooSiliconElabMemModule.core.wires =
      cuckooWireFnWith ins regs (evalRtlExpr ins (fun _ => 0#64) regs (mkBank8ReadMux (.regRead 2))) := by
  unfold evalWireTable cuckooSiliconElabMemModule; dsimp only
  generalize hw0 : evalRtlExpr ins (fun _ => 0#64) regs (mkBank8ReadMux (.regRead 2)) = w0
  let w1 := (w0 >>> 60) &&& 0xF#64; let w2 := (w0 >>> 16) &&& 0x1FF#64; let w3 := w0 &&& 0x1FF#64
  let w4 := (w0 >>> 59) &&& 1#64; let w5 := (w0 >>> 58) &&& 1#64; let w6 := (w0 >>> 56) &&& 1#64
  let w7 := if (if regs 1 == 1#64 then 1#64 else 0#64) != 0#64 then w2
            else if (if regs 1 == 2#64 then 1#64 else 0#64) != 0#64 then w3 else regs 0
  let w8 := (w7 >>> 6) &&& 7#64; let w9 := w7 &&& 0x3F#64
  let w10 := ins 5 &&& (if regs 1 != 0#64 then 1#64 else 0#64)
  let w11 := regs 7 ||| (w10 &&& w6); let w12 := regs 8 ||| (w10 &&& w5)
  let w13 := if w11 != 0#64 then 0#64 else if w12 != 0#64 then 2#64
             else if (ins 7 &&& 1#64) != 0#64 then
               (if (((ins 7 >>> 1) &&& 1#64) &&& cuckooHwReadyVal ins regs) != 0#64 then 1#64 else 2#64)
             else 3#64
  let w14 := if regs 9 == 1#64 then 1#64 else 0#64
  refine (wire_foldl_step _ _ _ _ _ w0 hw0).trans ((wire_foldl_step _ _ _ _ _ w1 rfl).trans ?_)
  refine (wire_foldl_step _ _ _ _ _ w2 rfl).trans ((wire_foldl_step _ _ _ _ _ w3 rfl).trans ?_)
  refine (wire_foldl_step _ _ _ _ _ w4 rfl).trans ((wire_foldl_step _ _ _ _ _ w5 rfl).trans ?_)
  refine (wire_foldl_step _ _ _ _ _ w6 rfl).trans ((wire_foldl_step _ _ _ _ _ w7 rfl).trans ?_)
  refine (wire_foldl_step _ _ _ _ _ w8 rfl).trans ((wire_foldl_step _ _ _ _ _ w9 rfl).trans ?_)
  refine (wire_foldl_step _ _ _ _ _ w10 rfl).trans ((wire_foldl_step _ _ _ _ _ w11 rfl).trans ?_)
  refine (wire_foldl_step _ _ _ _ _ w12 rfl).trans ((wire_foldl_step _ _ _ _ _ w13 rfl).trans ?_)
  exact (wire_foldl_step _ _ _ _ _ w14 rfl).trans rfl

@[simp] private theorem cuckooWF_1 (ins regs : Nat → BitVec 64) (w0 : BitVec 64) : cuckooWireFnWith ins regs w0 1 = (w0 >>> 60) &&& 0xF#64 := rfl
@[simp] private theorem cuckooWF_3 (ins regs : Nat → BitVec 64) (w0 : BitVec 64) : cuckooWireFnWith ins regs w0 3 = w0 &&& 0x1FF#64 := rfl
@[simp] private theorem cuckooWF_4 (ins regs : Nat → BitVec 64) (w0 : BitVec 64) : cuckooWireFnWith ins regs w0 4 = (w0 >>> 59) &&& 1#64 := rfl
@[simp] private theorem cuckooWF_8 (ins regs : Nat → BitVec 64) (w0 : BitVec 64) :
    cuckooWireFnWith ins regs w0 8 = ((if (if regs 1 == 1#64 then 1#64 else 0#64) != 0#64 then (w0 >>> 16) &&& 0x1FF#64 else if (if regs 1 == 2#64 then 1#64 else 0#64) != 0#64 then w0 &&& 0x1FF#64 else regs 0) >>> 6) &&& 7#64 := rfl
@[simp] private theorem cuckooWF_9 (ins regs : Nat → BitVec 64) (w0 : BitVec 64) :
    cuckooWireFnWith ins regs w0 9 = (if (if regs 1 == 1#64 then 1#64 else 0#64) != 0#64 then (w0 >>> 16) &&& 0x1FF#64 else if (if regs 1 == 2#64 then 1#64 else 0#64) != 0#64 then w0 &&& 0x1FF#64 else regs 0) &&& 0x3F#64 := rfl
@[simp] private theorem cuckooWF_11 (ins regs : Nat → BitVec 64) (w0 : BitVec 64) :
    cuckooWireFnWith ins regs w0 11 = regs 7 ||| ((ins 5 &&& (if regs 1 != 0#64 then 1#64 else 0#64)) &&& ((w0 >>> 56) &&& 1#64)) := rfl
@[simp] private theorem cuckooWF_12 (ins regs : Nat → BitVec 64) (w0 : BitVec 64) :
    cuckooWireFnWith ins regs w0 12 = regs 8 ||| ((ins 5 &&& (if regs 1 != 0#64 then 1#64 else 0#64)) &&& ((w0 >>> 58) &&& 1#64)) := rfl
@[simp] private theorem cuckooWF_13 (ins regs : Nat → BitVec 64) (w0 : BitVec 64) :
    cuckooWireFnWith ins regs w0 13 = (if (regs 7 ||| ((ins 5 &&& (if regs 1 != 0#64 then 1#64 else 0#64)) &&& ((w0 >>> 56) &&& 1#64))) != 0#64 then 0#64 else if (regs 8 ||| ((ins 5 &&& (if regs 1 != 0#64 then 1#64 else 0#64)) &&& ((w0 >>> 58) &&& 1#64))) != 0#64 then 2#64 else if (ins 7 &&& 1#64) != 0#64 then (if (((ins 7 >>> 1) &&& 1#64) &&& cuckooHwReadyVal ins regs) != 0#64 then 1#64 else 2#64) else 3#64) := rfl
private def cuckooRegNextExpr (i : Nat) : RtlExpr :=
  match cuckooSiliconElabMemModule.core.regs[i]? with | some r => r.nextExpr | none => .const 0#64
private theorem cuckooStep_coreReg {i : Nat} (hi : i < 10) (ins : Nat → BitVec 64) (st : MemState) :
    (stepMemModule cuckooSiliconElabMemModule false ins st).regs i =
      evalRtlExpr ins (cuckooWireFnWith ins st.regs (evalRtlExpr ins (fun _ => 0#64) st.regs (mkBank8ReadMux (.regRead 2)))) st.regs (cuckooRegNextExpr i) := by
  have h : (stepMemModule cuckooSiliconElabMemModule false ins st).regs i = stepModuleRegs cuckooSiliconElabMemModule.core false ins st.regs i := by
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  rw [h]; unfold stepModuleRegs; rw [cuckooWireTable_eq]
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
private theorem cuckooStep_ramReg {b : Nat} (hb : b < 8) (ins : Nat → BitVec 64) (st : MemState) :
    (stepMemModule cuckooSiliconElabMemModule false ins st).regs (10 + b) =
      st.mems b (truncToWidth 6 (evalWireTable ins st.regs cuckooSiliconElabMemModule.core.wires 9)) := by
  have hTru64 : ∀ v : BitVec 64, truncToWidth 64 v = v := fun v => by change v &&& 0xFFFFFFFFFFFFFFFF#64 = v; exact BitVec.and_allOnes
  unfold stepMemModule; dsimp only [cuckooSiliconElabMemModule, evalSyncRamReadNext, evalRtlExpr, List.map, List.foldl]
  rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨ b = 5 ∨ b = 6 ∨ b = 7) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact hTru64 _
theorem cuckooZ4_rejects_sorry_or_mvar (st : MemState) (ins : Nat → BitVec 64)
    (hIn4 : ins 4 = 0#64) (hLatch : (ins 7 >>> 2) &&& 1#64 = 1#64) (hBad : st.regs 7 = 1#64 ∨ st.regs 8 = 1#64) :
    (stepMemModule cuckooSiliconElabMemModule false ins st).regs 9 ≠ 1#64 := by
  rw [cuckooStep_coreReg (by decide)]; generalize evalRtlExpr ins (fun _ => 0#64) st.regs (mkBank8ReadMux (.regRead 2)) = w0
  dsimp only [cuckooRegNextExpr, cuckooSiliconElabMemModule, List.getElem?_cons_zero, List.getElem?_cons_succ]
  simp only [evalRtlExpr, evalAluOp, cuckooWF_13, hIn4, show (2#64).toNat % 64 = 2 from rfl, hLatch, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, show (1#64 != 0#64) = true from rfl]
  have hOr1 : ∀ (x : BitVec 64), ((1#64 ||| x) != 0#64) = true := fun x => bne_iff_ne.mpr fun hZ => by have h := congrArg (fun v : BitVec 64 => v.getLsbD 0) hZ; simp at h
  have hIte : ∀ (c : Bool), (if c = true then (0#64 : BitVec 64) else 2#64) ≠ 1#64 := fun c => by cases c <;> decide
  rcases hBad with hS | hM; · rw [hS, hOr1, ifTrue rfl]; decide
  · rw [hM, hOr1, ifTrue rfl]; exact hIte _
theorem cuckooZ4_sticky_and_requires_work (st : MemState) (ins : Nat → BitVec 64) :
    (st.regs 7 = 1#64 → (stepMemModule cuckooSiliconElabMemModule false ins st).regs 7 = 1#64) ∧
    (st.regs 8 = 1#64 → (stepMemModule cuckooSiliconElabMemModule false ins st).regs 8 = 1#64) ∧
    (st.regs 5 = 0#64 → st.regs 9 ≠ 1#64 → (stepMemModule cuckooSiliconElabMemModule false ins st).regs 9 ≠ 1#64) ∧
    (st.regs 1 ≠ 0#64 ∨ st.regs 5 ≠ 0#64 → (stepMemModule cuckooSiliconElabMemModule false ins st).mems = st.mems) := by
  have hOrBit : ∀ (x : BitVec 64), 1#64 ||| (x &&& 1#64) = 1#64 := fun x => by
    apply BitVec.eq_of_toNat_eq; have h1 : (1#64).toNat = 2 ^ 1 - 1 := rfl
    simp only [BitVec.toNat_or, BitVec.toNat_and, h1, Nat.and_two_pow_sub_one_eq_mod]
    rcases (by omega : x.toNat % 2 = 0 ∨ x.toNat % 2 = 1) with h0 | h2
    · simp [h0]
    · simp [h2]
  refine ⟨fun h7 => ?_, fun h8 => ?_, fun h5 h9 => ?_, fun hLock => ?_⟩
  · rw [cuckooStep_coreReg (by decide)]; generalize evalRtlExpr ins (fun _ => 0#64) st.regs (mkBank8ReadMux (.regRead 2)) = w0
    dsimp only [cuckooRegNextExpr, cuckooSiliconElabMemModule, List.getElem?_cons_zero, List.getElem?_cons_succ]
    simp only [evalRtlExpr, cuckooWF_11, h7, ← BitVec.and_assoc]; exact hOrBit _
  · rw [cuckooStep_coreReg (by decide)]; generalize evalRtlExpr ins (fun _ => 0#64) st.regs (mkBank8ReadMux (.regRead 2)) = w0
    dsimp only [cuckooRegNextExpr, cuckooSiliconElabMemModule, List.getElem?_cons_zero, List.getElem?_cons_succ]
    simp only [evalRtlExpr, cuckooWF_12, h8, ← BitVec.and_assoc]; exact hOrBit _
  · rw [cuckooStep_coreReg (by decide)]; generalize evalRtlExpr ins (fun _ => 0#64) st.regs (mkBank8ReadMux (.regRead 2)) = w0
    dsimp only [cuckooRegNextExpr, cuckooSiliconElabMemModule, List.getElem?_cons_zero, List.getElem?_cons_succ]
    simp only [evalRtlExpr, evalAluOp, cuckooWF_13, cuckooHwReadyVal, h5, show (2#64).toNat % 64 = 2 from rfl, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, BitVec.zero_and, BitVec.and_zero]
    by_cases hc4 : (ins 4 != 0#64) = true
    · rw [ifTrue hc4]; decide
    · rw [ifFalse hc4]; by_cases hcL : (((ins 7 >>> 2) &&& 1#64) != 0#64) = true
      · rw [ifTrue hcL]
        by_cases hA : ((st.regs 7 ||| ((ins 5 &&& (if st.regs 1 != 0#64 then 1#64 else 0#64)) &&& ((w0 >>> 56) &&& 1#64))) != 0#64) = true
        · rw [ifTrue hA]; decide
        · rw [ifFalse hA]; by_cases hB : ((st.regs 8 ||| ((ins 5 &&& (if st.regs 1 != 0#64 then 1#64 else 0#64)) &&& ((w0 >>> 58) &&& 1#64))) != 0#64) = true
          · rw [ifTrue hB]; decide
          · rw [ifFalse hB]; cases ((ins 7 &&& 1#64) != 0#64) <;> decide
      · rw [ifFalse hcL]; exact h9
  · have hGate0 : ((if st.regs 1 == 0#64 then (1#64 : BitVec 64) else 0#64) &&& (if st.regs 5 == 0#64 then 1#64 else 0#64)) = 0#64 := by
      rcases hLock with h1 | h5
      · simp [beq_eq_false_iff_ne.mpr h1]
      · simp [beq_eq_false_iff_ne.mpr h5]
    dsimp only [stepMemModule, cuckooSiliconElabMemModule, stepSyncRamArray, List.map, List.foldl]
    simp only [evalRtlExpr, evalAluOp, truncToWidth]
    funext k; by_cases h0 : k = 0 <;> by_cases h1 : k = 1 <;> by_cases h2 : k = 2 <;> by_cases h3 : k = 3 <;>
      by_cases h4 : k = 4 <;> by_cases h5 : k = 5 <;> by_cases h6 : k = 6 <;> by_cases h7 : k = 7 <;> simp_all

private theorem cuckooStep_phase01 (appH lamH argH : CamHandle) (hAppB : appH < 512) (hLamB : lamH < 512) (hArgB : argH < 512)
    (appW lamW : PackedNodeWord) (sApp sLam : Bool) (hAppTag : appW.tag = 4) (hAppL : appW.h0 = lamH) (hAppR : appW.h1 = argH)
    (st0 st2 : MemState) (hR0 : st0.regs 0 = BitVec.ofNat 64 appH) (hR1 : st0.regs 1 = 0#64) (hR5 : st0.regs 5 = 0#64) (hR7 : st0.regs 7 = 0#64)
    (hMemApp : st0.mems (appH / 64) (BitVec.ofNat 64 (appH % 64)) = (packNodeWord128 appW sApp appH).lo64)
    (hMemLam : st0.mems (lamH / 64) (BitVec.ofNat 64 (lamH % 64)) = (packNodeWord128 lamW sLam lamH).lo64)
    (hd2 : stepMemModule cuckooSiliconElabMemModule false cuckooIdleStepInputs
      (stepMemModule cuckooSiliconElabMemModule false cuckooIdleStepInputs st0) = st2) :
    st2.mems = st0.mems ∧ st2.regs 0 = BitVec.ofNat 64 appH ∧ st2.regs 1 = 2#64 ∧
    st2.regs 2 = BitVec.ofNat 64 (lamH / 64) ∧ st2.regs 5 = 0#64 ∧
    st2.regs 7 = (if sApp then 1#64 else 0#64) ∧ st2.regs (10 + lamH / 64) = (packNodeWord128 lamW sLam lamH).lo64 := by
  obtain ⟨hAppBk, hAppRw, hAppBkLt⟩ := handle_bank_row hAppB; obtain ⟨hLamBk, hLamRw, hLamBkLt⟩ := handle_bank_row hLamB
  obtain ⟨hSlAppTag, _, _, hSlAppSor, hSlAppH0, _⟩ := packLo64_slices appW sApp appH (by omega) (by omega) (by rw [hAppR]; exact hArgB)
  rw [hAppTag] at hSlAppTag; rw [hAppL] at hSlAppH0
  generalize hd1 : stepMemModule cuckooSiliconElabMemModule false cuckooIdleStepInputs st0 = st1 at hd2
  have hM1 : st1.mems = st0.mems := hd1 ▸ cuckooIdle_mems_eq st0
  have hM2 : st2.mems = st0.mems := (hd2 ▸ cuckooIdle_mems_eq st1).trans hM1
  have hSt1 : st1.regs 0 = BitVec.ofNat 64 appH ∧ st1.regs 1 = 1#64 ∧ st1.regs 2 = BitVec.ofNat 64 (appH / 64) ∧
      st1.regs 5 = 0#64 ∧ st1.regs 7 = 0#64 ∧ st1.regs (10 + appH / 64) = (packNodeWord128 appW sApp appH).lo64 := by
    rw [← hd1]; refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [cuckooStep_coreReg (by decide)]; dsimp only [cuckooRegNextExpr, cuckooSiliconElabMemModule, List.getElem?_cons_zero, List.getElem?_cons_succ]; simp [cuckooIdleStepInputs, evalRtlExpr, evalAluOp, hR0, hR1]
    · rw [cuckooStep_coreReg (by decide)]; dsimp only [cuckooRegNextExpr, cuckooSiliconElabMemModule, List.getElem?_cons_zero, List.getElem?_cons_succ]; simp [cuckooIdleStepInputs, evalRtlExpr, evalAluOp, hR1]
    · rw [cuckooStep_coreReg (by decide)]; dsimp only [cuckooRegNextExpr, cuckooSiliconElabMemModule, List.getElem?_cons_zero, List.getElem?_cons_succ]; simp [cuckooIdleStepInputs, evalRtlExpr, hR0, hR1, hAppBk]
    · rw [cuckooStep_coreReg (by decide)]; dsimp only [cuckooRegNextExpr, cuckooSiliconElabMemModule, List.getElem?_cons_zero, List.getElem?_cons_succ]; simp [cuckooIdleStepInputs, evalRtlExpr, evalAluOp, hR1, hR5]
    · rw [cuckooStep_coreReg (by decide)]; dsimp only [cuckooRegNextExpr, cuckooSiliconElabMemModule, List.getElem?_cons_zero, List.getElem?_cons_succ]; simp [cuckooIdleStepInputs, evalRtlExpr, hR1, hR7]
    · rw [cuckooStep_ramReg hAppBkLt, cuckooWireTable_eq]; simpa [hR0, hR1, hAppRw] using hMemApp
  obtain ⟨h1_0, h1_1, h1_2, h1_5, h1_7, h1_ram⟩ := hSt1
  have hW0_1 := (evalBank8ReadMux_eq hAppBkLt h1_2).trans h1_ram
  refine ⟨hM2, ?_⟩; rw [← hd2]; refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [cuckooStep_coreReg (by decide), hW0_1]; dsimp only [cuckooRegNextExpr, cuckooSiliconElabMemModule, List.getElem?_cons_zero, List.getElem?_cons_succ]; simp [cuckooIdleStepInputs, evalRtlExpr, evalAluOp, h1_0, h1_1]
  · rw [cuckooStep_coreReg (by decide), hW0_1]; dsimp only [cuckooRegNextExpr, cuckooSiliconElabMemModule, List.getElem?_cons_zero, List.getElem?_cons_succ]; simp [cuckooIdleStepInputs, evalRtlExpr, evalAluOp, h1_1, hSlAppTag]
  · rw [cuckooStep_coreReg (by decide), hW0_1]; dsimp only [cuckooRegNextExpr, cuckooSiliconElabMemModule, List.getElem?_cons_zero, List.getElem?_cons_succ]; simp [cuckooIdleStepInputs, evalRtlExpr, h1_1, hSlAppH0, hLamBk]
  · rw [cuckooStep_coreReg (by decide), hW0_1]; dsimp only [cuckooRegNextExpr, cuckooSiliconElabMemModule, List.getElem?_cons_zero, List.getElem?_cons_succ]; simp [cuckooIdleStepInputs, evalRtlExpr, evalAluOp, h1_1, h1_5, hSlAppTag]
  · rw [cuckooStep_coreReg (by decide), hW0_1]; dsimp only [cuckooRegNextExpr, cuckooSiliconElabMemModule, List.getElem?_cons_zero, List.getElem?_cons_succ]; simp [cuckooIdleStepInputs, evalRtlExpr, h1_1, h1_7, hSlAppSor]; cases sApp <;> decide
  · rw [cuckooStep_ramReg hLamBkLt, hM1, cuckooWireTable_eq, hW0_1]; simpa [h1_1, hSlAppH0, hLamRw] using hMemLam

private theorem cuckooStep_phase23 (appH lamH bodyH : CamHandle) (hLamB : lamH < 512) (hBodyB : bodyH < 512)
    (lamW bodyW : PackedNodeWord) (sApp sLam sBody : Bool) (hLamTag : lamW.tag = 5) (hLamL : lamW.h0 < 512) (hLamR : lamW.h1 = bodyH)
    (hBodyTag : bodyW.tag < 16) (hBodyL : bodyW.h0 < 512) (hBodyR : bodyW.h1 < 512) (hClosed : bodyW.hasLooseBVar = false)
    (st0 st2 st4 : MemState) (hM2 : st2.mems = st0.mems) (h2_0 : st2.regs 0 = BitVec.ofNat 64 appH) (h2_1 : st2.regs 1 = 2#64)
    (h2_2 : st2.regs 2 = BitVec.ofNat 64 (lamH / 64)) (h2_5 : st2.regs 5 = 0#64) (h2_7 : st2.regs 7 = (if sApp then 1#64 else 0#64))
    (h2_ram : st2.regs (10 + lamH / 64) = (packNodeWord128 lamW sLam lamH).lo64)
    (hMemBody : st0.mems (bodyH / 64) (BitVec.ofNat 64 (bodyH % 64)) = (packNodeWord128 bodyW sBody bodyH).lo64)
    (hd4 : stepMemModule cuckooSiliconElabMemModule false cuckooIdleStepInputs
      (stepMemModule cuckooSiliconElabMemModule false cuckooIdleStepInputs st2) = st4) :
    st4.regs 0 = BitVec.ofNat 64 bodyH ∧ st4.regs 1 = 0#64 ∧ st4.regs 5 = 1#64 ∧ st4.regs 6 = 1#64 ∧
    st4.regs 7 = (if sApp || sLam || sBody then 1#64 else 0#64) := by
  obtain ⟨_, _, hLamBkLt⟩ := handle_bank_row hLamB; obtain ⟨hBodyBk, hBodyRw, hBodyBkLt⟩ := handle_bank_row hBodyB
  obtain ⟨hSlLamTag, _, _, hSlLamSor, _, hSlLamH1⟩ := packLo64_slices lamW sLam lamH (by omega) hLamL (by rw [hLamR]; exact hBodyB)
  obtain ⟨_, hSlBodyLoose, _, hSlBodySor, _, _⟩ := packLo64_slices bodyW sBody bodyH hBodyTag hBodyL hBodyR
  rw [hLamTag] at hSlLamTag; rw [hLamR] at hSlLamH1; rw [hClosed] at hSlBodyLoose
  generalize hd3 : stepMemModule cuckooSiliconElabMemModule false cuckooIdleStepInputs st2 = st3 at hd4
  have hW0_2 := (evalBank8ReadMux_eq hLamBkLt h2_2).trans h2_ram
  have hSt3 : st3.regs 0 = BitVec.ofNat 64 appH ∧ st3.regs 1 = 3#64 ∧ st3.regs 2 = BitVec.ofNat 64 (bodyH / 64) ∧
      st3.regs 4 = BitVec.ofNat 64 bodyH ∧ st3.regs 5 = 0#64 ∧ st3.regs 7 = (if sApp || sLam then 1#64 else 0#64) ∧
      st3.regs (10 + bodyH / 64) = (packNodeWord128 bodyW sBody bodyH).lo64 := by
    rw [← hd3]; refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [cuckooStep_coreReg (by decide), hW0_2]; dsimp only [cuckooRegNextExpr, cuckooSiliconElabMemModule, List.getElem?_cons_zero, List.getElem?_cons_succ]; simp [cuckooIdleStepInputs, evalRtlExpr, evalAluOp, h2_0, h2_1, hSlLamTag]
    · rw [cuckooStep_coreReg (by decide), hW0_2]; dsimp only [cuckooRegNextExpr, cuckooSiliconElabMemModule, List.getElem?_cons_zero, List.getElem?_cons_succ]; simp [cuckooIdleStepInputs, evalRtlExpr, evalAluOp, h2_1, hSlLamTag]
    · rw [cuckooStep_coreReg (by decide), hW0_2]; dsimp only [cuckooRegNextExpr, cuckooSiliconElabMemModule, List.getElem?_cons_zero, List.getElem?_cons_succ]; simp [cuckooIdleStepInputs, evalRtlExpr, h2_1, hSlLamH1, hBodyBk]
    · rw [cuckooStep_coreReg (by decide), hW0_2]; dsimp only [cuckooRegNextExpr, cuckooSiliconElabMemModule, List.getElem?_cons_zero, List.getElem?_cons_succ]; simp [cuckooIdleStepInputs, evalRtlExpr, evalAluOp, h2_1, hSlLamH1]
    · rw [cuckooStep_coreReg (by decide), hW0_2]; dsimp only [cuckooRegNextExpr, cuckooSiliconElabMemModule, List.getElem?_cons_zero, List.getElem?_cons_succ]; simp [cuckooIdleStepInputs, evalRtlExpr, evalAluOp, h2_1, h2_5, hSlLamTag]
    · rw [cuckooStep_coreReg (by decide), hW0_2]; dsimp only [cuckooRegNextExpr, cuckooSiliconElabMemModule, List.getElem?_cons_zero, List.getElem?_cons_succ]; simp [cuckooIdleStepInputs, evalRtlExpr, h2_1, h2_7, hSlLamSor]; cases sApp <;> cases sLam <;> decide
    · rw [cuckooStep_ramReg hBodyBkLt, hM2, cuckooWireTable_eq, hW0_2]; simpa [h2_1, hSlLamH1, hBodyRw] using hMemBody
  obtain ⟨_, h3_1, h3_2, h3_4, h3_5, h3_7, h3_ram⟩ := hSt3
  have hW0_3 := (evalBank8ReadMux_eq hBodyBkLt h3_2).trans h3_ram
  rw [← hd4]; refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [cuckooStep_coreReg (by decide), hW0_3]; dsimp only [cuckooRegNextExpr, cuckooSiliconElabMemModule, List.getElem?_cons_zero, List.getElem?_cons_succ]; simp [cuckooIdleStepInputs, evalRtlExpr, evalAluOp, h3_1, h3_4, hSlBodyLoose]
  · rw [cuckooStep_coreReg (by decide), hW0_3]; dsimp only [cuckooRegNextExpr, cuckooSiliconElabMemModule, List.getElem?_cons_zero, List.getElem?_cons_succ]; simp [cuckooIdleStepInputs, evalRtlExpr, evalAluOp, h3_1]
  · rw [cuckooStep_coreReg (by decide), hW0_3]; dsimp only [cuckooRegNextExpr, cuckooSiliconElabMemModule, List.getElem?_cons_zero, List.getElem?_cons_succ]; simp [cuckooIdleStepInputs, evalRtlExpr, evalAluOp, h3_1, h3_5]
  · rw [cuckooStep_coreReg (by decide), hW0_3]; dsimp only [cuckooRegNextExpr, cuckooSiliconElabMemModule, List.getElem?_cons_zero, List.getElem?_cons_succ]; simp [cuckooIdleStepInputs, evalRtlExpr, evalAluOp, h3_1, hSlBodyLoose]
  · rw [cuckooStep_coreReg (by decide), hW0_3]; dsimp only [cuckooRegNextExpr, cuckooSiliconElabMemModule, List.getElem?_cons_zero, List.getElem?_cons_succ]; simp [cuckooIdleStepInputs, evalRtlExpr, h3_1, h3_7, hSlBodySor]; cases sApp <;> cases sLam <;> cases sBody <;> decide

/-- **Cycle-Accurate 8-Bank `SyncRam` WHNF Simulation & Node-Metadata Zone-4 Gate (`cuckooElabRtl_simulates_stepCamWhnf`)**. -/
theorem cuckooElabRtl_simulates_stepCamWhnf
    (cam : HwExprCAM) (appH lamH bodyH argH : CamHandle)
    (hAppB : appH < 512) (hLamB : lamH < 512) (hBodyB : bodyH < 512) (hArgB : argH < 512)
    (appW lamW bodyW : PackedNodeWord) (sApp sLam sBody : Bool)
    (hApp : cam.nodes[appH]? = some appW) (hAppTag : appW.tag = 4) (hAppL : appW.h0 = lamH) (hAppR : appW.h1 = argH)
    (hLam : cam.nodes[lamH]? = some lamW) (hLamTag : lamW.tag = 5) (hLamL : lamW.h0 < 512) (hLamR : lamW.h1 = bodyH)
    (hBody : cam.nodes[bodyH]? = some bodyW) (hBodyTag : bodyW.tag < 16)
    (hBodyL : bodyW.h0 < 512) (hBodyR : bodyW.h1 < 512) (hClosed : bodyW.hasLooseBVar = false)
    (st0 : MemState)
    (hR0 : st0.regs 0 = BitVec.ofNat 64 appH) (hR1 : st0.regs 1 = 0#64) (hR5 : st0.regs 5 = 0#64) (hR7 : st0.regs 7 = 0#64)
    (hMemApp  : st0.mems (appH / 64)  (BitVec.ofNat 64 (appH % 64))  = (packNodeWord128 appW sApp appH).lo64)
    (hMemLam  : st0.mems (lamH / 64)  (BitVec.ofNat 64 (lamH % 64))  = (packNodeWord128 lamW sLam lamH).lo64)
    (hMemBody : st0.mems (bodyH / 64) (BitVec.ofNat 64 (bodyH % 64)) = (packNodeWord128 bodyW sBody bodyH).lo64) :
    let st4 := runMemModuleTrace cuckooSiliconElabMemModule st0 (List.replicate 4 (false, cuckooIdleStepInputs))
    let sw1 := stepCamWhnf { cam := cam, focusHandle := appH, argStack := [], done := false, steps := 0 }
    st4.regs 0 = BitVec.ofNat 64 sw1.focusHandle ∧ st4.regs 1 = 0#64 ∧
    st4.regs 5 = BitVec.ofNat 64 sw1.steps ∧ st4.regs 6 = 1#64 ∧
    st4.regs 7 = (if sApp || sLam || sBody then 1#64 else 0#64) ∧
    (∀ (st : MemState) (ins : Nat → BitVec 64),
      ins 4 = 0#64 → (ins 7 >>> 2) &&& 1#64 = 1#64 → (st.regs 7 = 1#64 ∨ st.regs 8 = 1#64) →
      (stepMemModule cuckooSiliconElabMemModule false ins st).regs 9 ≠ 1#64) := by
  have hSw := stepCamWhnf_closed_beta_one_step cam appH lamH bodyH argH appW lamW bodyW
    hApp hAppTag hAppL hAppR hLam hLamTag hLamR hBody hClosed
  generalize hst4 : runMemModuleTrace cuckooSiliconElabMemModule st0 (List.replicate 4 (false, cuckooIdleStepInputs)) = st4
  have hTr : runMemModuleTrace cuckooSiliconElabMemModule st0 (List.replicate 4 (false, cuckooIdleStepInputs)) =
      stepMemModule cuckooSiliconElabMemModule false cuckooIdleStepInputs
        (stepMemModule cuckooSiliconElabMemModule false cuckooIdleStepInputs
          (stepMemModule cuckooSiliconElabMemModule false cuckooIdleStepInputs
            (stepMemModule cuckooSiliconElabMemModule false cuckooIdleStepInputs st0))) := rfl
  rw [hTr] at hst4; dsimp only; rw [hSw]; dsimp only
  generalize hd2 : stepMemModule cuckooSiliconElabMemModule false cuckooIdleStepInputs
    (stepMemModule cuckooSiliconElabMemModule false cuckooIdleStepInputs st0) = st2 at hst4
  obtain ⟨hM2, h2_0, h2_1, h2_2, h2_5, h2_7, h2_ram⟩ := cuckooStep_phase01 appH lamH argH hAppB hLamB hArgB
    appW lamW sApp sLam hAppTag hAppL hAppR st0 st2 hR0 hR1 hR5 hR7 hMemApp hMemLam hd2
  obtain ⟨h4_0, h4_1, h4_5, h4_6, h4_7⟩ := cuckooStep_phase23 appH lamH bodyH hLamB hBodyB lamW bodyW sApp sLam sBody
    hLamTag hLamL hLamR hBodyTag hBodyL hBodyR hClosed st0 st2 st4 hM2 h2_0 h2_1 h2_2 h2_5 h2_7 h2_ram hMemBody hst4
  exact ⟨h4_0, h4_1, h4_5, h4_6, h4_7, cuckooZ4_rejects_sorry_or_mvar⟩

end Obend.Lower.SiliconElabFabric
end
