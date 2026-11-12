module
/-
# SiliconRealismTest — End-to-End Verification & `#tooth` Refutation Suite

Tests all architectural realism invariants with universally quantified theorems, negative-pole
refusal checks, `#tooth` kernel mutation probes, and `#print axioms` verification (`0 sorryAx`):

1. **Upgrade 1 (`Obend.Lower.LeanKernel` & `Obend.Lower.Proofs.SiliconKernel`)**:
   - `kernelIsDefEqFull`: `Nat` literal ↔ `Nat.zero` / `Nat.succ` bridging, fail-closed lambda
     $\eta$-equivalence (`etaDomCompat_fail_closed_sound`), `Sort 0` (`Prop`) proof irrelevance,
     universe-polymorphic `reduceGeneralIota?_univ_poly_sound`, and universal 5-stage `kernelGateLExpr`
     hardware agreement (`silicon_kernel_5stage_check_sound`).
2. **Upgrade 2 (`Obend.Lower.ExprCAM`)**:
   - Pure integer/word hardware CAM memory image (`HwCamNodeWord`, `HwCamImage`, `HwExprCAM`) with
     first-class `.mvar` (`tag == 10`) and 3-child `letE` (`h0, h1, h2`), universal lossless roundtrip
     `reconstructFromHwImage_intern_roundtrip`, `.proj` no-double-offset (`fromLeanExprWithProjShift_no_double_offset`),
     `FastHwExprCAM` $O(1)$ hash-consed environment cone interning, and universal open substitution
     `reconstructFromHwExprCAM_hwCamInstantiateAt`.
3. **Upgrade 3 (`Obend.Hardware.ReductionMachine`)**:
   - Spatial packet-switched 2D XY NoC transition system (`noc_step_conserves_flits`,
     `stepNocRouter_conserves_flits_and_credits`) and `dprTile_moved_pin_blocks`.
4. **Upgrade 4 (`Obend.Hardware.Compiler`)**:
   - Structural 2-state linear recurrence extractor (`compileLinearRec2State_sound`) and inter-slot
     pipelined call argument wiring (`compileTermPipelined_arg_wired_and_stage_correspondence`).
-/
public import Obend.Tactic.Tooth
import all Obend.Lower.LeanKernel
import all Obend.Lower.ExprCAM
import all Obend.Lower.Proofs.SiliconKernel
import all Obend.Hardware.ReductionMachine
import all Obend.Hardware.Compiler
public import Obend.Lower.LeanKernel
public import Obend.Lower.ExprCAM
public import Obend.Lower.Proofs.SiliconKernel
public import Obend.Hardware.ReductionMachine
public import Obend.Hardware.Compiler
@[expose] public section

namespace Obend.Tests.SiliconRealism
open Obend.Core.Term
open Obend.Logic
open Obend.Slot
open Obend.Slot.World
open Obend.Leaf
open Obend.Lower
open Obend.Lower.Inductive
open Obend.Lower.LeanKernel
open Obend.Lower.ExprCAM
open Obend.Lower.Proofs.SiliconKernel
open Obend.Hardware.HDL
open Obend.Hardware.Compiler
open Obend.Hardware.ReductionMachine
set_option autoImplicit false

/-! ## 1. Upgrade 1: Full Definitional Equality (`kernelIsDefEqFull`), Polymorphic $\iota$ & 5-Stage Kernel Gate -/

theorem silicon_realism_defeq_and_lowered_kernel_suite :
    (∀ (env : KEnv) (fuel : Nat) (e : KExpr) (ctx : List KExpr),
      kernelIsDefEqFull env fuel e e ctx = true) ∧
    (∀ (env : KEnv) (fuel : Nat) (n : Nat) (ctx : List KExpr),
      kernelIsDefEqFull env (fuel + 2)
        (.lit (.natVal (n + 1)))
        (.app (.const (KName.mkSimple "Nat.succ") []) (.lit (.natVal n))) ctx = true) ∧
    kernelIsDefEqFull defEqFullTestEnv 8
      (.lam kNatConst (.app (.const (KName.mkSimple "extFn") []) (.bvar 0)))
      (.const (KName.mkSimple "extFn") []) [] = true ∧
    kernelIsDefEqFull defEqFullTestEnv 8
      (.lam kNatConst (.lit (.natVal 0)))
      (.lam kBoolConst (.lit (.natVal 0))) [] = false ∧
    kernelIsDefEqFull defEqFullTestEnv 8
      (.lam kBoolConst (.app (.const (KName.mkSimple "extFn") []) (.bvar 0)))
      (.const (KName.mkSimple "extFn") []) [] = false ∧
    kernelIsDefEqFull defEqFullTestEnv 8
      (.const (KName.mkSimple "proof1") [])
      (.const (KName.mkSimple "proof2") []) [] = true ∧
    kernelIsDefEqFull defEqFullTestEnv 8
      (.lit (.natVal 0))
      (.lit (.natVal 1)) [] = false ∧
    SSteps (.app kernelGateLExpr (.lit (kernelDeclStatusTag stdKernelEnv 8 validIdNatDecl))) (.lit 1) ∧
    SSteps (.app kernelGateLExpr (.lit (kernelDeclStatusTag stdKernelEnv 8 invalidMismatchDecl))) (.lit 0) ∧
    SSteps (.app kernelGateLExpr (.lit (kernelDeclStatusTag stdKernelEnv 8 invalidSorryDecl))) (.lit 0) := by
  refine ⟨fun env fuel e ctx => kernelIsDefEqFull_refl env fuel e ctx,
          fun env fuel n ctx => kernelIsDefEqFull_nat_succ_bridge env fuel n ctx,
          rfl,
          rfl,
          rfl,
          rfl,
          rfl,
          (silicon_kernel_5stage_check_sound stdKernelEnv 8 validIdNatDecl).1,
          (silicon_kernel_5stage_check_sound stdKernelEnv 8 invalidMismatchDecl).1,
          (silicon_kernel_5stage_check_sound stdKernelEnv 8 invalidSorryDecl).1⟩

/-! ## 2. Upgrade 2: Lossless `HwCamImage` & `FastHwExprCAM` Without AST Side-Channel -/

/-- Complex `KExpr` term exercising `letE` (3 distinct child handles), `forallE`, `lam`, `app`,
`proj`, `const`, `fvar`, `mvar`, `bvar`, `lit`, and `sort`. -/
def sampleDeepLetKExpr : KExpr :=
  .letE
    kNatConst
    (.app (.const (KName.mkSimple "idNat") [.zero]) (.lit (.natVal 42)))
    (.lam
      (.forallE kNatConst (.sort .zero))
      (.app
        (.app (.proj (KName.mkSimple "Prod") 1 (.fvar 7)) (.mvar 5))
        (.bvar 0)))

private theorem allocFastSymbol_consts (s : HwCamSymbolEntry) (fc : FastHwExprCAM) :
    (allocFastSymbol s fc).2.consts = fc.consts := by
  unfold allocFastSymbol
  split <;> rfl

private theorem allocFastNode_consts (w : PackedNodeWord) (fc : FastHwExprCAM) :
    (allocFastNode w fc).2.consts = fc.consts := by
  unfold allocFastNode
  split <;> rfl

private theorem internToFastHwExprCAM_consts :
    ∀ (e : KExpr) (fc : FastHwExprCAM), (internToFastHwExprCAM e fc).2.consts = fc.consts
  | .bvar _, fc => allocFastNode_consts _ fc
  | .fvar _, fc => allocFastNode_consts _ fc
  | .mvar _, fc => allocFastNode_consts _ fc
  | .sort _, fc => by
    simp only [internToFastHwExprCAM, allocFastNode_consts, allocFastSymbol_consts]
  | .const _ _, fc => by
    simp only [internToFastHwExprCAM, allocFastNode_consts, allocFastSymbol_consts]
  | .app f a, fc => by
    simp only [internToFastHwExprCAM, allocFastNode_consts]
    rw [internToFastHwExprCAM_consts a, internToFastHwExprCAM_consts f]
  | .lam d b, fc => by
    simp only [internToFastHwExprCAM, allocFastNode_consts]
    rw [internToFastHwExprCAM_consts b, internToFastHwExprCAM_consts d]
  | .forallE d b, fc => by
    simp only [internToFastHwExprCAM, allocFastNode_consts]
    rw [internToFastHwExprCAM_consts b, internToFastHwExprCAM_consts d]
  | .letE t v b, fc => by
    simp only [internToFastHwExprCAM, allocFastNode_consts]
    rw [internToFastHwExprCAM_consts b, internToFastHwExprCAM_consts v, internToFastHwExprCAM_consts t]
  | .lit _, fc => by
    simp only [internToFastHwExprCAM, allocFastNode_consts, allocFastSymbol_consts]
  | .proj _ _ s, fc => by
    simp only [internToFastHwExprCAM, allocFastNode_consts, allocFastSymbol_consts]
    exact internToFastHwExprCAM_consts s fc

theorem internKEnvConeFast_consts_length (env : KEnv) :
    (internKEnvConeFast env).consts.length = env.constants.length := by
  unfold internKEnvConeFast FastHwExprCAM.toHwExprCAM
  dsimp only
  have hRec :
      ∀ (rs : List KRecRule) (fc : FastHwExprCAM),
        (rs.foldl
          (fun fc r =>
            let (rhsH, fcA) := internToFastHwExprCAM r.rhs fc
            let entry : HwCamRecRuleEntry :=
              { recName := r.recName, ctorName := r.ctorName, numParams := r.numPrefixArgs, numFields := r.numFields, rhsHandle := rhsH }
            let recLP :=
              if r.levelParams.isEmpty || fcA.recLevelParams.any (fun p => p.1 == r.recName) then fcA.recLevelParams
              else fcA.recLevelParams ++ [(r.recName, r.levelParams)]
            { fcA with recRules := fcA.recRules.push entry, recLevelParams := recLP })
          fc).consts = fc.consts := by
    intro rs
    induction rs with
    | nil => intro fc; rfl
    | cons r rs ih =>
      intro fc
      simp only [List.foldl_cons]
      rw [ih]
      dsimp only
      exact internToFastHwExprCAM_consts r.rhs fc
  rw [hRec]
  have hConsts :
      ∀ (cs : List KConstInfo) (fc : FastHwExprCAM),
        (cs.foldl
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
          fc).consts.size = fc.consts.size + cs.length := by
    intro cs
    induction cs with
    | nil => intro fc; simp
    | cons c cs ih =>
      intro fc
      simp only [List.foldl_cons, List.length_cons]
      rw [ih]
      cases c <;>
        simp [Array.size_push, internToFastHwExprCAM_consts, allocFastSymbol_consts] <;>
        omega
  have hSize := hConsts env.constants FastHwExprCAM.empty
  simp [Array.length_toList, FastHwExprCAM.empty] at hSize ⊢
  exact hSize

theorem silicon_realism_hw_cam_image_roundtrip_suite :
    (∀ (fuel : Nat) (e : KExpr) (img : HwCamImage),
      KExpr.depth e ≤ fuel →
      reconstructFromHwImage fuel (internToHwImage e img).2 (internToHwImage e img).1 = some e) ∧
    (let res := internToHwImage sampleDeepLetKExpr emptyHwCamImage
     reconstructFromHwImage 16 res.2 res.1 = some sampleDeepLetKExpr) ∧
    (let (h1, img1) := internToHwImage sharedSubtermExpr emptyHwCamImage
     let (h2, img2) := internToHwImage sharedSubtermExpr img1
     img1.nodes.length = 6 ∧ h1 = h2 ∧ img2.nodes.length = 6 ∧
     reconstructFromHwImage 8 img1 h1 = some sharedSubtermExpr) ∧
    (∀ (env : KEnv), (internKEnvConeFast env).consts.length = env.constants.length) ∧
    reconstructFromHwImage 0 (internToHwImage sampleDeepLetKExpr emptyHwCamImage).2
      (internToHwImage sampleDeepLetKExpr emptyHwCamImage).1 = none := by
  refine ⟨reconstructFromHwImage_intern_roundtrip, ?_, ⟨rfl, rfl, rfl, rfl⟩, internKEnvConeFast_consts_length, rfl⟩
  exact reconstructFromHwImage_intern_roundtrip 16 sampleDeepLetKExpr emptyHwCamImage (by decide +kernel)

/-! ## 3. Upgrade 3: Spatial Packet-Switched 2D XY NoC & `dprTileSlot` Pin-Guarded DPR -/

theorem silicon_realism_noc_and_dpr_slot_suite :
    (∀ (fab : NocFabric) (t : NocTileState),
      tileTotalFlits (stepNocRouter t) = tileTotalFlits t ∧
      tileCreditsPlusOutbox (stepNocRouter t) = tileCreditsPlusOutbox t ∧
      fabricTotalFlits (stepNocFabric fab) = fabricTotalFlits fab ∧
      fabricCreditsPlusOutbox (stepNocFabric fab) = fabricCreditsPlusOutbox fab) ∧
    (∀ (t : NocTileState),
      tileTotalFlits (stepNocRouter t) = tileTotalFlits t ∧
      tileCreditsPlusOutbox (stepNocRouter t) = tileCreditsPlusOutbox t) ∧
    (∀ {v : LeafView} {name : String} {C : Composition}
       (specTile baseTile : AutomatonTile) (digest : BitVec 64),
      C.closedB = true →
      (digest != 0#64) = true →
      ∀ {p : LeafPin}, p ∈ (Candidate.book name C).supports → holdsAt v p = false →
      (∃ d, specSlot.read (holdsAt v) (some (.book name C)) = .blocked (.book name C) d ∧ p ∈ d) ∧
      (∃ d, dprTileSlot.read (holdsAt v) (some (.specializedTile name C specTile digest)) =
        .blocked (.specializedTile name C specTile digest) d ∧ p ∈ d) ∧
      (slotAdvance : Advance LeafView LeafPin TileBitstreamCandidate).advance
          dprTileSlot v (dprTileOrder name C specTile baseTile digest)
          (some (.specializedTile name C specTile digest)) =
        .ok (.baselineTile baseTile)) := by
  exact ⟨noc_step_conserves_flits,
         stepNocRouter_conserves_flits_and_credits,
         fun {_} {_} {_} specTile baseTile digest hj hdig {_} hp hd =>
           dprTile_moved_pin_blocks specTile baseTile digest hj hdig hp hd⟩

/-! ## 4. Upgrade 4: Structural 2-State Linear Recurrence & Pipelined Call Wiring -/

theorem silicon_realism_compiler_suite :
    (∀ (nVal init0 init1 cCurr cPrev k : Nat),
      k ≤ nVal →
      runLinearRec2StateLoop nVal init0 init1 cCurr cPrev k =
        (k,
         (linearRec2StateSpec init0 init1 cCurr cPrev k).1,
         (linearRec2StateSpec init0 init1 cCurr cPrev k).2)) ∧
    (∀ (cCurr cPrev : Nat),
      extractTwoStateCombCoeffs
        (.binary .add (.binary .multiply (.bound 2) (.nat cPrev)) (.binary .multiply (.bound 0) (.nat cCurr))) =
        some (cCurr, cPrev) ∧
      extractTwoStateCombCoeffs
        (.binary .add (.binary .multiply (.bound 0) (.nat cCurr)) (.bound 6)) =
        some (cCurr, 1)) ∧
    (∀ (inputs wires regs : Nat → BitVec 64) (slots : List String) (slotBodies : List RtlExpr)
       (t : Term) (selfDepth : Nat) (varEnv : List RtlExpr) (e : RtlExpr),
      compileTermPipelined slots slotBodies selfDepth varEnv t = some e →
      evalTermPipelinedHw slots slotBodies inputs wires regs selfDepth
        (varEnv.map (evalRtlExpr inputs wires regs)) t =
        some (evalRtlExpr inputs wires regs e)) ∧
    (∀ (k : Nat) (inputs wires regs : Nat → BitVec 64),
      let calleeBody := RtlExpr.alu .mul (.inputPort 0) (.const 3#64)
      let directCall := Term.app (.get (.bound 1) "scale3") (.bound 0)
      let nonDirectCall := Term.app (.get (.bound 1) "scale3") (.nat k)
      let expectedRtl := RtlExpr.alu .mul (.const (BitVec.ofNat 64 k)) (.const 3#64)
      compileTermPipelined ["scale3", "caller"] [calleeBody] 1 [.inputPort 0] directCall = some (.regRead 0) ∧
      compileTermPipelined ["scale3", "caller"] [calleeBody] 1 [.inputPort 0] nonDirectCall = some expectedRtl ∧
      compileTermPipelined ["scale3", "caller"] [] 1 [.inputPort 0] nonDirectCall = none ∧
      evalRtlExpr inputs wires regs expectedRtl = BitVec.ofNat 64 k * 3#64 ∧
      evalTermPipelinedHw ["scale3", "caller"] [calleeBody] inputs wires regs 1 [inputs 0] nonDirectCall =
        some (BitVec.ofNat 64 k * 3#64)) :=
  ⟨compileLinearRec2State_sound.1,
   fun _ _ => ⟨rfl, rfl⟩,
   compileTermPipelined_sound,
   compileTermPipelined_arg_wired_and_stage_correspondence⟩

/-! ## 5. Six `#tooth` Kernel Mutation Probes Across All 4 Upgrades -/

/-- 1. Broken `etaDomCompat` in `Obend.Lower.LeanKernel` that defaults `none ↦ true`, unsoundly
permitting one-sided $\lambda$-$\eta$ expansion against untyped free variables. -/
def etaDomCompatFailOpenProbe (env : KEnv) (fuel : Nat)
    (inferPrev : List KExpr → KExpr → Option KExpr)
    (defEqPrev : List KExpr → KExpr → KExpr → Bool)
    (ctx : List KExpr) (dom other : KExpr) : Bool :=
  match inferPrev ctx other with
  | some otherTy =>
    match kernelWhnf env fuel otherTy with
    | .forallE otherDom _ => defEqPrev ctx dom otherDom
    | _ => false
  | none => true

#tooth Obend.Lower.LeanKernel.etaDomCompat_fail_closed_sound by mutation Obend.Lower.LeanKernel.etaDomCompat := etaDomCompatFailOpenProbe

/-- 2. Broken `reconstructFromHwImage` in `Obend.Lower.ExprCAM` that reads `w.h1` twice on `.letE`
(`tag == 7`) instead of distinct `w.h1` (`val`) and `w.h2` (`body`). -/
def reconstructFromHwImageLossyLet : Nat → HwCamImage → Nat → Option KExpr
  | 0, _, _ => none
  | fuel + 1, img, h =>
    match img.nodes[h]? with
    | none => none
    | some w =>
      if w.tag == 0 then
        some (.bvar w.h0)
      else if w.tag == 7 then
        match reconstructFromHwImageLossyLet fuel img w.h0,
              reconstructFromHwImageLossyLet fuel img w.h1,
              reconstructFromHwImageLossyLet fuel img w.h1 with
        | some t, some v, some b => some (.letE t v b)
        | _, _, _ => none
      else
        none

#tooth Obend.Lower.ExprCAM.reconstructFromHwImage_intern_roundtrip by mutation Obend.Lower.ExprCAM.reconstructFromHwImage := reconstructFromHwImageLossyLet

/-- 3. Broken `stepNocRouter` in `Obend.Hardware.ReductionMachine` that drops transit flits. -/
def stepNocRouterDropTransit (t : NocTileState) : NocTileState :=
  if t.credits == 0 then
    t
  else
    match t.inbox with
    | [] => t
    | _ :: rest => { t with inbox := rest }

#tooth Obend.Hardware.ReductionMachine.noc_step_conserves_flits by mutation Obend.Hardware.ReductionMachine.stepNocRouter := stepNocRouterDropTransit

/-- 4. Broken `TileBitstreamCandidate.supports` in `Obend.Hardware.ReductionMachine` that forgets to
pin `(Candidate.book name C).supports` on `.specializedTile`. -/
def dprTileSupportsUnpinned : TileBitstreamCandidate → List LeafPin
  | .specializedTile _ _ _ _ => []
  | .baselineTile _          => []

#tooth Obend.Hardware.ReductionMachine.dprTile_moved_pin_blocks by mutation Obend.Hardware.ReductionMachine.TileBitstreamCandidate.supports := dprTileSupportsUnpinned

/-- Universal structural extraction projection of `compileLinearRec2State_sound`. -/
theorem extractTwoStateLinearRec_mkTwoStateLinearRecTerm (init0 init1 cCurr cPrev : Nat) :
    extractTwoStateLinearRec (mkTwoStateLinearRecTerm init0 init1 cCurr cPrev) =
      some (init0, init1, cCurr, cPrev) :=
  compileLinearRec2State_sound.2.1 init0 init1 cCurr cPrev

/-- 5. Broken `extractTwoStateLinearRec` in `Obend.Hardware.Compiler` returning hardcoded `(0, 1, 1, 1)`. -/
def extractTwoStateLinearRecHardcodedFib (_ : Term) : Option (Nat × Nat × Nat × Nat) :=
  some (0, 1, 1, 1)

#tooth extractTwoStateLinearRec_mkTwoStateLinearRecTerm by mutation Obend.Hardware.Compiler.extractTwoStateLinearRec := extractTwoStateLinearRecHardcodedFib

/-- 6. Broken `compileTermPipelined` in `Obend.Hardware.Compiler` discarding the compiled call argument. -/
def compileTermPipelinedDiscardArg
    (slots : List String)
    (slotBodies : List RtlExpr)
    (selfDepth : Nat)
    (varEnv : List RtlExpr) :
    Term → Option RtlExpr
  | .record [] => some (.const 0#64)
  | .nat n => some (.const (BitVec.ofNat 64 n))
  | .boolean b => some (.const (if b then 1#64 else 0#64))
  | .bound idx => varEnv[idx]?
  | .get (.bound idx) member =>
    if idx == selfDepth then
      match slots.idxOf? member with
      | some slotIdx => some (.regRead slotIdx)
      | none => none
    else none
  | .app fn arg =>
    match fn with
    | .get (.bound idx) member =>
      if idx == selfDepth then
        match slots.idxOf? member,
              compileTermPipelinedDiscardArg slots slotBodies selfDepth varEnv arg with
        | some slotIdx, some _ =>
          some (.regRead slotIdx)
        | _, _ => none
      else none
    | _ => none
  | _ => none

#tooth Obend.Hardware.Compiler.compileTermPipelined_arg_wired_and_stage_correspondence by mutation Obend.Hardware.Compiler.compileTermPipelined := compileTermPipelinedDiscardArg

/-! ## 6. Axiom Hygiene Verification (`0 sorryAx`, `0` Custom Axioms) -/

#print axioms Obend.Lower.LeanKernel.kernelIsDefEqFull_refl
#print axioms Obend.Lower.LeanKernel.kernelIsDefEqFull_nat_succ_bridge
#print axioms Obend.Lower.LeanKernel.etaDomCompat_fail_closed_sound
#print axioms Obend.Lower.LeanKernel.stepLExpr?_sound
#print axioms Obend.Lower.LeanKernel.runLExprSteps_sound
#print axioms Obend.Lower.Proofs.SiliconKernel.silicon_kernel_5stage_check_sound
#print axioms Obend.Lower.ExprCAM.reconstructFromHwImage_mono
#print axioms Obend.Lower.ExprCAM.reconstructFromHwImage_intern_roundtrip
#print axioms Obend.Lower.ExprCAM.reconstructFromHwExprCAM_hwCamInstantiateAt
#print axioms Obend.Lower.ExprCAM.fromLeanExprWithProjShift_no_double_offset
#print axioms Obend.Hardware.ReductionMachine.stepNocRouter_conserves_flits_and_credits
#print axioms Obend.Hardware.ReductionMachine.noc_step_conserves_flits
#print axioms Obend.Hardware.ReductionMachine.noc_multi_hop_delivery_and_eval_sound
#print axioms Obend.Hardware.ReductionMachine.baselineTile_usable
#print axioms Obend.Hardware.ReductionMachine.dprTileSlot_choice
#print axioms Obend.Hardware.ReductionMachine.dprTile_moved_pin_blocks
#print axioms Obend.Hardware.Compiler.runLinearRec2StateLoop_le_bound
#print axioms Obend.Hardware.Compiler.compileLinearRec2State_sound
#print axioms Obend.Hardware.Compiler.compileTermPipelined_sound
#print axioms Obend.Hardware.Compiler.compileTermPipelined_arg_wired_and_stage_correspondence
#print axioms Obend.Tests.SiliconRealism.silicon_realism_defeq_and_lowered_kernel_suite
#print axioms Obend.Tests.SiliconRealism.silicon_realism_hw_cam_image_roundtrip_suite
#print axioms Obend.Tests.SiliconRealism.silicon_realism_noc_and_dpr_slot_suite
#print axioms Obend.Tests.SiliconRealism.silicon_realism_compiler_suite

end Obend.Tests.SiliconRealism
end
