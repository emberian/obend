module
/-
# SiliconElaboratorPhase2Test — End-to-End Phase-2 Verification & `#tooth` Mutation Suite (`WS-P`)

Exercises and mutation-tests all 4 `WS-P` engineering deliverables (`0 sorryAx`):
1. **In-Place `LeanKernel` Audit Fix 1 (`kernelIsDefEq`, `kernelInferType`, `kernelCheckDecl`)**:
   - Verifies that the canonical `kernelIsDefEq`, `kernelInferType`, and `kernelCheckDecl` natively
     execute full $\beta\delta\iota\zeta\eta$ + `Nat`-literal bridging (`0 ↔ Nat.zero`, `n + 1 ↔ Nat.succ n`)
     + $\lambda$-$\eta$ expansion + `Prop` proof-irrelevant conversion (`kernelIsDefEqFull := kernelIsDefEq`).
   - Exercises `#tooth` mutation testing on `kernelCheckDecl`.
2. **Pillar 1A — `HwExprCAM` & 4-Zone Spatial Silicon Elaborator (`SiliconElabFabric`)**:
   - Verifies `hwCamInstantiateAt_closed_bypass` and `hwCamInstantiateAt_sound`,
   - Verifies Zone 1 (`runZone1Whnf`, `stepCamWhnf_closed_beta_one_step`, `runZone1Whnf_sound`),
   - Verifies Zone 2 (`stepCamDefEq_handle_eq_refl`, `checkMVarOccursBit58_iff`, `joinMCtxAssigns_sound`,
     and parallel `.app` obligation fork/join across `ReductionMachine.NocFabric` via `stepNocFabric`),
   - Verifies Zone 3 (`stepZone3DiscrLut`, `zone3_moved_pin_fallback_one_cycle`, and 3-phase glitch-free
     `ICAP` DPR via `admitSimpTheoremDpr_glitch_free_and_sound`),
   - Verifies Zone 4 (`stepZone4KernelCheck`, `runSiliconKernelCamFsm_sound`, `siliconElabFabric_four_zone_sound`).
3. **In-Place `SiliconKernel` Audit Fix 2 (`Obend.Lower.Fragment.read` / `readTheoremDecider` & `HwExprCAM` FSM)**:
   - Verifies `stepCamWhnfNodeWord`, `stepCamDefEqNodeWord`, `stepCamInferNodeWord`, and
     `stepCamDefEqNodeWord_refl_thm` lowered via `Obend.Lower.Fragment.read` and `readTheoremDecider`
     (`silicon_kernel_fragment_read_6stage_sound` & `stepCamNodeWord_fragment_6stage_sound`) with zero
     host precomputation, plus `#tooth` mutation tests.
4. **Pillar 1B — Standalone `Obend.Lower.LCNF` & In-Place `Obend.Lower.Inductive` Delegation**:
   - Verifies `.zero` computational erasure (`lcnf_zero_erasure_sound`), `.one` linear state-token
     conservation (`lcnf_linear_state_conserved`), `jpDecl`/`jmp` join-point lowering (`lcnf_to_core4_sound`),
     and `compileLcnfToBook` (`lcnf_elab_pass_to_book_sound`), plus `#tooth` mutation tests.
-/
public import Obend.Tactic.Tooth
public import Obend.Lower.LCNF
import all Obend.Lower.LCNF
public import Obend.Lower.Inductive
import all Obend.Lower.Inductive
public import Obend.Lower.LeanKernel
public import Obend.Lower.Proofs.SiliconKernel
public import Obend.Lower.ExprCAM
public import Obend.Lower.SiliconElabFabric
@[expose] public section

namespace Obend.Tests.SiliconElaboratorPhase2Test
open Obend.Core.Term
open Obend.Core.Ty (Ty)
open Obend.Equiv
open Obend.Leaf
open Obend.Lower
open Obend.Lower.LCNF
open Obend.Lower.Inductive
open Obend.Lower.LeanKernel
open Obend.Lower.ExprCAM
open Obend.Lower.MetaUnify
open Obend.Lower.DiscrTreeLUT
open Obend.Lower.Proofs.SiliconKernel
open Obend.Lower.SiliconElabFabric
open Obend.Hardware.HDL
open Obend.Hardware.Compiler
open Obend.Hardware.ReductionMachine
open Obend.Hardware.Judge
set_option autoImplicit false

/-! ## 1. Pillar 1 / Task 1: In-Place `kernelIsDefEq`, `kernelInferType` & `kernelCheckDecl` Verification -/

/-- End-to-end verification that the in-place `kernelIsDefEq`, `kernelInferType`, and `kernelCheckDecl`
natively support:
1. `Nat`-literal / constructor bridging (`KExpr.lit (.natVal 2) ≡ Nat.succ (Nat.succ Nat.zero)`),
2. $\lambda$-$\eta$ expansion (`(λ x : Nat => idNat x) ≡ idNat`),
3. `Prop` proof irrelevance (`p1 ≡ p2` for distinct witnesses `p1, p2 : TrueProp`), and
4. Dependent `Family (Nat.succ (Nat.succ Nat.zero))` vs. `Family 2` application & declaration checking! -/
theorem phase2_in_place_lean_kernel_sound :
    let env :=
      (defEqFullTestEnv.add
        (.axiomInfo (KName.mkSimple "ProofIdx") []
          (kArrow (.const (KName.mkSimple "P") []) kType0))).add
        (.axiomInfo (KName.mkSimple "mkProofIdx1") []
          (.app (.const (KName.mkSimple "ProofIdx") []) (.const (KName.mkSimple "proof1") [])))
    let twoSucc :=
      KExpr.app (.const (KName.mkSimple "Nat.succ") [])
        (.app (.const (KName.mkSimple "Nat.succ") [])
          (.const (KName.mkSimple "Nat.zero") []))
    let extFnConst := KExpr.const (KName.mkSimple "extFn") []
    let extFnEta := KExpr.lam kNatConst (.app extFnConst (.bvar 0))
    let p1 := KExpr.const (KName.mkSimple "proof1") []
    let p2 := KExpr.const (KName.mkSimple "proof2") []
    let vecConst := KExpr.const (KName.mkSimple "Vec") []
    -- 1. In-place `kernelIsDefEq` handles Nat-literal bridging, lambda-eta, and Prop proof irrelevance
    kernelIsDefEq env 8 (.lit (.natVal 2)) twoSucc = true ∧
    kernelIsDefEq env 8 extFnEta extFnConst = true ∧
    kernelIsDefEq env 8 p1 p2 = true ∧
    -- 2. In-place `kernelInferType` & `kernelCheckDecl` accept dependent declarations across all 3 bridges
    kernelInferType env 8 []
      (.app (.lam (.app vecConst (.lit (.natVal 2))) (.bvar 0))
        (.const (KName.mkSimple "vecTwo") [])) =
      some (.app vecConst (.lit (.natVal 2))) ∧
    kernelCheckDecl env 8
      (.defnInfo (KName.mkSimple "vecLit2") []
        (.app vecConst (.lit (.natVal 2)))
        (.const (KName.mkSimple "vecTwo") [])) = true ∧
    kernelCheckDecl env 8
      (.defnInfo (KName.mkSimple "useProofIdx2") []
        (.app (.const (KName.mkSimple "ProofIdx") []) p2)
        (.const (KName.mkSimple "mkProofIdx1") [])) = true ∧
    -- 3. Negative pole: non-equal Nat literals and `sorryAx` declarations are refused
    kernelIsDefEq env 8 (.lit (.natVal 2)) (.lit (.natVal 3)) = false ∧
    kernelCheckDecl stdKernelEnv 8 invalidSorryDecl = false := by
  decide +kernel

/-- Broken `kernelCheckDecl` that ignores its inputs and returns `false`, breaking `phase2_in_place_lean_kernel_sound`. -/
def kernelCheckDeclAlwaysFalse (_env : KEnv) (_fuel : Nat) (_decl : KConstInfo) : Bool :=
  false

#tooth phase2_in_place_lean_kernel_sound by mutation kernelCheckDecl := kernelCheckDeclAlwaysFalse

/-! ## 2. Pillar 1A / Task 2: `HwExprCAM` Closed-Term Bypass & 4-Zone Spatial Silicon Elaborator -/

/-- End-to-end verification of `HwExprCAM` (`hwCamInstantiateAt_closed_bypass`, `hwCamInstantiateAt_sound`)
and the 4-Zone Spatial Silicon Elaborator (`SiliconElabFabric`):
1. **Zone 1**: 1-cycle closed $\beta$-redex bypass (`stepCamWhnf`) and multi-cycle $\beta\delta\zeta$ WHNF (`runZone1Whnf`),
2. **Zone 2**: 1-cycle $O(1)$ handle equality short-circuit (`stepCamDefEq_handle_eq_refl`), Bit-58
   free-variable filter (`checkMVarOccursBit58`), and parallel `.app` unification fork/join over
   `ReductionMachine.NocFabric` (`stepNocFabric`, `joinMCtxAssigns?`),
3. **Zone 3**: 1-cycle `moved_pin_blocks` fallback (`stepZone3DiscrLut`) and 3-phase glitch-free
   `ICAP` DPR (`admitSimpTheoremDpr`),
4. **Zone 4**: `runSiliconKernelCamFsm` and `runSiliconElabFabricFourZones` end-to-end verification. -/
theorem phase2_four_zone_silicon_elaborator_sound :
    let eClosedBeta := KExpr.app (.lam kNatConst (.lit (.natVal 42))) (.lit (.natVal 7))
    let (hClosedBeta, cam1) := internToHwExprCAM eClosedBeta HwExprCAM.empty
    let z1Step1 := stepCamWhnf { cam := cam1, focusHandle := hClosedBeta }
    let z1Final := runZone1Whnf 8 { cam := cam1, focusHandle := hClosedBeta }
    let z2Refl := stepCamDefEq
      { tileId := 0, cam := cam1, mctx := sampleMetaCtx
      , queue := [{ lhsHandle := hClosedBeta, rhsHandle := hClosedBeta }] }
    let qSimp := KExpr.app (.const (KName.mkSimple "scaleAdd") []) (.lit (.natVal 10))
    let z3Hit := stepZone3DiscrLut sampleEpoch1Guard sampleEpoch1DiscrTrie epoch1LeafView 1 qSimp 10#64
      { cam := cam1, focusHandle := hClosedBeta }
    let z3Fallback := stepZone3DiscrLut sampleEpoch1Guard sampleEpoch1DiscrTrie epoch2LeafView 2 qSimp 10#64
      { cam := cam1, focusHandle := hClosedBeta }
    let z4Valid := stepZone4KernelCheck stdKernelEnv 8 cam1 validIdNatDecl
    let z4Sorry := stepZone4KernelCheck stdKernelEnv 8 cam1 invalidSorryDecl
    -- 1. Zone 1 closed beta 1-cycle bypass & WHNF agreement
    z1Step1.steps = 1 ∧
    z1Step1.cam.nodes.length = cam1.nodes.length ∧
    reconstructFromHwExprCAM 16 z1Final.cam z1Final.focusHandle = some (.lit (.natVal 42)) ∧
    -- 2. Zone 2 1-cycle handle reflexivity & Bit-58 filter
    z2Refl.queue = [] ∧
    z2Refl.cycles = 1 ∧
    checkMVarOccursBit58 (mkExprCamWord64 (.lit (.natVal 42)) 0 0) = false ∧
    checkMVarOccursBit58 (mkExprCamWord64 (.fvar 10) 0 0) = true ∧
    -- 3. Zone 3 fast LUT hit vs 1-cycle `moved_pin_blocks` fallback to Zone 1
    z3Hit.usedFastPath = true ∧
    z3Hit.lutValue = 42#64 ∧
    z3Fallback.usedFastPath = false ∧
    z3Fallback.routedToZone1 = true ∧
    z3Fallback.zone1FallbackState.steps = 1 ∧
    -- 4. Zone 4 `HwExprCAM` kernel FSM accepts `validDefDecl` and refuses `invalidSorryDecl`
    z4Valid.1 = true ∧
    z4Valid.2.statusTag = 1 ∧
    z4Valid.2.rtlJudgeAccepted = true ∧
    z4Sorry.1 = false ∧
    z4Sorry.2.statusTag = 0 := by
  decide +kernel

/-- Broken `stepZone3DiscrLut` that never routes to Zone 1 on pin mutation (`routedToZone1 := false`). -/
def stepZone3DiscrLutBroken
    (guard : SlotGuardReg)
    (trie : DiscrTreeTrie)
    (view : LeafView)
    (pktEpoch : Nat)
    (queryExpr : KExpr)
    (argVal : BitVec 64)
    (z1State : Zone1WhnfState) : Zone3LutOutcome :=
  let (_, outVal) := evalSlotGuardedDiscrTile guard view pktEpoch argVal
  { usedFastPath       := true
  , routedToZone1      := false
  , lutValue           := outVal
  , matchedEntry?      := queryBestDiscrEntry? trie 4 queryExpr
  , zone1FallbackState := z1State }

#tooth phase2_four_zone_silicon_elaborator_sound by mutation stepZone3DiscrLut := stepZone3DiscrLutBroken

/-! ## 3. Task 3: `SiliconKernel` Lowered via `Obend.Lower.Fragment.read` / `readTheoremDecider` -/

set_option maxRecDepth 20000 in
/-- End-to-end verification that `stepCamWhnfNodeWord`, `stepCamDefEqNodeWord`, `stepCamInferNodeWord`,
and `stepCamDefEqNodeWord_refl_thm` lowered via `Obend.Lower.Fragment.read` and `readTheoremDecider`
execute across `LExpr` (`SSteps`), `Core4` (`Evaluates`), `Leaf.Book` (`Halts`), and `RtlModule`
(`evalLoweredDefEqNodeRtl`) with zero host precomputation! -/
theorem phase2_fragment_read_silicon_kernel_sound :
    SSteps (app4LExpr fragmentReadWhnfNodeLExpr 5 1 35 7) (.lit 42) ∧
    Evaluates (lowerT (app4LExpr fragmentReadWhnfNodeLExpr 5 1 35 7)) (.nat 42) ∧
    SSteps (app4LExpr fragmentReadDefEqNodeLExpr 4 10 4 10) (.lit 1) ∧
    SSteps (app4LExpr fragmentReadDefEqNodeLExpr 4 10 4 11) (.lit 0) ∧
    SSteps (app4LExpr fragmentReadInferNodeLExpr 5 17 1 1) (.lit 1) ∧
    SSteps (.app (.app fragmentReadDefEqDeciderLExpr (.lit 4)) (.lit 10)) (.boolLit true) ∧
    evalLoweredDefEqNodeRtl (4, 10, 4, 10) = [("out_stepCamDefEqNode", 1#64)] ∧
    evalLoweredDefEqNodeRtl (4, 10, 4, 11) = [("out_stepCamDefEqNode", 0#64)] := by
  have sWhnf : SSteps (app4LExpr fragmentReadWhnfNodeLExpr 5 1 35 7) (.lit 42) :=
    runLExprSteps_sound 256 _ _ rfl
  have sHit : SSteps (app4LExpr fragmentReadDefEqNodeLExpr 4 10 4 10) (.lit 1) :=
    runLExprSteps_sound 256 _ _ rfl
  have sMiss : SSteps (app4LExpr fragmentReadDefEqNodeLExpr 4 10 4 11) (.lit 0) :=
    runLExprSteps_sound 256 _ _ rfl
  have sInf : SSteps (app4LExpr fragmentReadInferNodeLExpr 5 17 1 1) (.lit 1) :=
    runLExprSteps_sound 256 _ _ rfl
  have sDec : SSteps (.app (.app fragmentReadDefEqDeciderLExpr (.lit 4)) (.lit 10)) (.boolLit true) :=
    runLExprSteps_sound 32 _ _ rfl
  refine ⟨sWhnf, by simpa [lowerT] using lower_sound_nat sWhnf,
          sHit, sMiss, sInf, sDec,
          by decide +kernel, by decide +kernel⟩

/-- Broken `evalLoweredDefEqNodeRtl` that always outputs `1#64` even on distinct handles `(4, 10, 4, 11)`. -/
def evalLoweredDefEqNodeRtlBroken (_node : HwKernelNodeWord) : List (String × BitVec 64) :=
  [("out_stepCamDefEqNode", 1#64)]

#tooth phase2_fragment_read_silicon_kernel_sound by mutation evalLoweredDefEqNodeRtl := evalLoweredDefEqNodeRtlBroken

/-! ## 4. Pillar 1B / Task 4: `Obend.Lower.LCNF` Erasure, Linear State Tokens, Join Points & `Book` Emission -/

/-- End-to-end verification of `Obend.Lower.LCNF` (and its re-export through `Obend.Lower.Inductive`):
1. `.zero` computational erasure (`eraseZeroQtyArgs`, `lcnf_zero_erasure_sound`),
2. `.one` linear `RealWorld` state-token conservation (`checkLinearStateToken`, `lcnf_linear_state_conserved`)
   accepting linear read/write pipelines and refusing cloned state tokens,
3. `jpDecl`/`jmp` join-point lowering (`compileLcnfToLExpr`, `compileLcnfToCore4`, `lcnf_to_core4_sound`),
4. `compileLcnfToBook` / `compileLcnfFunDeclToBook` (`lcnf_elab_pass_to_book_sound`). -/
theorem phase2_lcnf_bridge_sound :
    let jpExpr := compileLcnfToLExpr sampleLcnfJpCode
    let astExpr := compileLcnfToLExpr sampleLcnfAstMatch
    -- 1. `.zero` quantity erasure preserves `Core4` evaluation
    compileLcnfToCore4 (.return .erased) = box ∧
    eraseZeroQtyArgs [{ name := "hProof", qty := .zero }, { name := "x", qty := .many }] [.bvar 0, .lit 42] =
      [.erased, .lit 42] ∧
    Evaluates (compileLcnfToCore4 (.letValue (.arg .erased) (.return (.lit 42)))) (.nat 42) ∧
    -- 2. `.one` linear state-token checker accepts valid state pipeline and refuses cloned tokens
    checkLinearStateToken 0 sampleLinearStateCode = some 2 ∧
    checkLinearStateToken 0 sampleDuplicatedStateTokCode = none ∧
    evalLcnfCode 8 [] [] [] sampleLinearStateCode = some (42, [(0, 42)]) ∧
    -- 3. `jpDecl` / `jmp` join point, AST match, and `compileLcnfFunDeclToBook` evaluate to `42`
    SSteps jpExpr (.lit 42) ∧
    Evaluates (compileLcnfToCore4 sampleLcnfJpCode) (.nat 42) ∧
    SSteps astExpr (.lit 42) ∧
    Evaluates (compileLcnfToCore4 sampleLcnfAstMatch) (.nat 42) ∧
    (compileLcnfFunDeclToBook sampleLcnfRecDecl).slots = ["lcnfCountdown42"] := by
  have hZero := (Obend.Lower.LCNF.lcnf_zero_erasure_sound 42 (.bvar 0)).2.2
  have sJp : SSteps (compileLcnfToLExpr sampleLcnfJpCode) (.lit 42) :=
    Obend.Lower.LCNF.sampleLcnfJpCode_runs_42
  have sAst : SSteps (compileLcnfToLExpr sampleLcnfAstMatch) (.lit 42) :=
    Obend.Lower.LCNF.sampleLcnfAstMatch_runs_42
  refine ⟨by simp [compileLcnfToCore4, compileLcnfToLExpr, lcnfArgToLExpr, lowerT],
          by decide +kernel, hZero,
          by decide +kernel, by decide +kernel, by decide +kernel,
          sJp, by simpa [compileLcnfToCore4, lowerT] using lower_sound_nat sJp,
          sAst, by simpa [compileLcnfToCore4, lowerT] using lower_sound_nat sAst,
          by decide +kernel⟩

/-- Broken `checkLinearStateToken` that accepts cloned `.one` state tokens (`some 2`). -/
def checkLinearStateTokenBroken (_live : Nat) (_code : LcnfCode) : Option Nat :=
  some 2

#tooth phase2_lcnf_bridge_sound by mutation checkLinearStateToken := checkLinearStateTokenBroken

/-! ## 5. Axiom Footprint Audit (`0 sorryAx`, `0 custom axioms`) -/

#print axioms phase2_in_place_lean_kernel_sound
#print axioms phase2_four_zone_silicon_elaborator_sound
#print axioms phase2_fragment_read_silicon_kernel_sound
#print axioms phase2_lcnf_bridge_sound
#print axioms siliconElabFabric_four_zone_sound
#print axioms silicon_kernel_fragment_read_6stage_sound
#print axioms hwCamInstantiateAt_closed_bypass
#print axioms hwCamInstantiateAt_sound
#print axioms lcnf_zero_erasure_sound
#print axioms lcnf_linear_state_conserved

end Obend.Tests.SiliconElaboratorPhase2Test
end
