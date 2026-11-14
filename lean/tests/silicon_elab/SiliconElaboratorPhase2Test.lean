module
/-
# SiliconElaboratorPhase2Test — End-to-End Phase-2 Verification & `#tooth` Mutation Suite

Exercises and mutation-tests all 4 `SiliconElab` & `LCNF` engineering layers (`0 sorryAx`):
1. **In-Place `LeanKernel` (`kernelIsDefEq`, `kernelInferType`, `kernelCheckDecl`, `.proj` & Polymorphic $\iota$)**:
   - Verifies `Nat`-literal / constructor bridging, $\lambda$-$\eta$ expansion, `Prop` proof irrelevance,
     parameterized `.proj` (`Prod.fst` / `Prod.snd` skipping `numParams = 2`), and universe-polymorphic
     `reduceGeneralIota?_univ_poly_sound`.
2. **`HwExprCAM` Open-Substitution Simulation & 4-Zone `SiliconElabFabric`**:
   - Verifies `hwCamInstantiateAt_closed_bypass` and universal open substitution
     `reconstructFromHwExprCAM_hwCamInstantiateAt`,
   - Verifies Zone 1 (`runZone1Whnf`, `stepCamWhnf_closed_beta_one_step`),
   - Verifies Zone 2 (`stepCamDefEq`, `camOccursMVar_bit58_false_sound`, `mergeBranchAssigns_conflict_refused_sound`),
   - Verifies Zone 3 (`stepZone3DiscrLut`, `zone3_moved_pin_fallback_sound`, `admitSimpTheoremDpr_glitch_free_sound`),
   - Verifies Zone 4 (`stepZone4KernelCheck`, `runSiliconKernelCamFsm_sound`, `siliconElabFabric_four_zone_sound`).
3. **Synthesizable `siliconElabRtlModule` (`emitModuleSV siliconElabRtlModule`)**:
   - Verifies `siliconElabRtlModule_valid` (`checkRtlModule = true ∧ checkRtlModuleW = true ∧ checkRtlSynth = .ok`).
4. **Standalone `Obend.Lower.LCNF`**:
   - Verifies `.zero` computational erasure (`lcnf_zero_erasure_sound`), `.one` linear state-token
     threading across `.stateWrite` / `.stateRead` (`lcnf_linear_state_conserved`), intervening-`let`
     `jpDecl`/`jmp` de Bruijn depth (`mkShiftedJpCode_runs`), and `compileLcnfFunDeclToBook`.
-/
public import Obend.Tactic.Tooth
public import Obend.Leaf.Static
public import Obend.Lower.LCNF
import all Obend.Lower.LCNF
import all Obend.Lower.Proofs.Complete
public import Obend.Lower.Inductive
import all Obend.Lower.Inductive
public import Obend.Lower.LeanKernel
import all Obend.Lower.LeanKernel
public import Obend.Lower.Proofs.SiliconKernel
public import Obend.Lower.ExprCAM
import all Obend.Lower.ExprCAM
public import Obend.Lower.SiliconElabFabric
import all Obend.Lower.SiliconElabFabric
@[expose] public section

namespace Obend.Tests.SiliconElaboratorPhase2Test
open Obend.Core.Term
open Obend.Core.Ty (Ty)
open Obend.Equiv
open Obend.Leaf
open Obend.Leaf.Static
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

/-! ## 1. In-Place `kernelIsDefEq`, `.proj` Parameter Offset & Polymorphic $\iota$-Reduction -/

def prodKernelTestEnv : KEnv where
  constants :=
    stdKernelEnv.constants ++
    [ .inductInfo (KName.mkSimple "Prod") [KName.mkSimple "u", KName.mkSimple "v"]
        (kArrow (.sort (.succ (.param (KName.mkSimple "u"))))
          (kArrow (.sort (.succ (.param (KName.mkSimple "v"))))
            (.sort (.succ (.max (.param (KName.mkSimple "u")) (.param (KName.mkSimple "v")))))))
    , .ctorInfo (KName.mkSimple "Prod.mk") [KName.mkSimple "u", KName.mkSimple "v"]
        kType0 (KName.mkSimple "Prod") ]
  recRules := []
  inductDecls :=
    [ { name := KName.mkSimple "Prod"
      , levelParams := [KName.mkSimple "u", KName.mkSimple "v"]
      , numParams := 2
      , numIndices := 0
      , type := kType0
      , ctors := []
      , recRules := [] } ]

theorem phase2_in_place_lean_kernel_verified (u v payload : KLevel) :
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
    let prodMk := KExpr.const (KName.mkSimple "Prod.mk") [.zero, .zero]
    let pairExpr :=
      KExpr.app (.app (.app (.app prodMk kNatConst) kBoolConst) (.lit (.natVal 42)))
        (.const (KName.mkSimple "Bool.true") [])
    -- 1. Nat-literal bridging, lambda-eta, and Prop proof irrelevance
    kernelIsDefEq env 8 (.lit (.natVal 2)) twoSucc = true ∧
    kernelIsDefEq env 8 extFnEta extFnConst = true ∧
    kernelIsDefEq env 8 p1 p2 = true ∧
    -- 2. Parameterized `.proj "Prod" 0` and `.proj "Prod" 1` skip `numParams = 2` cleanly
    kernelWhnf prodKernelTestEnv 8 (.proj (KName.mkSimple "Prod") 0 pairExpr) = .lit (.natVal 42) ∧
    kernelWhnf prodKernelTestEnv 8 (.proj (KName.mkSimple "Prod") 1 pairExpr) = .const (KName.mkSimple "Bool.true") [] ∧
    -- 3. Polymorphic recursor universe-level instantiation (`reduceGeneralIota?_univ_poly_sound`)
    kernelWhnf inductKernelEnv 8
      (.app (.app (.const (KName.mkSimple "PolyBox.rec") [v, u]) (.lam (.sort u) (.bvar 0)))
        (.app (.const (KName.mkSimple "PolyBox.mk") [u]) (.sort payload))) = .sort v ∧
    kernelCheckDecl env 8
      (.defnInfo (KName.mkSimple "vecLit2") []
        (.app vecConst (.lit (.natVal 2)))
        (.const (KName.mkSimple "vecTwo") [])) = true ∧
    kernelCheckDecl env 8
      (.defnInfo (KName.mkSimple "useProofIdx2") []
        (.app (.const (KName.mkSimple "ProofIdx") []) p2)
        (.const (KName.mkSimple "mkProofIdx1") [])) = true ∧
    kernelCheckDecl stdKernelEnv 8 invalidSorryDecl = false := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel,
          by decide +kernel, by decide +kernel,
          (reduceGeneralIota?_univ_poly_sound v u payload).1,
          by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- Broken `kernelCheckDecl` that ignores its inputs and returns `false`. -/
def kernelCheckDeclAlwaysFalse (_ : KEnv) (_ : Nat) (_ : KConstInfo) : Bool :=
  false

#tooth phase2_in_place_lean_kernel_verified by mutation kernelCheckDecl := kernelCheckDeclAlwaysFalse

/-! ## 2. `HwExprCAM` Open-Substitution & 4-Zone Spatial Silicon Elaborator + Synthesizable `siliconElabRtlModule` -/

def phase2Epoch1Guard : SlotGuardReg := mkAffineSlotGuard "discrEpoch" 1 4 2
def phase2Epoch1View  : LeafView := viewOf 1 "discrEpoch" phase2Epoch1Guard.composition
def phase2Epoch2Guard : SlotGuardReg := mkAffineSlotGuard "discrEpoch" 2 6 10
def phase2Epoch2View  : LeafView := viewOf 2 "discrEpoch" phase2Epoch2Guard.composition
def phase2DiscrTrie   : DiscrTrieNode :=
  let pat := KExpr.app (.const (KName.mkSimple "scaleAdd") []) (.mvar 0)
  let path := exprToDiscrPath 8 pat
  insertDiscrTrieNode path
    { ruleName := KName.mkSimple "scaleAdd_eq"
    , path     := path
    , lutTag   := 101
    , kind     := .simpLemma (.lit (.natVal 42)) 1000 0 }
    .empty

theorem phase2_four_zone_silicon_elaborator_verified (k : Nat) :
    let eClosedBeta := KExpr.app (.lam kNatConst (.lit (.natVal 42))) (.lit (.natVal 7))
    let (hClosedBeta, cam1) := internToHwExprCAM eClosedBeta HwExprCAM.empty
    let z1Step1 := stepCamWhnf { cam := cam1, focusHandle := hClosedBeta }
    let z1Final := runZone1Whnf 8 { cam := cam1, focusHandle := hClosedBeta }
    let z2Refl := stepCamDefEq
      { tileId := 0, cam := cam1
      , queue := [{ lhsHandle := hClosedBeta, rhsHandle := hClosedBeta }] }
    let qSimp := KExpr.app (.const (KName.mkSimple "scaleAdd") []) (.lit (.natVal 10))
    let z3Hit := stepZone3DiscrLut phase2Epoch1Guard phase2DiscrTrie phase2Epoch1View 1 qSimp 10#64
      { cam := cam1, focusHandle := hClosedBeta }
    let z3Fallback := stepZone3DiscrLut phase2Epoch1Guard phase2DiscrTrie phase2Epoch2View 2 qSimp 10#64
      { cam := cam1, focusHandle := hClosedBeta }
    let z4Valid := stepZone4KernelCheck stdKernelEnv 8 cam1 validIdNatDecl
    let z4Sorry := stepZone4KernelCheck stdKernelEnv 8 cam1 invalidSorryDecl
    -- Open substitution under nested binder (`λ y : Nat => .bvar 1 + .bvar 0` instantiated with `.lit k`)
    let openBody := KExpr.lam kNatConst (.app (.bvar 1) (.bvar 0))
    let (hOpen, camO1) := internToHwExprCAM openBody HwExprCAM.empty
    let (hArg, camO2) := internToHwExprCAM (.lit (.natVal k)) camO1
    let (hInst, camO3) := hwCamInstantiateAt 16 hOpen 0 hArg camO2
    reconstructFromHwExprCAM 16 camO3 hInst =
      some (KExpr.instantiateAt 0 (.lit (.natVal k)) openBody) ∧
    runZone1WhnfRegressionOk = true ∧
    z1Step1.steps = 1 ∧
    z1Step1.cam.nodes.length = cam1.nodes.length ∧
    reconstructFromHwExprCAM 16 z1Final.cam z1Final.focusHandle = some (.lit (.natVal 42)) ∧
    z2Refl.queue = [] ∧
    z2Refl.cycles = 1 ∧
    z3Hit.usedFastPath = true ∧
    z3Hit.lutValue = 42#64 ∧
    z3Fallback.usedFastPath = false ∧
    z3Fallback.routedToZone1 = true ∧
    z3Fallback.zone1FallbackState.steps = 1 ∧
    z4Valid.1 = true ∧
    z4Valid.2.statusTag = 1 ∧
    z4Valid.2.rtlJudgeAccepted = true ∧
    z4Sorry.1 = false ∧
    z4Sorry.2.statusTag = 0 ∧
    checkRtlModule siliconElabRtlModule = true ∧
    checkRtlModuleW siliconElabRtlModule = true ∧
    checkRtlSynth 0 "silicon_elab_top" siliconElabRtlModule = .ok := by
  have hOpenSim :=
    reconstructFromHwExprCAM_hwCamInstantiateAt 16 0
      (.lam kNatConst (.app (.bvar 1) (.bvar 0))) (.lit (.natVal k)) HwExprCAM.empty
      (by simp [ExprCAM.depth, kNatConst])
  refine ⟨hOpenSim, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
          by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
          by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
          by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
          siliconElabRtlModule_valid.1, siliconElabRtlModule_valid.2.1, siliconElabRtlModule_valid.2.2⟩

/-- Broken `stepZone3DiscrLut` that never routes to Zone 1 on pin mutation (`routedToZone1 := false`). -/
def stepZone3DiscrLutBroken
    (guard : SlotGuardReg)
    (trie : DiscrTrieNode)
    (view : LeafView)
    (pktEpoch : Nat)
    (queryExpr : KExpr)
    (argVal : BitVec 64)
    (z1State : Zone1WhnfState) : Zone3LutOutcome :=
  let (_, outVal) := evalSlotGuardedDiscrTile guard view pktEpoch argVal
  let hits := queryDiscrTrieNode trie (exprToDiscrPath 8 queryExpr)
  { usedFastPath       := true
  , routedToZone1      := false
  , lutValue           := outVal
  , matchedEntry?      := hits.head?
  , zone1FallbackState := z1State }

#tooth Obend.Lower.SiliconElabFabric.zone3_moved_pin_fallback_sound by mutation stepZone3DiscrLut := stepZone3DiscrLutBroken

/-! ## 3. `Obend.Lower.LCNF` Erasure, Linear State Threading & Shifted Join Points -/

theorem phase2_lcnf_bridge_verified (addr val v1 v2 offset : Nat) :
    compileLcnfToCore4 (.return .erased) = box ∧
    eraseZeroQtyArgs [{ name := "hProof", qty := .zero }, { name := "x", qty := .many }] [.bvar 0, .lit 42] =
      [.erased, .lit 42] ∧
    Evaluates (compileLcnfToCore4 (.letValue (.arg .erased) (.return (.lit val)))) (.nat val) ∧
    checkLinearStateToken 0 (mkLinearStateWriteRead addr val) = some 2 ∧
    checkLinearStateToken 0 sampleDuplicatedStateTokCode = none ∧
    -- Linear state write at `addr = 7, val = 99` reads back `99` (NOT raw address `7`!)
    SSteps (compileLcnfToLExpr (mkLinearStateWriteRead addr val)) (.lit val) ∧
    Evaluates (compileLcnfToCore4 (mkLinearStateWriteRead addr val)) (.nat val) ∧
    -- Join point with 2 intervening `letValue`s tracks de Bruijn shift (`v1 + v2 + offset`)
    SSteps (compileLcnfToLExpr (mkShiftedJpCode v1 v2 offset)) (.lit (v1 + v2 + offset)) ∧
    Evaluates (compileLcnfToCore4 (mkShiftedJpCode v1 v2 offset)) (.nat (v1 + v2 + offset)) ∧
    (compileLcnfFunDeclToBook sampleLcnfRecDecl).slots = ["lcnfCountdown42"] := by
  have hZero := (Obend.Lower.LCNF.lcnf_zero_erasure_sound val (.bvar 0)).2.2
  have hLin := Obend.Lower.LCNF.lcnf_linear_state_conserved addr val
  have sJp := Obend.Lower.LCNF.mkShiftedJpCode_runs v1 v2 offset
  refine ⟨by simp [compileLcnfToCore4, compileLcnfToLExpr, codeUsesState, compileLcnfWithCtx, lcnfArgToLExprCtx, lowerT],
          by decide +kernel, hZero,
          hLin.1, by decide +kernel,
          hLin.2.2.2.1, hLin.2.2.2.2,
          sJp, by simpa [compileLcnfToCore4, lowerT] using lower_sound_nat sJp,
          by decide +kernel⟩

/-- Broken `checkLinearStateToken` that accepts cloned `.one` state tokens (`some 2`). -/
def brokenCheckLinearStateToken (_ : Nat) (_ : LcnfCode) : Option Nat :=
  some 2

#tooth Obend.Lower.LCNF.lcnf_eval_cases_proj_sound by mutation
  Obend.Lower.LCNF.evalLcnfCode := fun _ _ _ st _ => some (0, st)
#tooth Obend.Lower.LCNF.lcnf_eval_cases_proj_sound by mutation
  Obend.Lower.LCNF.evalLcnfCodeVal := fun _ _ _ st _ => some (.scalar 0, st)
#tooth Obend.Lower.LCNF.lcnf_eval_cases_proj_sound by mutation
  Obend.Lower.LCNF.evalLcnfArgVal := fun _ _ => some (.scalar 0)

-- Recursive application rebinds self to the original, unsaturated lexical closure.
example : Obend.Lower.LCNF.evalLcnfLetValueVal 32
    [.closure [] [] Obend.Lower.LCNF.sampleLcnfRecDecl] [] []
    (.app (.bvar 0) (.lit 2)) = some (.scalar 42, []) := by rfl

#tooth Obend.Lower.LCNF.lcnf_eval_closure_sound by mutation
  Obend.Lower.LCNF.evalLcnfCodeVal := fun _ _ _ st _ => some (.scalar 0, st)
#tooth Obend.Lower.LCNF.lcnf_eval_invalid_refused by mutation
  Obend.Lower.LCNF.evalLcnfCode := fun _ _ _ st _ => some (0, st)

#tooth phase2_lcnf_bridge_verified by mutation checkLinearStateToken := brokenCheckLinearStateToken

#tooth Obend.Lower.LCNF.evalLcnfCode_simulates_core4 by mutation
  Obend.Lower.LCNF.evalLcnfCodeVal := fun _ _ _ st _ => some (.scalar 0, st)
#tooth Obend.Lower.LCNF.evalLcnfCode_simulates_core4 by mutation
  Obend.Lower.LCNF.compileLcnfToCore4 := fun _ => .nat 0

-- Inhabitedness for the structural theorem includes aggregate dispatch and projection.
example (x y : Nat) : PureBlock (casesProjCode x y) := by
  apply PureBlock.letValue rfl
  apply PureBlock.cases
  intro arm h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl
  · exact .ret _
  · exact .letValue rfl (.ret _)

example (x y : Nat) : PureBlock (namedProjCode "snd" x y) :=
  .letValue rfl (.letValue rfl (.ret _))

#print axioms evalLcnfCodeVal_simulates_ssteps
#print axioms evalLcnfCode_simulates_core4

-- Captured variables remain lexical even across intervening bindings.
#tooth Obend.Lower.LCNF.lcnf_jp_lexical_capture_sound by mutation
  Obend.Lower.LCNF.evalLcnfCodeVal := fun _ _ _ st _ => some (.scalar 0, st)
#tooth Obend.Lower.LCNF.lcnf_jp_lexical_capture_sound by mutation
  Obend.Lower.LCNF.compileLcnfToLExpr := fun _ => .lit 0

example : evalLcnfCode 2 [] [] [] (.return (.boolLit true)) = none := by rfl
example : evalLcnfCode 2 [] [] [] (.return (.stateTok 7)) = none := by rfl
example : evalLcnfCodeBool 2 [] [] [] (.return (.boolLit true)) = some (true, []) := by rfl
example : evalLcnfCodeBool 2 [] [] [] (.return (.lit 1)) = none := by rfl

-- A same-named join at the jump site cannot replace the join captured by a body.
example : evalLcnfCode 10 [] [] []
    (.jpDecl 1 0 (.return (.lit 7))
      (.jpDecl 0 0 (.jmp 1 [])
        (.jpDecl 1 0 (.return (.lit 99)) (.jmp 0 [])))) = some (7, []) := by rfl

-- Top-level function calls do not inherit local join points from their caller.
example : evalLcnfCodeVal 10
    [.closure [] [] { name := "noCallerJoins", numParams := 1, body := .jmp 0 [] }] [] []
    (.jpDecl 0 0 (.return (.lit 99))
      (.letValue (.app (.bvar 0) (.lit 1)) (.return (.bvar 0)))) = none := by rfl

-- The full three-layer agreement (`sampleLcnfRecModule_eval_agreed`) is a tier-2 fixture in
-- `Obend/Teeth/Lower/LcnfRecModule.lean`; the interpreter layer is checked here directly.
example : evalLcnfModule 32 sampleLcnfRecModule = some (42, []) := by rfl

#print axioms lcnf_jp_lexical_capture_sound

/-! ## 4. Axiom Footprint Audit (`0 sorryAx`, `0 custom axioms`) -/

#print axioms phase2_in_place_lean_kernel_verified
#print axioms phase2_four_zone_silicon_elaborator_verified
#print axioms phase2_lcnf_bridge_verified
#print axioms siliconElabFabric_four_zone_sound
#print axioms siliconElabRtlModule_valid
#print axioms hwCamInstantiateAt_closed_bypass
#print axioms reconstructFromHwExprCAM_hwCamInstantiateAt
#print axioms lcnf_zero_erasure_sound
#print axioms lcnf_linear_state_conserved

end Obend.Tests.SiliconElaboratorPhase2Test
end
