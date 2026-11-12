module
/-
# SiliconElabTest — Positive/Negative Poles, Kernel & Hardware Verification, and `#tooth` Mutation Tests

Verifies the Silicon Lean Kernel, `ExprCAM`, `MetaUnify`, `DiscrTreeLUT`, and `Proofs.SiliconKernel`:
1. `Obend.Lower.Inductive`: Recursive algebraic AST datatypes (`KName`, `KLevel`, `KLiteral`, `KExpr`
   including first-class `.mvar`, `KSyntax`), structural pattern matching & `recConst` lowering
   (`lower_inductive_sound`), and LCNF lowering (`lcnf_to_core4_sound`).
2. `Obend.Leaf.Static`: `bequiv_dataPinSpecialize` and `staticApply_slot_sound`.
3. `Obend.Lower.LeanKernel`: Pure Lean kernel (`kernelWhnf`, `kernelIsDefEq`, `kernelInferType`,
   `kernelCheckDecl`) with polymorphic general $\iota$-reduction (`reduceGeneralIota?_univ_poly_sound`)
   and fail-closed $\eta$-expansion (`etaDomCompat_fail_closed_sound`).
4. `Obend.Lower.Proofs.SiliconKernel`: Universal 5-stage `ReductionMachine` hardware co-simulation
   (`silicon_kernel_5stage_check_sound`), DPR specialization (`silicon_elab_residual_dpr_specialize_sound`),
   1-cycle environment mutation fallback (`silicon_elab_env_mutation_fallback_sound`), and hardware
   interaction-net $\beta$-reduction (`silicon_kernel_inet_beta_agrees`).
5. **19 `#tooth` Kernel Mutation Tests** verifying that weakening any check or lowering pass is
   rejected by the Lean kernel.
-/
public import Obend.Tactic.Tooth
import all Obend.Lower.Inductive
import all Obend.Leaf.Static
import all Obend.Lower.LeanKernel
import all Obend.Lower.ExprCAM
import all Obend.Lower.MetaUnify
import all Obend.Lower.DiscrTreeLUT
import all Obend.Lower.Proofs.SiliconKernel
import all Obend.Hardware.HDL
import all Obend.Hardware.Compiler
import all Obend.Hardware.ReductionMachine
import all Obend.Analysis.Diff
import all Obend.Analysis.Flowpipe
import all Obend.Analysis.TaylorModel
import all Obend.Analysis.Groebner
import all Obend.Analysis.Hybrid
import all Obend.Vault.PhysicalProjection
public import Obend.Lower.ExprCAM
public import Obend.Lower.MetaUnify
public import Obend.Lower.DiscrTreeLUT
public import Obend.Lower.Proofs.SiliconKernel
public import Obend.Analysis.Diff
public import Obend.Analysis.Flowpipe
public import Obend.Analysis.TaylorModel
public import Obend.Analysis.Groebner
public import Obend.Analysis.Hybrid
public import Obend.Vault.PhysicalProjection
@[expose] public section

namespace Obend.Tests.SiliconElab
open Obend.Core.Term
open Obend.Core.Ty (Ty)
open Obend.Equiv
open Obend.Slot
open Obend.Slot.World
open Obend.Leaf
open Obend.Leaf.Static
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
set_option autoImplicit false

/-! ## 1. End-to-End Verification Suite Across All Silicon Elaborator Modules -/

theorem silicon_elaborator_master_suite (n : Nat) :
    -- 1. Recursive AST Inductives (including first-class `.mvar`) & LCNF Lowering
    decodeExprTerm (lowerExpr (.mvar n)) = some (.mvar n) ∧
    decodeExprTerm (lowerExpr (.app (.lam kNatConst (.bvar 0)) (.lit (.natVal 42)))) =
      some (.app (.lam kNatConst (.bvar 0)) (.lit (.natVal 42))) ∧
    decodeCoreTerm (lowerCoreTerm (.app (.lam (.bound 0)) (.nat 42))) =
      some (.app (.lam (.bound 0)) (.nat 42)) ∧
    fromLeanName (toLeanName (KName.mkSimple "LeanKernel")) = KName.mkSimple "LeanKernel" ∧
    Evaluates (lowerLCNF sampleLcnfAstMatch) (.nat 42) ∧
    Evaluates (.app (lowerLCNFFunDecl sampleLcnfRecDecl) (.nat 0)) (.nat 42) ∧
    -- 2. Self-Hosted Lean Kernel Positive & Negative Poles + Parametric Levels + Nat ι-Reduction
    kernelCheckDecl stdKernelEnv 8 validIdNatDecl = true ∧
    kernelCheckDecl stdKernelEnv 8 validPropIdDecl = true ∧
    kernelCheckDecl stdKernelEnv 8 validApplyId42Decl = true ∧
    kernelCheckDecl stdKernelEnv 8 invalidMismatchDecl = false ∧
    kernelCheckDecl stdKernelEnv 8 invalidBadAppDecl = false ∧
    kernelCheckDecl stdKernelEnv 8 invalidUniverseDecl = false ∧
    kernelCheckDecl stdKernelEnv 8 invalidSorryDecl = false ∧
    kernelLevelEq (.imax (.param (KName.mkSimple "u")) .zero) .zero = true ∧
    kernelWhnf stdKernelEnv 4 (.app (.app (.const (KName.mkSimple "Nat.add") []) (.lit (.natVal n))) (.lit (.natVal 2))) =
      .lit (.natVal (n + 2)) ∧
    -- 3. SiliconKernel 5-Stage Hardware, XY Mesh, ICAP Codec & DPR Co-Simulation
    residualSimpTerm = specializedSimpTerm ∧
    specSlot.usable (holdsAt pinnedSimpView) specializedSimpCand = true ∧
    specSlot.usable (holdsAt mutatedSimpView) specializedSimpCand = false ∧
    specSlot.usable (holdsAt mutatedSimpView) .machine = true ∧
    (encodeTileIcapWords specializedSimpTile).length = 5 := by
  refine ⟨decodeExprTerm_lowerT (.mvar n),
    (lower_inductive_sound .anonymous .zero (.app (.lam kNatConst (.bvar 0)) (.lit (.natVal 42))) .missing).2.2.2.2.2.2.1,
    decodeCoreTerm_lowerT (.app (.lam (.bound 0)) (.nat 42)),
    fromLeanName_toLeanName (KName.mkSimple "LeanKernel"),
    lcnf_to_core4_sound.2.2.2.2.1,
    lcnf_to_core4_sound.2.2.2.2.2,
    by decide +kernel,
    by decide +kernel,
    by decide +kernel,
    by decide +kernel,
    by decide +kernel,
    by decide +kernel,
    kernelCheckDecl_refuses_sorry stdKernelEnv 8 invalidSorryDecl rfl,
    (kernelLevelEq_parametric_laws (KName.mkSimple "u") (KName.mkSimple "v")).2.2.2.1,
    (kernelWhnf_nat_iota_sound n 2).2.2.2.2,
    residualSimpTerm_eq_lowerLite.1,
    (silicon_elab_residual_dpr_specialize_sound).1,
    (silicon_elab_env_mutation_fallback_sound).1,
    (silicon_elab_env_mutation_fallback_sound).2.1,
    (silicon_elab_mesh_xy_and_icap_codec_sound).1⟩

/-! ## 2. Nineteen `#tooth` Kernel Mutation Tests -/

/-- 1. Broken `exprContainsSorry` in `Obend.Lower.LeanKernel` that never flags `sorryAx` (`false`). -/
def exprContainsSorryBlind : KExpr → Bool :=
  fun _ => false

#tooth silicon_elaborator_master_suite by mutation Obend.Lower.LeanKernel.exprContainsSorry := exprContainsSorryBlind

/-- 2. Broken `kernelCheckDecl` in `Obend.Lower.LeanKernel` that rubber-stamps every declaration (`true`). -/
def kernelCheckDeclRubberStamp (_ : KEnv) (_ : Nat) (_ : KConstInfo) : Bool :=
  true

#tooth Obend.Lower.LeanKernel.kernelCheckDecl_refuses_sorry by mutation Obend.Lower.LeanKernel.kernelCheckDecl := kernelCheckDeclRubberStamp

/-- 3. Broken `kernelWhnf` in `Obend.Lower.LeanKernel` that skips β/ζ/δ/ι reduction. -/
def kernelWhnfNoReduce (_ : KEnv) (_ : Nat) (e : KExpr) : KExpr :=
  e

#tooth Obend.Lower.LeanKernel.kernelWhnf_nat_iota_sound by mutation Obend.Lower.LeanKernel.kernelWhnf := kernelWhnfNoReduce

/-- 4. Broken `kernelDeclStatusTag` in `Obend.Lower.Proofs.SiliconKernel` that misclassifies
`sorryAx`-contaminated declarations as `1` (Accepted) instead of `0` (Refused). -/
def kernelDeclStatusTagAcceptSorry (_ : KEnv) (_ : Nat) (_ : KConstInfo) : Nat :=
  1

#tooth Obend.Lower.Proofs.SiliconKernel.kernelDeclStatusTag_eq_one_iff by mutation Obend.Lower.Proofs.SiliconKernel.kernelDeclStatusTag := kernelDeclStatusTagAcceptSorry

/-- 5. Broken `kernelGateBody` in `Obend.Lower.Proofs.SiliconKernel` that inverts the hardware
acceptance gate (returning `1` on rejected tags and `0` on valid tag `1`). -/
def kernelGateBodyInverted : LExpr :=
  .boolRec .natural
    (.lit 1)
    (.lit 0)
    (.natBin .beq (.bvar 0) (.lit 1))

#tooth Obend.Lower.Proofs.SiliconKernel.silicon_kernel_5stage_check_sound by mutation Obend.Lower.Proofs.SiliconKernel.kernelGateBody := kernelGateBodyInverted

/-- 6. Broken `isZeroLevelLExpr` in `Obend.Lower.Inductive` that maps `"zero"` to `false` instead of `true`. -/
def isZeroLevelLExprBroken : LExpr :=
  .lam .emptyRow
    (.cases .boolean
      [ ("zero",  [], .boolLit false)
      , ("succ",  ["pred"], .lam .emptyRow (.boolLit false))
      , ("max",   ["lhs", "rhs"], .lam .emptyRow (.lam .emptyRow (.boolLit false)))
      , ("imax",  ["lhs", "rhs"], .lam .emptyRow (.lam .emptyRow (.boolLit false)))
      , ("param", ["name"], .lam .emptyRow (.boolLit false)) ]
      (.bvar 0))

#tooth Obend.Lower.Inductive.lower_inductive_sound by mutation Obend.Lower.Inductive.isZeroLevelLExpr := isZeroLevelLExprBroken

/-- 7. Broken `dprPhase3ReleaseFence` in `Obend.Hardware.ReductionMachine` that unconditionally
releases the Region Isolation Fence (`isolated := false`) even when the bitstream CRC check fails. -/
def dprPhase3ReleaseFenceIgnoreCrc (frame : IcapBitstreamFrame) (t : ReconfigTileState) : ReconfigTileState :=
  if t.tileId == frame.targetTileId then
    { t with isolated := false }
  else
    t

#tooth Obend.Lower.Proofs.SiliconKernel.silicon_elab_env_mutation_fallback_sound by mutation Obend.Hardware.ReductionMachine.dprPhase3ReleaseFence := dprPhase3ReleaseFenceIgnoreCrc

/-- 8. Broken `KLevel.normalize` in `Obend.Lower.LeanKernel` that skips algebraic `max`/`imax` normalization. -/
def kLevelNormalizeNoOp (l : KLevel) : KLevel :=
  l

#tooth Obend.Lower.LeanKernel.kernelLevelEq_parametric_laws by mutation Obend.Lower.LeanKernel.KLevel.normalize := kLevelNormalizeNoOp

/-- 9. Broken `reduceNatIota?` in `Obend.Lower.LeanKernel` that skips `Nat` literal and `Bool.rec` $\iota$-reduction. -/
def reduceNatIotaNoOp (_ _ : KExpr) : Option KExpr :=
  none

#tooth Obend.Lower.LeanKernel.kernelWhnf_nat_iota_sound by mutation Obend.Lower.LeanKernel.reduceNatIota? := reduceNatIotaNoOp

/-- 10. Broken `reduceGeneralIota?` in `Obend.Lower.LeanKernel` that skips user-defined recursor $\iota$-reduction. -/
def reduceGeneralIotaNoOp (_ : KEnv) (_ _ : KExpr) : Option KExpr :=
  none

#tooth Obend.Lower.LeanKernel.kernelWhnf_general_iota_sound by mutation Obend.Lower.LeanKernel.reduceGeneralIota? := reduceGeneralIotaNoOp

/-- 11. Broken `reduceQuotLift?` in `Obend.Lower.LeanKernel` that skips `Quot.lift` reduction on `Quot.mk`. -/
def reduceQuotLiftNoOp (_ _ : KExpr) : Option KExpr :=
  none

#tooth Obend.Lower.LeanKernel.kernelWhnf_quot_lift_sound by mutation Obend.Lower.LeanKernel.reduceQuotLift? := reduceQuotLiftNoOp

/-- 12. Broken `internRootNode` in `Obend.Lower.ExprCAM` that skips CAM lookup deduplication. -/
def internRootNodeNoDedup (cam : ExprCAM) (e : KExpr) (leftH rightH : Nat) : ExprCAM × CamHandle :=
  let h := cam.entries.length
  let entry : CamSlotEntry :=
    { handle := h
    , word64 := mkExprCamWord64 e leftH rightH
    , expr   := e }
  ({ entries := cam.entries ++ [entry] }, h)

#tooth Obend.Lower.ExprCAM.exprCam_eq_iff_handle_eq by mutation Obend.Lower.ExprCAM.internRootNode := internRootNodeNoDedup

/-- 13. Broken `DualRat.mul` in `Obend.Analysis.Diff` that drops the second Leibniz product term. -/
def dualRatMulBroken (a b : Obend.Analysis.DualRat) : Obend.Analysis.DualRat :=
  ⟨a.val * b.val, a.der * b.val⟩

#tooth Obend.Analysis.interval_mean_value_enclosure by mutation Obend.Analysis.DualRat.mul := dualRatMulBroken

/-- 14. Broken `verifyTrajectorySafety` in `Obend.Analysis.Flowpipe` that rubber-stamps unsafe trajectories. -/
def brokenVerifyTrajectorySafety
    (_ : Obend.Analysis.OdeSystem)
    (_ : List (String × Obend.Analysis.Interval))
    (_ : Nat)
    (_ : List (String × Obend.Analysis.Interval)) : Bool :=
  true

#tooth Obend.Analysis.flowpipe_step_encloses_euler by mutation Obend.Analysis.verifyTrajectorySafety := brokenVerifyTrajectorySafety

/-- Universal occurs-check refusal for cyclic `.app ... (.mvar id)` assignments. -/
theorem assignMVar?_cyclic_succ_refused (id : Obend.Lower.MetaUnify.MVarId) :
    Obend.Lower.MetaUnify.assignMVar? {} 8 id
      (.app (.const (KName.mkSimple "Nat.succ") []) (.mvar id)) = none := by
  simp [Obend.Lower.MetaUnify.assignMVar?, Obend.Lower.MetaUnify.instantiateMVarsFuel,
    Obend.Lower.MetaUnify.MetavarContext.getAssignment?, Obend.Lower.MetaUnify.occursMVar]

/-- 15. Broken `occursMVar` in `Obend.Lower.MetaUnify` that skips the cyclic occurs-check (`false`). -/
def occursMVarSkip (_ : Obend.Lower.MetaUnify.MVarId) (_ : KExpr) : Bool :=
  false

#tooth assignMVar?_cyclic_succ_refused by mutation Obend.Lower.MetaUnify.occursMVar := occursMVarSkip

/-- 16. Broken `queryDiscrTrieNode` in `Obend.Lower.DiscrTreeLUT` that drops indexed rules (`[]`). -/
def queryDiscrTrieNodeEmpty (_ : DiscrTrieNode) (_ : DiscrPath) : List DiscrTreeEntry :=
  []

#tooth Obend.Lower.DiscrTreeLUT.queryDiscrTrieNode_insert_mem_of_matchDiscrPath by mutation Obend.Lower.DiscrTreeLUT.queryDiscrTrieNode := queryDiscrTrieNodeEmpty

/-- 17. Broken `tmSub` in `Obend.Analysis.TaylorModel` that adds instead of subtracting polynomial coefficients. -/
def tmSubBroken (a b : Obend.Analysis.TaylorModel) : Obend.Analysis.TaylorModel :=
  Obend.Analysis.tmAdd a b

#tooth Obend.Analysis.taylorModel_transcendental_enclosure_sound by mutation Obend.Analysis.tmSub := tmSubBroken

/-- 18. Broken `checkGroebnerBasis` in `Obend.Analysis.Groebner` that rubber-stamps non-Gröbner bases (`true`). -/
def brokenCheckGroebnerBasis (_ : Nat) (_ : List Obend.Judge.SOS.Poly) : Bool :=
  true

#tooth Obend.Analysis.groebner_ideal_membership_sound by mutation Obend.Analysis.checkGroebnerBasis := brokenCheckGroebnerBasis

/-- 19. Broken `positivstellensatzCheck` in `Obend.Analysis.Groebner` that accepts invalid certificates (`.ok`). -/
def positivstellensatzCheckRubberStamp
    (_ : Nat)
    (_ : Obend.Analysis.PositivstellensatzQuery)
    (_ : Obend.Analysis.PositivstellensatzCert) :
    Obend.Judge.Verdict Obend.Analysis.PositivstellensatzClause :=
  .ok

#tooth Obend.Analysis.stengle_positivstellensatz_sound by mutation Obend.Analysis.positivstellensatzCheck := positivstellensatzCheckRubberStamp

/-- 20. Broken `verifyHybridScheduleSafety` in `Obend.Analysis.Hybrid` that rubber-stamps out-of-guard jumps (`true`). -/
def brokenVerifyHybridScheduleSafety
    (_ : Obend.Analysis.HybridAutomaton)
    (_ : Obend.Analysis.HybridState)
    (_ : List Obend.Analysis.HybridAction) : Bool :=
  true

#tooth Obend.Analysis.hybrid_flowpipe_safety_admits_contract by mutation Obend.Analysis.verifyHybridScheduleSafety := brokenVerifyHybridScheduleSafety

/-! ## 3. Axiom Hygiene Verification (`0 sorryAx`, `0` Custom Axioms) -/

#print axioms Obend.Lower.Inductive.lower_inductive_sound
#print axioms Obend.Lower.Inductive.decodeCoreTerm_lowerT
#print axioms Obend.Lower.Inductive.fromLeanName_toLeanName
#print axioms Obend.Lower.Inductive.lcnf_to_core4_sound
#print axioms Obend.Leaf.Static.bequiv_dataPinSpecialize
#print axioms Obend.Leaf.Static.staticApply_slot_sound
#print axioms Obend.Lower.LeanKernel.kernelLevelEq_parametric_laws
#print axioms Obend.Lower.LeanKernel.kernelCheckDecl_refuses_sorry
#print axioms Obend.Lower.LeanKernel.kernelWhnf_nat_iota_sound
#print axioms Obend.Lower.LeanKernel.reduceGeneralIota?_univ_poly_sound
#print axioms Obend.Lower.LeanKernel.kernelWhnf_general_iota_sound
#print axioms Obend.Lower.LeanKernel.kernelWhnf_quot_lift_sound
#print axioms Obend.Lower.ExprCAM.unpack_pack_camWord64
#print axioms Obend.Lower.ExprCAM.exprCam_looseBVar_flag_sound
#print axioms Obend.Lower.ExprCAM.exprCam_eq_iff_handle_eq
#print axioms Obend.Lower.ExprCAM.intern_unintern_roundtrip
#print axioms Obend.Lower.ExprCAM.exprCam_handle_eq_imp_expr_eq
#print axioms Obend.Lower.ExprCAM.exprCam_hash26_collision_and_capacity_sound
#print axioms Obend.Lower.ExprCAM.exprCam_roundtrip_sound
#print axioms Obend.Lower.ExprCAM.reconstructFromHwExprCAM_hwCamInstantiateAt
#print axioms Obend.Lower.ExprCAM.fromLeanExprWithProjShift_no_double_offset
#print axioms Obend.Lower.MetaUnify.metaUnify_assign_sound
#print axioms Obend.Lower.MetaUnify.metaUnify_binder_opening_scope_sound
#print axioms Obend.Lower.MetaUnify.metaUnify_miller_pattern_sound
#print axioms Obend.Lower.MetaUnify.metaUnify_occurs_check_and_scope_refusal
#print axioms Obend.Lower.DiscrTreeLUT.skipSubterms_exprToDiscrPath
#print axioms Obend.Lower.DiscrTreeLUT.queryDiscrTrieNode_insert_mem_of_matchDiscrPath
#print axioms Obend.Lower.DiscrTreeLUT.compileDiscrTrieToRtl_matches_first_rule
#print axioms Obend.Analysis.evalDual_fst_eq_eval
#print axioms Obend.Analysis.symbolicDeriv_agrees_with_dual
#print axioms Obend.Analysis.interval_mean_value_enclosure
#print axioms Obend.Analysis.flowpipe_step_encloses_euler
#print axioms Obend.Analysis.flowpipe_safety_implies_contract_holds
#print axioms Obend.Analysis.taylorModel_transcendental_enclosure_sound
#print axioms Obend.Analysis.taylorModel_picard_sound
#print axioms Obend.Analysis.groebner_ideal_membership_sound
#print axioms Obend.Analysis.stengle_positivstellensatz_sound
#print axioms Obend.Analysis.hybrid_flowpipe_safety_admits_contract
#print axioms Obend.Vault.PhysicalProjection.physical_projection_deterministic
#print axioms Obend.Vault.PhysicalProjection.physical_cnc_abbe_projection_sound
#print axioms Obend.Vault.PhysicalProjection.physical_openusd_lifecycle_projection_sound
#print axioms Obend.Vault.PhysicalProjection.physical_projection_doc_noninterference
#print axioms Obend.Lower.Proofs.SiliconKernel.silicon_kernel_5stage_check_sound
#print axioms Obend.Lower.Proofs.SiliconKernel.silicon_elab_residual_dpr_specialize_sound
#print axioms Obend.Lower.Proofs.SiliconKernel.silicon_elab_env_mutation_fallback_sound
#print axioms Obend.Lower.Proofs.SiliconKernel.silicon_kernel_inet_beta_agrees
#print axioms Obend.Lower.Proofs.SiliconKernel.silicon_elab_mesh_xy_and_icap_codec_sound
#print axioms Obend.Tests.SiliconElab.silicon_elaborator_master_suite

end Obend.Tests.SiliconElab
end
