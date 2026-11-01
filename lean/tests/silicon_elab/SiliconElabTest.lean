module
/-
# SiliconElabTest — Positive/Negative Poles, Elaborator & Kernel Verification, and 8 `#tooth` Mutation Tests

Verifies the complete Silicon Lean Kernel & Elaborator (`WS 23` / `SILICON-ELABORATOR.md`):
1. `Obend.Lower.Inductive`: Recursive algebraic AST datatypes (`KName`, `KLevel`, `KLiteral`, `KExpr`,
   `KSyntax`), structural pattern matching & `recConst` lowering (`lower_inductive_sound`), and LCNF
   lowering (`lcnf_to_core4_sound`).
2. `Obend.Leaf.Futamura`: Static data-pin specialization (`data_pin_flatten_sound`) and 1st, 2nd,
   and 3rd Futamura projections (`futamura1_env_specialize_sound`, `futamura2_self_specialize_sound`,
   `futamura3_cogen_sound`).
3. `Obend.Lower.LeanKernel`: Pure Lean kernel (`kernelWhnf`, `kernelIsDefEq`, `kernelInferType`,
   `kernelCheckDecl`) and pure elaborator passes (`expandMacrosFuel`, `simpRewriteFuel`,
   `synthInstanceFuel`), plus lowered `Core4` theorems (`silicon_kernel_whnf_sound`,
   `silicon_kernel_check_sound`).
4. `Obend.Lower.Proofs.SiliconKernel`: End-to-end 5-stage `ReductionMachine` hardware co-simulation
   (`silicon_kernel_5stage_check_sound`), Futamura `ICAP` DPR specialization
   (`silicon_elab_futamura_dpr_specialize_sound`), 1-cycle environment mutation fallback
   (`silicon_elab_env_mutation_fallback_sound`), and hardware interaction-net $\beta$-reduction
   (`silicon_kernel_inet_beta_agrees`).
5. **8 `#tooth` Kernel Mutation Tests** verifying that weakening any check or lowering pass is
   rejected by the Lean kernel.
-/
public import Obend.Tactic.Tooth
import all Obend.Lower.Inductive
import all Obend.Leaf.Futamura
import all Obend.Lower.LeanKernel
import all Obend.Lower.ExprCAM
import all Obend.Lower.Proofs.SiliconKernel
import all Obend.Hardware.ReductionMachine
public import Obend.Lower.ExprCAM
public import Obend.Lower.Proofs.SiliconKernel
@[expose] public section

namespace Obend.Tests.SiliconElab
open Obend.Core.Term
open Obend.Core.Ty (Ty)
open Obend.Equiv
open Obend.Slot
open Obend.Slot.World
open Obend.Leaf
open Obend.Leaf.Futamura
open Obend.Lower
open Obend.Lower.Inductive
open Obend.Lower.LeanKernel
open Obend.Lower.ExprCAM
open Obend.Lower.Proofs.SiliconKernel
open Obend.Hardware.HDL
open Obend.Hardware.Compiler
open Obend.Hardware.ReductionMachine
set_option autoImplicit false

/-! ## 1. Pure Elaborator Passes: Macro Expansion, `simp` Discrimination Tree, and Typeclass Synthesis -/

/-- Sample macro rules expanding `unlessStx` (`arity = 2`) into `iteNotStx`. -/
def sampleMacroRules : List MacroRule :=
  [ { kind := KName.mkSimple "unless"
    , arity := 2
    , targetKind := KName.mkSimple "iteNot" } ]

theorem macro_expansion_positive_and_negative :
    let cond := KSyntax.ident (KName.mkSimple "flag")
    let body := KSyntax.atom "body"
    -- Positive pole: arity-2 `unless` macro expands to `iteNot`
    expandMacrosFuel sampleMacroRules 4 (.node (KName.mkSimple "unless") [cond, body]) =
      .node (KName.mkSimple "iteNot") [cond, body] ∧
    -- Negative pole: wrong arity (1 arg instead of 2) is left unexpanded
    expandMacrosFuel sampleMacroRules 4 (.node (KName.mkSimple "unless") [cond]) =
      .node (KName.mkSimple "unless") [cond] := by
  exact ⟨rfl, rfl⟩

/-- Sample `simp` rewrite rule table indexed by `DiscrTreeKey`:
1. `add_zero : add x 0 = x` (concrete instance `add 42 0 ↦ 42`),
2. `id_nat_42 : idNat 42 ↦ 42`. -/
def sampleSimpRules : List SimpRule :=
  [ { name := KName.mkSimple "idNat_42"
    , key  := .app (KName.mkSimple "idNat")
    , lhs  := .app (.const (KName.mkSimple "idNat") []) (.lit (.natVal 42))
    , rhs  := .lit (.natVal 42) }
  , { name := KName.mkSimple "double_42"
    , key  := .app (KName.mkSimple "double")
    , lhs  := .app (.const (KName.mkSimple "double") []) (.lit (.natVal 42))
    , rhs  := .lit (.natVal 84) } ]

theorem simp_rewrite_engine_positive_and_negative :
    let nestedTerm := KExpr.app (.const (KName.mkSimple "double") [])
      (.app (.const (KName.mkSimple "idNat") []) (.lit (.natVal 42)))
    let unmatchedTerm := KExpr.app (.const (KName.mkSimple "unknownFn") []) (.lit (.natVal 7))
    -- Positive pole: bottom-up discrimination-tree rewrite simplifies `double (idNat 42) ↦ 84`
    -- and records the exact trace `[idNat_42, double_42]`
    simpRewriteFuel sampleSimpRules 4 nestedTerm =
      (.lit (.natVal 84), [KName.mkSimple "idNat_42", KName.mkSimple "double_42"]) ∧
    -- Negative pole: non-matching head symbol `unknownFn` produces 0 rewrites and empty trace `[]`
    simpRewriteFuel sampleSimpRules 4 unmatchedTerm = (unmatchedTerm, []) := by
  exact ⟨rfl, rfl⟩

/-- Sample typeclass table with `Add Nat` (`instAddNat`) and compound `Add (List Nat)`
requiring `[Add Nat]` as a subgoal (`instAddList`). -/
def sampleClassTable : List ClassInstance :=
  [ { instName   := KName.mkSimple "instAddNat"
    , className  := KName.mkSimple "Add"
    , targetType := kNatConst
    , subgoals   := [] }
  , { instName   := KName.mkSimple "instAddList"
    , className  := KName.mkSimple "Add"
    , targetType := .app (.const (KName.mkSimple "List") []) kNatConst
    , subgoals   := [(KName.mkSimple "Add", kNatConst)] } ]

theorem typeclass_synthesis_positive_and_negative :
    let listNat := KExpr.app (.const (KName.mkSimple "List") []) kNatConst
    let listBool := KExpr.app (.const (KName.mkSimple "List") []) kBoolConst
    -- Positive pole: backward-chaining synthesizes `instAddList instAddNat` for `Add (List Nat)`
    synthInstanceFuel sampleClassTable 4 (KName.mkSimple "Add") listNat =
      some (.app (.const (KName.mkSimple "instAddList") []) (.const (KName.mkSimple "instAddNat") [])) ∧
    -- Negative pole: `Add (List Bool)` fails because `Add Bool` is not registered
    synthInstanceFuel sampleClassTable 4 (KName.mkSimple "Add") listBool = none := by
  exact ⟨rfl, rfl⟩

/-! ## 2. End-to-End Verification Suite Across All 4 Silicon Elaborator Modules -/

theorem silicon_elaborator_master_suite :
    -- 1. Recursive AST Inductives (`KExpr`, `Obend.Core.Term`, `Lean.Name` bridge) & LCNF Lowering (including recursion)
    decodeExprTerm (lowerExpr (.app (.lam kNatConst (.bvar 0)) (.lit (.natVal 42)))) =
      some (.app (.lam kNatConst (.bvar 0)) (.lit (.natVal 42))) ∧
    decodeCoreTerm (lowerCoreTerm (.app (.lam (.bound 0)) (.nat 42))) =
      some (.app (.lam (.bound 0)) (.nat 42)) ∧
    fromLeanName (toLeanName (KName.mkSimple "LeanKernel")) = KName.mkSimple "LeanKernel" ∧
    Evaluates (lowerLCNF sampleLcnfAstMatch) (.nat 42) ∧
    Evaluates (.app (lowerLCNFFunDecl sampleLcnfRecDecl) (.nat 0)) (.nat 42) ∧
    -- 2. Futamura Projections (1st, 2nd, 3rd)
    dataPinSpecialize (.app sampleElabLookupTerm (pinTableToTerm sampleEnvPinTable)) = .nat 50 ∧
    Evaluates (.app (futamura1Specialize (futamura2SelfSpecialize (elabRuleSpec 10)) (.nat 32)) (.nat 5)) (.nat 47) ∧
    Evaluates (.app (.app (futamura3Cogen 100) (.nat 23)) (.nat 0)) (.nat 123) ∧
    -- 3. Self-Hosted Lean Kernel Positive & Negative Poles + Parametric Levels + Nat ι-Reduction
    kernelCheckDecl stdKernelEnv 8 validIdNatDecl = true ∧
    kernelCheckDecl stdKernelEnv 8 validPropIdDecl = true ∧
    kernelCheckDecl stdKernelEnv 8 validApplyId42Decl = true ∧
    kernelCheckDecl stdKernelEnv 8 invalidMismatchDecl = false ∧
    kernelCheckDecl stdKernelEnv 8 invalidBadAppDecl = false ∧
    kernelCheckDecl stdKernelEnv 8 invalidUniverseDecl = false ∧
    kernelCheckDecl stdKernelEnv 8 invalidSorryDecl = false ∧
    kernelLevelEq (.imax (.param (KName.mkSimple "u")) .zero) .zero = true ∧
    kernelWhnf stdKernelEnv 4 (.app (.app (.const (KName.mkSimple "Nat.add") []) (.lit (.natVal 40))) (.lit (.natVal 2))) = .lit (.natVal 42) ∧
    -- 4. SiliconKernel 5-Stage Hardware, Sequential RTL, XY Mesh, ICAP Codec & DPR Co-Simulation
    futamura1ElabSimpTerm = specializedSimpTerm ∧
    specSlot.usable (holdsAt pinnedSimpView) specializedSimpCand = true ∧
    specSlot.usable (holdsAt mutatedSimpView) specializedSimpCand = false ∧
    specSlot.usable (holdsAt mutatedSimpView) .machine = true ∧
    (encodeTileIcapWords specializedSimpTile).length = 5 := by
  refine ⟨(lower_inductive_sound .anonymous .zero (.app (.lam kNatConst (.bvar 0)) (.lit (.natVal 42))) .missing).2.2.2.2.2.2.1,
    decodeCoreTerm_lowerT (.app (.lam (.bound 0)) (.nat 42)),
    fromLeanName_toLeanName (KName.mkSimple "LeanKernel"),
    lcnf_to_core4_sound.2.2.2.2.1,
    lcnf_to_core4_sound.2.2.2.2.2,
    data_pin_flatten_sound.2.2.2,
    (futamura2_self_specialize_sound (elabRuleSpec 10) (.nat 32)).2.2.2.2,
    (futamura3_cogen_sound 100).2.2.2,
    silicon_kernel_check_sound.1,
    silicon_kernel_check_sound.2.1,
    silicon_kernel_check_sound.2.2.1,
    silicon_kernel_check_sound.2.2.2.1,
    silicon_kernel_check_sound.2.2.2.2.1,
    silicon_kernel_check_sound.2.2.2.2.2.1,
    silicon_kernel_check_sound.2.2.2.2.2.2.1,
    (kernelLevelEq_parametric_laws (KName.mkSimple "u") (KName.mkSimple "v")).2.2.2.1,
    (silicon_kernel_whnf_iota_and_nonLam_sound 0).2.1,
    futamura1ElabSimpTerm_eq_lowerLite.1,
    silicon_elab_futamura_dpr_specialize_sound.1,
    silicon_elab_env_mutation_fallback_sound.1,
    silicon_elab_env_mutation_fallback_sound.2.1,
    silicon_elab_mesh_xy_and_icap_codec_sound.1⟩

/-! ## 3. Ten `#tooth` Kernel Mutation Tests -/

/-- 1. Broken `exprContainsSorry` in `Obend.Lower.LeanKernel` that never flags `sorryAx` (`false`),
allowing `sorryAx`-contaminated theorems to slip past the kernel check. -/
def exprContainsSorryBlind : KExpr → Bool :=
  fun _ => false

#tooth Obend.Lower.LeanKernel.silicon_kernel_check_sound by mutation Obend.Lower.LeanKernel.exprContainsSorry := exprContainsSorryBlind

/-- 2. Broken `kernelCheckDecl` in `Obend.Lower.LeanKernel` that rubber-stamps every declaration
(`true`) without checking definitional equality or universe levels. -/
def kernelCheckDeclRubberStamp (_env : KEnv) (_fuel : Nat) (_decl : KConstInfo) : Bool :=
  true

#tooth Obend.Lower.LeanKernel.silicon_kernel_check_sound by mutation Obend.Lower.LeanKernel.kernelCheckDecl := kernelCheckDeclRubberStamp

/-- 3. Broken `kernelWhnf` in `Obend.Lower.LeanKernel` that skips β/ζ/δ reduction and returns
the unreduced expression `e`. -/
def kernelWhnfNoReduce (_env : KEnv) (_fuel : Nat) (e : KExpr) : KExpr :=
  e

#tooth Obend.Lower.LeanKernel.silicon_kernel_whnf_sound by mutation Obend.Lower.LeanKernel.kernelWhnf := kernelWhnfNoReduce

/-- 4. Broken `encodeDeclStatusTag` in `Obend.Lower.Proofs.SiliconKernel` that misclassifies
`sorryAx`-contaminated declarations as `1` (Accepted) instead of `0` (Refused). -/
def encodeDeclStatusTagAcceptSorry (_env : KEnv) (_fuel : Nat) (_decl : KConstInfo) : Nat :=
  1

#tooth Obend.Lower.Proofs.SiliconKernel.silicon_kernel_5stage_check_sound by mutation Obend.Lower.Proofs.SiliconKernel.encodeDeclStatusTag := encodeDeclStatusTagAcceptSorry

/-- 5. Broken `kernelGateBody` in `Obend.Lower.Proofs.SiliconKernel` that inverts the hardware
acceptance gate (returning `1` on rejected tags and `0` on valid tag `1`). -/
def kernelGateBodyInverted : LExpr :=
  .boolRec .natural
    (.lit 1)
    (.lit 0)
    (.natBin .beq (.bvar 0) (.lit 1))

#tooth Obend.Lower.Proofs.SiliconKernel.silicon_kernel_5stage_check_sound by mutation Obend.Lower.Proofs.SiliconKernel.kernelGateBody := kernelGateBodyInverted

/-- 6. Broken `dataPinSpecialize` in `Obend.Leaf.Futamura` that performs `0` specialization passes
(failing to fold static environment lookups and constructor cases). -/
def dataPinSpecializeNoOp (t : Term) : Term :=
  t

#tooth Obend.Leaf.Futamura.data_pin_flatten_sound by mutation Obend.Leaf.Futamura.dataPinSpecialize := dataPinSpecializeNoOp

/-- 7. Broken `isZeroLevelLExpr` in `Obend.Lower.Inductive` that maps `"zero"` to `false` instead of `true`. -/
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

/-- 8. Broken `dprPhase3ReleaseFence` in `Obend.Hardware.ReductionMachine` that unconditionally
releases the Region Isolation Fence (`isolated := false`) even when the bitstream CRC check fails. -/
def dprPhase3ReleaseFenceIgnoreCrc (frame : IcapBitstreamFrame) (t : ReconfigTileState) : ReconfigTileState :=
  if t.tileId == frame.targetTileId then
    { t with isolated := false }
  else
    t

#tooth Obend.Lower.Proofs.SiliconKernel.silicon_elab_env_mutation_fallback_sound by mutation Obend.Hardware.ReductionMachine.dprPhase3ReleaseFence := dprPhase3ReleaseFenceIgnoreCrc

/-- 9. Broken `KLevel.normalize` in `Obend.Lower.LeanKernel` that skips algebraic `max`/`imax`
normalization on parametric universe levels. -/
def kLevelNormalizeNoOp (l : KLevel) : KLevel :=
  l

#tooth Obend.Lower.LeanKernel.kernelLevelEq_parametric_laws by mutation Obend.Lower.LeanKernel.KLevel.normalize := kLevelNormalizeNoOp

/-- 10. Broken `reduceNatIota?` in `Obend.Lower.LeanKernel` that skips `Nat` literal and `Bool.rec`
$\iota$-reduction during `kernelWhnf`. -/
def reduceNatIotaNoOp (_fn : KExpr) (_arg : KExpr) : Option KExpr :=
  none

#tooth Obend.Lower.LeanKernel.silicon_kernel_whnf_iota_and_nonLam_sound by mutation Obend.Lower.LeanKernel.reduceNatIota? := reduceNatIotaNoOp

/-- 11. Broken `reduceGeneralIota?` in `Obend.Lower.LeanKernel` that skips dynamic user-defined
inductive recursor $\iota$-reduction (`OptionNat.rec`, `PairNat.rec`). -/
def reduceGeneralIotaNoOp (_env : KEnv) (_fn _arg : KExpr) : Option KExpr :=
  none

#tooth Obend.Lower.LeanKernel.kernelWhnf_general_iota_sound by mutation Obend.Lower.LeanKernel.reduceGeneralIota? := reduceGeneralIotaNoOp

/-- 12. Broken `reduceQuotLift?` in `Obend.Lower.LeanKernel` that skips `Quot.lift` reduction on `Quot.mk`. -/
def reduceQuotLiftNoOp (_fn _arg : KExpr) : Option KExpr :=
  none

#tooth Obend.Lower.LeanKernel.kernelWhnf_quot_lift_sound by mutation Obend.Lower.LeanKernel.reduceQuotLift? := reduceQuotLiftNoOp

/-- 13. Broken `internRootNode` in `Obend.Lower.ExprCAM` that skips CAM lookup deduplication and
allocates a duplicate handle every time. -/
def internRootNodeNoDedup (cam : ExprCAM) (e : KExpr) (leftH rightH : Nat) : ExprCAM × CamHandle :=
  let h := cam.entries.length
  let entry : CamSlotEntry :=
    { handle := h
    , word64 := mkExprCamWord64 e leftH rightH
    , expr   := e }
  ({ entries := cam.entries ++ [entry] }, h)

#tooth Obend.Lower.ExprCAM.exprCam_eq_iff_handle_eq by mutation Obend.Lower.ExprCAM.internRootNode := internRootNodeNoDedup

/-! ## 4. Axiom Hygiene Verification (`0 sorryAx`, `0` Custom Axioms) -/

#print axioms Obend.Lower.Inductive.lower_inductive_sound
#print axioms Obend.Lower.Inductive.decodeCoreTerm_lowerT
#print axioms Obend.Lower.Inductive.fromLeanName_toLeanName
#print axioms Obend.Lower.Inductive.lcnf_to_core4_sound
#print axioms Obend.Leaf.Futamura.data_pin_flatten_sound
#print axioms Obend.Leaf.Futamura.futamura1_env_specialize_sound
#print axioms Obend.Leaf.Futamura.futamura2_self_specialize_sound
#print axioms Obend.Leaf.Futamura.futamura3_cogen_sound
#print axioms Obend.Lower.LeanKernel.kernelLevelEq_parametric_laws
#print axioms Obend.Lower.LeanKernel.silicon_kernel_whnf_sound
#print axioms Obend.Lower.LeanKernel.silicon_kernel_whnf_iota_and_nonLam_sound
#print axioms Obend.Lower.LeanKernel.silicon_kernel_check_sound
#print axioms Obend.Lower.LeanKernel.kernelWhnf_general_iota_sound
#print axioms Obend.Lower.LeanKernel.kernelWhnf_quot_lift_sound
#print axioms Obend.Lower.ExprCAM.unpack_pack_camWord64
#print axioms Obend.Lower.ExprCAM.exprCam_looseBVar_flag_sound
#print axioms Obend.Lower.ExprCAM.exprCam_eq_iff_handle_eq
#print axioms Obend.Lower.ExprCAM.exprCam_roundtrip_sound
#print axioms Obend.Lower.ExprCAM.silicon_live_env_decl_check_sound
#print axioms Obend.Lower.Proofs.SiliconKernel.silicon_kernel_5stage_check_sound
#print axioms Obend.Lower.Proofs.SiliconKernel.silicon_elab_futamura_dpr_specialize_sound
#print axioms Obend.Lower.Proofs.SiliconKernel.silicon_elab_env_mutation_fallback_sound
#print axioms Obend.Lower.Proofs.SiliconKernel.silicon_kernel_inet_beta_agrees
#print axioms Obend.Lower.Proofs.SiliconKernel.silicon_kernel_seq_rtl_fuel_sound
#print axioms Obend.Lower.Proofs.SiliconKernel.silicon_elab_mesh_xy_and_icap_codec_sound
#print axioms Obend.Tests.SiliconElab.silicon_elaborator_master_suite

end Obend.Tests.SiliconElab
end
