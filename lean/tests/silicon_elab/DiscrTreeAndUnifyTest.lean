import Obend.Lower.DiscrTreeLUT
import Obend.Lower.MetaUnify
import Obend.Lower.Inductive
import Obend.Lower.Proofs.Hardware
import Obend.Hardware.Fabric

/-!
# End-to-End Test Suite: Branched Radix `DiscrTree`, Priority TCAM Synthesis, `ExprCAM` Miller Unification & Multi-Constructor Recursor Lowering (`WS-H`)
-/

namespace Obend.Tests.SiliconElab

open Obend.Core.Term
open Obend.Lower
open Obend.Lower.Inductive
open Obend.Lower.LeanKernel
open Obend.Lower.ExprCAM
open Obend.Lower.MetaUnify
open Obend.Lower.DiscrTreeLUT
open Obend.Hardware.HDL
open Obend.Hardware.Fabric

/-! ## 1. Branched Radix `DiscrTrieNode` Insertion, Prefix Sharing & Wildcard `.star` Lookup -/

def testTrieRoot : DiscrTrieNode :=
  buildDiscrTrieNode sampleEpoch1DiscrTrie.entries

example (path : DiscrPath) (entry : DiscrTreeEntry) (node : DiscrTrieNode) :
    entry ∈ queryDiscrTrieNode (insertDiscrTrieNode path entry node) path :=
  queryDiscrTrieNode_insert_mem path entry node

example (patPath qPath : DiscrPath) (entry : DiscrTreeEntry) (node : DiscrTrieNode)
    (hMatch : matchDiscrPath patPath qPath = true) :
    entry ∈ queryDiscrTrieNode (insertDiscrTrieNode patPath entry node) qPath :=
  queryDiscrTrieNode_insert_mem_of_matchDiscrPath patPath qPath entry node hMatch

/-- Wildcard `.star` branch exploration, exact key matching, and cross-branch priority ordering in `DiscrTrieNode`. -/
example :
    let qSimpPath := exprToDiscrPath 4 (.app (.const (KName.mkSimple "scaleAdd") []) (.lit (.natVal 10)))
    let qAddNatPath := exprToDiscrPath 4 (.app (.const (KName.mkSimple "Add") []) kNatConst)
    let qAddBoolPath := exprToDiscrPath 4 (.app (.const (KName.mkSimple "Add") []) kBoolConst)
    (queryDiscrTrieNode testTrieRoot qSimpPath).map (·.lutTag) = [101] ∧
    (queryDiscrTrieNode testTrieRoot qAddNatPath).map (·.lutTag) = [202] ∧
    queryDiscrTrieNode testTrieRoot qAddBoolPath = [] := by
  decide +kernel

example :
    let rWild : DiscrTreeEntry :=
      { ruleName := KName.mkSimple "simp_scale_wild"
      , path     := [.app (KName.mkSimple "scaleAdd"), .star]
      , lutTag   := 101
      , kind     := .simpLemma (.lit (.natVal 42)) 4 2 }
    let rExact : DiscrTreeEntry :=
      { ruleName := KName.mkSimple "simp_scale_exact10"
      , path     := [.app (KName.mkSimple "scaleAdd"), .lit (.natVal 10)]
      , lutTag   := 303
      , kind     := .simpLemma (.lit (.natVal 500)) 50 0 }
    let qPath : DiscrPath := [.app (KName.mkSimple "scaleAdd"), .lit (.natVal 10)]
    (queryDiscrTrieNode (buildDiscrTrieNode [rWild, rExact]) qPath).map (·.lutTag) = [303, 101] ∧
    (queryDiscrTrieNode (buildDiscrTrieNode [rExact, rWild]) qPath).map (·.lutTag) = [303, 101] :=
  queryDiscrTrieNode_star_and_exact_priority_sound

/-- info: [101] -/
#guard_msgs in
#eval (queryDiscrTrieNode testTrieRoot
  (exprToDiscrPath 4 (.app (.const (KName.mkSimple "scaleAdd") []) (.lit (.natVal 10))))).map (·.lutTag)

/-! ## 2. Multi-Rule Priority TCAM Synthesis (`compileDiscrTrieToRtl`) -/

def samplePriorityRules : List (Nat × Nat × Nat) :=
  [ (101, 4, 2)
  , (202, 6, 10)
  , (101, 99, 99) ] -- shadowed lower-priority rule with same patternTag = 101

def samplePriorityTcamRtl : RtlModule :=
  compileDiscrTrieToRtl "test_priority_tcam" samplePriorityRules

example : checkRtlModule samplePriorityTcamRtl = true :=
  compileDiscrTrieToRtl_dag_valid "test_priority_tcam" samplePriorityRules

/-- info: [("out_tcam", 42#64)] -/
#guard_msgs in
#eval evalModuleOutputs samplePriorityTcamRtl (fun | 0 => 101#64 | 1 => 10#64 | _ => 0#64) (fun _ => 0#64)

/-- Verify first-matching rule priority shadowing, second-rule hit, and default `0#64` miss. -/
example :
    let inRule1 : Nat → BitVec 64 | 0 => 101#64 | 1 => 10#64 | _ => 0#64
    let inRule2 : Nat → BitVec 64 | 0 => 202#64 | 1 => 10#64 | _ => 0#64
    let inMiss  : Nat → BitVec 64 | 0 => 999#64 | 1 => 10#64 | _ => 0#64
    evalModuleOutputs samplePriorityTcamRtl inRule1 (fun _ => 0#64) = [("out_tcam", 42#64)] ∧
    evalModuleOutputs samplePriorityTcamRtl inRule2 (fun _ => 0#64) = [("out_tcam", 70#64)] ∧
    evalModuleOutputs samplePriorityTcamRtl inMiss  (fun _ => 0#64) = [("out_tcam", 0#64)] := by
  decide +kernel

example (inputs regs : Nat → BitVec 64) (h : inputs 0 = 101#64) :
    evalModuleOutputs samplePriorityTcamRtl inputs regs =
      [("out_tcam", inputs 1 * 4#64 + 2#64)] :=
  (compileDiscrTrieToRtl_matches_first_rule "test_priority_tcam" 101 4 2
    [(202, 6, 10), (101, 99, 99)] inputs regs).2 h

/-! ## 3. `ExprCAM` Bit-58/59 $O(1)$ Scope Filtering, Transitive MVar Compression & Ternary Miller Unification -/

example (e : KExpr) (l r : Nat) (allowed : List Nat) :
    (checkMVarOccursBit58 (mkExprCamWord64 e l r) = true ↔ KExpr.hasFVar e = true) ∧
    (checkLooseBVarBit59 (mkExprCamWord64 e l r) = true ↔ KExpr.hasLooseBVar e = true) ∧
    (checkMVarOccursBit58 (mkExprCamWord64 e l r) = false → scopeCheckFVars allowed e = true) :=
  checkMVarOccursBit58_iff e l r allowed

example :
    checkMVarOccursBit58 (mkExprCamWord64 (.fvar 10) 0 0) = true ∧
    checkMVarOccursBit58 (mkExprCamWord64 kNatConst 0 0) = false ∧
    compressMVarChainFuel 4 sampleChainMCtx 0 = some (.lit (.natVal 42)) ∧
    compressMVarChainFuel 1 (compressMCtxChain 4 sampleChainMCtx 0) 0 =
      compressMVarChainFuel 4 sampleChainMCtx 0 ∧
    compressMVarChainFuel 4 (compressMCtxChain 4 sampleChainMCtx 99) 99 = none := by
  refine ⟨rfl, rfl, compressMVarChainFuel_idempotent.2.1, compressMVarChainFuel_idempotent.2.2, rfl⟩

/-- info: some (Obend.Lower.Inductive.KExpr.lit (Obend.Lower.Inductive.KLiteral.natVal 42)) -/
#guard_msgs in
#eval compressMVarChainFuel 4 sampleChainMCtx 0

example :
    let lhs3 := KExpr.app (.app (.app (mkMVarExpr 3) (.fvar 10)) (.fvar 11)) (.fvar 12)
    let rhs3 :=
      KExpr.app
        (.app (.const (KName.mkSimple "Nat.add") [])
          (.app (.app (.const (KName.mkSimple "Nat.mul") []) (.fvar 12)) (.fvar 10)))
        (.fvar 11)
    (metaUnifyFuel stdKernelEnv 8 sampleTernaryMetaCtx lhs3 rhs3).isSome = true ∧
    millerPatternUnify? sampleTernaryMetaCtx 8 3 [.fvar 10, .fvar 11, .fvar 10] (.fvar 10) = none := by
  decide +kernel

/-! ## 4. Multi-Constructor & Nested Recursor Lowering (`compileMultiCtorIota`) -/

example :
    Evaluates (lowerT (.app natRecIotaLExpr (peanoNatToLExpr 3))) (.nat 3) ∧
    Evaluates (lowerT (.app (optionRecIotaLExpr 42) (optionNatToLExpr none))) (.nat 42) ∧
    Evaluates (lowerT (.app (optionRecIotaLExpr 42) (optionNatToLExpr (some 99)))) (.nat 99) ∧
    Evaluates (lowerT (.app listLenIotaLExpr (natListToLExpr [10, 20, 30]))) (.nat 3) ∧
    Evaluates (lowerT (.app nestedOptionListIotaLExpr (optionListToLExpr none))) (.nat 0) ∧
    Evaluates (lowerT (.app nestedOptionListIotaLExpr (optionListToLExpr (some [10, 20, 30])))) (.nat 3) := by
  have h := multiCtorIota_hardware_bridge_sound 3 42 99 [10, 20, 30]
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, nestedOptionListIota_eval none, h.2.2.2.2.1⟩

/-! ## 5. Linear/Affine Wire-Fanout & Zero-Fork Elastic Handshake Verifier -/

/-- info: (1, true, 0, false, 1) -/
#guard_msgs in
#eval
  let netLinear : NetFanoutExpr := .add64 (.wire "x") (.wire "y")
  let netDup    : NetFanoutExpr := .add64 (.wire "x") (.wire "x")
  ( countSinkFanout "x" netLinear
  , checkWireMult .linear (countSinkFanout "x" netLinear)
  , requiredElasticForks "x" netLinear
  , checkWireMult .linear (countSinkFanout "x" netDup)
  , requiredElasticForks "x" netDup )

example :
    let netLinear : NetFanoutExpr := .add64 (.wire "x") (.wire "y")
    let netDup    : NetFanoutExpr := .add64 (.wire "x") (.wire "x")
    countSinkFanout "x" netLinear = 1 ∧
    checkWireMult .linear (countSinkFanout "x" netLinear) = true ∧
    requiredElasticForks "x" netLinear = 0 ∧
    checkWireMult .linear (countSinkFanout "x" netDup) = false ∧
    requiredElasticForks "x" netDup = 1 := by
  decide +kernel

example (w : String) (e : NetFanoutExpr)
    (hok : checkWireMult .linear (countSinkFanout w e) = true) :
    requiredElasticForks w e = 0 :=
  linear_or_affine_wire_zero_elastic_forks w .linear e (Or.inl rfl) hok

end Obend.Tests.SiliconElab
