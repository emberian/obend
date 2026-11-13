import Obend.Lower.DiscrTreeLUT
import Obend.Lower.MetaUnify
import Obend.Lower.Inductive
import Obend.Lower.Proofs.Hardware

/-!
# End-to-End Test Suite: Arity-Tagged Polish `DiscrTrieNode`, Priority TCAM Synthesis, First-Class `.mvar` Miller Unification & Multi-Constructor Recursor Lowering
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

/-! ## 1. Arity-Tagged Polish `DiscrTrieNode` Insertion, Non-Collision & Wildcard `.star` Lookup -/

def testTrieEntries : List DiscrTreeEntry :=
  let scalePat := KExpr.app (.const (KName.mkSimple "scaleAdd") []) (.mvar 0)
  let addNatPat := KExpr.app (.const (KName.mkSimple "Add") []) kNatConst
  [ { ruleName := KName.mkSimple "scaleAdd_rule"
    , path     := exprToDiscrPath 4 scalePat
    , lutTag   := 101
    , kind     := .simpLemma (.lit (.natVal 42)) 4 2 }
  , { ruleName := KName.mkSimple "addNat_inst"
    , path     := exprToDiscrPath 4 addNatPat
    , lutTag   := 202
    , kind     := .synthInstance (KName.mkSimple "Add") (.const (KName.mkSimple "instAddNat") []) 1000 } ]

def testTrieRoot : DiscrTrieNode :=
  buildDiscrTrieNode testTrieEntries

example (path : DiscrPath) (entry : DiscrTreeEntry) (node : DiscrTrieNode) :
    entry ∈ queryDiscrTrieNode (insertDiscrTrieNode path entry node) path :=
  queryDiscrTrieNode_insert_mem path entry node

example (patPath qPath : DiscrPath) (entry : DiscrTreeEntry) (node : DiscrTrieNode)
    (hMatch : matchDiscrPath patPath qPath = true) :
    entry ∈ queryDiscrTrieNode (insertDiscrTrieNode patPath entry node) qPath :=
  queryDiscrTrieNode_insert_mem_of_matchDiscrPath patPath qPath entry node hMatch

/-- Arity-tagged Polish `exprToDiscrPath` separates nested vs curried spines `h (c a) b` and `h (c a b)`
with zero false-positive prefix collisions in `DiscrTrieNode`! -/
example :
    let hConst := KExpr.const (KName.mkSimple "h") []
    let cConst := KExpr.const (KName.mkSimple "c") []
    let aConst := KExpr.const (KName.mkSimple "a") []
    let bConst := KExpr.const (KName.mkSimple "b") []
    let nestedSpine := KExpr.app (.app hConst (.app cConst aConst)) bConst
    let flatSpine   := KExpr.app hConst (.app (.app cConst aConst) bConst)
    let pNested := exprToDiscrPath 8 nestedSpine
    let pFlat   := exprToDiscrPath 8 flatSpine
    let entryNested : DiscrTreeEntry :=
      { ruleName := KName.mkSimple "nested_rule"
      , path     := pNested
      , lutTag   := 701
      , kind     := .simpLemma aConst 1000 0 }
    let trie := insertDiscrTrieNode pNested entryNested .empty
    pNested ≠ pFlat ∧
    (queryDiscrTrieNode trie pNested).map (·.lutTag) = [701] ∧
    queryDiscrTrieNode trie pFlat = [] := by
  decide +kernel

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
      , path     := [.const (KName.mkSimple "scaleAdd") 1, .star]
      , lutTag   := 101
      , kind     := .simpLemma (.lit (.natVal 42)) 4 2 }
    let rExact : DiscrTreeEntry :=
      { ruleName := KName.mkSimple "simp_scale_exact10"
      , path     := [.const (KName.mkSimple "scaleAdd") 1, .lit (.natVal 10)]
      , lutTag   := 303
      , kind     := .simpLemma (.lit (.natVal 500)) 50 0 }
    let qPath : DiscrPath := [.const (KName.mkSimple "scaleAdd") 1, .lit (.natVal 10)]
    (queryDiscrTrieNode (buildDiscrTrieNode [rWild, rExact]) qPath).map (·.lutTag) = [303, 101] ∧
    (queryDiscrTrieNode (buildDiscrTrieNode [rExact, rWild]) qPath).map (·.lutTag) = [303, 101] := by
  decide +kernel

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

/-! ## 3. First-Class `KExpr.mvar`, Bit-58/59 Scope Filtering, Binder Opening & Ternary Miller Unification -/

example (e : KExpr) (l r : Nat) (allowed : List Nat) :
    (checkMVarOccursBit58 (mkExprCamWord64 e l r) = true ↔ KExpr.hasFVar e = true) ∧
    (checkLooseBVarBit59 (mkExprCamWord64 e l r) = true ↔ KExpr.hasLooseBVar e = true) ∧
    (checkMVarOccursBit58 (mkExprCamWord64 e l r) = false → scopeCheckFVars allowed e = true) :=
  checkMVarOccursBit58_iff e l r allowed

/-- First-class `KExpr.mvar` roundtrips across `Inductive` and `HwExprCAM`, transitive MVar chain
compression idempotence, and fresh-`.fvar` binder opening under `.lam` / `.forallE`. -/
example :
    decodeExprTerm (lowerExpr (.mvar 7)) = some (.mvar 7) ∧
    reconstructFromHwExprCAM 4 (internToHwExprCAM (.mvar 7) HwExprCAM.empty).2
      (internToHwExprCAM (.mvar 7) HwExprCAM.empty).1 = some (.mvar 7) ∧
    checkMVarOccursBit58 (mkExprCamWord64 (.fvar 10) 0 0) = true ∧
    checkMVarOccursBit58 (mkExprCamWord64 kNatConst 0 0) = false ∧
    compressMVarChainFuel 4 sampleChainMCtx 0 = some (.lit (.natVal 42)) ∧
    compressMVarChainFuel 1 (compressMCtxChain 4 sampleChainMCtx 0) 0 =
      compressMVarChainFuel 4 sampleChainMCtx 0 ∧
    compressMVarChainFuel 4 (compressMCtxChain 4 sampleChainMCtx 99) 99 = none ∧
    -- Fresh-fvar binder opening: rejects bound-variable escape `?2 := x`, accepts Miller `?0 x =?= x`
    metaUnifyFuel stdKernelEnv 8 samplePostponedMCtx
      (.lam kNatConst (.mvar 2)) (.lam kNatConst (.bvar 0)) = none ∧
    (metaUnifyFuel stdKernelEnv 8 samplePostponedMCtx
      (.lam kBoolConst (.app (.mvar 0) (.bvar 0)))
      (.lam kBoolConst (.bvar 0))).bind (fun m => m.getAssignment? 0) =
      some (.lam kBoolConst (.bvar 0)) := by
  refine ⟨decodeExprTerm_lowerT (.mvar 7), by decide +kernel, rfl, rfl, rfl,
          compressMVarChainFuel_idempotent 4 0 sampleChainMCtx 0 (.lit (.natVal 42)) rfl rfl,
          rfl, by decide +kernel, by decide +kernel⟩

/-- info: some (Obend.Lower.Inductive.KExpr.lit (Obend.Lower.Inductive.KLiteral.natVal 42)) -/
#guard_msgs in
#eval compressMVarChainFuel 4 sampleChainMCtx 0

example :
    let lhs3 := KExpr.app (.app (.app (.mvar 3) (.fvar 10)) (.fvar 11)) (.fvar 12)
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

end Obend.Tests.SiliconElab
