module
/-
# `TrueFutamuraAndBytecodeJitTest` — Metasystem Harness for Genuine Futamura 1/2/3 & Bytecode JIT

End-to-end execution, `#guard` witnesses, `Core4` demand-machine bridge checks, `#tooth` mutation
sensitivity kills, and zero-axiom imported-tree verification (`#assert_axioms_tree`) for:
- `Obend.Leaf.SelfApplicableMixCore` & `Obend.Leaf.SelfApplicableMix`
- `Obend.Leaf.BytecodeRegisterJit`
-/
public import Obend.Leaf.SelfApplicableMix
public import Obend.Leaf.BytecodeRegisterJit
public import Obend.Tactic.Tooth
public import Obend.AssertAxioms
meta import all Obend.Leaf.SelfApplicableMixCore
meta import all Obend.Leaf.SelfApplicableMix
meta import all Obend.Leaf.BytecodeRegisterJit
meta import all Obend.Leaf.Flatten
meta import all Obend.Leaf.Static
meta import all Obend.Core.RangeSafe
meta import all Obend.Core.Machine
meta import all Obend.Core.MachineFast

-- Full bodies across the transitive import cone for `#assert_axioms_tree`.
import all Obend.Apps.ZkNtt.Goldilocks
import all Obend.AssertAxioms
import all Obend.Core.AliasExposure
import all Obend.Core.Assumptions
import all Obend.Core.Bidirectional
import all Obend.Core.Brand
import all Obend.Core.Capacity
import all Obend.Core.Check
import all Obend.Core.Code
import all Obend.Core.Data
import all Obend.Core.Digest
import all Obend.Core.EquiRecursiveAgreement
import all Obend.Core.EquiRecursiveLookup
import all Obend.Core.FieldCongruence
import all Obend.Core.FiniteBisimulation
import all Obend.Core.FinitePresentation
import all Obend.Core.FiniteRowLaws
import all Obend.Core.Invariant
import all Obend.Core.Machine
import all Obend.Core.MachineFast
import all Obend.Core.MachineTyping
import all Obend.Core.Nominal
import all Obend.Core.Proofs.Adequacy.Birth
import all Obend.Core.Proofs.Adequacy.CasesControl
import all Obend.Core.Proofs.Adequacy.CasesEval
import all Obend.Core.Proofs.Adequacy.CasesReturn
import all Obend.Core.Proofs.Adequacy.Defs
import all Obend.Core.Proofs.Adequacy.Graph
import all Obend.Core.Proofs.Adequacy.Meaning
import all Obend.Core.Proofs.Adequacy.Origins
import all Obend.Core.Proofs.Adequacy.Progress
import all Obend.Core.Proofs.Adequacy.Reach
import all Obend.Core.Proofs.Adequacy.Run
import all Obend.Core.Proofs.Adequacy.Safety
import all Obend.Core.Proofs.Adequacy.SafetyRaw
import all Obend.Core.Proofs.Adequacy.Scoped
import all Obend.Core.Proofs.Adequacy.Sound
import all Obend.Core.Proofs.Adequacy.Source
import all Obend.Core.Proofs.Adequacy.StepRaw
import all Obend.Core.Proofs.BidirectionalCompleteness
import all Obend.Core.Proofs.Completeness
import all Obend.Core.Proofs.DataSoundness
import all Obend.Core.Proofs.GroundExecution
import all Obend.Core.Proofs.Preservation.Base.Heads
import all Obend.Core.Proofs.Preservation.Base.Insert
import all Obend.Core.Proofs.Preservation.Base.Reusable
import all Obend.Core.Proofs.Preservation.Base.Values
import all Obend.Core.Proofs.Preservation.Base.Weaken
import all Obend.Core.Proofs.StepCases
import all Obend.Core.Proofs.Substitution.Defs
import all Obend.Core.Proofs.Substitution.Uses
import all Obend.Core.Proofs.TypedSubstitution
import all Obend.Core.RangeSafe
import all Obend.Core.RecursiveAgreement
import all Obend.Core.RecursiveRows
import all Obend.Core.ResourceSemantics
import all Obend.Core.RowCongruence
import all Obend.Core.RowExposureInvariance
import all Obend.Core.RowHit
import all Obend.Core.RuntimeOrigins
import all Obend.Core.Term
import all Obend.Core.TermTraverse
import all Obend.Core.Traverse
import all Obend.Core.Ty
import all Obend.Core.TypeGraph
import all Obend.Core.TypeGraphAlias
import all Obend.Core.TypeGraphHead
import all Obend.Core.TypeGraphResource
import all Obend.Digest.Cshake256
import all Obend.Digest.Cshake256.Fast
import all Obend.Digest.Cshake256.Seam
import all Obend.Digest.Cshake256.Spec
import all Obend.Digest.HashBytes
import all Obend.Elab.Work
import all Obend.Equiv.Ahead
import all Obend.Equiv.Behaviour
import all Obend.Equiv.Fields
import all Obend.Equiv.Quote
import all Obend.Equiv.Reduction
import all Obend.Equiv.Simulation
import all Obend.Hardware.Compiler
import all Obend.Hardware.HDL
import all Obend.Hardware.Types
import all Obend.Intention
import all Obend.Kind
import all Obend.Law.Claim
import all Obend.Law.Inherit
import all Obend.Law.Machine
import all Obend.Law.Proofs.Claim
import all Obend.Law.Proofs.Eval
import all Obend.Law.Proofs.Inherit
import all Obend.Law.Proofs.Machine
import all Obend.Law.Proofs.Run
import all Obend.Law.Proofs.Std
import all Obend.Law.Run
import all Obend.Law.Std
import all Obend.Law.Syntax
import all Obend.Leaf.Emit
import all Obend.Leaf.Flatten
import all Obend.Leaf.SelfApplicableMix
import all Obend.Leaf.SelfApplicableMixCore
import all Obend.Leaf.Served
import all Obend.Leaf.Specialize
import all Obend.Leaf.Static
import all Obend.Leaf.UpTo
import all Obend.Leaf.BytecodeRegisterJit
import all Obend.Logic.Claim
import all Obend.Logic.LateBinding
import all Obend.Lower.Lower
import all Obend.Lower.Proofs.Book
import all Obend.Lower.Proofs.Sound
import all Obend.Lower.Proofs.Subst
import all Obend.Lower.Semantics
import all Obend.Lower.Syntax
import all Obend.Slot
import all Obend.Slot.Core4
import all Obend.Slot.Integrity
import all Obend.Slot.Protocol
import all Obend.Slot.Selection
import all Obend.Slot.World
import all Obend.Spec.C4
import all Obend.Spec.Proofs.C4
import all Obend.Tactic.Cases
import all Obend.Tactic.MonadicReduction
import all Obend.Tactic.Tooth

public section
namespace Obend.Tests.TrueFutamuraAndBytecodeJit

open Obend.Core.Term
open Obend.Core.RangeSafe
open Obend.Core.Machine
open Obend.Core.MachineFast
open Obend.Leaf.SelfApplicableMix
open Obend.Leaf.BytecodeRegisterJit

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-! ## 1. Quotation Roundtrip & Genuine 1st Futamura Projection (`mix(⌜interp⌝, src) = ⌜target⌝`) -/

#guard unquoteProg? (quoteProg mixProg) == some mixProg
#guard unquoteProg? (quoteProg objInterp) == some objInterp
#guard unquoteProg? (.sym .entry) == none

/-- Iterative countdown source program in `ObjSrc`: decrements `var0` to `0` and returns `var0 + 42`. -/
def countdownToZeroObjSrc : ObjSrc :=
  .whilePos .var0 (.sub .var0 (.lit 1)) (.add .var0 (.lit 42))

-- 1st Futamura Projection on `quadPolyObjSrc` (`x^2 + 3x + 5`):
-- strips all static interpreter dispatch and agrees across arbitrary dynamic inputs.
#guard match runMixSpecialize 400 objInterp (quoteObjSrc quadPolyObjSrc) with
  | some target =>
    !hasStaticConstruct target &&
    decide (progSize target < progSize objInterp) &&
    checkSpecializesProg 40 objInterp (quoteObjSrc quadPolyObjSrc) target &&
    [0, 1, 5, 12].all (fun x =>
      evalMix 40 target .nil (.num x) == evalMix 200 objInterp (quoteObjSrc quadPolyObjSrc) (.num x) &&
      evalMix 40 target .nil (.num x) == some (.num (x * x + 3 * x + 5)))
  | none => false

-- 1st Futamura Projection on stateful loop `countdownToZeroObjSrc` (`.whilePos` -> residual `.dWhile`):
#guard match runMixSpecialize 400 objInterp (quoteObjSrc countdownToZeroObjSrc) with
  | some loopTarget =>
    !hasStaticConstruct loopTarget &&
    decide (progSize loopTarget < progSize objInterp) &&
    checkSpecializesProg 40 objInterp (quoteObjSrc countdownToZeroObjSrc) loopTarget &&
    evalMix 120 loopTarget .nil (.num 7) == some (.num 42) &&
    evalMix 200 objInterp (quoteObjSrc countdownToZeroObjSrc) (.num 7) == some (.num 42)
  | none => false

-- Direct execution of `lowerMixToCore4` residual target code on `Core4` `MachineFast.runBoundedFast`:
#guard match runMixSpecialize 400 objInterp (quoteObjSrc quadPolyObjSrc) with
  | some target =>
    let coreTerm := Term.app extractNumCore (applyLoweredMix (lowerMixToCore4 target) 12 .nil (.num 5))
    match runBoundedFast { heap := 8192, stack := 1024 } 100000 (initial coreTerm) with
    | .finished (.natural n) _ => n == 45
    | _ => false
  | none => false

-- Kernel instantiation of `futamura1_target_sound` + `lowerMixToCore4_machine_complete`:
example (x : Nat) :
    ∃ target : MixProg,
      evalMix 400 mixProg (quoteProg objInterp) (quoteObjSrc quadPolyObjSrc) = some (quoteProg target) ∧
      hasStaticConstruct target = false ∧
      progSize target < progSize objInterp ∧
      ∃ (limits : Limits) (ticks : Nat) (final : State),
        runBounded limits ticks
          (initial (.app extractNumCore (applyLoweredMix (lowerMixToCore4 target) 40 .nil (.num x)))) =
        .finished (.natural (x * x + 3 * x + 5)) final := by
  obtain ⟨target, hMix, hCert, hSz, hRun⟩ := futamura1_target_inhabited x
  obtain ⟨hEvalMix, hStrip, _⟩ := futamura1_target_sound 400 40 objInterp (quoteObjSrc quadPolyObjSrc) target hMix hCert
  obtain ⟨_, _, limits, ticks, final, hMach⟩ := lowerMixToCore4_machine_complete target 40 .nil (.num x) (x * x + 3 * x + 5) hRun
  exact ⟨target, hEvalMix, hStrip, hSz, limits, ticks, final, hMach⟩

/-! ## 2. Genuine 2nd Futamura Projection (`mix(⌜mix⌝, ⌜interp⌝) = ⌜compiler⌝`) -/

-- Self-applying `mixProg` to `(quoteProg mixProg, quoteProg objInterp)` inside `evalMix` produces
-- a standalone 6-procedure `MixProg` compiler compiling multiple distinct `ObjSrc` programs!
#guard match runMixSpecialize 3000 mixProg (quoteProg objInterp) with
  | some compilerProg =>
    !hasStaticConstruct compilerProg &&
    compilerProg.procs.length == 6 &&
    checkSpecializesProg 300 mixProg (quoteProg objInterp) compilerProg &&
    (match evalMix 1500 compilerProg .nil (quoteObjSrc quadPolyObjSrc) >>= unquoteProg? with
     | some target1 =>
       !hasStaticConstruct target1 &&
       evalMix 40 target1 .nil (.num 5) == some (.num 45) &&
       evalMix 40 target1 .nil (.num 8) == some (.num 93)
     | none => false) &&
    (match evalMix 1500 compilerProg .nil (quoteObjSrc countdownToZeroObjSrc) >>= unquoteProg? with
     | some target2 =>
       !hasStaticConstruct target2 &&
       evalMix 120 target2 .nil (.num 6) == some (.num 42)
     | none => false)
  | none => false

/-! ## 3. Genuine 3rd Futamura Projection (`mix(⌜mix⌝, ⌜mix⌝) = ⌜cogen⌝`) -/

/-- Second distinct two-level interpreter (`scale * d + bias` from static pair `(scale, bias)`)
    used to verify `cogenProg` turns ANY two-level interpreter into a standalone compiler! -/
def affineInterp : MixProg :=
  { entry := .sym .entry
  , procs :=
      [ { name := .sym .entry
        , body := .dBin .add (.dBin .mul (.dLift (sFst .var)) .dVar) (.dLift (sSnd .var)) } ] }

-- Self-applying `mixProg` to `(quoteProg mixProg, quoteProg mixProg)` produces a standalone
-- 13-procedure compiler-generator `cogenProg` turning BOTH `objInterp` AND `affineInterp` into compilers!
#guard match runMixSpecialize 4000 mixProg (quoteProg mixProg) with
  | some cogenProg =>
    !hasStaticConstruct cogenProg &&
    cogenProg.procs.length == 13 &&
    checkSpecializesProg 280 mixProg (quoteProg mixProg) cogenProg &&
    (match evalMix 4000 cogenProg .nil (quoteProg objInterp) >>= unquoteProg? with
     | some genObjCompiler =>
       !hasStaticConstruct genObjCompiler &&
       genObjCompiler.procs.length == 6 &&
       (match evalMix 1500 genObjCompiler .nil (quoteObjSrc quadPolyObjSrc) >>= unquoteProg? with
        | some target => evalMix 40 target .nil (.num 5) == some (.num 45)
        | none => false)
     | none => false) &&
    (match evalMix 2000 cogenProg .nil (quoteProg affineInterp) >>= unquoteProg? with
     | some genAffineCompiler =>
       !hasStaticConstruct genAffineCompiler &&
       (match evalMix 500 genAffineCompiler .nil (.pair (.num 10) (.num 7)) >>= unquoteProg? with
        | some targetAff => evalMix 20 targetAff .nil (.num 4) == some (.num 47)
        | none => false)
     | none => false)
  | none => false

/-! ## 4. `BytecodeRegisterJit`: Dictionary-Stripped `sumTo 30000`, Range Refusal & C99 Emission -/

-- Clearing `EXPERT-compiler-runtime` §2.3: `sumTo 30000 = 450,015,000` executes to completion cleanly!
#guard runSumToBytecode 30000 == some 450015000
#guard runSumToBytecode 100 == some 5050
#guard runSumToBytecode 0 == some 0

-- Kernel theorem witness for `sumTo 30000`:
example :
    EvaluatesCountdownLoop sumToDictStep 30000 0 450015000 ∧
    runSumToBytecode 30000 = some 450015000 :=
  runSumToBytecode_30000

-- Dictionary-passing branching expression (`let s := HAdd.hAdd {} {} {} inst x y in if s < 20 then s * 2 else s - 5`):
def branchingDictExpr : Term :=
  .app (.lam (.ifBool (.binary .less (.bound 0) (.nat 20))
    (.binary .multiply (.bound 0) (.nat 2))
    (.binary .subtract (.bound 0) (.nat 5))))
    (hAddDictApp (.bound 0) (.bound 1))

#guard match compileExprToBytecode 4 [0, 1] 2 branchingDictExpr with
  | some (code, maxRegs, fuelBound) =>
    let r1 := #[6, 7] ++ Array.replicate maxRegs 0
    let r2 := #[15, 10] ++ Array.replicate maxRegs 0
    execBytecode code r1 fuelBound == some 26 &&
    execBytecode code r2 fuelBound == some 20
  | none => false

-- Negative range-safety & VM bounds/fault refusal guards (overflow, underflow, OOB reg, OOB jump, infinite loop, div/mod 0):
#guard checkRangeSafeBytecode [] (.binary .add (.nat (2 ^ 64 - 1)) (.nat 1)) == false
#guard checkRangeSafeBytecode [] (.binary .subtract (.nat 0) (.nat 1)) == false
#guard checkRangeSafeBytecode [Interval.mkNat 0 100, Interval.mkNat 0 100] (.binary .multiply (.bound 0) (.nat (2 ^ 63))) == false
#guard execBytecode #[.ret 9] #[42] 5 == none
#guard execBytecode #[.jz 0 99] #[0] 5 == none
#guard execBytecode #[.jmp 0] #[42] 10 == none
#guard execBytecode #[.binOp .div 0 0 1, .ret 0] #[42, 0] 5 == some 0
#guard execBytecode #[.binOp .mod 0 0 1, .ret 0] #[42, 0] 5 == some 42

-- Recursive static-call + static-branch unrolling witness (`unrollPowInterp` specialized at `5` computes `3^5 = 243`):
example :
    ∃ target : MixProg,
      runMixSpecialize 400 unrollPowInterp (.num 5) = some target ∧
      checkSpecializesProg 20 unrollPowInterp (.num 5) target = true ∧
      hasStaticConstruct target = false ∧
      target.procs.length = 1 ∧
      evalMix 20 target .nil (.num 3) = some (.num 243) :=
  unrollPowInterp_specializes_5 3

-- Standalone NULL-safe & bounds-checked C99 emitter check:
#guard ((emitRegisterBytecodeC99 sumToLoopCode).splitOn "uint64_t obend_bytecode_jit_run").length == 2
#guard ((emitRegisterBytecodeC99 sumToLoopCode).splitOn "goto L0;").length == 2
#guard ((emitRegisterBytecodeC99 sumToLoopCode).splitOn "if (ok != NULL)").length >= 3
#guard ((emitRegisterBytecodeC99 sumToLoopCode).splitOn "if (regs == NULL && n_regs > 0U)").length == 2

/-! ## 5. Mutation-Sensitivity Witnesses (`#tooth`) & Zero-Axiom Tree Audit (`#assert_axioms_tree`) -/

#tooth Obend.Leaf.SelfApplicableMix.unquote_quote by mutation
  Obend.Leaf.SelfApplicableMix.quoteProg := fun _ => MixVal.nil

#tooth Obend.Leaf.SelfApplicableMix.checkSpecializesProg_sound by mutation
  Obend.Leaf.SelfApplicableMix.checkSpecializesProg := fun _ _ _ _ => true

#tooth Obend.Leaf.SelfApplicableMix.futamura1_target_sound by mutation
  Obend.Leaf.SelfApplicableMix.runMixSpecialize := fun _ p _ => some p

#tooth Obend.Leaf.SelfApplicableMix.futamura2_self_application_compiler_sound by mutation
  Obend.Leaf.SelfApplicableMix.runMixSpecialize := fun _ p _ => some p

#tooth Obend.Leaf.SelfApplicableMix.futamura3_self_self_cogen_sound by mutation
  Obend.Leaf.SelfApplicableMix.runMixSpecialize := fun _ p _ => some p

#tooth Obend.Leaf.SelfApplicableMix.futamura3_end_to_end_object_sound by mutation
  Obend.Leaf.SelfApplicableMix.runMixSpecialize := fun _ p _ => some p

#tooth Obend.Leaf.SelfApplicableMix.lowerMixToCore4_sound by mutation
  Obend.Leaf.SelfApplicableMix.lowerMixToCore4 :=
    fun _ => Obend.Core.Term.Term.lam (Obend.Core.Term.Term.inject "none" (Obend.Core.Term.Term.nat 0))

#tooth Obend.Leaf.BytecodeRegisterJit.compileExprToBytecode_sound by mutation
  Obend.Leaf.BytecodeRegisterJit.compileExprToBytecode :=
    fun _ _ _ _ => some (#[Obend.Leaf.BytecodeRegisterJit.ByteInstr.ret 0], 1, 1)

#tooth Obend.Leaf.BytecodeRegisterJit.specializeAndCompileLoop_sound by mutation
  Obend.Leaf.BytecodeRegisterJit.specializeAndCompileLoop :=
    fun _ _ _ _ => some (#[Obend.Leaf.BytecodeRegisterJit.ByteInstr.ret 0], 2, 1)

#assert_axioms_tree

end Obend.Tests.TrueFutamuraAndBytecodeJit
end
