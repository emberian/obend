module
-- Expose imported proof bodies to the package axiom audit.
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
import all Obend.Crypto.Multilinear
import all Obend.Crypto.Sumcheck
import all Obend.Crypto.Transcript
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
import all Obend.Judge.Class
import all Obend.Judge.Computational
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
import all Obend.Leaf.UpTo
import all Obend.Logic.Claim
import all Obend.Logic.LateBinding
import all Obend.Slot
import all Obend.Slot.Core4
import all Obend.Slot.Protocol
import all Obend.Spec.C4
import all Obend.Spec.Proofs.C4
import all Obend.SymbolicZk.CompileToPiop
import all Obend.SymbolicZk.CompileToPiopCore
import all Obend.SymbolicZk.SkolemChaseCore
import all Obend.Tactic.Cases
import all Obend.Tactic.MonadicReduction
import all Obend.Tactic.Tooth
public import Obend.SymbolicZk.CompileToPiopCore
public import Obend.SymbolicZk.CompileToPiop
public import Obend.AssertAxioms
public import Obend.Tactic.Tooth

/-!
# `tests/metasystem/PiopWeldTest.lean` — End-to-End Verification & `#tooth` Suite for `SymbolicZk → PIOP`

Exercises both modules of the `Lookup + LinMem + Before → Multilinear PIOP / Sumcheck` weld
(`Obend.SymbolicZk.CompileToPiopCore` and `Obend.SymbolicZk.CompileToPiop`):
1. `Goldilocks` constructive Proth primality (`goldilocksPrime_isPrime`), `LawfulIntegralDomain`,
   and Bézout `LawfulField` inverse (`Goldilocks.inv`).
2. `Before` range-safe bit-slack arithmetization (`beforePolyConstraint_iff_lt`,
   `checkBeforePolyArray_sound`) and 63-bit mod-$p$ wraparound refutation (`beforeWraparound_at_63bits`).
3. `LinMem` characteristic-product multiset weld (`charPoly_eq_iff_perm`,
   `linmemPolyIdentity_implies_perm`) and univariate Schwartz–Zippel root bound.
4. `Lookup` LogUp rational-fraction & cleared-polynomial weld (`logUpFrac_iff_clearedPoly`,
   `logUpIdentity_complete`, `logUpIdentity_implies_lookup`).
5. `eqPoly`-weighted hypercube batching, multilinear Schwartz–Zippel grid bound
   (`mle_schwartzZippel_grid_bound`), and `Sumcheck` compiler
   (`compileSymbolicTraceToSumcheck_complete` & `compileSymbolicTraceToSumcheck_sound`).
6. Five `#tooth` mutation kills + `#assert_axioms_tree` + strict 0-sorry / 0-native / 0-closed-theorem census.
-/

public section
namespace Obend.Tests.PiopWeldTest

open Obend.Apps.ZkNtt (goldilocksPrime)
open Obend.Crypto
open Obend.Digest.Cshake256
open Obend.SymbolicZk.CompileToPiop

set_option autoImplicit false

-- ============================================================================
-- 1. Field Inverse & `Before` RangeSafe Arithmetization + Wraparound Guard
-- ============================================================================

def g7 : Goldilocks := Goldilocks.ofNat 7
def g42 : Goldilocks := Goldilocks.ofNat 42

#guard Goldilocks.mul g7 (Obend.SymbolicZk.CompileToPiop.Goldilocks.inv g7) == Goldilocks.one
#guard Goldilocks.mul g42 (Obend.SymbolicZk.CompileToPiop.Goldilocks.inv g42) == Goldilocks.one
#guard Obend.SymbolicZk.CompileToPiop.Goldilocks.inv Goldilocks.zero == Goldilocks.zero

-- Width guard: 62 bits is safe (2 * 2^62 = 2^63 < p), 63 bits is unsafe (2 * 2^63 = 2^64 > p)
#guard beforeWidthSafe 32 == true
#guard beforeWidthSafe 62 == true
#guard beforeWidthSafe 63 == false

def validBefore : BeforeConstraint := ⟨19, 42, 16⟩
def equalBefore : BeforeConstraint := ⟨42, 42, 16⟩
def reversedBefore : BeforeConstraint := ⟨50, 19, 16⟩

#guard checkBeforePolyArray validBefore (compileBeforeWitness validBefore) == true
#guard checkBeforePolyArray equalBefore (compileBeforeWitness equalBefore) == false
#guard checkBeforePolyArray reversedBefore (compileBeforeWitness reversedBefore) == false

-- Concrete 63-bit mod-p wraparound forgery: a = p - 2^63 < 2^63, b = 0, yet slack residual vanishes!
def wrapLhs63 : Nat := goldilocksPrime - 2 ^ 63
def forgedBits63 : Array Goldilocks := (compileBeforeBits 63 (goldilocksPrime - wrapLhs63 - 1)).toArray

#guard forgedBits63.size == 63
#guard forgedBits63.all (fun b => decide (boolBitResidual b == CommRingOps.zero))
#guard beforeSlackResidualArray wrapLhs63 0 forgedBits63 == CommRingOps.zero
#guard checkBeforePolyArray ⟨wrapLhs63, 0, 63⟩ forgedBits63 == false

-- ============================================================================
-- 2. `LinMem` Characteristic Polynomial & `Lookup` LogUp Welds
-- ============================================================================

def linInit : Array Goldilocks := #[Goldilocks.ofNat 11, Goldilocks.ofNat 22]
def linProd : Array Goldilocks := #[Goldilocks.ofNat 33, Goldilocks.ofNat 11]
def linCons : Array Goldilocks := #[Goldilocks.ofNat 22, Goldilocks.ofNat 11]
def linFinal : Array Goldilocks := #[Goldilocks.ofNat 11, Goldilocks.ofNat 33]
def linForgedFinal : Array Goldilocks := #[Goldilocks.ofNat 11, Goldilocks.ofNat 44]

def chalLin : Goldilocks := Goldilocks.ofNat 9001

#guard charPolyEvalArray (linInit ++ linProd) chalLin ==
       charPolyEvalArray (linCons ++ linFinal) chalLin
#guard charPolyEvalArray (linInit ++ linProd) chalLin !=
       charPolyEvalArray (linCons ++ linForgedFinal) chalLin

def lupTable : Array Goldilocks := #[Goldilocks.ofNat 100, Goldilocks.ofNat 200, Goldilocks.ofNat 300]
def lupQueries : Array Goldilocks :=
  #[Goldilocks.ofNat 200, Goldilocks.ofNat 100, Goldilocks.ofNat 200, Goldilocks.ofNat 200]
def lupMultsHonest : Array Nat := #[1, 3, 0]
def lupMultsForged : Array Nat := #[2, 2, 0]
def chalLup : Goldilocks := Goldilocks.ofNat 7777

-- Both fractional LogUp sum (using Goldilocks.inv) and inverse-free cleared-polynomial check hold!
#guard logUpTableFracSum chalLup (lupTable.toList.zip lupMultsHonest.toList) ==
       logUpQueryFracSum chalLup lupQueries.toList

def honestTableEval := logUpTableEvalArray lupTable lupMultsHonest chalLup
def forgedTableEval := logUpTableEvalArray lupTable lupMultsForged chalLup
def queryEval := logUpQueryEvalArray lupQueries chalLup

#guard CommRingOps.mul honestTableEval.1 queryEval.2 == CommRingOps.mul queryEval.1 honestTableEval.2
#guard CommRingOps.mul forgedTableEval.1 queryEval.2 != CommRingOps.mul queryEval.1 forgedTableEval.2

-- ============================================================================
-- 3. End-to-End `SymbolicZkStmt` → `eqPoly` Batching → `Sumcheck` Prover/Verifier
-- ============================================================================

def sampleStmt : SymbolicZkStmt :=
  { beforeConstraints := #[⟨5, 12, 4⟩, ⟨0, 3, 2⟩]
    linmemInit := linInit
    linmemProd := linProd
    linmemCons := linCons
    linmemFinal := linFinal
    lookupTable := lupTable
    lookupQueries := lupQueries
    numVars := 4 }

def sampleWit : SymbolicZkWitness :=
  { beforeBits := sampleStmt.beforeConstraints.map compileBeforeWitness
    lookupMults := lupMultsHonest }

def tau4 : List Goldilocks :=
  [Goldilocks.ofNat 13, Goldilocks.ofNat 29, Goldilocks.ofNat 37, Goldilocks.ofNat 53]

def boundPiopTr : Transcript .instanceBound :=
  (bindInstance ByteArray.empty
    (bindRelation "obend.symboliczk.piop/v1"
      (Native.bytesOfList [0xca, 0xfe])
      (Native.bytesOfList [0x01, 0x02])
      (Transcript.newUnseeded (Native.bytesOfList [0x42])))).transcript

#guard stmtWitnessStructValid sampleStmt sampleWit == true
#guard (symbolicResidualVector sampleStmt sampleWit chalLin chalLup).all (fun r => r == CommRingOps.zero)

def batchedTbl := batchedSymbolicPiopTable sampleStmt sampleWit chalLin chalLup tau4
def proverOut := honestSumcheckProver sampleStmt.numVars batchedTbl boundPiopTr

#guard match verifySumcheck 1 sampleStmt.numVars CommRingOps.zero proverOut.1 boundPiopTr with
       | some (claim, _) => claim.expectedVal == mleEval batchedTbl claim.point
       | none => false

-- Forged `Before` ordering (12 < 5 is false!) yields non-zero residual and non-zero batched sum
def invalidStmt : SymbolicZkStmt :=
  { sampleStmt with beforeConstraints := #[⟨12, 5, 4⟩, ⟨0, 3, 2⟩] }
def invalidTbl := batchedSymbolicPiopTable invalidStmt sampleWit chalLin chalLup tau4
#guard hypercubeSum invalidStmt.numVars invalidTbl != CommRingOps.zero

-- End-to-end bound `verifySymbolicSumcheck` check: accepts authentic `symbolicWitnessCommit`, rejects forged `witComm`
def sampleSeed : Transcript .relationBound :=
  bindRelation "obend.symboliczK.piop.test/v1" ByteArray.empty ByteArray.empty
    (Transcript.newUnseeded (Native.bytesOfList [0x77]))
def sampleWitComm : ByteArray := symbolicWitnessCommit sampleWit
def sampleChals := symbolicChallenges sampleStmt sampleWitComm sampleSeed
def sampleBoundTbl := batchedSymbolicPiopTable sampleStmt sampleWit sampleChals.1 sampleChals.2.1 sampleChals.2.2.1
def sampleBoundProver := honestSumcheckProver sampleStmt.numVars sampleBoundTbl sampleChals.2.2.2

#guard (verifySymbolicSumcheck sampleStmt sampleWit sampleWitComm 1 sampleBoundProver.1 sampleSeed).isSome
#guard (verifySymbolicSumcheck sampleStmt sampleWit ByteArray.empty 1 sampleBoundProver.1 sampleSeed).isNone

-- Regression guard for P0 #1: all-zero round polynomials on false witness (`invalidStmt`: `12 < 5`) are refused!
def allZeroRoundForgery : List (RoundPoly Goldilocks) :=
  List.replicate invalidStmt.numVars ⟨[]⟩

#guard (verifySymbolicSumcheck invalidStmt sampleWit sampleWitComm 1 allZeroRoundForgery sampleSeed).isNone

-- ============================================================================
-- 4. `#tooth` Mutation Kills Across All 3 Primitives & Sumcheck Weld (7 Kills)
-- ============================================================================

-- Kill 1: Dropping the `RangeSafe` width guard (`2 * 2^w ≤ p`) allows 63-bit mod-p wraparound
-- and breaks `checkBeforePolyArray_sound`!
#tooth Obend.SymbolicZk.CompileToPiop.checkBeforePolyArray_sound by mutation
  Obend.SymbolicZk.CompileToPiop.beforeWidthSafe := fun _ => true

-- Kill 2: Dropping bit booleanity (`bit * (bit - 1) = 0`) allows arbitrary field slack
-- and breaks `beforePolyConstraint_iff_lt`!
#tooth Obend.SymbolicZk.CompileToPiop.beforePolyConstraint_iff_lt by mutation
  Obend.SymbolicZk.CompileToPiop.boolBitResidual := fun _ => CommRingOps.zero

-- Kill 3: Ignoring the linear factor `(X - a)` in `mulLinFactor` breaks
-- `linmemPolyIdentity_implies_perm`!
#tooth Obend.SymbolicZk.CompileToPiop.linmemPolyIdentity_implies_perm by mutation
  Obend.SymbolicZk.CompileToPiop.mulLinFactor := fun _ p => p

-- Kill 4: Ignoring witness multiplicities `m_i` in LogUp polynomial scaling breaks
-- `logUpIdentity_implies_lookup`!
#tooth Obend.SymbolicZk.CompileToPiop.logUpIdentity_implies_lookup by mutation
  Obend.SymbolicZk.CompileToPiop.polyScale := fun _ p => p

-- Kill 5: Dropping compiled symbolic residuals in `symbolicResidualVector` breaks
-- `compileSymbolicTraceToSumcheck_sound`!
#tooth Obend.SymbolicZk.CompileToPiop.compileSymbolicTraceToSumcheck_sound by mutation
  Obend.SymbolicZk.CompileToPiop.symbolicResidualVector := fun _ _ _ _ => []

-- Kill 6: Skipping `witComm = symbolicWitnessCommit w` check in `verifySymbolicSumcheck`
-- allows post-challenge witness grinding and breaks `compileSymbolicTraceToSumcheck_sound`!
#tooth Obend.SymbolicZk.CompileToPiop.compileSymbolicTraceToSumcheck_sound by mutation
  Obend.SymbolicZk.CompileToPiop.verifySymbolicSumcheck := fun s w witComm maxDeg rounds seed =>
    if stmtWitnessStructValid s w then
      let chals := symbolicChallenges s witComm seed
      let tbl := batchedSymbolicPiopTable s w chals.1 chals.2.1 chals.2.2.1
      match verifySumcheck maxDeg s.numVars CommRingOps.zero rounds chals.2.2.2 with
      | some (claim, trFinal) =>
        if decide (claim.expectedVal = mleEval tbl claim.point) then some (claim, trFinal) else none
      | none => none
    else none

-- Kill 7: Skipping the final `claim.expectedVal = mleEval tbl claim.point` check in
-- `verifySymbolicSumcheck` admits all-zero round-polynomial forgeries and breaks
-- `compileSymbolicTraceToSumcheck_sound`!
#tooth Obend.SymbolicZk.CompileToPiop.compileSymbolicTraceToSumcheck_sound by mutation
  Obend.SymbolicZk.CompileToPiop.verifySymbolicSumcheck := fun s w witComm maxDeg rounds seed =>
    if stmtWitnessStructValid s w && decide (witComm = symbolicWitnessCommit w) then
      verifySumcheck maxDeg s.numVars CommRingOps.zero rounds (symbolicChallenges s witComm seed).2.2.2
    else none

-- ============================================================================
-- 5. `#assert_axioms_tree`, Strict Axiom Purity & Zero-Closed-Theorem Audit
-- ============================================================================

#assert_axioms_tree

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let targetMods : List Name :=
    [`Obend.SymbolicZk.CompileToPiopCore, `Obend.SymbolicZk.CompileToPiop]
  let mut checkedCount : Nat := 0
  for (cName, _) in env.constants.map₁.toList do
    let some modIdx := env.getModuleIdxFor? cName | continue
    let some modName := env.header.moduleNames[modIdx.toNat]? | continue
    unless targetMods.contains modName do continue
    checkedCount := checkedCount + 1
    let axs ← liftCoreM <| collectAxioms cName
    for ax in axs do
      unless Obend.AssertAxioms.standard.contains ax do
        throwError m!"Non-standard or native_decide axiom {ax} found in {cName}"
  if checkedCount == 0 then
    throwError "Zero constants inspected in Obend.SymbolicZk!"

  let rows ← liftTermElabM Obend.AssertAxioms.theoremCensus
  let mut foundDir := false
  for (dir, universal, closed) in rows do
    if dir == `Obend.SymbolicZk then
      foundDir := true
      let userClosed := closed.filter fun n =>
        n.components.getLast? != some `sizeOf_spec &&
        match env.getModuleIdxFor? n with
        | none => false
        | some i => (env.header.moduleNames[i.toNat]?).any targetMods.contains
      unless userClosed.isEmpty do
        throwError m!"The two PIOP modules have closed theorems (must be 0): {userClosed.toList}"
      if universal == 0 then
        throwError "Obend.SymbolicZk reported 0 universal theorems"
      logInfo m!"PIOP modules clean: {checkedCount} constants (0 sorryAx, 0 custom axioms, 0 native_decide), {universal} universal theorems, 0 closed theorems"
  unless foundDir do
    throwError "Obend.SymbolicZk missing from theoremCensus!"

end Obend.Tests.PiopWeldTest
