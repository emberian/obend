import Obend.SymbolicZk.CompileToPiopCore
import Obend.SymbolicZk.CompileToPiop
import Obend.AssertAxioms
import Obend.Tactic.Tooth

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

#guard Goldilocks.mul g7 (Goldilocks.inv g7) == Goldilocks.one
#guard Goldilocks.mul g42 (Goldilocks.inv g42) == Goldilocks.one
#guard Goldilocks.inv Goldilocks.zero == Goldilocks.zero

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

def boundPiopTr : Transcript .relationBound :=
  bindRelation "obend.symboliczk.piop/v1"
    (Native.bytesOfList [0xca, 0xfe])
    (Native.bytesOfList [0x01, 0x02])
    (Transcript.newUnseeded (Native.bytesOfList [0x42]))

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

-- ============================================================================
-- 4. `#tooth` Mutation Kills Across All 3 Primitives & Sumcheck Weld (5 Kills)
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
      let userClosed := closed.filter fun n => n.components.getLast? != some `sizeOf_spec
      unless userClosed.isEmpty do
        throwError m!"Obend.SymbolicZk has closed theorems (must be 0): {userClosed.toList}"
      if universal == 0 then
        throwError "Obend.SymbolicZk reported 0 universal theorems"
      logInfo m!"Obend.SymbolicZk clean: {checkedCount} constants (0 sorryAx, 0 custom axioms, 0 native_decide), {universal} universal theorems, 0 closed theorems"
  unless foundDir do
    throwError "Obend.SymbolicZk missing from theoremCensus!"

end Obend.Tests.PiopWeldTest
