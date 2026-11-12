import Obend.Crypto
import Obend.AssertAxioms
import Obend.Tactic.Tooth

/-!
# `tests/metasystem/ModularCryptoSpineTest.lean` — End-to-End Verification & `#tooth` Probe Suite (`G3`)

Exercises all 6 modules of Obend's Dual-Track Post-Quantum Cryptographic Spine (`Obend.Crypto`):
1. `Obend.Crypto.Transcript`:
   - Fenzi (`ePrint 2026/1838`) `TranscriptPhase` gating (`bindRelation` sole entry to `.relationBound`),
   - Full 32-byte (`256`-bit) `cSHAKE256` sponge state (`state.size = 32`),
   - Unconditional LEB128 domain-frame injectivity (`encodeFrame_injective`, `bindRelation_injective_prefix`).
2. `Obend.Crypto.Multilinear` & `Obend.Crypto.Sumcheck`:
   - Hardware-matched `Goldilocks` ($p = 2^{64} - 2^{32} + 1$) and 128-bit `GoldilocksExt2` ($\mathbb{F}_p[u]/(u^2 - 7)$),
   - `foldFirstVar`, `mleEval_foldFirstVar`, `honestSumcheckProver`, `verifySumcheck`, and LFKN soundness.
3. `Obend.Crypto.PCS`:
   - Oct 2026 Binary RS Proximity-Gap Guard (`ePrint 2026/2424`: `ValidProximityConfig` locks `.binaryAdditive` to `.uniqueDecodingRadius`),
   - 32-byte `canopyMerklePCS` over `Goldilocks` (`verifyMerklePath_completeness`, `merkle_double_open_yields_hash_collision`).
4. `Obend.Crypto.DualSpine`:
   - `PikkuFold` (`ePrint 2026/1809`) ternary $\{-1,0,1\}$ projection norm guard (`normInf_ternaryProj_le`),
   - `ajtaiCommit_add` homomorphism, `ajtaiLatticePCS`, `Akita` (`2026/1983`) $O(\text{rows})$ `ajtaiSparseOneHot`,
   - Cross-assumption `DualPCS P₁ P₂` (`dualPCS_completeness`, `dualPCS_sound_of_either`, `verifyDualSumcheckPIOP`).
5. `Obend.Crypto.SameOpening`:
   - `Choe–Kang–Stehlé` (`ePrint 2026/2546`) mandatory threshold decryption smudging guard (`SmudgeSafe`),
   - `BitZ` (`ePrint 2026/2141`) free $B$-bit range bound (`bitsToNat_lt_two_pow`),
   - Lawful `privateConvexSameOpeningJudge` (`Obend.Judge`) certifying exact zero-gap KKT welfare optimality.
6. `#tooth` mutation probes across all 6 modules + `#assert_axioms_tree` + 0-closed-theorem census check.
-/

namespace Obend.Tests.ModularCryptoSpineTest

open Obend.Crypto
open Obend.Digest.Cshake256
open Obend.Judge
open Obend.Ledger

-- ============================================================================
-- 1. Fenzi-Safe 256-Bit Transcript (`Obend.Crypto.Transcript`)
-- ============================================================================

def seedBytesA : ByteArray := Native.bytesOfList [0x01, 0x02, 0x03, 0x04]
def relBytesA  : ByteArray := Native.bytesOfList [0x10, 0x20, 0x30]
def relBytesB  : ByteArray := Native.bytesOfList [0x10, 0x20, 0x31]
def ioBytesA   : ByteArray := Native.bytesOfList [0xaa, 0xbb]

def unseededTr : Transcript .unseeded := Transcript.newUnseeded seedBytesA
def boundTrA   : Transcript .relationBound := bindRelation "obend.piop/v1" relBytesA ioBytesA unseededTr
def boundTrB   : Transcript .relationBound := bindRelation "obend.piop/v1" relBytesB ioBytesA unseededTr

-- Full 32-byte (256-bit) sponge state invariant (defeats 1-felt 15.5-bit truncation)
#guard unseededTr.state.size == 32
#guard boundTrA.state.size == 32
#guard boundTrA != boundTrB

-- Deterministic challenge squeezing in 256-bit bytes, Goldilocks, and 128-bit GoldilocksExt2
def squeezed256 := squeezeChallenge256 boundTrA
#guard squeezed256.1.val.size == 32
#guard squeezed256.2.state.size == 32
#guard squeezed256.1.val != squeezed256.2.state

def squeezedExt2A := squeezeGoldilocksExt2 boundTrA
def squeezedExt2B := squeezeGoldilocksExt2 boundTrB
#guard squeezedExt2A.1 != squeezedExt2B.1

-- Mutation probe: raw concatenation without LEB128 length prefixes breaks `encodeFrame_injective`
#tooth Obend.Crypto.encodeFrame_injective by mutation
  Obend.Crypto.encodeFrameList := fun a b c => a ++ b ++ c

-- Mutation probe: ignoring `canonicalRelBytes` (Fenzi `2026/1838` delayed/omitted relation binding!)
-- is caught immediately by `bindRelation_injective_prefix`
#tooth Obend.Crypto.bindRelation_injective_prefix by mutation
  Obend.Crypto.canonicalPrefix := fun pid _ io =>
    encodeFrame (encodeStringCodepoints pid) ByteArray.empty io

-- ============================================================================
-- 2. Polymorphic Rings, `Goldilocks` / `GoldilocksExt2` & `Sumcheck`
-- ============================================================================

def sampleTable3 : List Goldilocks :=
  [Goldilocks.ofNat 3, Goldilocks.ofNat 7, Goldilocks.ofNat 11, Goldilocks.ofNat 5,
   Goldilocks.ofNat 13, Goldilocks.ofNat 2, Goldilocks.ofNat 19, Goldilocks.ofNat 23]

def challengePt3 : List Goldilocks :=
  [Goldilocks.ofNat 17, Goldilocks.ofNat 29, Goldilocks.ofNat 41]

-- Hardware butterfly fold agrees identically with full multilinear evaluation
#guard mleEval (foldFirstVar sampleTable3 (Goldilocks.ofNat 17))
         [Goldilocks.ofNat 29, Goldilocks.ofNat 41] ==
       mleEval sampleTable3 challengePt3

-- GoldilocksExt2 non-residue u^2 = 7 check
def uUnit : GoldilocksExt2 := ⟨Goldilocks.zero, Goldilocks.one⟩
#guard CommRingOps.mul uUnit uUnit == GoldilocksExt2.ofBase (Goldilocks.ofNat 7)

-- Honest Sumcheck over Goldilocks (v = 3, sum = 3+7+11+5+13+2+19+23 = 83)
def sumClaim3 : Goldilocks := hypercubeSum 3 sampleTable3
#guard sumClaim3 == Goldilocks.ofNat 83

def proverRun3 := honestSumcheckProver 3 sampleTable3 boundTrA
#guard match verifySumcheck 1 3 sumClaim3 proverRun3.1 boundTrA with
       | some (claim, _) =>
         claim == proverRun3.2.1 &&
         claim.expectedVal == mleEval sampleTable3 claim.point
       | none => false

-- Forged hypercube sum (84 != 83) is rejected or produces a false final evaluation claim
#guard match verifySumcheck 1 3 (Goldilocks.ofNat 84) proverRun3.1 boundTrA with
       | none => true
       | some _ => false

-- Honest Sumcheck over 128-bit GoldilocksExt2 extension field
def sampleTableExt2 : List GoldilocksExt2 :=
  sampleTable3.map GoldilocksExt2.ofBase

def proverRunExt2 := honestSumcheckProver 3 sampleTableExt2 boundTrA
#guard match verifySumcheck 1 3 (hypercubeSum 3 sampleTableExt2) proverRunExt2.1 boundTrA with
       | some (claim, _) => claim.expectedVal == mleEval sampleTableExt2 claim.point
       | none => false

-- Mutation probes on multilinear folding and Sumcheck soundness/completeness
#tooth Obend.Crypto.mleEval_foldFirstVar by mutation
  Obend.Crypto.mleEval := fun {R} [CommRingOps R] _ pt =>
    match pt with
    | [] => CommRingOps.one
    | r :: _ => r

#tooth Obend.Crypto.verifySumcheckRound_complete by mutation
  Obend.Crypto.verifySumcheckRound := fun {_R} [_] [_] [_] _ _ _ _ => none

#tooth Obend.Crypto.verifySumcheck_round_sound by mutation
  Obend.Crypto.verifySumcheckRound := fun {R} [CommRingOps R] [_] [TranscriptChallenge R] _ _ p tr =>
    let (r, tr') := absorbAndSqueezeRound p tr
    some (r, p.eval r, tr')

-- ============================================================================
-- 3. Proximity-Gap Guard (`2026/2424`) & 32-Byte `CanopyMerklePCS` (`Obend.Crypto.PCS`)
-- ============================================================================

-- Oct 2026 Binary RS Proximity-Gap Guard (`Dao–Kominers–Thaler–Zheng, ePrint 2026/2424`)
#guard checkProximityConfig .binaryAdditive .uniqueDecodingRadius == true
#guard checkProximityConfig .binaryAdditive .johnsonBound == false
#guard checkProximityConfig .binaryAdditive .capacityBound == false
#guard checkProximityConfig .primeField .johnsonBound == true
#guard checkProximityConfig .primeField .capacityBound == true

#tooth Obend.Crypto.checkProximityConfig_iff by mutation
  Obend.Crypto.checkProximityConfig := fun _ _ => true

-- Concrete 32-byte CanopyMerklePCS commit, open, and verify
def canopyComm3 : CanopyCommitment :=
  (canopyMerklePCS).commit () 3 sampleTable3

#guard canopyComm3.root.bytes.size == 32

def canopyClaim3 : EvalClaim Goldilocks 3 :=
  ⟨challengePt3, rfl, mleEval sampleTable3 challengePt3⟩

def canopyOpen3 :=
  (canopyMerklePCS).openEval () 3 sampleTable3 canopyClaim3 boundTrA

#guard ((canopyMerklePCS).verifyEval () 3 canopyComm3 canopyClaim3 canopyOpen3.1 boundTrA).1 == true

-- Tampered expected evaluation value is rejected by `canopyMerklePCS`
def badCanopyClaim3 : EvalClaim Goldilocks 3 :=
  ⟨challengePt3, rfl, Goldilocks.add canopyClaim3.expectedVal Goldilocks.one⟩

#guard ((canopyMerklePCS).verifyEval () 3 canopyComm3 badCanopyClaim3 canopyOpen3.1 boundTrA).1 == false

#tooth Obend.Crypto.verifyMerklePath_completeness by mutation
  Obend.Crypto.verifyMerklePath := fun _ _ _ _ _ _ => false

#tooth Obend.Crypto.merkle_double_open_yields_hash_collision by mutation
  Obend.Crypto.canopyVerifyEval := fun _ _ _ _ _ tr => (true, tr)

-- ============================================================================
-- 4. Lattice Ajtai, `PikkuFold` Ternary Guard, `Akita` One-Hot & `DualPCS`
-- ============================================================================

def ternaryMatrix : List (List TernaryCoeff) :=
  [[.one, .zero, .negOne, .one],
   [.negOne, .one, .zero, .negOne]]

def shortWitness : List Int := [12, -19, 25, -7]
#guard checkShortNorm 25 shortWitness == true
#guard checkShortNorm (3 * 25) (applyTernaryProj ternaryMatrix shortWitness) == true

#tooth Obend.Crypto.normInf_ternaryProj_le by mutation
  Obend.Crypto.applyTernaryProj := fun _ w => w.map (· * 1024 + [999999].headD 0)

def latticeParams : AjtaiParams where
  modulus := 65537
  modulus_pos := by decide
  matrix :=
    [ (List.range 32).map (fun j => ((3 * j + 5 : Nat) : Int))
    , (List.range 32).map (fun j => ((7 * j + 11 : Nat) : Int))
    , (List.range 32).map (fun j => ((13 * j + 2 : Nat) : Int))
    , (List.range 32).map (fun j => ((19 * j + 23 : Nat) : Int)) ]

-- Modular Ajtai additive homomorphism check
def vecW1 : List Int := [4, -9, 15, 22, -3, 8, 11, -6]
def vecW2 : List Int := [-7, 14, 2, -19, 5, -1, 9, 12]
#guard ajtaiCommit latticeParams (vecAdd vecW1 vecW2) ==
       vecAddMod (latticeParams.modulus : Int)
         (ajtaiCommit latticeParams vecW1)
         (ajtaiCommit latticeParams vecW2)

-- `Akita` (`2026/1983`) / `Twist & Shout` O(rows) sparse 1-hot column lookup equals dense commit
#guard ajtaiCommitOneHotColumn latticeParams 3 5 ==
       ajtaiLatticeCommit latticeParams 3 (oneHotTable Goldilocks 3 5)
example : SparseOneHotCommit.commitOneHot (P := ajtaiLatticePCS latticeParams) () 3 5 =
    (ajtaiLatticePCS latticeParams).commit () 3 (oneHotTable Goldilocks 3 5) := rfl

-- Cross-Assumption `canopyAjtaiDualPCS` + `verifyDualSumcheckPIOP` end-to-end run
def dualScheme := canopyAjtaiDualPCS deployedCanopyHash32 latticeParams
def dualComm3 := dualScheme.commit ((), ()) 3 sampleTable3
def dualSumcheck := honestSumcheckProver 3 sampleTable3 boundTrA
def dualOpen3 := dualScheme.openEval ((), ()) 3 sampleTable3 dualSumcheck.2.1 dualSumcheck.2.2

#guard verifyDualSumcheckPIOP
         (canopyMerklePCS deployedCanopyHash32)
         (ajtaiLatticePCS latticeParams)
         ((), ()) 1 3 dualComm3 sumClaim3 dualSumcheck.1 dualOpen3.1 boundTrA == true

-- Single-track corruption test 1: corrupt ONLY the Canopy Merkle proof -> `DualPCS` rejects
def corruptedCanopyPrf : CanopyOpeningProof := ⟨[]⟩
#guard verifyDualSumcheckPIOP
         (canopyMerklePCS deployedCanopyHash32)
         (ajtaiLatticePCS latticeParams)
         ((), ()) 1 3 dualComm3 sumClaim3 dualSumcheck.1
         (corruptedCanopyPrf, dualOpen3.1.2) boundTrA == false

-- Single-track corruption test 2: corrupt ONLY the Ajtai short limbs -> `DualPCS` rejects
def corruptedAjtaiPrf : AjtaiOpeningProof := ⟨List.replicate 32 70000⟩
#guard verifyDualSumcheckPIOP
         (canopyMerklePCS deployedCanopyHash32)
         (ajtaiLatticePCS latticeParams)
         ((), ()) 1 3 dualComm3 sumClaim3 dualSumcheck.1
         (dualOpen3.1.1, corruptedAjtaiPrf) boundTrA == false

-- Mutation probe: weakening `DualPCS` conjunction `ok₁ && ok₂` to disjunction `ok₁ || ok₂`
-- breaks `dualPCS_sound_of_either`!
#tooth Obend.Crypto.dualPCS_sound_of_either by mutation
  Obend.Crypto.dualVerdictJoin := fun ok₁ ok₂ => ok₁ || ok₂

-- ============================================================================
-- 5. `SameOpening` Judge: Smudging (`2026/2546`), `BitZ` (`2026/2141`) & KKT
-- ============================================================================

-- BitZ boolean bit-packing: qty = 5 ([true, false, true]), bid total = 60 ([false, false, true, true, true, true]),
-- ask total = 40 ([false, false, false, true, false, true]), cleared at uniform price = 10
def bidBitsWitness : OrderBitWitness where
  qtyBits   := [true, false, true]                      -- 1 + 4 = 5 (< 2^8)
  totalBits := [false, false, true, true, true, true]   -- 4 + 8 + 16 + 32 = 60 (< 2^8)

def askBitsWitness : OrderBitWitness where
  qtyBits   := [true, false, true]                      -- 1 + 4 = 5 (< 2^8)
  totalBits := [false, false, false, true, false, true] -- 8 + 32 = 40 (< 2^8)

#guard bidBitsWitness.qty == 5
#guard bidBitsWitness.total == 60
#guard askBitsWitness.qty == 5
#guard askBitsWitness.total == 40

def committedBid : CommittedOrderSpec :=
  commitPrivateOrder latticeParams 101 .bid 8 bidBitsWitness

def committedAsk : CommittedOrderSpec :=
  commitPrivateOrder latticeParams 202 .ask 8 askBitsWitness

def clearingMarket : Market :=
  { currency := 1, goods := 2, epsilon := 0 }

-- SmudgeSafe with noiseBound = 16, secBits = 40, smudgeBound = 16 * 2^40
def smudgedQuery : SameOpeningQuery where
  market := clearingMarket
  ajtaiParams := latticeParams
  noiseBound := 16
  smudgeBound := 16 * (2 ^ 40)
  secBits := 40
  committedOrders := [committedBid, committedAsk]

-- Goods transfer: 5 units from ask (202) to bid (101); Currency transfer: 50 units from bid (101) to ask (202)
def optimalTransfers : List ResourcePosting :=
  [ { source := 202, destination := 101, asset := 2, amount := 5 }
  , { source := 101, destination := 202, asset := 1, amount := 50 } ]

-- KKT duals: price = 10, potentials = (0, 1) => diff = 1;
-- bid: diff + s₀ = 1 + 0 ≥ 1; ask: -diff + s₁ = -1 + 2 = 1 ≥ 1;
-- primalObjective = 5 + 5 = 10, dualObjective = 5*0 + 5*2 = 10 => zero duality gap!
def optimalKktCert : Certificate where
  price := 10
  potentials := (0, 1)
  slacks := [0, 2]

def honestSameOpeningCert : SameOpeningWitness where
  orderWitnesses := [bidBitsWitness, askBitsWitness]
  transfers := optimalTransfers
  kktCert := optimalKktCert

-- 5a. Honest smudged + DualPCS-bound + zero-gap KKT witness is ACCEPTED by `privateConvexSameOpeningJudge`
#guard verifySameOpening smudgedQuery honestSameOpeningCert == .ok
example (fuel : Nat) (q : SameOpeningQuery) (w : SameOpeningWitness) :
    privateConvexSameOpeningJudge.check fuel q w = verifySameOpening q w := rfl

-- 5b. Unsmudged collective decryption (`smudgeBound = 0`, Choe–Kang–Stehlé `2026/2546` attack!)
-- is REFUSED AND marked REFUTING (`refutes = true`)
def unsmudgedQuery : SameOpeningQuery :=
  { smudgedQuery with smudgeBound := 0 }

#guard verifySameOpening unsmudgedQuery honestSameOpeningCert == .refused .unsmudgedThresholdNoise []
#guard privateConvexSameOpeningJudge.refutes .unsmudgedThresholdNoise == true
example : privateConvexSameOpeningJudge.check 0 unsmudgedQuery honestSameOpeningCert =
    .refused .unsmudgedThresholdNoise [] := rfl

-- 5c. BitZ range width violation (`maxBits = 2` on qty = 5 needing 3 bits) is REFUSED
def narrowRangeBid : CommittedOrderSpec :=
  commitPrivateOrder latticeParams 101 .bid 2 bidBitsWitness

def narrowRangeQuery : SameOpeningQuery :=
  { smudgedQuery with committedOrders := [narrowRangeBid, committedAsk] }

#guard verifySameOpening narrowRangeQuery honestSameOpeningCert == .refused (.bitzRangeExceeded 0) []

-- 5d. `SameOpening` bait-and-switch (opening different private order bits to KKT than committed!) is REFUSED
def tamperedOrderWitness : SameOpeningWitness :=
  { honestSameOpeningCert with
    orderWitnesses := [{ bidBitsWitness with qtyBits := [false, true] }, askBitsWitness] }

#guard verifySameOpening smudgedQuery tamperedOrderWitness == .refused (.dualCommitmentMismatch 0) []

-- 5e. Non-zero primal-dual KKT gap (`slacks := [1, 2]` => dual = 15 != primal = 10) is REFUSED
def suboptimalKktWitness : SameOpeningWitness :=
  { honestSameOpeningCert with
    kktCert := { optimalKktCert with slacks := [1, 2] } }

#guard verifySameOpening smudgedQuery suboptimalKktWitness != .ok

-- Mutation probe: disabling the `2026/2546` smudging guard breaks `verifySameOpening_sound`!
#tooth Obend.Crypto.verifySameOpening_sound by mutation
  Obend.Crypto.checkSmudgeSafe := fun _ _ _ => true

-- Mutation probe: disabling the KKT zero primal-dual gap check breaks `verifySameOpening_sound`!
#tooth Obend.Crypto.verifySameOpening_sound by mutation
  Obend.Crypto.kktPrimalDualGapZero := fun _ _ _ _ => true

-- ============================================================================
-- 6. Axiom Census & Zero-Closed-Theorem Verification for `Obend.Crypto`
-- ============================================================================

#assert_axioms_tree

open Lean Elab Command in
run_cmd do
  let rows ← liftTermElabM Obend.AssertAxioms.theoremCensus
  for (dir, universal, closed) in rows do
    if dir == `Obend.Crypto then
      let userClosed := closed.filter fun n => n.components.getLast? != some `sizeOf_spec
      unless userClosed.isEmpty do
        throwError m!"Obend.Crypto has closed theorems (must be 0): {userClosed.toList}"
      if universal == 0 then
        throwError "Obend.Crypto reported 0 universal theorems"
      logInfo m!"Obend.Crypto census clean: {universal} universal theorems, 0 user closed theorems"

end Obend.Tests.ModularCryptoSpineTest
