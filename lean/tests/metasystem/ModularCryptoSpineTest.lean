import Obend.Crypto
import Obend.AssertAxioms
import Obend.Tactic.Tooth

/-!
# `tests/metasystem/ModularCryptoSpineTest.lean` — End-to-End Verification & `#tooth` Probe Suite

Exercises all 6 modules of Obend's Dual-Track Post-Quantum Cryptographic Spine (`Obend.Crypto`):
1. `Obend.Crypto.Transcript`:
   - Fenzi (`ePrint 2026/1838`) `TranscriptPhase` gating (`.unseeded → .relationBound → .instanceBound`),
   - `BoundTranscript` instance binding (`bindInstance`), `CanonicalLift` (`< goldilocksPrime`),
   - Sign-injective `encodeSignedIntBytes` and point-injective `encodePointBytes`,
   - Full 32-byte (`256`-bit) `cSHAKE256` sponge state (`state.size = 32`).
2. `Obend.Crypto.Multilinear` & `Obend.Crypto.Sumcheck`:
   - `Goldilocks` ($p = 2^{64} - 2^{32} + 1$) Proth primality & 128-bit `GoldilocksExt2` ($\mathbb{F}_p[u]/(u^2 - 7)$)
     constructive field inversion (`GoldilocksExt2.inv`), `NoZeroDivisors`, and degree-$d$ root bound,
   - `foldFirstVar`, `honestSumcheckProver`, `honestBoundSumcheckProver`, `verifySumcheck`, `verifyBoundSumcheck`.
3. `Obend.Crypto.PCS`:
   - Oct 2026 Binary RS Proximity-Gap Guard (`ePrint 2026/2424`),
   - 32-byte `canopyMerklePCS` with `BoundedCollision` non-vacuity (`toyInjectiveHash32`) & point binding (`canopyOpenFrame`).
4. `Obend.Crypto.DualSpine`:
   - Exact-dimension `dotInt`, `NonPigeonholeSISParams`, inhabited `ModuleSISHard` (`inhabitedAjtaiParams_sisHard`),
   - Constructive `0 Classical` `Type`-valued witness extraction (`dualExtract`, `dualExtractBoth`),
   - Instance-bound `verifyDualSumcheckPIOP` (`bindDualSumcheckInstance`) & point-bound `ajtaiLatticeVerifyEval`.
5. `Obend.Crypto.SameOpening`:
   - `Choe–Kang–Stehlé` (`ePrint 2026/2546`) mandatory threshold decryption smudging guard (`SmudgeSafe`),
   - Canonical `< goldilocksPrime` field lift (`orderWitnessTable?_injective`, refusing `goldilocksPrime` wrap-around),
   - Explicit 128-bit `GoldilocksExt2` salt (`commitPrivateOrder`, defeating unsalted price dictionary lookup),
   - Lawful `privateConvexSameOpeningJudge` (`Obend.Judge`) certifying zero-gap KKT welfare optimality.
6. `#tooth` mutation probes across all repaired invariants + `0 Classical` check + 0-closed-theorem census.
-/

namespace Obend.Tests.ModularCryptoSpineTest

open Obend.Crypto
open Obend.Digest.Cshake256
open Obend.Apps.ZkNtt
open Obend.Judge
open Obend.Ledger

-- ============================================================================
-- 1. Fenzi-Safe 256-Bit `Transcript`, `BoundTranscript` & `CanonicalLift`
-- ============================================================================

def seedBytesA : ByteArray := Native.bytesOfList [0x01, 0x02, 0x03, 0x04]
def relBytesA  : ByteArray := Native.bytesOfList [0x10, 0x20, 0x30]
def relBytesB  : ByteArray := Native.bytesOfList [0x10, 0x20, 0x31]
def ioBytesA   : ByteArray := Native.bytesOfList [0xaa, 0xbb]

def unseededTr : Transcript .unseeded := Transcript.newUnseeded seedBytesA
def boundTrA   : Transcript .relationBound := bindRelation "obend.piop/v1" relBytesA ioBytesA unseededTr
def boundTrB   : Transcript .relationBound := bindRelation "obend.piop/v1" relBytesB ioBytesA unseededTr

-- Full 32-byte (256-bit) sponge state invariant
#guard unseededTr.state.size == 32
#guard boundTrA.state.size == 32
#guard boundTrA != boundTrB

-- Canonical `< goldilocksPrime` lift refuses `goldilocksPrime` (closing `0` vs `p` alias!)
#guard canonicalLift? 0 == some Goldilocks.zero
#guard canonicalLift? goldilocksPrime == none
#guard canonicalLift? (goldilocksPrime + 7) == none

-- Sign-injective `encodeSignedIntBytes` distinguishes `+1` and `-1`
#guard encodeSignedIntBytes [1, -5] != encodeSignedIntBytes [-1, 5]

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
#tooth Obend.Crypto.bindRelation_injective_prefix by mutation
  Obend.Crypto.canonicalPrefix := fun pid _ io =>
    encodeFrame (encodeStringCodepoints pid) ByteArray.empty io

-- Mutation probe: dropping integer sign (`z.natAbs`) breaks `encodeSignedIntBytes_injective`
#tooth Obend.Crypto.encodeSignedIntBytes_injective by mutation
  Obend.Crypto.encodeSignedInt := fun z => (0x00 : UInt8) :: leb128 z.natAbs

-- ============================================================================
-- 2. `Goldilocks` / 128-Bit `GoldilocksExt2` Field Inversion & `Sumcheck`
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

-- GoldilocksExt2 non-residue u^2 = 7 and 128-bit field inversion check
def uUnit : GoldilocksExt2 := ⟨Goldilocks.zero, Goldilocks.one⟩
def sampleExt2Elem : GoldilocksExt2 := ⟨Goldilocks.ofNat 123456789, Goldilocks.ofNat 987654321⟩
#guard CommRingOps.mul uUnit uUnit == GoldilocksExt2.ofBase (Goldilocks.ofNat 7)
#guard CommRingOps.mul sampleExt2Elem (GoldilocksExt2.inv sampleExt2Elem) == CommRingOps.one

-- Honest Sumcheck over Goldilocks (v = 3, sum = 3+7+11+5+13+2+19+23 = 83)
def sumClaim3 : Goldilocks := hypercubeSum 3 sampleTable3
#guard sumClaim3 == Goldilocks.ofNat 83

def proverRun3 := honestSumcheckProver 3 sampleTable3 boundTrA
#guard match verifySumcheck 1 3 sumClaim3 proverRun3.1 boundTrA with
       | some (claim, _) =>
         claim == proverRun3.2.1 &&
         claim.expectedVal == mleEval sampleTable3 claim.point
       | none => false

-- Forged hypercube sum (84 != 83) is rejected
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
  Obend.Crypto.verifySumcheckRound := fun {_R} [_] [_] [_] {_phase} [_] _ _ _ _ => none

#tooth Obend.Crypto.verifySumcheck_round_sound by mutation
  Obend.Crypto.verifySumcheckRound := fun {R} [CommRingOps R] [_] [TranscriptChallenge R] {_phase} [_] _ _ p tr =>
    let (r, tr') := absorbAndSqueezeRound p tr
    some (r, p.eval r, tr')

-- ============================================================================
-- 3. Proximity-Gap Guard (`2026/2424`), Bounded-Collision & Point-Bound `CanopyMerklePCS`
-- ============================================================================

#guard checkProximityConfig .binaryAdditive .uniqueDecodingRadius == true
#guard checkProximityConfig .binaryAdditive .johnsonBound == false
#guard checkProximityConfig .binaryAdditive .capacityBound == false
#guard checkProximityConfig .primeField .johnsonBound == true
#guard checkProximityConfig .primeField .capacityBound == true

#tooth Obend.Crypto.checkProximityConfig_iff by mutation
  Obend.Crypto.checkProximityConfig := fun _ _ => true

def canopyComm3 : CanopyCommitment :=
  (canopyMerklePCS).commit () 3 sampleTable3

#guard canopyComm3.root.bytes.size == 32

def canopyClaim3 : EvalClaim Goldilocks 3 :=
  ⟨challengePt3, rfl, mleEval sampleTable3 challengePt3⟩

def canopyOpen3 :=
  (canopyMerklePCS).openEval () 3 sampleTable3 canopyClaim3 boundTrA

#guard ((canopyMerklePCS).verifyEval () 3 canopyComm3 canopyClaim3 canopyOpen3.1 boundTrA).1 == true

def badCanopyClaim3 : EvalClaim Goldilocks 3 :=
  ⟨challengePt3, rfl, Goldilocks.add canopyClaim3.expectedVal Goldilocks.one⟩

#guard ((canopyMerklePCS).verifyEval () 3 canopyComm3 badCanopyClaim3 canopyOpen3.1 boundTrA).1 == false

#tooth Obend.Crypto.verifyMerklePath_completeness by mutation
  Obend.Crypto.verifyMerklePath := fun _ _ _ _ _ _ => false

#tooth Obend.Crypto.merkle_double_open_yields_bounded_collision by mutation
  Obend.Crypto.canopyVerifyEval := fun _ {_phase} [_] _ _ _ _ tr => (true, tr)

-- Mutation probe (`F5`): omitting `claim.point` from `canopyOpenFrame` breaks `canopyVerifyEval_binds_point`!
#tooth Obend.Crypto.canopyVerifyEval_binds_point by mutation
  Obend.Crypto.canopyOpenFrame := fun {_v} root claim =>
    encodeFrame root.bytes ByteArray.empty (encodeGoldilocksBytes claim.expectedVal)

-- ============================================================================
-- 4. Exact-Dimension Ajtai, Point Binding, Instance-Bound `verifyDualSumcheckPIOP` & `dualExtract`
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
  rows := 4
  cols := 32
  rows_pos := by decide
  modulus := 65537
  modulus_pos := by decide
  matrix :=
    [ (List.range 32).map (fun j => ((3 * j + 5 : Nat) : Int))
    , (List.range 32).map (fun j => ((7 * j + 11 : Nat) : Int))
    , (List.range 32).map (fun j => ((13 * j + 2 : Nat) : Int))
    , (List.range 32).map (fun j => ((19 * j + 23 : Nat) : Int)) ]
  matrix_rows := rfl
  matrix_cols := by
    intro row hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl <;> simp

-- Exact-dimension modular Ajtai additive homomorphism check (`w.length = 32 = latticeParams.cols`)
def vecW1 : List Int := (List.range 32).map fun (i : Nat) => ((i : Int) - 15)
def vecW2 : List Int := (List.range 32).map fun (i : Nat) => (10 - (2 * (i : Int)))
#guard ajtaiCommit latticeParams (vecAdd vecW1 vecW2) (by decide) ==
       vecAddMod (latticeParams.modulus : Int)
         (ajtaiCommit latticeParams vecW1 (by decide))
         (ajtaiCommit latticeParams vecW2 (by decide))

-- `Akita` (`2026/1983`) / `Twist & Shout` O(rows) sparse 1-hot column lookup equals dense commit
#guard ajtaiCommitOneHotColumn latticeParams 3 5 ==
       ajtaiLatticeCommit latticeParams 3 (oneHotTable Goldilocks 3 5)
example : SparseOneHotCommit.commitOneHot (P := ajtaiLatticePCS latticeParams) () 3 5 =
    (ajtaiLatticePCS latticeParams).commit () 3 (oneHotTable Goldilocks 3 5) :=
  SparseOneHotCommit.commitOneHot_eq_commit (P := ajtaiLatticePCS latticeParams) () 3 5 rfl (by decide)

-- Instance-bound `canopyAjtaiDualPCS` + `verifyDualSumcheckPIOP` end-to-end run
def dualScheme := canopyAjtaiDualPCS deployedCanopyHash32 latticeParams
def dualComm3 : CanopyCommitment × AjtaiCommitment := dualScheme.commit ((), ()) 3 sampleTable3
def dualSumcheck := honestBoundSumcheckProver dualComm3 3 sampleTable3 boundTrA
def dualOpen3 := dualScheme.openEval ((), ()) 3 sampleTable3 dualSumcheck.2.1 dualSumcheck.2.2

#guard verifyDualSumcheckPIOP
         (canopyMerklePCS deployedCanopyHash32)
         (ajtaiLatticePCS latticeParams)
         ((), ()) 1 3 dualComm3 sumClaim3 dualSumcheck.1 dualOpen3.1 boundTrA == true

-- `F3` Grinding Defense Check: replaying `dualSumcheck` against a different commitment `altComm3`
-- (even with matching `0` sum or shifted table) fails because `comm` is bound into `.instanceBound`!
def altSampleTable3 : List Goldilocks :=
  [Goldilocks.ofNat 4, Goldilocks.ofNat 6, Goldilocks.ofNat 11, Goldilocks.ofNat 5,
   Goldilocks.ofNat 13, Goldilocks.ofNat 2, Goldilocks.ofNat 19, Goldilocks.ofNat 23]
def altDualComm3 : CanopyCommitment × AjtaiCommitment := dualScheme.commit ((), ()) 3 altSampleTable3
#guard hypercubeSum 3 altSampleTable3 == sumClaim3
#guard verifyDualSumcheckPIOP
         (canopyMerklePCS deployedCanopyHash32)
         (ajtaiLatticePCS latticeParams)
         ((), ()) 1 3 altDualComm3 sumClaim3 dualSumcheck.1 dualOpen3.1 boundTrA == false

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

-- Mutation probe (`F3`): omitting `(comm, claimedSum)` (`instBytes`) from `instancePreimageList`
-- breaks `bindDualSumcheckInstance_binds`!
#tooth Obend.Crypto.bindDualSumcheckInstance_binds by mutation
  Obend.Crypto.instancePreimageList := fun relState stepCount _ =>
    encodeFrameList relState.data.toList (leb128 stepCount) []

-- Mutation probe (`F5`): omitting `claim.point` from `ajtaiOpenFrame` breaks `ajtaiLatticeVerifyEval_binds_point`!
#tooth Obend.Crypto.ajtaiLatticeVerifyEval_binds_point by mutation
  Obend.Crypto.ajtaiOpenFrame := fun {_v} syn claim =>
    encodeFrame (encodeSyndromeBytes syn) ByteArray.empty (encodeGoldilocksBytes claim.expectedVal)

-- Mutation probe: weakening `DualPCS` conjunction `ok₁ && ok₂` to disjunction `ok₁ || ok₂`
#tooth Obend.Crypto.dualPCS_sound_of_either by mutation
  Obend.Crypto.dualVerdictJoin := fun ok₁ ok₂ => ok₁ || ok₂

-- Executable `dualExtract` verification across all three forgery branches (`Type` data, `0 noncomputable`):
def brokenConstHash32 : Hash32 where
  eval _ := List.replicate 32 0
  len_eq _ := by simp

def brokenZeroAjtai : AjtaiParams where
  rows := 1
  cols := 4
  rows_pos := by decide
  modulus := 65537
  modulus_pos := by decide
  matrix := [[0, 0, 0, 0]]
  matrix_rows := rfl
  matrix_cols := by
    intro row hmem
    simp only [List.mem_singleton] at hmem
    subst hmem; rfl

-- Branch 1: `sameTableMerkleMismatch` -> concretely extracts colliding leaf preimages!
def sampleSameTableForgery : DualForgery brokenConstHash32 brokenZeroAjtai 0 :=
  .sameTableMerkleMismatch [Goldilocks.zero] rfl 0 (by decide) Goldilocks.one
    (openMerkle brokenConstHash32 [Goldilocks.one] 0)
    (by decide)
    (verifyMerklePath_openMerkle brokenConstHash32 0 [Goldilocks.one] rfl 0 (by decide))

#guard match dualExtract sampleSameTableForgery with
       | .inl w => w.msgA != w.msgB && w.msgA.length <= merkleMaxPreimageBytes 0
       | .inr _ => false

-- Branch 2: `crossTableMismatch` (Merkle branch against `openMerkle`) -> extracts colliding preimages!
def crossClaimOne0 : EvalClaim Goldilocks 0 := ⟨[], rfl, mleEval [Goldilocks.one] []⟩
def crossPrfOne0 :=
  (canopyAjtaiDualPCS brokenConstHash32 brokenZeroAjtai).openEval
    ((), ()) 0 [Goldilocks.one] crossClaimOne0 boundTrA

def sampleCrossMerkleForgery : DualForgery brokenConstHash32 brokenZeroAjtai 0 :=
  .crossTableMismatch [Goldilocks.zero] [Goldilocks.one] rfl rfl rfl
    crossClaimOne0 crossPrfOne0.1 boundTrA
    (dualPCS_completeness (canopyMerklePCS brokenConstHash32) (ajtaiLatticePCS brokenZeroAjtai)
      ((), ()) 0 [Goldilocks.one] [] rfl boundTrA ⟨trivial, rfl⟩ rfl)
    (.inl (by decide))

#guard match dualExtract sampleCrossMerkleForgery with
       | .inl w => w.msgA != w.msgB && w.msgB.length <= merkleMaxPreimageBytes 0
       | .inr _ => false

-- Branch 3: `crossTableMismatch` (Ajtai SIS branch) -> extracts short kernel vector `[1, 0, 0, 0]`!
def sampleCrossAjtaiForgery : DualForgery brokenConstHash32 brokenZeroAjtai 0 :=
  .crossTableMismatch [Goldilocks.one] [Goldilocks.zero] rfl rfl rfl
    crossClaimOne0 crossPrfOne0.1 boundTrA
    (by
      have hAjEq : ajtaiLatticeCommit brokenZeroAjtai 0 [Goldilocks.zero] =
          ajtaiLatticeCommit brokenZeroAjtai 0 [Goldilocks.one] := by decide
      rw [hAjEq]
      exact dualPCS_completeness (canopyMerklePCS brokenConstHash32) (ajtaiLatticePCS brokenZeroAjtai)
        ((), ()) 0 [Goldilocks.one] [] rfl boundTrA ⟨trivial, rfl⟩ rfl)
    (.inr (by decide))

#guard match dualExtract sampleCrossAjtaiForgery with
       | .inl _ => false
       | .inr sisW => sisW.shortVec == [1, 0, 0, 0]

-- ============================================================================
-- 5. Salted `SameOpening` (`DarkBazaar`): Canonical Lift, Salt Hiding & KKT
-- ============================================================================

def bidSalt : GoldilocksExt2 := ⟨Goldilocks.ofNat 0x123456789abcdef0, Goldilocks.ofNat 0x0fedcba987654321⟩
def askSalt : GoldilocksExt2 := ⟨Goldilocks.ofNat 0x0badf00dcafebabe, Goldilocks.ofNat 0x1122334455667788⟩

def bidBitsWitness : OrderBitWitness where
  qtyBits   := [true, false, true]                      -- 5 (< 2^8)
  totalBits := [false, false, true, true, true, true]   -- 60 (< 2^8)
  salt      := bidSalt

def askBitsWitness : OrderBitWitness where
  qtyBits   := [true, false, true]                      -- 5 (< 2^8)
  totalBits := [false, false, false, true, false, true] -- 40 (< 2^8)
  salt      := askSalt

#guard bidBitsWitness.qty == 5
#guard bidBitsWitness.total == 60
#guard askBitsWitness.qty == 5
#guard askBitsWitness.total == 40

def committedBid : CommittedOrderSpec :=
  commitPrivateOrder latticeParams 101 .bid 8 bidSalt bidBitsWitness

def committedAsk : CommittedOrderSpec :=
  commitPrivateOrder latticeParams 202 .ask 8 askSalt askBitsWitness

-- Salted `commitPrivateOrder` never collides with unsalted (`salt = 0`) dictionary entry!
def unsaltedBidLookup : CommittedOrderSpec :=
  commitPrivateOrder latticeParams 101 .bid 8 GoldilocksExt2.zero bidBitsWitness
#guard committedBid.dualComm != unsaltedBidLookup.dualComm

def clearingMarket : Market :=
  { currency := 1, goods := 2, epsilon := 0 }

def smudgedQuery : SameOpeningQuery where
  market := clearingMarket
  ajtaiParams := latticeParams
  noiseBound := 16
  smudgeBound := 16 * (2 ^ 40)
  secBits := 40
  committedOrders := [committedBid, committedAsk]

def optimalTransfers : List ResourcePosting :=
  [ { source := 202, destination := 101, asset := 2, amount := 5 }
  , { source := 101, destination := 202, asset := 1, amount := 50 } ]

def optimalKktCert : Certificate where
  price := 10
  potentials := (0, 1)
  slacks := [0, 2]

def honestSameOpeningCert : SameOpeningWitness where
  orderWitnesses := [bidBitsWitness, askBitsWitness]
  transfers := optimalTransfers
  kktCert := optimalKktCert

-- 5a. Honest smudged + salted + canonical + zero-gap KKT witness is ACCEPTED
#guard verifySameOpening smudgedQuery honestSameOpeningCert == .ok
example (fuel : Nat) (q : SameOpeningQuery) (w : SameOpeningWitness) :
    privateConvexSameOpeningJudge.check fuel q w = verifySameOpening q w := by
  unfold privateConvexSameOpeningJudge; rfl

-- 5b. Unsmudged collective decryption (`smudgeBound = 0`, `2026/2546` attack!) is REFUSED & REFUTED
def unsmudgedQuery : SameOpeningQuery :=
  { smudgedQuery with smudgeBound := 0 }

#guard verifySameOpening unsmudgedQuery honestSameOpeningCert == .refused .unsmudgedThresholdNoise []
#guard privateConvexSameOpeningJudge.refutes .unsmudgedThresholdNoise == true

-- 5c. BitZ range width violation (`maxBits = 2` on qty = 5 needing 3 bits) is REFUSED
def narrowRangeBid : CommittedOrderSpec :=
  commitPrivateOrder latticeParams 101 .bid 2 bidSalt bidBitsWitness

def narrowRangeQuery : SameOpeningQuery :=
  { smudgedQuery with committedOrders := [narrowRangeBid, committedAsk] }

#guard verifySameOpening narrowRangeQuery honestSameOpeningCert == .refused (.bitzRangeExceeded 0) []

-- 5d. Non-canonical 64-bit `goldilocksPrime` wrap-around alias (`qty = p = 2^64 - 2^32 + 1`, `maxBits = 64`)
-- passes 64-bit `BitZ` length check (`64 ≤ 64`) yet is REFUSED by `CanonicalLift`!
def primeAliasBits : List Bool :=
  true :: (List.replicate 31 false ++ List.replicate 32 true)
#guard primeAliasBits.length == 64
#guard bitsToNat primeAliasBits == goldilocksPrime

def primeAliasWitness : OrderBitWitness :=
  { bidBitsWitness with qtyBits := primeAliasBits }
def primeAliasCommitted : CommittedOrderSpec :=
  commitPrivateOrder latticeParams 101 .bid 64 bidSalt primeAliasWitness
def primeAliasQuery : SameOpeningQuery :=
  { smudgedQuery with committedOrders := [primeAliasCommitted, committedAsk] }
def primeAliasCert : SameOpeningWitness :=
  { honestSameOpeningCert with orderWitnesses := [primeAliasWitness, askBitsWitness] }

#guard verifySameOpening primeAliasQuery primeAliasCert == .refused (.nonCanonicalFieldLift 0) []

-- 5e. `SameOpening` bait-and-switch (opening different private order bits OR wrong salt!) is REFUSED
def tamperedOrderWitness : SameOpeningWitness :=
  { honestSameOpeningCert with
    orderWitnesses := [{ bidBitsWitness with qtyBits := [false, true] }, askBitsWitness] }

#guard verifySameOpening smudgedQuery tamperedOrderWitness == .refused (.dualCommitmentMismatch 0) []

def wrongSaltWitness : SameOpeningWitness :=
  { honestSameOpeningCert with
    orderWitnesses := [{ bidBitsWitness with salt := GoldilocksExt2.zero }, askBitsWitness] }

#guard verifySameOpening smudgedQuery wrongSaltWitness == .refused (.dualCommitmentMismatch 0) []

-- 5f. Non-zero primal-dual KKT gap (`slacks := [1, 2]` => dual = 15 != primal = 10) is REFUSED
def suboptimalKktWitness : SameOpeningWitness :=
  { honestSameOpeningCert with
    kktCert := { optimalKktCert with slacks := [1, 2] } }

#guard verifySameOpening smudgedQuery suboptimalKktWitness != .ok

-- Mutation probe (`K7`): replacing `canonicalLift?` with modular `Goldilocks.ofNat`
-- re-opens the `0` vs `p = 2^64 - 2^32 + 1` wrap-around alias and breaks `orderWitnessTable?_injective`!
#tooth Obend.Crypto.orderWitnessTable?_injective by mutation
  Obend.Crypto.canonicalLift? := fun n => some (Goldilocks.ofNat n)

-- Mutation probe: disabling the `2026/2546` smudging guard breaks `verifySameOpening_sound`!
#tooth Obend.Crypto.verifySameOpening_sound by mutation
  Obend.Crypto.checkSmudgeSafe := fun _ _ _ => true

-- Mutation probe: disabling the KKT zero primal-dual gap check breaks `verifySameOpening_sound`!
#tooth Obend.Crypto.verifySameOpening_sound by mutation
  Obend.Crypto.kktPrimalDualGapZero := fun _ _ _ _ => true

-- ============================================================================
-- 6. Zero-`Classical` Check (`dualExtract`), Axiom Census & 0-Closed-Theorem Check
-- ============================================================================

#assert_axioms_tree

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for decl in [``Obend.Crypto.dualExtract, ``Obend.Crypto.dualExtractBoth,
               ``Obend.Crypto.extractDualCommitCollisionBoth,
               ``Obend.Crypto.extractCanopyDoubleOpenCollision,
               ``Obend.Crypto.extractCanopyOpenMerkleCollision,
               ``Obend.Crypto.extractAjtaiDoubleOpenSIS] do
    if Lean.isNoncomputable env decl then
      throwError m!"{decl} is noncomputable (must be constructive executable Type data!)"
    let axs ← collectAxioms decl
    for ax in axs do
      unless Obend.AssertAxioms.standard.contains ax do
        throwError m!"{decl} depends on non-standard axiom {ax}: {axs.toList}"
  for (name, _) in env.constants.map₁.toList do
    if Obend.AssertAxioms.packageModule? env name |>.any (fun m => Obend.AssertAxioms.directoryOf m == `Obend.Crypto) then
      if Lean.isNoncomputable env name then
        throwError m!"Obend.Crypto contains noncomputable declaration (must be 0 Classical/noncomputable): {name}"
  let rows ← liftTermElabM Obend.AssertAxioms.theoremCensus
  for (dir, universal, closed) in rows do
    if dir == `Obend.Crypto then
      let userClosed := closed.filter fun n => n.components.getLast? != some `sizeOf_spec
      unless userClosed.isEmpty do
        throwError m!"Obend.Crypto has closed theorems (must be 0): {userClosed.toList}"
      if universal == 0 then
        throwError "Obend.Crypto reported 0 universal theorems"
      logInfo m!"Obend.Crypto census clean: {universal} universal theorems, 0 user closed theorems, 0 noncomputable"

end Obend.Tests.ModularCryptoSpineTest
