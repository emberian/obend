import Obend.Crypto.Multilinear
import Obend.Crypto.Transcript
import Obend.Crypto.Sumcheck
import Obend.Crypto.PCS
import Obend.Crypto.DualSpine
import Obend.Crypto.SameOpening
import Obend.Crypto.FastRing
import Obend.Crypto.GameSoundness
import Obend.Crypto.PikkuFoldLayered
import Obend.Crypto.CanopyReduce
import Obend.AssertAxioms
import Obend.Tactic.Tooth

/-!
# `tests/metasystem/GameSoundnessAndDualSpineTest.lean` — Cryptographic Game-Reduction & `#tooth` Suite

End-to-end verification and mutation-killing probe suite across the Wave-7 Cryptographic Game Spine:
1. `Obend.Crypto.GameSoundness`:
   - Exact rational `RatProb` ↔ `Obend.Category.GradeMonoid RatSlack` bridge & `FinDist` monad laws,
   - Total-variation coupling (`tvDist_le_of_bad_event`) & uniform smudging (`uniformShift_tvDist_le`),
   - Maurer `CryptoPackage` / `Converter` game-hopping (`adv_triangle`, `adv_compose_converter`),
   - Stateful `LazyRO` constructive Birthday bound (`lazyRO_collision_prob_le_birthday`) & `extractFromROLog`,
   - Constructive Minkowski / Pigeonhole refutation (`pigeonhole_short_kernel_construct`, `unbroken_sis_false_when_compressing`)
     vs. uniform-CRS compressing `MSISGame` reduction (`binding_advantage_le_msis_advantage`),
   - Simulator-based `StatisticalZK`, $\land$-privacy (`dual_zk_requires_both_hiding`), refutation of
     cleartext openings (`cleartext_opening_destroys_dual_zk`), and `TranscriptTree` extraction (`extractFromForkingTree_within_sisBeta`).
2. `Obend.Crypto.PCS` & `Obend.Crypto.CanopyReduce`:
   - Compressing Merkle (`v ≥ 1`, `merkleMaxPreimageBytes v = 65 > 32`) `LazyRO` collision-free log binding
     (`canopyMerklePCS_bind_of_roLog`, `canopyMerklePCS_extractDoubleOpenOrEq`),
   - Fenzi-safe `.instanceBound` Canopy batch reduction (`verifyCanopyCommitAndReduceTranscript`).
3. `Obend.Crypto.DualSpine`:
   - Compressing `compressingMSISParams` (`rows = 2, cols = 12, 4 * 2 < 12`) Pigeonhole refutation + `MSISGame` binding,
   - Cleartext `AjtaiOpeningProof` witness recovery (`cleartextAjtaiOpen_recovers_table`) & ZK impossibility,
   - Lyubashevsky/Schnorr `verifyMaskedAjtaiOpening` completeness, 2-special-soundness rewinding,
     joint-transcript `(t, z)` HVZK (`maskedAjtai_statistical_zk`), and `dualSpine_masked_both_bind_and_zk`.
4. `Obend.Crypto.PikkuFoldLayered`:
   - Fenzi-safe `.instanceBound` cross-term absorption (`fenziSafeFoldTranscript`),
   - Small-norm challenge squeezing (`squeezeBoundedSignedChal_abs_le`), `checkNormRefreshGate`, and `verifyBoundedChallengeFold`.
5. `Obend.Crypto.SameOpening`:
   - `thresholdSmudge_tvDist_le`, `ModulusNoWrapSafe` / `.modulusWraparoundUnsafe` refusal,
   - Non-vacuous `unsaltedCommitDictionary_miss_of_roLog_or_sis`,
   - Non-tautological `WellFormedEmptyBookQuery` `Judge` fragment (`verifySameOpening_emptyBook_complete`),
   - Zero-leakage `PublicSameOpeningVerdict` (`toPublicZkVerdict_hides_private_index`).
6. 10 `#tooth` mutation kills + `#assert_axioms_tree` + `0 Classical` / `0 closed theorems` census.
-/

namespace Obend.Tests.GameSoundnessAndDualSpineTest

open Obend.Category
open Obend.Crypto
open Obend.Crypto.GameSoundness
open Obend.Crypto.Fast
open Obend.Digest.Cshake256
open Obend.Digest.HashBytes
open Obend.Apps.ZkNtt
open Obend.Judge
open Obend.Ledger

-- ============================================================================
-- 1. `GameSoundness`: `RatProb` ↔ `RatSlack`, `FinDist`, `LazyRO` & Minkowski vs `MSISGame`
-- ============================================================================

def halfProb : RatProb := ⟨1, 2, by decide⟩
def thirdProb : RatProb := ⟨1, 3, by decide⟩

#guard (halfProb.add thirdProb).num == 5
#guard (halfProb.add thirdProb).den == 6
#guard (tvDist (FinDist.pure (true : Bool)) (FinDist.pure false)).num == 1
#guard (tvDist (FinDist.pure (true : Bool)) (FinDist.pure false)).den == 1

-- GradeMonoid RatSlack bridge check
example (p q : RatProb) : (p.toRatSlack ≤ q.toRatSlack) ↔ RatProb.le p q :=
  RatProb.toRatSlack_le_iff p q

-- Concrete constructive Pigeonhole kernel witness on a compressing 1×3 binary-ternary matrix mod 5 (5^1 < 2^3 = 8)
def toyCompressingMat : List (List Int) := [[1, 2, 3]]
def extractedToyKernel :=
  pigeonhole_short_kernel_construct 1 3 5 1 (by decide) toyCompressingMat rfl
    (by intro r hr; simp [toyCompressingMat] at hr; rw [hr]; rfl) (by decide)

#guard extractedToyKernel.1.length == 3
#guard extractedToyKernel.1.any (· != 0)
#guard extractedToyKernel.1.all (fun x => decide (x.natAbs ≤ 1))
#guard (GameSoundness.dotInt [1, 2, 3] extractedToyKernel.1) % 5 == 0

-- Unkeyed `UnbrokenMSIS` is provably `False` on `compressingMSISParams` (2 × 12 mod 262147, norm ≤ 16),
-- trivial wrap-around `(q, 0, …, 0)` is rejected (`beta = 131070 < q = 262147`),
-- and `binding_advantage_le_msis_advantage` holds with exact factor-1 advantage over `uniformMatDist`!
example (A : List (List Int)) (hR : A.length = 2) (hC : ∀ r ∈ A, r.length = 12) :
    UnbrokenMSIS 12 262147 16 A → False :=
  compressingMSISParams_unbroken_false A hR hC

#guard isMSISWin compressingMSISParams [[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
         ((compressingMSISParams.q : Int) :: List.replicate 11 0) == false

example (adv : List (List Int) → FinDist (List Int × List Int)) :
    RatProb.le
      (bindBreakProb compressingMSISParams 65535 adv)
      (msisAdvantage compressingMSISParams (reduceBindToMSIS adv)) :=
  (maskedAjtai_binding_advantage_le_msis compressingMSISParams 65535
    (compressingMSISParams_is_compressing 0) (by decide) adv).2

-- Straight-line `LazyRO` witness extraction & collision detection
def sampleROLog : ROLog Nat (BitVec 8) := [(10, 0xAA#8), (20, 0xBB#8)]
#guard hasLogCollision sampleROLog == false
#guard extractFromROLog (fun n => some (n + 1)) (0xAA#8) sampleROLog == some (10, 11)
#guard hasLogCollision ((30, 0xAA#8) :: sampleROLog) == true

-- Birthday bound instantiation for any q-query 256-bit RO adversary
example {q : Nat} (adv : QueryProg ByteArray (BitVec 256) Bool q) :
    RatProb.le
      ((runProg lazyRO256 adv []).probEvent (fun (_, lf) => hasLogCollision lf))
      ⟨q * (q - 1), 2 * (2 ^ 256), Nat.mul_pos (by decide) (Nat.pow_pos (by decide))⟩ :=
  lazyRO_collision_prob_le_birthday adv

-- Multi-round `TranscriptTree` special-soundness extraction within `sisBetaBound`
def sampleForkTree : TranscriptTree 1 :=
  .fork2 [2] [0] 0 1 (.leaf [2] [1, 1]) (.leaf [2] [1, 1])

#guard (extractFromForkingTree sampleForkTree).1 == [-1, -1]
#guard (extractFromForkingTree sampleForkTree).2 == -1
#guard normAtDepth 1 1 1 == 2

-- ============================================================================
-- 2. `PCS` (`v = 2`, 65-Byte Compressing Nodes) `LazyRO` Binding & `CanopyReduce`
-- ============================================================================

#guard merkleMaxPreimageBytes 0 == 10
#guard merkleMaxPreimageBytes 2 == 65

def pcsTable2 : List Goldilocks :=
  [Goldilocks.ofNat 11, Goldilocks.ofNat 22, Goldilocks.ofNat 33, Goldilocks.ofNat 44]
def pcsPt2 : List Goldilocks := [Goldilocks.ofNat 5, Goldilocks.ofNat 9]
def pcsSeedTr : Transcript .relationBound :=
  bindRelation "test.pcs/v1" ByteArray.empty ByteArray.empty (Transcript.newUnseeded ByteArray.empty)

def pcsComm2 := canopyCommit deployedCanopyHash32 2 pcsTable2
def pcsClaim2 : EvalClaim Goldilocks 2 := ⟨pcsPt2, rfl, mleEval pcsTable2 pcsPt2⟩
def pcsOpen2 := (canopyOpenEval deployedCanopyHash32 2 pcsTable2 pcsClaim2 pcsSeedTr).1

#guard (canopyVerifyEval deployedCanopyHash32 2 pcsComm2 pcsClaim2 pcsOpen2 pcsSeedTr).1 == true

-- Build an explicit collision-free full-width 32-byte `Digest32` `ROLog` containing all Merkle frames of `pcsOpen2`
def pcsOpen2Log : ROLog (List UInt8) Digest32 :=
  (canopyOpeningFrames deployedCanopyHash32 2 pcsOpen2).eraseDups.map
    (fun m => (m, evalDigest32 deployedCanopyHash32 m))

#guard hasLogCollision pcsOpen2Log == false

-- Concrete Fenzi-safe `.instanceBound` `CanopyReduce` batch check
def canopyCfg : Canopy.Config := ⟨1, 1, by decide, 2, .primeField, .uniqueDecodingRadius, .primeUDR⟩
def canopyTbl : Canopy.Table canopyCfg :=
  Sized.ofFn fun i => Sized.ofFn fun j => Goldilocks.ofNat (10 * i.val + j.val + 1)
def canopyQs : Array (Canopy.Query canopyCfg) := #[⟨0, by decide⟩, ⟨2, by decide⟩]
def canopyDigest := Canopy.commit canopyCfg canopyTbl
def canopyBatchOpen := Canopy.openBatchCanopy canopyCfg canopyTbl canopyQs
def canopyChals :=
  Canopy.deriveCanopyChallenges 1 canopyCfg ByteArray.empty ByteArray.empty canopyDigest canopyQs canopyBatchOpen.cap
def canopyExpectedClaim : Goldilocks :=
  (Canopy.foldRows canopyChals.1 (Canopy.pairedRows canopyCfg rfl canopyBatchOpen.rows)).coeffs.foldl
    (fun acc row => Goldilocks.add (Canopy.canopyMul canopyChals.2.1 acc) (Canopy.evalRow canopyChals.2.2 row))
    Goldilocks.zero

#guard Canopy.verifyCanopyCommitAndReduceTranscript canopyCfg (w := 1) rfl
         ByteArray.empty ByteArray.empty canopyDigest canopyQs canopyBatchOpen canopyExpectedClaim == true

-- ============================================================================
-- 3. `DualSpine`: Cleartext Leakage vs. Joint-Transcript `(t, z)` Masked Ajtai HVZK
-- ============================================================================

-- Cleartext `ajtaiLatticeOpenEval` leaks the entire table `pcsTable2`
#guard gadgetRecomposeTable
         (ajtaiLatticeOpenEval (inhabitedAjtaiParams 2) 2 pcsTable2 pcsClaim2 pcsSeedTr).1.shortLimbs ==
       some pcsTable2

-- Masked Ajtai opening (`z = c · w + y`) passes `verifyMaskedAjtaiOpening` and satisfies joint `(t, z)` HVZK
def demoMat : List (List Int) := [[3, 5, 7, 11], [2, 13, 17, 19]]
def demoW   : List Int := [2, -1, 3, -2]
def demoY   : List Int := [10, -7, 4, 8]
def demoCm  : List Int := ajtaiSyndrome 65537 demoMat demoW
def demoT   : List Int := ajtaiSyndrome 65537 demoMat demoY
def demoZ1  : List Int := maskedResponse 2 demoW demoY
def demoZ2  : List Int := maskedResponse (-1) demoW demoY

#guard verifyMaskedAjtaiOpening 65537 4 30 demoMat demoCm demoT 2 demoZ1 == true
#guard verifyMaskedAjtaiOpening 65537 4 30 demoMat demoCm demoT (-1) demoZ2 == true

-- Rewinding two distinct challenges (c₁ = 2, c₂ = -1) recovers Δz = 3 · w
#guard vecLinComb 1 (-1) demoZ1 demoZ2 == [6, -3, 9, -6]

-- Non-vacuous joint-transcript `(t, z)` HVZK TV distance on smudge box B = 64, cols = 2, cMax = 1, bW = 2:
-- TV distance ≤ (2 * 1 * 2) / (2 * 64 + 1) = 4 / 129 < 1!
def demoMaskedMat2 : List (List Int) := [[3, 5], [2, 13]]
def demoMaskedW2   : List Int := [2, -1]
def demoMaskedStmt : MaskedAjtaiStmt :=
  { q := 65537, cols := 2, matrix := demoMaskedMat2, cm := ajtaiSyndrome 65537 demoMaskedMat2 demoMaskedW2, chal := 1 }

example : RatProb.le
    (tvDist ((maskedAjtaiZKProtocol 64 2 1).realView demoMaskedStmt demoMaskedW2)
            ((maskedAjtaiSimulator 64).simView demoMaskedStmt ()))
    ⟨2 * (1 * 2), 2 * 64 + 1, by decide⟩ :=
  maskedAjtai_statistical_zk 64 2 1 demoMaskedStmt demoMaskedW2
    ⟨rfl, by intro x hx; simp [demoMaskedW2] at hx; rcases hx with rfl | rfl <;> decide,
     by decide, rfl⟩

-- ============================================================================
-- 4. `PikkuFoldLayered`: Fenzi-Safe `.instanceBound` Fold & `LatticeFold+` Norm Gate
-- ============================================================================

def pikkuMat : IntMatrix 2 4 :=
  Sized.ofFn fun i => Sized.ofFn fun j => ((i.val + 1) * (j.val + 2) : Int)
def pikkuU : FastIntPoly 4 := ⟨#[1, -2, 3, -1], rfl⟩
def pikkuV : FastIntPoly 4 := ⟨#[-1, 2, -2, 1], rfl⟩
def pikkuCm1 := matVecModQ pikkuMat 65537 pikkuU
def pikkuCm2 := matVecModQ pikkuMat 65537 pikkuV
def pikkuDimDesc := pikkuBoundedDimDesc pikkuMat 65537 2 9 37 ByteArray.empty
def pikkuBTr := fenziSafeFoldTranscript pikkuDimDesc pikkuCm1.coeffs.toList pikkuCm2.coeffs.toList
                  ByteArray.empty ByteArray.empty (Native.bytesOfList [0x42])
def pikkuFoldOut := boundedFoldFromTranscript 2 pikkuBTr.transcript pikkuU pikkuV

#guard checkNormRefreshGate 3 3 2 9 37 == true
#guard checkNormRefreshGate 3 3 2 9 36 == false
#guard pikkuFoldOut.1.natAbs ≤ 2
#guard verifyBoundedChallengeFold pikkuMat 65537 3 3 2 9 37
         ByteArray.empty ByteArray.empty ByteArray.empty (Native.bytesOfList [0x42])
         pikkuCm1 pikkuCm2 pikkuFoldOut.2.1 == true

-- Tampering with `crossTerms` OR bound `nextRoundCap` after commitment changes the `.instanceBound` challenge and rejects!
#guard verifyBoundedChallengeFold pikkuMat 65537 3 3 2 9 37
         ByteArray.empty ByteArray.empty ByteArray.empty (Native.bytesOfList [0x43])
         pikkuCm1 pikkuCm2 pikkuFoldOut.2.1 == false
#guard verifyBoundedChallengeFold pikkuMat 65537 3 3 2 10 41
         ByteArray.empty ByteArray.empty ByteArray.empty (Native.bytesOfList [0x42])
         pikkuCm1 pikkuCm2 pikkuFoldOut.2.1 == false

-- Parallel bounded-challenge grinding amplification: (2*bChal + 1)^(-k)
example (target : List Int) :
    RatProb.le
      ((uniformVecDist 2 target.length).probEvent (· == target))
      ⟨1, (2 * 2 + 1) ^ target.length, Nat.pow_pos (by omega)⟩ :=
  parallelBoundedChalHitProb_le 2 target

-- End-to-end accepted masked transcript fork reduction (`DualSpine`) & `LazyRO` PCS forgery birthday bound (`PCS`)
example (adv : List (List Int) → FinDist MaskedTranscriptFork) :
    RatProb.le
      (((uniformMatDist compressingMSISParams).bind
        (fun A => (adv A).map (isValidMaskedTranscriptFork compressingMSISParams 100 10 2 A))).probEvent id)
      (msisAdvantage compressingMSISParams (reduceBindToMSIS (fun A => (adv A).map reduceMaskedForkStep))) :=
  (maskedTranscriptFork_advantage_le_msis compressingMSISParams 100 10 2
    (compressingMSISParams_is_compressing 0) (by decide) adv).2

example {q : Nat} (dom : List Digest32) (hne : dom ≠ []) (hNodup : dom.Nodup)
    (forger : QueryProg (List UInt8) Digest32 (EvalClaim Goldilocks 2 × EvalClaim Goldilocks 2 × CanopyOpeningProof × CanopyOpeningProof) q) :
    RatProb.le
      ((runProg (lazyROPackage dom hne) forger []).probEvent
        (isLoggedDoubleOpenForgery deployedCanopyHash32 2 pcsComm2 pcsSeedTr pcsSeedTr))
      ⟨q * (q - 1), 2 * dom.length, Nat.mul_pos (by decide) (length_pos_of_ne_nil hne)⟩ :=
  canopyDoubleOpen_forger_prob_le_birthday deployedCanopyHash32 2 dom hne hNodup pcsComm2 pcsSeedTr pcsSeedTr forger

-- ============================================================================
-- 5. `SameOpening`: `MLWE` Commitment Hiding, `effectiveMsgBound`, Non-Empty `Fragment` & Public ZK Verdict
-- ============================================================================

#guard centeredModDecode 1000 ((120 + (-5) + 300 : Int) % 1000) == 415
#guard centeredModDecode 1000 (((-120) + (-5) + (-200) : Int) % 1000) == -325

-- LWE-blinded order commitment hiding (`≤ 2 · MLWEAdv`)
example (P : MLWEParams) (m₀ m₁ : List Int)
    (h₀ : m₀.length = P.samples + 1) (h₁ : m₁.length = P.samples + 1)
    (D : (List (List Int) × List Int) → Bool) :
    RatProb.le
      (RatProb.absDiff ((mlweBlindedCommitDist P m₀).probEvent D) ((mlweBlindedCommitDist P m₁).probEvent D))
      (RatProb.add
        (mlweAdv P (fun (A, b) => D (A, addModVec P.q b m₀)))
        (mlweAdv P (fun (A, b) => D (A, addModVec P.q b m₁)))) :=
  mlweBlindedCommit_hiding_le_two_mlweAdv P m₀ m₁ h₀ h₁ D

-- Non-empty 2-order `[bid, ask]` inhabitedness of `privateConvexSameOpeningJudge.Fragment` (`WellFormedZeroBookQuery`)
example : ∃ q : SameOpeningQuery, q.committedOrders.length = 2 ∧ privateConvexSameOpeningJudge.Fragment q :=
  wellFormedZeroBookQuery_twoOrders_inhabited 10 20 (by decide) (by decide) (by decide)

def demoEmptyQuery : SameOpeningQuery :=
  { market := { currency := 1, goods := 2, epsilon := 0 }
    ajtaiParams := inhabitedAjtaiParams 3
    msgBound := 500
    noiseBound := 4
    smudgeBound := 4 * (2 ^ 40)
    secBits := 40
    qModulus := 2 ^ 62
    committedOrders := [] }

#guard verifySameOpening demoEmptyQuery emptyBookClearingWitness == .ok

-- Modulus wrap-around (`qModulus = 100` too small for `2 * (effectiveMsgBound + noise + smudge)`) is REFUSED & REFUTED!
def wrapUnsafeQuery : SameOpeningQuery :=
  { demoEmptyQuery with qModulus := 100 }

#guard verifySameOpening wrapUnsafeQuery emptyBookClearingWitness == .refused .modulusWraparoundUnsafe []
#guard privateConvexSameOpeningJudge.refutes .modulusWraparoundUnsafe == true

-- Private refusal indices (`bitzRangeExceeded 0` vs `dualCommitmentMismatch 1` vs `nonzeroPrimalDualGap`)
-- collapse to the exact same `.privateWitnessRejected` public ZK verdict!
#guard toPublicZkVerdict (.refused (.bitzRangeExceeded 0) []) == .privateWitnessRejected
#guard toPublicZkVerdict (.refused (.dualCommitmentMismatch 1) []) == .privateWitnessRejected
#guard toPublicZkVerdict (.refused (.nonzeroPrimalDualGap 15 10) []) == .privateWitnessRejected

-- ============================================================================
-- 6. `#tooth` Mutation Kills Across All Upgraded Cryptographic Invariants (16 Probes)
-- ============================================================================

-- 6.1 Dropping the second hop in `RatProb.add` breaks game-hopping triangle inequality
#tooth Obend.Crypto.GameSoundness.RatProb.absDiff_triangle by mutation
  Obend.Crypto.GameSoundness.RatProb.add := fun p _ => p

-- 6.2 Blindly reporting `hasLogCollision := false` breaks `hasLogCollision_iff`
#tooth Obend.Crypto.GameSoundness.hasLogCollision_iff by mutation
  Obend.Crypto.GameSoundness.hasLogCollision := fun _ => false

-- 6.3 Returning `w₁` instead of `w₁ - w₂` breaks the uniform-CRS `MSISGame` binding reduction
#tooth Obend.Crypto.GameSoundness.binding_advantage_le_msis_advantage by mutation
  Obend.Crypto.GameSoundness.reduceBindToMSIS := fun adv A => (adv A).map Prod.fst

-- 6.4 Omitting masking vector `y` in `maskedResponse` (`z := w`) breaks `verifyMaskedAjtaiOpening_complete`
#tooth Obend.Crypto.verifyMaskedAjtaiOpening_complete by mutation
  Obend.Crypto.maskedResponse := fun _ w _ => w

-- 6.5 Accepting unchecked masked openings breaks 2-special-soundness rewinding (`verifyMaskedAjtaiOpening_forking_sound`)
#tooth Obend.Crypto.verifyMaskedAjtaiOpening_forking_sound by mutation
  Obend.Crypto.verifyMaskedAjtaiOpening := fun _ _ _ _ _ _ _ _ => true

-- 6.6 Disabling `LatticeFold+` norm-refresh gate breaks `checkNormRefreshGate_sound`
#tooth Obend.Crypto.Fast.checkNormRefreshGate_sound by mutation
  Obend.Crypto.Fast.checkNormRefreshGate := fun _ _ _ _ _ => true

-- 6.7 Squeezing an out-of-range challenge (`bChal + 1`) breaks `squeezeBoundedSignedChal_abs_le`
#tooth Obend.Crypto.Fast.squeezeBoundedSignedChal_abs_le by mutation
  Obend.Crypto.Fast.squeezeBoundedSignedChal := fun bChal tr => (((bChal + 1 : Nat) : Int), tr)

-- 6.8 Disabling `checkModulusNoWrap` breaks `verifySameOpening_sound` (`ModulusNoWrapSafe` field)
#tooth Obend.Crypto.verifySameOpening_sound by mutation
  Obend.Crypto.checkModulusNoWrap := fun _ _ _ _ => true

-- 6.9 Injecting an unbalanced transfer breaks `verifySameOpening_emptyBook_complete`
#tooth Obend.Crypto.verifySameOpening_emptyBook_complete by mutation
  Obend.Crypto.emptyBookClearingWitness :=
    { orderWitnesses := []
      transfers := [{ source := 1, destination := 2, asset := 1, amount := 5 }]
      kktCert := { price := 1, potentials := (0, 0), slacks := [] } }

-- 6.10 Leaking trader 0's `BitZ` range failure into `.accepted` breaks `toPublicZkVerdict_hides_private_index`
#tooth Obend.Crypto.toPublicZkVerdict_hides_private_index by mutation
  Obend.Crypto.toPublicZkVerdict := fun v =>
    match v with
    | .ok => .accepted
    | .refused (.bitzRangeExceeded 0) _ => .accepted
    | _ => .privateWitnessRejected

-- 6.11 Returning a constant zero view `(t=0, z=0)` in `maskedAjtaiSimulator` breaks `maskedAjtai_statistical_zk`
#tooth Obend.Crypto.maskedAjtai_statistical_zk by mutation
  Obend.Crypto.maskedAjtaiSimulator := fun _ =>
    ⟨fun x _ => FinDist.pure (List.replicate x.matrix.length 0, List.replicate x.cols 0)⟩

-- 6.12 Omitting the norm check in `isMSISWin` allows trivial wrap-around `(q, 0, …, 0)` and breaks `msis_rejects_mod_wraparound`
#tooth Obend.Crypto.GameSoundness.msis_rejects_mod_wraparound by mutation
  Obend.Crypto.GameSoundness.isMSISWin := fun P A u =>
    (u.length == P.cols) && u.any (· != 0) && A.all (fun row => decide (GameSoundness.dotInt row u % (P.q : Int) == 0))

-- 6.13 Dropping negative representative centering in `centeredModDecode` breaks `centeredModDecode_exact_of_noWrap`
#tooth Obend.Crypto.centeredModDecode_exact_of_noWrap by mutation
  Obend.Crypto.centeredModDecode := fun qModulus r => r % (qModulus : Int)

-- 6.14 Dropping masked transcript fork reduction (`reduceMaskedForkStep`) breaks `maskedTranscriptFork_advantage_le_msis`
#tooth Obend.Crypto.maskedTranscriptFork_advantage_le_msis by mutation
  Obend.Crypto.reduceMaskedForkStep := fun _ => ([], [])

-- 6.15 Rejecting valid bounded-challenge folds breaks `verifyBoundedChallengeFold_complete`
#tooth Obend.Crypto.Fast.verifyBoundedChallengeFold_complete by mutation
  Obend.Crypto.Fast.verifyBoundedChallengeFold := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ => false

-- 6.16 Vacuously accepting unlogged / non-discrepant openings in `isLoggedDoubleOpenForgery` breaks `canopyDoubleOpen_forger_prob_le_birthday`
#tooth Obend.Crypto.canopyDoubleOpen_forger_prob_le_birthday by mutation
  Obend.Crypto.isLoggedDoubleOpenForgery := fun _ _ {_ _} [_] [_] _ _ _ _ => true

-- ============================================================================
-- 7. Axiom Census, Strict `0 Classical.choice` Check & `0` Closed Theorems
-- ============================================================================

#assert_axioms_tree

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  -- Pure Type-valued extractors, reductions & simulators: 0 Classical.choice even in erased Prop subterms!
  for pureDecl in [``Obend.Crypto.GameSoundness.extractFromROLog,
                   ``Obend.Crypto.GameSoundness.findCollision,
                   ``Obend.Crypto.GameSoundness.reduceBindToMSIS,
                   ``Obend.Crypto.GameSoundness.extractFromForkingTree,
                   ``Obend.Crypto.maskedAjtaiSimulator,
                   ``Obend.Crypto.reduceMaskedForkStep] do
    if Lean.isNoncomputable env pureDecl then
      throwError m!"{pureDecl} is noncomputable!"
    let axs ← collectAxioms pureDecl
    for ax in axs do
      if ax == ``Classical.choice || !Obend.AssertAxioms.standard.contains ax then
        throwError m!"{pureDecl} depends on Classical.choice or non-standard axiom {ax}: {axs.toList}"
  -- PSum / Subtype proof-carrying extractors: executable Type branching (isNoncomputable == false) & standard axioms only
  for decl in [``Obend.Crypto.GameSoundness.pigeonhole_short_kernel_construct,
               ``Obend.Crypto.canopyMerklePCS_extractDoubleOpenOrEq,
               ``Obend.Crypto.extractSaltedDictionaryCollisionBoth,
               ``Obend.Crypto.Fast.extractFenziSafeFoldCollisionOrEq,
               ``Obend.Crypto.Fast.Canopy.extractCanopyTranscriptCollisionOrEq,
               ``Obend.Crypto.Fast.Canopy.verifyCanopyCommitAndReduceTranscript_binding] do
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
      logInfo m!"Wave-7 CryptoGame census clean: {universal} universal theorems, 0 user closed theorems, 0 Classical.choice, 0 noncomputable"

end Obend.Tests.GameSoundnessAndDualSpineTest
