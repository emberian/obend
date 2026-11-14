module
public import Obend.Crypto.Poseidon2Goldilocks
public import Obend.Crypto.DarkBazaar
public import Obend.Tactic.Tooth
public import Obend.AssertAxioms
meta import all Obend.Crypto.Poseidon2Goldilocks
meta import all Obend.Crypto.DarkBazaar
meta import all Obend.Crypto.SameOpening
meta import all Obend.Crypto.FastRing
meta import all Obend.Crypto.DualSpine
meta import all Obend.Crypto.PCS
meta import all Obend.Crypto.Transcript
meta import all Obend.Analysis.TaylorModel
meta import all Obend.Logic.SeparationFrame

-- Full bodies are needed for the imported-tree axiom audit (`#assert_axioms_tree`).
import all Obend.Analysis.Diff
import all Obend.Analysis.Flowpipe
import all Obend.Analysis.RealAnalysis
import all Obend.Analysis.TaylorModel
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
import all Obend.Crypto.DarkBazaar
import all Obend.Crypto.DualSpine
import all Obend.Crypto.FastRing
import all Obend.Crypto.Multilinear
import all Obend.Crypto.PCS
import all Obend.Crypto.Poseidon2Goldilocks
import all Obend.Crypto.SameOpening
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
import all Obend.Fold
import all Obend.Hardware.Compiler
import all Obend.Hardware.HDL
import all Obend.Hardware.Types
import all Obend.Intention
import all Obend.Judge.Class
import all Obend.Judge.Clearing
import all Obend.Judge.Computational
import all Obend.Judge.Lrat
import all Obend.Kind
import all Obend.Law.Claim
import all Obend.Law.Contract
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
import all Obend.Ledger.Book
import all Obend.Ledger.Floors
import all Obend.Ledger.Register
import all Obend.Ledger.Seat
import all Obend.Logic.Claim
import all Obend.Logic.Frame
import all Obend.Logic.Ground
import all Obend.Logic.LateBinding
import all Obend.Logic.Obligation
import all Obend.Logic.Program
import all Obend.Logic.Receipt
import all Obend.Logic.Rewrite
import all Obend.Logic.SeparationFrame
import all Obend.Receipt
import all Obend.Receipt.Merkle
import all Obend.Run.Control
import all Obend.Run.Fold
import all Obend.Run.Fork
import all Obend.Run.Proofs.Control
import all Obend.Run.Proofs.Invariant
import all Obend.Run.Proofs.Shared
import all Obend.Run.Runner
import all Obend.Run.Shared
import all Obend.Run.Spec
import all Obend.Slot
import all Obend.Slot.Core4
import all Obend.Slot.Integrity
import all Obend.Slot.Proofs.Protocol
import all Obend.Slot.Proofs.ProtocolTyping
import all Obend.Slot.Protocol
import all Obend.Slot.Selection
import all Obend.Slot.World
import all Obend.Spec.C4
import all Obend.Spec.DataWire
import all Obend.Spec.Proofs.C4
import all Obend.Tactic.Cases
import all Obend.Tactic.MonadicReduction
import all Obend.Tactic.Tooth
import all Obend.Category.Refines
import all Obend.Crypto.GameSoundness
import all Obend.Consensus.Simplex
import all Obend.Consensus.SimplexProtocol
import all Obend.Polis.CapTP
import all Obend.Vault.Mandate

public section

/-!
# `tests/metasystem/Poseidon2AndDarkBazaarTest.lean` — Wave-5 Lane C7 Verification & `#tooth` Suite

Exercises:
1. `Obend.Crypto.Poseidon2Goldilocks`:
   - $x \mapsto x^7$ S-box & exact inverse $d_{\text{inv}} = 10540996611094048183$ over `Goldilocks`,
   - Full Width-12 (`R_F = 8, R_P = 22`) `Poseidon2` permutation & exact inverse roundtrip (`poseidon2Perm12Inv`),
   - Canonical `< 2^56` limb framing, `10*1` sponge padding, and 32-byte `poseidon2Hash32 : HashBytes.Hash` KATs.
2. `Obend.Crypto.DarkBazaar`:
   - 4-trader RLWE-encrypted batch auction welding `TaylorModel` nonlinear enclosures, `Sable` quantized
     `Goldilocks` inference, negacyclic RLWE order-book aggregation, smudged 3-of-3 threshold decryption,
     salted `SameOpening` zero-gap KKT clearing, and zero-sum `ConservedValue` settlement across multi-epoch
     `stepDarkBazaarEpoch` traces,
   - Deterministic refusals on noise-budget overflow, zero smudging, malformed non-canonical shares, and
     epoch-nullifier replay.
3. Six `#tooth` mutation kills + `#assert_axioms_tree` + `0 noncomputable` / `0` closed-theorem census.
-/

namespace Obend.Tests.Poseidon2AndDarkBazaarTest

open Obend.Crypto
open Obend.Crypto.Fast
open Obend.Apps.ZkNtt
open Obend.Analysis
open Obend.Judge
open Obend.Ledger
open Obend.Logic

-- ============================================================================
-- 1. Width-12 Goldilocks `Poseidon2` S-Box, Permutation & 256-Bit Sponge KATs
-- ============================================================================

#guard poseidon2DInv == 10540996611094048183
#guard (7 * poseidon2DInv) % (goldilocksPrime - 1) == 1

-- S-box roundtrip across boundary & interior Goldilocks elements
#guard [0, 1, 2, 42, 999999999, goldilocksPrime - 2, goldilocksPrime - 1].all fun n =>
  let x := Goldilocks.ofNat n
  sbox7Inv (sbox7 x) == x && sbox7 (sbox7Inv x) == x

-- Non-trivial Width-12 Poseidon2 state roundtrip (`poseidon2Perm12Inv ∘ poseidon2Perm12 = id`)
def samplePermState : Poseidon2State12 :=
  ⟨⟨Goldilocks.ofNat 17, Goldilocks.ofNat 1017, Goldilocks.ofNat 2017, Goldilocks.ofNat 3017⟩,
   ⟨Goldilocks.ofNat 4017, Goldilocks.ofNat 5017, Goldilocks.ofNat 6017, Goldilocks.ofNat 7017⟩,
   ⟨Goldilocks.ofNat 8017, Goldilocks.ofNat 9017, Goldilocks.ofNat 10017, Goldilocks.ofNat 11017⟩⟩

#guard poseidon2Perm12 samplePermState != samplePermState
#guard poseidon2Perm12Inv (poseidon2Perm12 samplePermState) == samplePermState
#guard poseidon2Perm12 (poseidon2Perm12Inv samplePermState) == samplePermState

-- Canonical 56-bit limb framing & `10*1` sponge padding roundtrips
def sampleBytesA : List UInt8 := [0x00, 0x01, 0x7f, 0x80, 0xff, 0x42, 0x13, 0x37, 0x99]
#guard limbs56ToBytes (bytesToLimbs56 sampleBytesA) == sampleBytesA
#guard limbs56ToBytes (bytesToLimbs56 [0x00]) == [0x00]
#guard bytesToLimbs56 [0x00] != bytesToLimbs56 [0x00, 0x00]

def sampleLimbs9 : List Goldilocks := (List.range 9).map Goldilocks.ofNat
#guard (poseidon2Pad sampleLimbs9).length % 8 == 0
#guard poseidon2Unpad (poseidon2Pad sampleLimbs9) == some sampleLimbs9

-- 32-byte (256-bit) `poseidon2Hash32 : HashBytes.Hash` KATs & domain separation
def hashEmpty : List UInt8 := poseidon2Hash32 []
def hashZero1 : List UInt8 := poseidon2Hash32 [0x00]
def hashZero2 : List UInt8 := poseidon2Hash32 [0x00, 0x00]
def hashOne1  : List UInt8 := poseidon2Hash32 [0x01]
def hashLong  : List UInt8 := poseidon2Hash32 ((List.range 65).map UInt8.ofNat)

#guard hashEmpty.length == 32
#guard hashZero1.length == 32
#guard hashLong.length == 32
#guard hashEmpty != hashZero1
#guard hashZero1 != hashZero2
#guard hashZero1 != hashOne1
#guard hashOne1 != hashLong

-- ============================================================================
-- 2. Pillar-4 `DarkBazaar` 4-Trader RLWE Encrypted Batch Auction Clearing
-- ============================================================================

def mkPoly4 (c0 c1 c2 c3 : Int) : FastIntPoly 4 :=
  Sized.ofFn fun i =>
    match i.val with
    | 0 => c0
    | 1 => c1
    | 2 => c2
    | _ => c3

-- Stage 1: Certified nonlinear quadratic `TaylorModel` utility/cost enclosures over `[-1/2, 1/2]`
def halfDom : Obend.Analysis.Interval :=
  { lo := CanonicalRat.mk (-1) 2, hi := CanonicalRat.mk 1 2 }
def centRem : Obend.Analysis.Interval :=
  { lo := CanonicalRat.mk (-1) 100, hi := CanonicalRat.mk 1 100 }

def utilCert0 : TraderUtilityCert where
  tm := { coeffs := [5, 1, -1], center := 0, domain := halfDom, rem := centRem }
  feature := CanonicalRat.mk 1 5
  tickScale := 10
  side := .bid
  submittedTotal := 48

def utilCert1 : TraderUtilityCert where
  tm := { coeffs := [2, 1, -1], center := 0, domain := halfDom, rem := centRem }
  feature := 0
  tickScale := 10
  side := .bid
  submittedTotal := 18

def utilCert2 : TraderUtilityCert where
  tm := { coeffs := [CanonicalRat.mk 14 5, 1, 1], center := 0, domain := halfDom, rem := centRem }
  feature := CanonicalRat.mk 1 10
  tickScale := 10
  side := .ask
  submittedTotal := 30

def utilCert3 : TraderUtilityCert where
  tm := { coeffs := [2, 1, 1], center := 0, domain := halfDom, rem := centRem }
  feature := CanonicalRat.mk 1 10
  tickScale := 10
  side := .ask
  submittedTotal := 22

#guard [utilCert0, utilCert1, utilCert2, utilCert3].all checkUtilityEnclosure

-- Stage 2: Overflow-free quantized `Sable` linear inference matching `Goldilocks` witness totals
def sableWit0 : SableLinearWitness 4 := ⟨mkPoly4 10 4 (-2) 6, mkPoly4 3 3 1 1, 2⟩   -- 48
def sableWit1 : SableLinearWitness 4 := ⟨mkPoly4 5 3 2 (-1), mkPoly4 2 2 1 0, 0⟩    -- 18
def sableWit2 : SableLinearWitness 4 := ⟨mkPoly4 7 5 (-1) 2, mkPoly4 3 1 2 2, 2⟩    -- 30
def sableWit3 : SableLinearWitness 4 := ⟨mkPoly4 6 4 1 (-2), mkPoly4 3 1 2 1, 0⟩    -- 22

#guard (sableDotGoldilocks sableWit0.weights sableWit0.features sableWit0.bias).val == 48
#guard (sableDotGoldilocks sableWit1.weights sableWit1.features sableWit1.bias).val == 18
#guard (sableDotGoldilocks sableWit2.weights sableWit2.features sableWit2.bias).val == 30
#guard (sableDotGoldilocks sableWit3.weights sableWit3.features sableWit3.bias).val == 22

-- Stage 3 & 4: Cyclotomic RLWE (`d = 4, q = 2^54, t = 256`) + Smudged 3-of-3 Threshold Decryption
def bazaarRlweParams : RlweParams := { d := 4, q := 2 ^ 54, t := 256 }
#guard bazaarRlweParams.wfB == true
#guard bazaarRlweParams.noiseCap == 2 ^ 45

def bazaarThresholdCfg : ThresholdDecryptConfig where
  params := bazaarRlweParams
  quorum := 3
  encNoiseBound := 8
  smudgeBound := 8 * (2 ^ 40)
  secBits := 40

-- 3 guardian secret-key shares (`sk = sk0 + sk1 + sk2`)
def guardianSk1 : FastIntPoly 4 := mkPoly4 1 (-1) 0 1
def guardianSk2 : FastIntPoly 4 := mkPoly4 0 1 (-1) 1
def guardianSk3 : FastIntPoly 4 := mkPoly4 (-1) 1 1 0
def aggregateSk : FastIntPoly 4 := sumPlainBatch 4 [guardianSk1, guardianSk2, guardianSk3]

-- Plaintext signed order vectors (`[+4,+48,0,0]`, `[+2,+18,0,0]`, `[-3,-30,0,0]`, `[-2,-22,0,0]`)
def plainOrd0 : FastIntPoly 4 := orderSignedPlainVec 4 .bid 4 48
def plainOrd1 : FastIntPoly 4 := orderSignedPlainVec 4 .bid 2 18
def plainOrd2 : FastIntPoly 4 := orderSignedPlainVec 4 .ask 3 30
def plainOrd3 : FastIntPoly 4 := orderSignedPlainVec 4 .ask 2 22

def encOrd0 : RlweCiphertext 4 :=
  rlweEncrypt bazaarRlweParams aggregateSk (mkPoly4 101 202 303 404) plainOrd0 (mkPoly4 2 (-1) 1 0)
def encOrd1 : RlweCiphertext 4 :=
  rlweEncrypt bazaarRlweParams aggregateSk (mkPoly4 505 606 707 808) plainOrd1 (mkPoly4 (-1) 2 0 (-1))
def encOrd2 : RlweCiphertext 4 :=
  rlweEncrypt bazaarRlweParams aggregateSk (mkPoly4 909 111 222 333) plainOrd2 (mkPoly4 1 1 (-2) 1)
def encOrd3 : RlweCiphertext 4 :=
  rlweEncrypt bazaarRlweParams aggregateSk (mkPoly4 444 555 666 777) plainOrd3 (mkPoly4 (-1) 1 1 (-2))

def encryptedBook : List (RlweCiphertext 4) := [encOrd0, encOrd1, encOrd2, encOrd3]
def aggregatedBookCt : RlweCiphertext 4 := rlweAggregateBatch bazaarRlweParams encryptedBook

-- Smudged partial decryption shares (`2^40`-scale drowning noise!)
def smudge1 : FastIntPoly 4 := mkPoly4 (3 * (2 ^ 40)) (-(2 * (2 ^ 40))) (2 ^ 40) 0
def smudge2 : FastIntPoly 4 := mkPoly4 (-(2 ^ 40)) (4 * (2 ^ 40)) (-(3 * (2 ^ 40))) (2 ^ 40)
def smudge3 : FastIntPoly 4 := mkPoly4 (2 * (2 ^ 40)) (-(2 ^ 40)) (2 * (2 ^ 40)) (-(4 * (2 ^ 40)))

def guardianShares : List (PartialDecryptionShare 4) :=
  [ computePartialShare bazaarRlweParams 1 guardianSk1 aggregatedBookCt.c1 smudge1
  , computePartialShare bazaarRlweParams 2 guardianSk2 aggregatedBookCt.c1 smudge2
  , computePartialShare bazaarRlweParams 3 guardianSk3 aggregatedBookCt.c1 smudge3 ]

#guard match thresholdDecryptChecked bazaarThresholdCfg aggregatedBookCt guardianShares with
       | .ok dec => dec == mkPoly4 1 14 0 0
       | .error _ => false

-- Stage 5: Salted `canopyAjtaiDualPCS` commitments + zero-duality-gap KKT clearing (`price = 11`)
def testAjtaiParams : AjtaiParams where
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

def salt0 : GoldilocksExt2 := ⟨Goldilocks.ofNat 0x1111222233334444, Goldilocks.ofNat 0x5555666677778888⟩
def salt1 : GoldilocksExt2 := ⟨Goldilocks.ofNat 0x9999aaaabbbbcccc, Goldilocks.ofNat 0xddddeeeeffff0001⟩
def salt2 : GoldilocksExt2 := ⟨Goldilocks.ofNat 0x123456789abcdef0, Goldilocks.ofNat 0x0fedcba987654321⟩
def salt3 : GoldilocksExt2 := ⟨Goldilocks.ofNat 0x2468ace013579bdf, Goldilocks.ofNat 0x13579bdf2468ace0⟩

def ordWit0 : OrderBitWitness := ⟨[false, false, true], [false, false, false, false, true, true], salt0⟩ -- 4, 48
def ordWit1 : OrderBitWitness := ⟨[false, true], [false, true, false, false, true], salt1⟩               -- 2, 18
def ordWit2 : OrderBitWitness := ⟨[true, true], [false, true, true, true, true], salt2⟩                  -- 3, 30
def ordWit3 : OrderBitWitness := ⟨[false, true], [false, true, true, false, true], salt3⟩                -- 2, 22

def commSpec0 : CommittedOrderSpec := commitPrivateOrder testAjtaiParams 10 .bid 8 salt0 ordWit0
def commSpec1 : CommittedOrderSpec := commitPrivateOrder testAjtaiParams 11 .bid 8 salt1 ordWit1
def commSpec2 : CommittedOrderSpec := commitPrivateOrder testAjtaiParams 12 .ask 8 salt2 ordWit2
def commSpec3 : CommittedOrderSpec := commitPrivateOrder testAjtaiParams 13 .ask 8 salt3 ordWit3

def bazaarMarket : Market := { currency := 1, goods := 2, epsilon := 0 }

def bazaarTransfers : List ResourcePosting :=
  [ { source := 12, destination := 10, asset := 2, amount := 3 }
  , { source := 10, destination := 12, asset := 1, amount := 33 }
  , { source := 13, destination := 10, asset := 2, amount := 1 }
  , { source := 10, destination := 13, asset := 1, amount := 11 } ]

def bazaarKktCert : Certificate :=
  { price := 11, potentials := (1, 0), slacks := [2, 2, 0, 0] }

def bazaarEpoch1 : DarkBazaarEpochBatch 4 bazaarThresholdCfg where
  epochNullifier := 1001
  utilityCerts := [utilCert0, utilCert1, utilCert2, utilCert3]
  sableWitnesses := [sableWit0, sableWit1, sableWit2, sableWit3]
  encryptedOrders := encryptedBook
  thresholdShares := guardianShares
  openingQuery :=
    { market := bazaarMarket
      ajtaiParams := testAjtaiParams
      noiseBound := bazaarThresholdCfg.encNoiseBound
      smudgeBound := bazaarThresholdCfg.smudgeBound
      secBits := bazaarThresholdCfg.secBits
      committedOrders := [commSpec0, commSpec1, commSpec2, commSpec3] }
  openingWitness :=
    { orderWitnesses := [ordWit0, ordWit1, ordWit2, ordWit3]
      transfers := bazaarTransfers
      kktCert := bazaarKktCert }

-- Full 5-stage `verifyAndClearDarkBazaarEpoch` execution & `ConservedValue` zero-sum verification
#guard match verifyAndClearDarkBazaarEpoch bazaarThresholdCfg bazaarEpoch1 with
       | .ok out =>
         out.decryptedBook == mkPoly4 1 14 0 0 &&
         sumDeltas out.currencySettlement.entries == 0 &&
         sumDeltas out.goodsSettlement.entries == 0 &&
         deltaAt out.currencySettlement.entries 10 == -44 &&
         deltaAt out.currencySettlement.entries 12 == 33 &&
         deltaAt out.currencySettlement.entries 13 == 11 &&
         deltaAt out.goodsSettlement.entries 10 == 4 &&
         deltaAt out.goodsSettlement.entries 12 == -3 &&
         deltaAt out.goodsSettlement.entries 13 == -1
       | .error _ => false

-- Multi-epoch `stepDarkBazaarEpoch` trace + replay-nullifier & budget-exhaustion refusal checks
def bazaarEpoch2 : DarkBazaarEpochBatch 4 bazaarThresholdCfg :=
  { bazaarEpoch1 with epochNullifier := 1002 }

#guard match stepDarkBazaarEpoch bazaarThresholdCfg (DarkBazaarState.init 6) bazaarEpoch1 with
       | .ok (st1, _) =>
         -- Replaying epoch 1001 is deterministically refused
         (match stepDarkBazaarEpoch bazaarThresholdCfg st1 bazaarEpoch1 with
          | .error (.nullifierAlreadySpent 1001) => true
          | _ => false) &&
         -- Fresh epoch 1002 succeeds and preserves zero-sum cumulative settlements
         match stepDarkBazaarEpoch bazaarThresholdCfg st1 bazaarEpoch2 with
         | .ok (st2, _) =>
           st2.epoch == 2 &&
           st2.remainingDecryptionBudget == 0 &&
           sumDeltas st2.cumulativeCurrency.entries == 0 &&
           sumDeltas st2.cumulativeGoods.entries == 0 &&
           deltaAt st2.cumulativeCurrency.entries 10 == -88 &&
           deltaAt st2.cumulativeGoods.entries 10 == 8 &&
           -- Third epoch after budget depletion is deterministically refused
           (match stepDarkBazaarEpoch bazaarThresholdCfg st2 { bazaarEpoch1 with epochNullifier := 1003 } with
            | .error (.decryptionBudgetExhausted 3 0) => true
            | _ => false)
         | .error _ => false
       | .error _ => false

-- Deterministic threshold decryption refusals (noise overflow, zero smudging, non-canonical share)
def overflowCfg : ThresholdDecryptConfig :=
  { bazaarThresholdCfg with smudgeBound := 16 * (2 ^ 40) }

#guard match thresholdDecryptChecked overflowCfg aggregatedBookCt guardianShares with
       | .error (.noiseBudgetExceeded tot cap) =>
         tot == 8 + 3 * (16 * (2 ^ 40)) && cap == 2 ^ 45
       | _ => false

def unsmudgedCfg : ThresholdDecryptConfig :=
  { bazaarThresholdCfg with smudgeBound := 0 }

#guard match thresholdDecryptChecked unsmudgedCfg aggregatedBookCt guardianShares with
       | .error .unsmudgedThresholdNoise => true
       | _ => false

def malformedShares : List (PartialDecryptionShare 4) :=
  { guardianId := 1, sharePoly := mkPoly4 (2 ^ 54) 0 0 0 } :: guardianShares.drop 1

#guard match thresholdDecryptChecked bazaarThresholdCfg aggregatedBookCt malformedShares with
       | .error (.nonCanonicalShare 1) => true
       | _ => false

-- ============================================================================
-- 3. Six `#tooth` Mutation Kills Across `Poseidon2Goldilocks` & `DarkBazaar`
-- ============================================================================

-- Tooth 1: Replacing $x^7$ with identity breaks `sbox7_bijective` (`x = 2 => 2^d_inv != 2`)
#tooth Obend.Crypto.sbox7_bijective by mutation
  Obend.Crypto.sbox7 := fun x => x

-- Tooth 2: Skipping `Poseidon2` external/internal rounds (`runRounds`) breaks `poseidon2Perm12_bijective`
#tooth Obend.Crypto.poseidon2Perm12_bijective by mutation
  Obend.Crypto.runRounds := fun _ _ s => s

-- Tooth 3: Dropping `10*1` boundary marker breaks `poseidon2Pad_injective`
#tooth Obend.Crypto.poseidon2Pad_injective by mutation
  Obend.Crypto.poseidon2Pad := fun _ => []

-- Tooth 4: Dropping second ciphertext summand breaks `rlweAdd_decrypts_to_sum`
#tooth Obend.Crypto.rlweAdd_decrypts_to_sum by mutation
  Obend.Crypto.rlweAdd := fun _ ct1 _ => ct1

-- Tooth 5: Bypassing `checkSmudgeSafe` breaks `thresholdDecrypt_exact_under_noise_cap`
#tooth Obend.Crypto.thresholdDecrypt_exact_under_noise_cap by mutation
  Obend.Crypto.checkSmudgeSafe := fun _ _ _ => true

-- Tooth 6: Emitting zero settlement instead of `netFlow` transfers breaks `darkBazaar_sable_rlwe_smudge_clearing_conserves`
#tooth Obend.Crypto.darkBazaar_sable_rlwe_smudge_clearing_conserves by mutation
  Obend.Crypto.settleAssetConserved := fun _ _ => ConservedValue.zero

-- ============================================================================
-- 4. Imported-Tree Axiom Audit, `0 noncomputable` & `0` Closed-Theorem Census
-- ============================================================================

#assert_axioms_tree

open Lean Elab Command in
run_cmd do
  let env ← getEnv
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

end Obend.Tests.Poseidon2AndDarkBazaarTest
end
