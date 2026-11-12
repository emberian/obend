module
public import Obend.Crypto.ThresholdFheAndLatticeVrf
public import Obend.Crypto.Poseidon2Goldilocks
public import Obend.Tactic.Tooth
public import Obend.AssertAxioms
meta import all Obend.Crypto.ThresholdFheAndLatticeVrf
meta import all Obend.Crypto.Poseidon2Goldilocks
meta import all Obend.Crypto.DarkBazaar
meta import all Obend.Crypto.SameOpening
meta import all Obend.Crypto.FastRing
meta import all Obend.Crypto.DualSpine
meta import all Obend.Crypto.PCS
meta import all Obend.Crypto.Transcript
meta import all Obend.Analysis.TaylorModel
meta import all Obend.Logic.SeparationFrame

-- Full bodies of the import cone, for the axiom audit and the teeth.
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
import all Obend.Core.CanonicalExtension
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
import all Obend.Core.LegacyAgreement
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
import all Obend.Crypto.ThresholdFheAndLatticeVrf

public section

/-!
# Tagged threshold decryption, packed-bit openings and the lattice VRF: witnesses and teeth

Concrete runs (`#guard`, compiled evaluation over the 32-byte `poseidon2Hash32`) of every checker
of `Obend.Crypto.ThresholdFheAndLatticeVrf`, accepted and refused; kernel-checked instances of the
list-level definitions; `#tooth` mutations of the checks the theorems rest on; the axiom audit.
-/

namespace Obend.Tests.ThresholdFheAndLatticeVrfTest

open Obend.Crypto
open Obend.Crypto.Fast
open Obend.Apps.ZkNtt
open Obend.Digest.HashBytes

def H : Hash := poseidon2Hash32
def mk1 (a : Int) : FastIntPoly 1 := ⟨#[a], rfl⟩
def mk2 (a b : Int) : FastIntPoly 2 := ⟨#[a, b], rfl⟩

-- ============================================================================
-- 1. Tagged threshold decryption: 2-of-3 Shamir over `ℤ[X]/(X²+1)`, `q = 2^48`, `t = 16`
-- ============================================================================

def pp : RlweParams := { d := 2, q := 2 ^ 48, t := 16 }
#guard pp.wfB && pp.noiseCap == 2 ^ 43

/-- Slack 1: quorums whose Lagrange coefficients at zero are integral. -/
def profA : TulvaProfile :=
  { params := pp, threshold := 2, slack := 1, encNoiseBound := 1, smudgeBound := 2 ^ 40, secBits := 40 }
/-- Slack 2: clears the denominator of the quorum `{1, 3}`. -/
def profB : TulvaProfile := { profA with slack := 2 }

def sk : FastIntPoly 2 := mk2 1 (-1)
def sharingPoly : List (FastIntPoly 2) := [sk, mk2 3 5]
def plain : FastIntPoly 2 := mk2 3 (-2)
def ct : RlweCiphertext 2 := rlweEncrypt pp sk (mk2 12345 678910) plain (mk2 1 (-1))
def ctx : List UInt8 := [1, 2, 3]

def smudgeOf : Int → FastIntPoly 2
  | 1 => mk2 (2 ^ 40) (-(2 ^ 39))
  | 2 => mk2 (-12345) (2 ^ 40)
  | _ => mk2 7 (-9)

def shareAt (context : List UInt8) (c : RlweCiphertext 2) (point : Int) : TulvaShare 2 :=
  tulvaPartialDecrypt H pp context c point (shamirShare sharingPoly point) (smudgeOf point)

def recovers (prof : TulvaProfile) (hd : prof.params.d = 2) (context : List UInt8)
    (entries : List (Int × TulvaShare 2)) : Bool :=
  match tulvaCombine H prof context (hd ▸ ct) (hd ▸ entries) with
  | .ok m => decide (hd ▸ m = plain)
  | .error _ => false

-- The Vandermonde-dual check, in the kernel: each quorum with its interpolation coefficients.
example : checkQuorumCoeffs (2 ^ 48) 2 1 [(1, 2), (2, -1)] = true := by decide
example : checkQuorumCoeffs (2 ^ 48) 2 1 [(2, 3), (3, -2)] = true := by decide
example : checkQuorumCoeffs (2 ^ 48) 2 2 [(1, 3), (3, -1)] = true := by decide
-- `{1, 3}` has no integral coefficients at slack 1, and wrong coefficients are refused.
example : checkQuorumCoeffs (2 ^ 48) 2 1 [(1, 3), (3, -1)] = false := by decide
example : checkQuorumCoeffs (2 ^ 48) 2 1 [(1, 1), (2, 1)] = false := by decide
-- Two shares do not reconstruct at threshold 3.
example : checkQuorumCoeffs (2 ^ 48) 3 1 [(1, 2), (2, -1)] = false := by decide
example : hornerInt [7, 3, 2] 5 = 7 + 3 * 5 + 2 * 25 := by decide

-- Every quorum recovers the plaintext from non-interactive tagged shares.
#guard recovers profA rfl ctx [(2, shareAt ctx ct 1), (-1, shareAt ctx ct 2)]
#guard recovers profA rfl ctx [(3, shareAt ctx ct 2), (-2, shareAt ctx ct 3)]
#guard recovers profB rfl ctx [(3, shareAt ctx ct 1), (-1, shareAt ctx ct 3)]
#guard recovers profB rfl ctx [(4, shareAt ctx ct 1), (-2, shareAt ctx ct 2)]

-- Refusals name the clause.
#guard match tulvaCombine H profA ctx ct [(1, shareAt ctx ct 1), (1, shareAt ctx ct 2)] with
       | .error .badCoefficients => true | _ => false
#guard match tulvaCombine H profA [9] ct [(2, shareAt ctx ct 1), (-1, shareAt ctx ct 2)] with
       | .error .tagMismatch => true | _ => false
#guard match tulvaCombine H { profA with smudgeBound := 0 } ctx ct
         [(2, shareAt ctx ct 1), (-1, shareAt ctx ct 2)] with
       | .error .unsmudged => true | _ => false
#guard match tulvaCombine H { profA with slack := 0 } ctx ct
         [(2, shareAt ctx ct 1), (-1, shareAt ctx ct 2)] with
       | .error .invalidParams => true | _ => false
-- `{2, 3}` at slack 2 has coefficients `(6, -4)`: weight 10, and `2 + 10·2^40 ≥ 2^43`.
#guard match tulvaCombine H profB ctx ct [(6, shareAt ctx ct 2), (-4, shareAt ctx ct 3)] with
       | .error (.noiseBudgetExceeded total cap) => total == 2 + 10 * 2 ^ 40 && cap == 2 ^ 43
       | _ => false

-- A tag is one query: the same ciphertext under another context has another tag.
#guard tulvaTag H ctx ct != tulvaTag H [9] ct
#guard tulvaTag H ctx ct != tulvaTag H ctx { ct with c0 := mk2 0 0 }
#guard (tulvaTag H ctx ct).length == 32

-- The unsmudged leak, on a scalar instance (`d = 1`, `q = 64`, `t = 4`, cap 8): one ciphertext,
-- two keys; the noise is 7 under key 0 and 9 under key 1, and exact decryption tells them apart.
def ppS : RlweParams := { d := 1, q := 64, t := 4 }
#guard rlweDecrypt ppS (mk1 0) ⟨mk1 7, mk1 2⟩ == mk1 0
#guard rlweDecrypt ppS (mk1 1) ⟨mk1 7, mk1 2⟩ == mk1 1
example : rlweDecodeSignedCoeff ppS (ppS.delta * 0 + 7) = 0 ∧
    rlweDecodeSignedCoeff ppS (ppS.delta * 0 + 9) = 0 + 1 :=
  tulva_unsmudged_boundary_oracle_leaks ppS (by decide) 0 7 9 (by decide) (by decide) (by decide)
    (by decide) (by decide)
-- An unsmudged share on `c₁ = 1` is the key share itself.
#guard (computePartialShare pp 1 sk (mk2 1 0) (mk2 0 0)).sharePoly == reducePolyMod pp.q sk

-- Flooding by counting: a shift of 2 leaves 2 of the 11 masks of `[-5, 5]` uncoupled, and with no
-- flooding the single mask is uncoupled.
example : (smudgeUncoupled 5 2).length = 2 := by decide
example : (smudgeUncoupled 5 (-3)).length = 3 := by decide
example : smudgeUncoupled 0 1 = smudgeSupport 0 := by decide
example : (smudgeUncoupled (2 ^ 40) 1).length * 2 ^ 40 ≤ 2 ^ 40 :=
  (tulva_smudge_floods_noise (noiseBound := 1) ((checkSmudgeSafe_iff 1 (2 ^ 40) 40).mp (by decide))
    1 (by decide)).1

-- ============================================================================
-- 2. Packed-bit openings
-- ============================================================================

def rows : List (List Int) := [[1, 0, 1, 0], [1, 1, 0, 0]]
def claims : List BitzClaim := [⟨5, goldOfInt 5⟩, ⟨3, goldOfInt 3⟩]

example : psiZ [1, 0, 1, 0] = 5 ∧ psiRq 16 [1, 0, 1, 0] = 5 ∧ psiRq 4 [1, 0, 1, 0] = 1 := by decide
example : checkBooleanRow [1, 0, 1, 0] = true ∧ checkBooleanRow [2, 0, 0, 0] = false := by decide
-- Why booleanity is checked over `ℤ` and not in the ciphertext ring: modulo a composite modulus
-- `c(1 - c) ≡ 0` has solutions that are not bits.
example : ((3 : Int) * (1 - 3)) % 6 = 0 ∧ (3 : Int) ≠ 0 ∧ (3 : Int) ≠ 1 := by decide

#guard bitzVerify H (2 ^ 48) 4 (bitzCommit H 4 rows) rows claims
#guard (bitzCommit H 4 rows).length == 32
-- A cell that is not a bit, though the recomposition matches the claim.
#guard !bitzVerify H (2 ^ 48) 4 (bitzCommit H 4 [[2, 0, 0, 0], [1, 1, 0, 0]])
        [[2, 0, 0, 0], [1, 1, 0, 0]] [⟨2, goldOfInt 2⟩, ⟨3, goldOfInt 3⟩]
-- A row one cell too wide: `16` is out of the 4-bit range.
#guard !bitzVerify H (2 ^ 48) 4 (bitzCommit H 4 [[0, 0, 0, 0, 1], [1, 1, 0, 0]])
        [[0, 0, 0, 0, 1], [1, 1, 0, 0]] [⟨16, goldOfInt 16⟩, ⟨3, goldOfInt 3⟩]
-- The two rings disagree.
#guard !bitzVerify H (2 ^ 48) 4 (bitzCommit H 4 rows) rows [⟨5, goldOfInt 6⟩, ⟨3, goldOfInt 3⟩]
-- Another matrix under the same commitment.
#guard !bitzVerify H (2 ^ 48) 4 (bitzCommit H 4 rows) [[1, 0, 1, 0], [0, 0, 1, 0]]
        [⟨5, goldOfInt 5⟩, ⟨4, goldOfInt 4⟩]
-- A ring too small to hold the range.
#guard !bitzVerify H 8 4 (bitzCommit H 4 rows) rows claims
-- The width is committed.
#guard bitzCommit H 4 rows != bitzCommit H 5 rows
-- The `SameOpening` witness the rows open.
#guard (bitzOrderWitness [1, 0, 1, 0] [1, 1, 0, 0] GoldilocksExt2.zero).qty == 5 &&
       (bitzOrderWitness [1, 0, 1, 0] [1, 1, 0, 0] GoldilocksExt2.zero).total == 3

-- ============================================================================
-- 3. The lattice VRF, on a toy matrix with a planted kernel
-- ============================================================================

/-- One row `(1, 1, 0)`: the image is `z₁ + z₂`, so Module-SIS for this `A` is broken on purpose. -/
def lavPP : LavParams 2 :=
  { q := 97, p := 8, beta := 2, cols := 3, outRows := 2, A := [[mk2 1 0, mk2 1 0, mk2 0 0]] }

def zKey : List (FastIntPoly 2) := [mk2 1 0, mk2 0 0, mk2 1 1]
/-- Another short preimage of the same public key. -/
def zTwin : List (FastIntPoly 2) := [mk2 0 0, mk2 1 0, mk2 1 1]
def zOther : List (FastIntPoly 2) := [mk2 0 1, mk2 0 1, mk2 0 0]
def zLong : List (FastIntPoly 2) := [mk2 3 0, mk2 0 0, mk2 1 1]

def keyDigest : List UInt8 := lavKeyDigest H (lavImage lavPP zKey)
def ringKeys : List (List UInt8) := [keyDigest, lavKeyDigest H (lavImage lavPP zOther)]
def ringD : List UInt8 := lavRingDigest H ringKeys

def evalAt (epoch slot : Nat) (z : List (FastIntPoly 2)) : List UInt8 × LavProof 2 :=
  lavEval H lavPP ringD epoch slot z

#guard keyDigest.length == 32 && (evalAt 0 5 zKey).1.length == 32
-- Completeness, and determinism of the value.
#guard lavVerify H lavPP keyDigest ringD 0 5 (evalAt 0 5 zKey).1 (evalAt 0 5 zKey).2
#guard (evalAt 0 5 zKey).1 == (evalAt 0 5 zKey).1
-- Domain separation: another slot, another epoch, another ring.
#guard !lavVerify H lavPP keyDigest ringD 0 6 (evalAt 0 5 zKey).1 (evalAt 0 5 zKey).2
#guard !lavVerify H lavPP keyDigest ringD 1 5 (evalAt 0 5 zKey).1 (evalAt 0 5 zKey).2
#guard !lavVerify H lavPP keyDigest (lavRingDigest H [keyDigest]) 0 5 (evalAt 0 5 zKey).1
        (evalAt 0 5 zKey).2
#guard (evalAt 0 5 zKey).1 != (evalAt 0 6 zKey).1 && (evalAt 0 5 zKey).1 != (evalAt 1 5 zKey).1
#guard lavInput [1] 2 3 != lavInput [1] 3 2 && lavInput [] 1 0 != lavInput [1] 0 0
-- The norm bound: a witness of norm 3 against `β = 2`.
#guard !lavVerify H lavPP (lavKeyDigest H (lavImage lavPP zLong)) ringD 0 5 (evalAt 0 5 zLong).1
        (evalAt 0 5 zLong).2
-- A tampered pre-output, a value under another key.
#guard !lavVerify H lavPP keyDigest ringD 0 5 (evalAt 0 5 zKey).1
        { (evalAt 0 5 zKey).2 with y := zKey }
#guard !lavVerify H lavPP (lavKeyDigest H (lavImage lavPP zOther)) ringD 0 5 (evalAt 0 5 zKey).1
        (evalAt 0 5 zKey).2
-- What the uniqueness theorem says, seen from the broken side: the planted kernel vector lets one
-- key digest equivocate, with two accepted values at one input.
#guard lavImage lavPP zKey == lavImage lavPP zTwin
#guard lavVerify H lavPP keyDigest ringD 0 5 (evalAt 0 5 zTwin).1 (evalAt 0 5 zTwin).2
#guard (evalAt 0 5 zKey).1 != (evalAt 0 5 zTwin).1
-- Ring tickets: the index names the key.
#guard lavRingVerify H lavPP ringKeys 0 5 ⟨0, (evalAt 0 5 zKey).1, (evalAt 0 5 zKey).2⟩
#guard lavRingVerify H lavPP ringKeys 0 5 ⟨1, (evalAt 0 5 zOther).1, (evalAt 0 5 zOther).2⟩
#guard !lavRingVerify H lavPP ringKeys 0 5 ⟨1, (evalAt 0 5 zKey).1, (evalAt 0 5 zKey).2⟩
#guard !lavRingVerify H lavPP ringKeys 0 5 ⟨2, (evalAt 0 5 zKey).1, (evalAt 0 5 zKey).2⟩

-- ============================================================================
-- 4. The auction machine: accepted runs, and each refusal
-- ============================================================================

def cfg (budget : Nat) : AuctionConfig :=
  { tulva := profA, lav := lavPP, width := 2, ringKeys := ringKeys, queryBudget := budget }

def bidRows : List (List Int) := [[1, 1], [0, 1]]
def bidClaims : List BitzClaim := [⟨3, goldOfInt 3⟩, ⟨2, goldOfInt 2⟩]

/-- A turn: the leader ticket for `ticketEpoch`, an encryption of `(3, 2)` with mask `a`, the
quorum `{1, 2}` of tagged shares, and the packed opening of `(3, 2)`. -/
def mkTurn (budget ticketEpoch slot : Nat) (context : List UInt8) (a : Int)
    (turnClaims : List BitzClaim := bidClaims) : AuctionTurn (cfg budget) :=
  let c : RlweCiphertext 2 := rlweEncrypt pp sk (mk2 a (a + 1)) (mk2 3 2) (mk2 (-1) 1)
  { slot := slot
    ticket := ⟨0, (evalAt ticketEpoch slot zKey).1, (evalAt ticketEpoch slot zKey).2⟩
    context := context
    ct := c
    entries := [(2, shareAt context c 1), (-1, shareAt context c 2)]
    commitment := bitzCommit H 2 bidRows
    rows := bidRows
    claims := turnClaims }

def runEpoch (budget : Nat) (turns : List (AuctionTurn (cfg budget))) : Option Nat :=
  (auctionRun H (cfg budget) .init turns).map (·.epoch)

-- Two batches, two epochs, four partial decryptions against a budget of four.
#guard runEpoch 4 [mkTurn 4 0 5 [1] 111, mkTurn 4 1 9 [2] 222] == some 2
#guard (auctionRun H (cfg 4) .init [mkTurn 4 0 5 [1] 111, mkTurn 4 1 9 [2] 222]).map
        (fun st => (st.queriesUsed, st.usedTags.length, st.leaders.length)) == some (4, 2, 2)
-- The same query decrypted twice: refused, though its ticket is good for the new epoch.
#guard runEpoch 4 [mkTurn 4 0 5 [1] 111, mkTurn 4 1 9 [1] 111] == none
-- The budget of released partial decryptions.
#guard runEpoch 3 [mkTurn 3 0 5 [1] 111, mkTurn 3 1 9 [2] 222] == none
#guard runEpoch 3 [mkTurn 3 0 5 [1] 111] == some 1
-- A leader ticket of an earlier epoch.
#guard runEpoch 4 [mkTurn 4 0 5 [1] 111, mkTurn 4 0 5 [2] 222] == none
-- Claims that are not the decrypted plaintext (a consistent opening of another value).
#guard runEpoch 4 [mkTurn 4 0 5 [1] 111 [⟨3, goldOfInt 3⟩, ⟨1, goldOfInt 1⟩]] == none

-- ============================================================================
-- 5. Teeth
-- ============================================================================

-- Accepting any interpolation coefficients breaks reconstruction.
#tooth Obend.Crypto.tulvaCombine_recovers_plaintext by mutation
  Obend.Crypto.checkQuorumCoeffs := fun _ _ _ _ => true

-- Counting no noise against the cap breaks the decoding bound.
#tooth Obend.Crypto.tulvaCombine_recovers_plaintext by mutation
  Obend.Crypto.tulvaNoiseTotal := fun _ _ _ => 0

-- Without the drowning ratio there is no flooding bound.
#tooth Obend.Crypto.tulva_smudge_floods_noise by mutation
  Obend.Crypto.SmudgeSafe := fun _ _ _ => True

-- Without booleanity there is no range.
#tooth Obend.Crypto.bitz_sameOpening_and_free_range_sound by mutation
  Obend.Crypto.checkBooleanRow := fun _ => true

-- A recomposition that does not reduce modulo `q` is not the `ℤ_q` image.
#tooth Obend.Crypto.bitz_sameOpening_and_free_range_sound by mutation
  Obend.Crypto.psiRq := fun _ row => Obend.Crypto.psiZ row

-- A commitment that drops the rows binds nothing.
#tooth Obend.Crypto.bitzCommit_binding by mutation
  Obend.Crypto.encodeIntRows := fun _ => []

-- Without the norm bound the difference of two witnesses is not short.
#tooth Obend.Crypto.lav_unique_output_or_msisBreak by mutation
  Obend.Crypto.lavShort := fun _ _ => true

-- An input that drops the ring, epoch and slot separates nothing.
#tooth Obend.Crypto.lavSeed_binds by mutation
  Obend.Crypto.lavInput := fun _ _ _ => []

-- A ring check that accepts every ticket gives no uniqueness.
#tooth Obend.Crypto.lav_T_uniqueness by mutation
  Obend.Crypto.lavRingVerify := fun _ _ _ _ _ _ _ => true

-- A turn check that accepts everything keeps neither the budget nor tag freshness.
#tooth Obend.Crypto.auctionRun_safe by mutation
  Obend.Crypto.auctionTurnCheck := fun _ _ _ _ => true

-- ============================================================================
-- 6. Axiom audit
-- ============================================================================

#assert_axioms_tree

-- No definition of the module (the checkers, the combiner, the evaluator, the machine) is
-- noncomputable, and none mentions a `Classical` constant in its body: every case split that
-- computes goes through a `Decidable` instance. (Proofs carried inside definitions, such as the
-- range proof of `goldOfInt`, are not computation and are covered by the audit above.)
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut seen := 0
  for (name, info) in env.constants.map₁.toList do
    let some idx := env.getModuleIdxFor? name | continue
    unless env.header.moduleNames[idx.toNat]? == some `Obend.Crypto.ThresholdFheAndLatticeVrf do continue
    let .defnInfo v := info | continue
    unless v.safety == .safe do continue
    seen := seen + 1
    if Lean.isNoncomputable env name then
      throwError m!"noncomputable definition: {name}"
    for c in v.value.getUsedConstantsAsSet.toList do
      if c.getRoot == `Classical then
        throwError m!"definition {name} computes through {c}"
  if seen == 0 then throwError "no definitions of the module were visible to the audit"

end Obend.Tests.ThresholdFheAndLatticeVrfTest
end
