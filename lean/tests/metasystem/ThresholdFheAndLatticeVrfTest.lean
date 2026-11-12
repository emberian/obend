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
  { q := 257, p := 8, beta := 2, cMax := 2, gamma := 8, cols := 3, outRows := 2,
    A := List.replicate 3 [mk2 1 0, mk2 1 0, mk2 0 0] }

def zKey : List (FastIntPoly 2) := [mk2 1 0, mk2 0 0, mk2 1 1]
/-- Another short preimage of the same public key. -/
def zTwin : List (FastIntPoly 2) := [mk2 0 0, mk2 1 0, mk2 1 1]
def zOther : List (FastIntPoly 2) := [mk2 0 1, mk2 0 1, mk2 0 0]
def zLong : List (FastIntPoly 2) := [mk2 3 0, mk2 0 0, mk2 1 1]

def keyDigest : List UInt8 := lavKeyDigest H (lavImage lavPP zKey)
def ringKeys : List (List UInt8) := [keyDigest, lavKeyDigest H (lavImage lavPP zOther)]
def ringD : List UInt8 := lavRingDigest H ringKeys

def lavMask : List (FastIntPoly 2) := [mk2 (-1) 1, mk2 1 (-1), mk2 (-1) (-1)]

def evalAt (epoch slot : Nat) (z : List (FastIntPoly 2)) : List UInt8 × LavProof 2 :=
  (lavEval H lavPP ringD epoch slot z lavMask).getD ([], ⟨[], [], [], [], []⟩)

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
        { (evalAt 0 5 zKey).2 with u := zKey }
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

-- A2: parameter non-vacuity, exact Shamir coupling, and bonded release.
example : ∃ p : LavParams 1, p.p = 2 ∧ p.outRows = 1 ∧ p.wfB = true ∧ IsEmpty (MsisBreakWitness p) :=
  lav_msisBreak_nonvacuous 2 1
def rigidLav : LavParams 1 := ⟨37, 2, 1, 2, 4, 1, 1, [[mk1 1]]⟩
#guard rigidLav.wfB
#guard let ev := (lavEval H rigidLav [] 0 0 [mk1 1] [mk1 (-1)]).getD ([], ⟨[], [], [], [], []⟩)
  lavVerify H rigidLav (lavKeyDigest H ev.2.pk) [] 0 0 ev.1 ev.2
#guard lavPP.wfB
#guard !( { lavPP with q := 64 } : LavParams 2).wfB
#guard !( { lavPP with q := 2 } : LavParams 2).wfB
#guard !( { lavPP with A := [] } : LavParams 2).wfB
#guard !( { lavPP with cols := 0 } : LavParams 2).wfB
#guard !( { lavPP with beta := 0 } : LavParams 2).wfB
#guard !( { lavPP with beta := 129 } : LavParams 2).wfB
#guard !( { lavPP with A := [[mk2 1 0]] } : LavParams 2).wfB
#guard !lavVerify H { lavPP with q := 64 } keyDigest ringD 0 5
  (evalAt 0 5 zKey).1 (evalAt 0 5 zKey).2
def plantedMsis : MsisBreakWitness lavPP := by
  refine ⟨[mk2 1 0, mk2 (-1) 0, mk2 0 0], rfl,
    ⟨mk2 1 0, by simp, by decide⟩, ?_, ?_⟩
  · decide
  · intro row hr k
    have hr' : row = [mk2 1 0, mk2 1 0, mk2 0 0] := by simpa [lavPP, List.mem_replicate] using hr
    subst row
    simp only [rowDot, addFast_eq_spec, zeroVec_spec, negacyclicMulFast_eq_spec]
    have hk : k = 0 ∨ k = 1 := by have := k.isLt; omega
    rcases hk with rfl | rfl <;> decide

-- Three responses have compatible bounded masks for two different candidate secrets.
def responseCs : List Nat := [1, 2, 1]
def responseZs : List (List (FastIntPoly 1)) := [[mk1 0], [mk1 2], [mk1 (-2)]]
example : (∀ pair ∈ responseCs.zip responseZs, lavShort rigidLav.gamma (lavMaskShift pair.1 [mk1 1] pair.2) = true) ∧
    (responseCs.zip responseZs).map (fun pair => lavResponse pair.1 [mk1 1] (lavMaskShift pair.1 [mk1 1] pair.2)) = responseZs :=
  lav_response_hides_sk_multi_eval rigidLav responseCs responseZs [mk1 1]
    (by decide) rfl (by decide) (by decide) (by decide)
example : (∀ pair ∈ responseCs.zip responseZs, lavShort rigidLav.gamma (lavMaskShift pair.1 [mk1 (-1)] pair.2) = true) ∧
    (responseCs.zip responseZs).map (fun pair => lavResponse pair.1 [mk1 (-1)] (lavMaskShift pair.1 [mk1 (-1)] pair.2)) = responseZs :=
  lav_response_hides_sk_multi_eval rigidLav responseCs responseZs [mk1 (-1)]
    (by decide) rfl (by decide) (by decide) (by decide)
#guard (lavEval H rigidLav [] 0 0 [mk1 1] [mk1 4]).isNone
#guard (lavEval H rigidLav [] 0 0 [mk1 1] [mk1 5]).isNone
#guard (lavEval H rigidLav [] 0 0 [mk1 2] [mk1 (-2)]).isNone
#guard (lavEval H rigidLav [] 0 0 [mk1 1] []).isNone
#guard !lavVerify H lavPP keyDigest ringD 0 5 (evalAt 0 5 zKey).1 { (evalAt 0 5 zKey).2 with z := zKey }
#guard !lavVerify H lavPP keyDigest ringD 0 5 (evalAt 0 5 zKey).1 { (evalAt 0 5 zKey).2 with wA := [] }
#guard !lavVerify H lavPP keyDigest ringD 0 5 (evalAt 0 5 zKey).1 { (evalAt 0 5 zKey).2 with wB := [] }
#guard !lavVerify H lavPP keyDigest ringD 0 5 (evalAt 0 5 zKey).1
  { (evalAt 0 5 zKey).2 with u := ((evalAt 0 5 zKey).2.u.map (intAdd (mk2 lavPP.q 0))) }
#guard !( { rigidLav with q := 39 } : LavParams 1).wfB
#guard !( { rigidLav with cMax := 1 } : LavParams 1).wfB
#guard !( { rigidLav with gamma := 2 } : LavParams 1).wfB
#guard match hash_frame_binding (fun _ => []) (a₁ := [1]) (b₁ := []) (c₁ := [])
    (a₂ := [2]) (b₂ := []) (c₂ := []) rfl with
  | .inl _ => false
  | .inr w => w.transcript.pre₁ == encodeFrameList [1] [] [] && w.transcript.pre₂ == encodeFrameList [2] [] []

-- Small explicit transcripts keep all three extraction branches kernel-checkable.
private def forkPP : LavParams 1 := ⟨37, 2, 1, 2, 4, 3, 1, List.replicate 3 [mk1 1, mk1 1, mk1 0]⟩
private def forkH : Hash := fun _ => [1]
private def forkπ₁ : LavProof 1 := ⟨List.replicate 3 (mk1 1), [mk1 2], List.replicate 3 (mk1 0), [mk1 36], [mk1 2, mk1 0, mk1 1]⟩
private def forkπ₂ : LavProof 1 := ⟨List.replicate 3 (mk1 1), [mk1 2], List.replicate 3 (mk1 0), [mk1 36], [mk1 0, mk1 2, mk1 1]⟩
private def forkπ₃ : LavProof 1 := ⟨List.replicate 3 (mk1 2), [mk1 2], List.replicate 3 (mk1 0), [mk1 36], [mk1 2, mk1 2, mk1 (-1)]⟩
private def forkKD := lavKeyDigest forkH forkπ₁.pk
private theorem forkB : lavHashMatrix forkH forkPP (lavSeed forkH [] 0 0) = [[mk1 1, mk1 1, mk1 1]] := by decide +kernel
macro "forkAlgebra" : tactic => `(tactic| (
  try simp only [lavHashImage, forkB]
  simp only [lavImage, lavHashImage, lavMatImage, forkB, forkPP, forkπ₁, forkπ₂, forkπ₃,
    polyVecAddMod, polyVecScaleMod, reduceVecMod, lavLin, List.map_replicate,
    List.zipWith_replicate, List.map_cons, List.map_nil, List.zipWith_cons_cons,
    List.zipWith_nil_left, List.cons.injEq, and_true]
  first | apply congrArg (List.replicate 3) | skip
  apply Sized.ext
  funext k
  have hk : k = 0 := Fin.ext (by have := k.isLt; omega)
  subst k
  simp only [reducePolyMod_spec, rowDot, addFast_eq_spec, scaleFast_eq_spec,
    zeroVec_spec, negacyclicMulFast_eq_spec]
  decide +kernel))
private def fork₁ : LavRewind forkH forkPP [] 0 0 forkπ₁ :=
  ⟨1, [mk1 1, mk1 0, mk1 0], by decide, by decide, by decide +kernel,
    by decide, by decide, by forkAlgebra, by forkAlgebra⟩
private def fork₂ : LavRewind forkH forkPP [] 0 0 forkπ₂ :=
  ⟨1, [mk1 0, mk1 1, mk1 0], by decide, by decide, by decide +kernel,
    by decide, by decide, by forkAlgebra, by forkAlgebra⟩
private def fork₃ : LavRewind forkH forkPP [] 0 0 forkπ₃ :=
  ⟨1, [mk1 1, mk1 1, mk1 (-1)], by decide, by decide, by decide +kernel,
    by decide, by decide, by forkAlgebra, by forkAlgebra⟩
private theorem forkAccepted₁ : lavVerify forkH forkPP forkKD [] 0 0 [1] forkπ₁ = true := by
  simp only [lavVerify, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨by decide, by decide +kernel⟩, by decide⟩, ?_, ?_, by decide +kernel⟩
  · forkAlgebra
  · forkAlgebra
private theorem forkAccepted₂ : lavVerify forkH forkPP forkKD [] 0 0 [1] forkπ₂ = true := by
  simp only [lavVerify, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨by decide, by decide +kernel⟩, by decide⟩, ?_, ?_, by decide +kernel⟩
  · forkAlgebra
  · forkAlgebra
private theorem forkAccepted₃ : lavVerify forkH forkPP forkKD [] 0 0 [1] forkπ₃ = true := by
  simp only [lavVerify, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨by decide, by decide +kernel⟩, by decide⟩, ?_, ?_, by decide +kernel⟩
  · forkAlgebra
  · forkAlgebra
#guard forkPP.wfB
#guard match extractLavUniqueOrMsis forkH forkPP forkKD [] 0 0 [1] [1] forkπ₁ forkπ₂
    forkAccepted₁ forkAccepted₂ fork₁ fork₂ with
  | .inr (.inl w) => w.w.length == forkPP.cols && lavShort forkPP.sisBound w.w &&
      w.w.any (fun a => a != zeroVec 1) && (lavImage forkPP w.w).all (fun a => a == zeroVec 1)
  | _ => false
#guard match extractLavUniqueOrMsis forkH forkPP forkKD [] 0 0 [1] [1] forkπ₁ forkπ₁
    forkAccepted₁ forkAccepted₁ fork₁ fork₁ with
  | .inl _ => true
  | _ => false
#guard match extractLavUniqueOrMsis forkH forkPP forkKD [] 0 0 [1] [1] forkπ₁ forkπ₃
    forkAccepted₁ forkAccepted₃ fork₁ fork₃ with
  | .inr (.inr w) => w.transcript.pre₁ == lavKeyPreimage forkπ₁.pk &&
      w.transcript.pre₂ == lavKeyPreimage forkπ₃.pk && w.transcript.pre₁ != w.transcript.pre₂
  | _ => false

-- Every coefficient vector is included, with the constant fixed; the map changes the random tail.
theorem seven_prime : IsPrimeNat 7 := by
  refine ⟨by decide, ?_⟩
  intro d hd
  have hb : d ≤ 7 := Nat.le_of_dvd (by decide) hd
  have hm : 7 % d = 0 := Nat.mod_eq_zero_of_dvd hd
  have hcases : ∀ d : Nat, d ≤ 7 → 7 % d = 0 → d = 1 ∨ d = 7 := by decide
  exact hcases d hb hm
example : let P := fun s => {p : ShamirPoly 7 3 // shamirPolyEval p 0 = s}
    ∃ (F : P 2 → P 5) (G : P 5 → P 2),
      (∀ p, G (F p) = p) ∧ (∀ p, F (G p) = p) ∧
      ∀ p, ([1, 2] : List (Fin 7)).map (shamirPolyEval (F p).val) =
        [1, 2].map (shamirPolyEval p.val) :=
  shamir_below_threshold_uniform_privacy seven_prime [1, 2] (by decide) (by decide) 2 5
def sep : ShamirPoly 7 3 := shamirSeparator [1, 2]
def randomPoly : ShamirPoly 7 3 := (2, 3, 4, ())
def coupledPoly : ShamirPoly 7 3 := shamirTranslate sep 3 randomPoly
example : shamirPolyEval sep 0 = 1 ∧ shamirPolyEval sep 1 = 0 ∧ shamirPolyEval sep 2 = 0 := by decide
example : shamirPolyEval randomPoly 0 = 2 ∧ shamirPolyEval coupledPoly 0 = 5 ∧
    ([1, 2] : List (Fin 7)).map (shamirPolyEval randomPoly) =
      [1, 2].map (shamirPolyEval coupledPoly) := by decide
example : shamirTranslate sep (-3) coupledPoly = randomPoly := by decide
-- Omitting the separator or allowing evaluation point zero leaks the secret.
example : shamirPolyEval coupledPoly 0 ≠ shamirPolyEval randomPoly 0 := by decide
example : shamirPolyEval (shamirTranslate (1, 0, 0, ()) 3 randomPoly) 1 ≠
    shamirPolyEval randomPoly 1 := by decide
example : 9 ≤ ((smudgeSupport 5).filter fun e => decide (-5 ≤ e + 2 ∧ e + 2 ≤ 5)).length ∧
    ∀ y : Int, -5 + 2 ≤ y → y ≤ 5 - 2 → ∃ e ∈ smudgeSupport 5, e + 2 = y :=
  tulva_smudge_shift_overlap_bound 5 2 2 (by decide)
example : ∀ y : Int, -5 + 3 ≤ y → y ≤ 5 - 3 → ∃ e ∈ smudgeSupport 5, e - 3 = y :=
  (tulva_smudge_shift_overlap_bound 5 3 (-3) (by decide)).2

-- The field hypothesis matters: a single share at 2 modulo 8 reveals secret parity.
example : ∀ r : Fin 8, shamirPolyEval (n := 2) ((2 : Fin 8), r, ()) (2 : Fin 8) ≠
    shamirPolyEval (n := 2) ((3 : Fin 8), 0, ()) 2 := by decide

-- An inhabited 40-bit flooding profile with explicit weighted-noise headroom.
def smallFlood : TulvaProfile := ⟨⟨1, 2 ^ 48, 16⟩, 2, 1, 1, 2 ^ 40, 40⟩
def smallEntries : List (Int × TulvaShare 1) := [(2, ⟨1, [], mk1 0⟩), (-1, ⟨2, [], mk1 0⟩)]
example : (7 : Int).natAbs ≤ 1 + 3 * 2 ^ 40 ∧ 1 + 3 * 2 ^ 40 < 2 ^ 48 / (2 * 16) ∧
    -(2 ^ 48 : Int) < 7 ∧ (7 : Int) < 2 ^ 48 :=
  tulva_smudge_no_wraparound (fun _ => []) smallFlood [] ⟨mk1 0, mk1 0⟩ smallEntries
    (by decide) 1 6 (by decide) (by decide)
#guard (computePartialShare ppS 1 (mk1 1) (mk1 2) (mk1 3)).sharePoly ==
  (computePartialShare ppS 1 (mk1 0) (mk1 2) (mk1 5)).sharePoly

-- Commitment first, opens later. A withheld or malformed last share loses its entire bond.
def releaseTurn : AuctionTurn (cfg 4) := mkTurn 4 0 5 [1] 111
def releaseTag : List UInt8 := tulvaTag H releaseTurn.context releaseTurn.ct
def openAt (id : Nat) : BondedShareOpening 2 :=
  ⟨shareAt releaseTurn.context releaseTurn.ct id, [id.toUInt8, 77]⟩
def member (id : Nat) (weight : Int) (bond : Nat) (o : BondedShareOpening 2 := openAt id) :
    BondedCommitteeMember :=
  ⟨id, weight, bond, ⟨commitShare H releaseTag id o, poseidon2Hash32_length _⟩⟩
def committee : List BondedCommitteeMember := [member 1 2 10, member 2 (-1) 20]
def allOpen : Nat → Option (BondedShareOpening 2) := fun id => some (openAt id)
def lastWithholds : Nat → Option (BondedShareOpening 2) := fun id => if id = 2 then none else allOpen id
def wrongSalt : Nat → Option (BondedShareOpening 2) := fun id =>
  if id = 2 then some { openAt id with salt := [] } else allOpen id
def badOpen : BondedShareOpening 2 :=
  { openAt 2 with share := { (openAt 2).share with sharePoly := mk2 (-1) 0 } }
def badCommittee : List BondedCommitteeMember := [member 1 2 10, member 2 (-1) 20 badOpen]
def badOpens : Nat → Option (BondedShareOpening 2) := fun id =>
  if id = 2 then some badOpen else allOpen id
#guard bondedLockCheck 2 committee
#guard !bondedLockCheck 3 committee
#guard !bondedLockCheck 0 committee
#guard !bondedLockCheck 2 [member 1 2 10, member 1 (-1) 20]
#guard !bondedLockCheck 2 [member 1 2 0, member 2 (-1) 20]
#guard (bondedAuctionResolve H pp.q releaseTag committee allOpen 7).slashedTotal == 7
#guard (bondedAuctionResolve H pp.q releaseTag committee allOpen 7).refunds == [(1, 10), (2, 20)]
#guard (bondedAuctionResolve H pp.q releaseTag committee lastWithholds 7).slashedTotal == 27
#guard (bondedAuctionResolve H pp.q releaseTag committee wrongSalt 7).slashedTotal == 27
#guard (bondedAuctionResolve H pp.q releaseTag committee wrongSalt 7).refunds == [(1, 10), (2, 0)]
#guard (bondedAuctionResolve H pp.q releaseTag badCommittee badOpens 7).slashedTotal == 27
#guard commitShare H releaseTag 1 (openAt 1) != commitShare H releaseTag 2 (openAt 1)
#guard commitShare H releaseTag 1 (openAt 1) != commitShare H [0] 1 (openAt 1)
#guard commitShare H releaseTag 1 (openAt 1) != commitShare H releaseTag 1 { openAt 1 with salt := [] }
#guard commitShare H releaseTag 1 (openAt 1) != commitShare H releaseTag 1
  { openAt 1 with share := { (openAt 1).share with point := 2 } }
#guard commitShare H releaseTag 1 (openAt 1) != commitShare H releaseTag 1
  { openAt 1 with share := { (openAt 1).share with tag := [] } }
#guard commitShare H releaseTag 1 (openAt 1) != commitShare H releaseTag 1
  { openAt 1 with share := { (openAt 1).share with sharePoly := mk2 0 0 } }
def bondedInit : BondedAuctionState := ⟨.init, 0, [], [], 0, none⟩
def bondedActions (opens : Nat → Option (BondedShareOpening 2)) : List (BondedAuctionAction (cfg 4)) :=
  [.commit releaseTag committee, .resolve releaseTurn opens]
#guard (bondedAuctionRun H (cfg 4) bondedInit (bondedActions allOpen)).auction.epoch == 1
#guard (bondedAuctionRun H (cfg 4) bondedInit (bondedActions allOpen)).slashedTotal == 0
#guard (bondedAuctionRun H (cfg 4) bondedInit (bondedActions lastWithholds)).auction.epoch == 0
#guard (bondedAuctionRun H (cfg 4) bondedInit (bondedActions lastWithholds)).slashedTotal == 20
#guard (bondedAuctionRun H (cfg 4) bondedInit (bondedActions lastWithholds)).released == 2
#guard (bondedAuctionRun H (cfg 4) bondedInit [.resolve releaseTurn allOpen]).auction.epoch == 0
#guard (bondedAuctionRun H (cfg 4) bondedInit
  (bondedActions lastWithholds ++ [.resolve releaseTurn lastWithholds])).slashedTotal == 20
#guard (bondedAuctionRun H (cfg 4) bondedInit
  (bondedActions lastWithholds ++ [.commit releaseTag committee])).pending.isNone
#guard (bondedAuctionRun H (cfg 4) bondedInit
  [.commit releaseTag [member 1 2 10], .resolve releaseTurn allOpen]).auction.epoch == 0
example : BondedAuctionInv (cfg 4) bondedInit := by intro tag ms h; cases h
#guard (bondedAuctionRun H (cfg 4) bondedInit
  (bondedActions lastWithholds ++ [.commit [99] (committee ++ [member 3 1 30])])).pending.isNone

-- ============================================================================
-- 5. Teeth
-- ============================================================================

-- The mutation tool accepts theorems; these retain the executable extractors in their proof terms.
theorem hash_frame_binding_tooth (H : Hash) {a₁ b₁ c₁ a₂ b₂ c₂ : List UInt8}
    (h : H (encodeFrameList a₁ b₁ c₁) = H (encodeFrameList a₂ b₂ c₂)) : Nonempty (    PSum (a₁ = a₂ ∧ b₁ = b₂ ∧ c₁ = c₂)
      (ExactCollision H (encodeFrameList a₁ b₁ c₁) (encodeFrameList a₂ b₂ c₂))) :=
  ⟨Obend.Crypto.hash_frame_binding H h⟩

theorem tulvaTag_binds_query_tooth (H : Hash) (ctx₁ ctx₂ : List UInt8) {d : Nat}
    (ct₁ ct₂ : RlweCiphertext d) (h : tulvaTag H ctx₁ ct₁ = tulvaTag H ctx₂ ct₂) : Nonempty (    PSum (ctx₁ = ctx₂ ∧ ct₁ = ct₂) (ExactCollision H
      (encodeFrameList tulvaTagDomain ctx₁ (ciphertextBytes ct₁))
      (encodeFrameList tulvaTagDomain ctx₂ (ciphertextBytes ct₂)))) :=
  ⟨Obend.Crypto.tulvaTag_binds_query H ctx₁ ctx₂ ct₁ ct₂ h⟩

theorem bitzCommit_binding_tooth (H : Hash) (w₁ w₂ : Nat) (rows₁ rows₂ : List (List Int))
    (h : bitzCommit H w₁ rows₁ = bitzCommit H w₂ rows₂) : Nonempty (    PSum (w₁ = w₂ ∧ rows₁ = rows₂) (ExactCollision H
      (encodeFrameList bitzDomain (leb128 w₁) (encodeIntRows rows₁))
      (encodeFrameList bitzDomain (leb128 w₂) (encodeIntRows rows₂)))) :=
  ⟨Obend.Crypto.bitzCommit_binding H w₁ w₂ rows₁ rows₂ h⟩

theorem bitz_sameOpening_and_free_range_sound_tooth (H : Hash) (q width : Nat)
    (commitment : List UInt8) (rows : List (List Int)) (claims : List BitzClaim)
    (h : bitzVerify H q width commitment rows claims = true) : Nonempty (    PProd (rows.length = claims.length ∧ ∀ row cl, (row, cl) ∈ rows.zip claims →
      ∃ n : Nat, n < 2 ^ width ∧ psiZ row = n ∧ cl.rq = n ∧ cl.fp.val = n)
    (∀ rows', bitzCommit H width rows' = commitment → PSum (rows' = rows)
      (ExactCollision H (encodeFrameList bitzDomain (leb128 width) (encodeIntRows rows'))
        (encodeFrameList bitzDomain (leb128 width) (encodeIntRows rows))))) :=
  ⟨Obend.Crypto.bitz_sameOpening_and_free_range_sound H q width commitment rows claims h⟩

theorem lavSeed_binds_tooth (H : Hash) (r₁ r₂ : List UInt8) (e₁ e₂ s₁ s₂ : Nat)
    (h : lavSeed H r₁ e₁ s₁ = lavSeed H r₂ e₂ s₂) : Nonempty (    PSum (r₁ = r₂ ∧ e₁ = e₂ ∧ s₁ = s₂)
      (ExactCollision H (lavInput r₁ e₁ s₁) (lavInput r₂ e₂ s₂))) :=
  ⟨Obend.Crypto.lavSeed_binds H r₁ r₂ e₁ e₂ s₁ s₂ h⟩

theorem lav_unique_output_or_msisBreak_tooth {d : Nat} (H : Hash) (pp : LavParams d)
    (keyDigest ring : List UInt8) (epoch slot : Nat) (v₁ v₂ : List UInt8) (π₁ π₂ : LavProof d)
    (h₁ : lavVerify H pp keyDigest ring epoch slot v₁ π₁ = true)
    (h₂ : lavVerify H pp keyDigest ring epoch slot v₂ π₂ = true)
    (f₁ : LavRewind H pp ring epoch slot π₁) (f₂ : LavRewind H pp ring epoch slot π₂) : Nonempty (    PSum (v₁ = v₂) (PSum (MsisBreakWitness pp) (ExactCollision H (lavKeyPreimage π₁.pk) (lavKeyPreimage π₂.pk)))) :=
  Obend.Crypto.lav_unique_output_or_msisBreak H pp keyDigest ring epoch slot v₁ v₂ π₁ π₂ h₁ h₂ f₁ f₂

theorem bondedShareCommit_binding_or_collision_tooth (H : Hash) {d : Nat} (tag₁ tag₂ : List UInt8)
    (id₁ id₂ : Nat) (o₁ o₂ : BondedShareOpening d)
    (h : commitShare H tag₁ id₁ o₁ = commitShare H tag₂ id₂ o₂) : Nonempty (    PSum (tag₁ = tag₂ ∧ id₁ = id₂ ∧ o₁ = o₂) (ExactCollision H
      (encodeFrameList [66, 79, 78, 68, 45, 83, 72, 65, 82, 69] tag₁ (shareOpeningBytes id₁ o₁))
      (encodeFrameList [66, 79, 78, 68, 45, 83, 72, 65, 82, 69] tag₂ (shareOpeningBytes id₂ o₂)))) :=
  ⟨Obend.Crypto.bondedShareCommit_binding_or_collision H tag₁ tag₂ id₁ id₂ o₁ o₂ h⟩

theorem lav_T_uniqueness_tooth {d : Nat} (H : Hash) (pp : LavParams d) (ringKeys : List (List UInt8))
    (epoch slot : Nat) (tickets : List (LavTicket d))
    (hc : ∀ t ∈ tickets, lavRingVerify H pp ringKeys epoch slot t = true)
    (hf : ∀ t ∈ tickets, LavRewind H pp (lavRingDigest H ringKeys) epoch slot t.proof)
    (hn : (tickets.map (·.output)).Nodup) :
    Nonempty (PSum (tickets.map (·.keyIndex)).Nodup (PSum (MsisBreakWitness pp) (TranscriptCollision H))) :=
  ⟨lav_T_uniqueness H pp ringKeys epoch slot tickets hc hf hn⟩

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
#tooth Obend.Tests.ThresholdFheAndLatticeVrfTest.bitz_sameOpening_and_free_range_sound_tooth by mutation
  Obend.Crypto.checkBooleanRow := fun _ => true

-- A recomposition that does not reduce modulo `q` is not the `ℤ_q` image.
#tooth Obend.Tests.ThresholdFheAndLatticeVrfTest.bitz_sameOpening_and_free_range_sound_tooth by mutation
  Obend.Crypto.psiRq := fun _ row => Obend.Crypto.psiZ row

-- A commitment that drops the rows binds nothing.
#tooth Obend.Tests.ThresholdFheAndLatticeVrfTest.bitzCommit_binding_tooth by mutation
  Obend.Crypto.encodeIntRows := fun _ => []

-- Removing the computed cross-difference breaks the concrete fork extractor.
#tooth Obend.Tests.ThresholdFheAndLatticeVrfTest.lav_unique_output_or_msisBreak_tooth by mutation
  Obend.Crypto.lavVecSub := fun _ _ => []

-- An input that drops the ring, epoch and slot separates nothing.
#tooth Obend.Tests.ThresholdFheAndLatticeVrfTest.lavSeed_binds_tooth by mutation
  Obend.Crypto.lavInput := fun _ _ _ => []

-- A ring check that accepts every ticket gives no uniqueness.
#tooth Obend.Tests.ThresholdFheAndLatticeVrfTest.lav_T_uniqueness_tooth by mutation
  Obend.Crypto.lavRingVerify := fun _ _ _ _ _ _ _ => true

-- A turn check that accepts everything keeps neither the budget nor tag freshness.
#tooth Obend.Crypto.auctionRun_safe by mutation
  Obend.Crypto.auctionTurnCheck := fun _ _ _ _ => true

#tooth Obend.Crypto.lavVerify_params by mutation
  Obend.Crypto.LavParams.wfB := fun _ => true
#tooth Obend.Crypto.shamir_below_threshold_uniform_privacy by mutation
  Obend.Crypto.shamirSeparator := fun C => Obend.Crypto.shamirExtend
    (Nat.zero_le (C.length + 1)) ()
#tooth Obend.Crypto.tulva_smudge_no_wraparound by mutation
  Obend.Crypto.tulvaNoiseTotal := fun _ _ _ => 0
#tooth Obend.Crypto.tulva_smudge_shift_overlap_bound by mutation
  Obend.Crypto.smudgeUncoupled := fun _ _ => []
#tooth Obend.Crypto.bondedAuctionResolve_slashes by mutation
  Obend.Crypto.bondedAuctionResolve := fun _ _ _ _ _ _ total => ⟨total, [], []⟩
#tooth Obend.Crypto.bondedAuctionResolve_conserves by mutation
  Obend.Crypto.bondedAuctionResolve := fun _ _ _ _ _ _ _ => ⟨0, [], []⟩
#tooth Obend.Crypto.honest_member_never_slashed by mutation
  Obend.Crypto.bondedSlash := fun _ _ _ _ m _ => m.bond
#tooth Obend.Tests.ThresholdFheAndLatticeVrfTest.bondedShareCommit_binding_or_collision_tooth by mutation
  Obend.Crypto.shareOpeningBytes := fun _ _ => []
#tooth Obend.Crypto.bondedOpeningValid_refused by mutation
  Obend.Crypto.bondedOpeningValid := fun _ _ _ _ _ _ => true
#tooth Obend.Crypto.bondedAuctionRun_locked by mutation
  Obend.Crypto.bondedLockCheck := fun _ _ => true

#tooth Obend.Crypto.lav_response_hides_sk_multi_eval by mutation
  Obend.Crypto.lavResponse := fun _ sk _ => sk
#tooth Obend.Crypto.lav_response_hides_sk_multi_eval by mutation
  Obend.Crypto.lavMaskShift := fun _ _ z => z
#tooth Obend.Crypto.lavEval_complete by mutation
  Obend.Crypto.lavResponse := fun _ sk _ => sk
#tooth Obend.Crypto.lavSimulate_correct by mutation
  Obend.Crypto.lavSimulate := fun _ _ _ _ pk u _ z => ⟨pk, u, pk, u, z⟩
#tooth Obend.Tests.ThresholdFheAndLatticeVrfTest.hash_frame_binding_tooth by mutation
  Obend.Crypto.encodeFrameList := fun _ _ _ => []
#tooth Obend.Tests.ThresholdFheAndLatticeVrfTest.tulvaTag_binds_query_tooth by mutation
  Obend.Crypto.ciphertextBytes := fun _ => []

-- ============================================================================
-- 6. Axiom audit
-- ============================================================================

#assert_axioms_tree

-- Check safe definitions, including proof dependencies, for classical choice and compiler trust.
-- Retain the dependency path to make a future regression actionable.
open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let mut seen := 0
  let mut theorems := 0
  for (name, info) in env.constants.map₁.toList do
    let some idx := env.getModuleIdxFor? name | continue
    unless env.header.moduleNames[idx.toNat]? == some `Obend.Crypto.ThresholdFheAndLatticeVrf do continue
    if let .thmInfo v := info then
      -- Derived constructor size laws are generated, not authored library theorems.
      unless name.isInternal || name.isInternalDetail || name.getString! == "sizeOf_spec" do
        if ← liftTermElabM (Obend.AssertAxioms.closedStatement v.type) then
          throwError m!"closed library theorem: {name}"
        theorems := theorems + 1
    let .defnInfo v := info | continue
    unless v.safety == .safe do continue
    seen := seen + 1
    let axioms ← liftCoreM <| Lean.collectAxioms name
    if axioms.contains ``Classical.choice then
      let mut todo : List (Name × List Name) := [(name, [name])]
      let mut visited : NameSet := {}
      while !todo.isEmpty do
        let (n, path) := todo.head!
        todo := todo.tail!
        if visited.contains n then continue
        visited := visited.insert n
        let some ci := env.checked.get.find? n | throwError m!"missing classical dependency: {path.reverse}"
        let val := match ci with
          | .defnInfo v => some v.value
          | .thmInfo v => some v.value
          | .opaqueInfo v => some v.value
          | _ => none
        let deps := (val.getD ci.type).getUsedConstantsAsSet.toList ++ ci.type.getUsedConstantsAsSet.toList
        let mut followed := false
        for c in deps do
          if c == ``Classical.choice then throwError m!"classical dependency: {path.reverse} -> {c}"
          let ca ← liftCoreM <| Lean.collectAxioms c
          if ca.contains ``Classical.choice then
            followed := true
            todo := (c, c :: path) :: todo
        unless followed do throwError m!"opaque classical dependency: {path.reverse}"
      throwError m!"definition {name} transitively uses Classical.choice"
    for ax in axioms do
      unless ax == ``propext || ax == ``Quot.sound do
        throwError m!"definition {name} depends on forbidden axiom {ax}"
    if Lean.isNoncomputable env name then
      throwError m!"noncomputable definition: {name}"
    for c in v.value.getUsedConstantsAsSet.toList do
      if c.getRoot == `Classical then
        throwError m!"definition {name} computes through {c}"
  if seen == 0 then throwError "no definitions of the module were visible to the audit"
  logInfo m!"A2 audit: {seen} safe definitions have no classical choice or compiler trust; {theorems} library theorems are non-closed."

end Obend.Tests.ThresholdFheAndLatticeVrfTest
end
