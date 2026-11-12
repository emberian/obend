module
/-
# SimplexLivenessAndOutboxTest — Wave-5 Lane C6 End-to-End Metasystem Suite

Exercises:
1. Post-GST honest-leader single-view finalization (`N = 4, f = 1` and `N = 7, f = 2`) and
   pre-GST / faulty-leader view-timeout progress (`Obend.Consensus.SimplexLiveness`).
2. Domain-framed sender signature authentication (`SignedSimplexMsg`, `verifySignedSent`),
   choice-free `PSum` forgery extraction (`extractForgedVoteSignature`), and constructive
   reduction to `Obend.Judge.Computational` (`forgedVoteSignature_reduces_to_hashCollision`,
   `signedSimplexCompJudge`).
3. Pillar-6 `seL4` Copy-Before-Verify SPSC isolation + 3-class external effect settlement
   (`Obend.Vault.IrreversibleOutbox`):
   - TOCTOU shared-ring post-copy DMA mutation immunity & pre-copy tamper refusal,
   - Unfinalized-block irreversible actuation refusals,
   - Duplicate / stale monotonic outbox nullifier refusals,
   - Optimistic `.compensatableEscrow` rollback compensation on orphaned branches,
   - Multi-turn / multi-view `ValidOutboxTrace` instantiation of
     `firmament_sel4_copy_before_verify_and_irreversible_outbox_safe` and
     `irreversible_at_most_once_and_never_rolled_back`.
4. Seven `#tooth` mutation-sensitivity witnesses and `#assert_axioms_tree` (`0 sorry`, `0` custom axioms).
-/

public import Obend.Consensus.SimplexLiveness
public import Obend.Vault.IrreversibleOutbox
public import Obend.Tactic.Tooth
public import Obend.AssertAxioms

import all Obend.Consensus.SimplexLiveness
import all Obend.Vault.IrreversibleOutbox
import all Obend.Trailblaze.Polis
import all Obend.Consensus.SimplexProtocol
import all Obend.Consensus.SimplexTrace
import all Obend.Consensus.Finality
import all Obend.Judge.Computational
meta import all Obend.Consensus.SimplexLiveness
meta import all Obend.Vault.IrreversibleOutbox
meta import all Obend.Trailblaze.Polis
meta import all Obend.Consensus.SimplexProtocol
meta import all Obend.Consensus.SimplexTrace
meta import all Obend.Consensus.Finality
meta import all Obend.Judge.Computational

-- Transitive package bodies for `#assert_axioms_tree`
import all Obend.AssertAxioms
import all Obend.Consensus.Simplex
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
import all Obend.Fold
import all Obend.Intention
import all Obend.Judge.Class
import all Obend.Judge.Clearing
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
import all Obend.Trailblaze.Obligations
import all Obend.Trailblaze.PolisBlum
import all Obend.Vault.Hyperedge

public section
namespace Obend.Tests.SimplexLivenessAndOutbox

open Obend.Consensus.SimplexProtocol
open Obend.Consensus.Simplex (NodeId)
open Obend.Consensus.SimplexProtocol
open Obend.Consensus.SimplexLiveness
open Obend.Vault.IrreversibleOutbox
open Obend.Trailblaze.Polis (sampleValidPartition checkMicrokitIsolation)
open Obend.Digest
open Obend.Digest.Cshake256.Native (bytesOfList)

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

/-! ## 1. Post-GST Finalization Runs (`N = 4, f = 1` and `N = 7, f = 2`) & Pre-GST Timeout Progress -/

/-- `N = 4, f = 1` committee (`quorum = 3`); validator `3` is Byzantine faulty. -/
def proto4 : Protocol :=
  ⟨[0, 1, 2, 3], 1, (· == 3), by decide, by decide, by decide⟩

/-- `N = 7, f = 2` committee (`quorum = 5`); validators `5` and `6` are Byzantine faulty. -/
def proto7 : Protocol :=
  ⟨[0, 1, 2, 3, 4, 5, 6], 2, (fun n => n == 5 || n == 6), by decide, by decide, by decide⟩

def cfg4 : PartialSyncConfig := ⟨100, 10, 25, 4⟩
def sched4_v1 : ViewExecutionSchedule := ⟨100, 0, (fun _ => 102), (fun _ => 111), (fun _ => 119)⟩

/-- View 1 post-GST finalization on `N = 4, f = 1` (`leader 1 = 0` honest, `Δ_timer = 25 > 20 = 2 Δ_net`). -/
def sent4_v1 : Sent :=
  runPostGstHonestLeaderView proto4 cfg4 sched4_v1 [] 1 401 []

example : proto4.quorum = 3 := rfl
example : (honestMembers proto4).length = 3 := rfl
example : effectiveDeltaTimer cfg4 sched4_v1 = 25 := rfl
example : (extractFinCert? proto4 sent4_v1 1 [.block 1 401]).isSome = true := by decide
example : [0, 1, 2].all (fun n => !voted sent4_v1 n 1 (.dummy 1)) = true := by decide
example : [0, 1, 2].all (fun n => voted sent4_v1 n 1 (.block [.block 1 401])) = true := by decide
example : [0, 1, 2].all (fun n => finalizeVoted sent4_v1 n 1 [.block 1 401]) = true := by decide

theorem proto4_v1_sync : PostGstHonestViewSync proto4 cfg4 sched4_v1 1 where
  postGst := by decide
  honestLeader := ⟨by decide, by decide⟩
  honestEnterBound := fun _ _ => ⟨by dsimp [sched4_v1]; omega, by dsimp [sched4_v1, cfg4]; omega⟩
  proposalDelivery := fun _ _ => by dsimp [sched4_v1, cfg4]; omega
  notarDelivery := fun _ _ => by dsimp [sched4_v1, cfg4]; omega
  timerMargin := by decide

/-- End-to-end instantiation of `gst_honest_leader_finalizes_in_view` on `N = 4, f = 1`. -/
example :
    Finalized proto4 sent4_v1 1 [.block 1 401] ∧
    ∃ cert : FinCert,
      cert.view = 1 ∧
      cert.chain = [.block 1 401] ∧
      cert.checks proto4 sent4_v1 = true := by
  have hEmptyNot : ChainNotarized proto4 ([] : Sent) [] := fun _ hk => by simp at hk
  have hFresh : ∀ n, proto4.honest n → votedAny ([] : Sent) n 1 = false := fun _ _ => rfl
  have hFast : ∀ n, proto4.honest n → sched4_v1.notarizationArrival n ≤ sched4_v1.viewStart + 2 * cfg4.deltaNet :=
    fun _ _ => by dsimp [sched4_v1, cfg4]; omega
  have hOut := @gst_honest_leader_finalizes_in_view proto4 cfg4 sched4_v1 [] 1 401 []
    Reach.nil (by decide) rfl hEmptyNot hFresh proto4_v1_sync hFast
  obtain ⟨_, hFin, cert, hcv, hcc, hchk, _⟩ := hOut
  exact ⟨hFin, cert, hcv, hcc, hchk⟩

/-- Pre-GST / silent-leader view-timeout advance on `proto4` in view 2 (`[.block 1 401, .dummy 2]`). -/
example :
    ∃ (sent2 : Sent) (e : Entry),
      Reach proto4 sent2 ∧
      e.view = 2 ∧
      ([Entry.block 1 401] ++ [e]).length = 2 ∧
      ChainNotarized proto4 sent2 ([Entry.block 1 401] ++ [e]) := by
  have hEmptyNot : ChainNotarized proto4 ([] : Sent) [] := fun _ hk => by simp at hk
  have hFresh1 : ∀ n, proto4.honest n → votedAny ([] : Sent) n 1 = false := fun _ _ => rfl
  have hV1 := @gst_honest_leader_finalizes proto4 cfg4 sched4_v1 [] 1 401 []
    Reach.nil (by decide) rfl hEmptyNot hFresh1 proto4_v1_sync
  have hFresh2 : ∀ n, proto4.honest n → votedAny sent4_v1 n 2 = false ∨ voted sent4_v1 n 2 (.dummy 2) = true := by
    intro n ⟨hmem, hnf⟩
    left
    simp [proto4] at hmem hnf
    rcases hmem with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · contradiction
  exact pre_gst_or_faulty_leader_advances_view hV1.1 (by decide) rfl hV1.2.2.2.2.2.2.2.1 (.inr hFresh2)

/-- `N = 7, f = 2` two-view consecutive post-GST finalization (`quorum = 5`, views 1 and 2). -/
def cfg7 : PartialSyncConfig := ⟨500, 15, 40, 4⟩
def sched7_v1 : ViewExecutionSchedule := ⟨500, 0, (fun _ => 505), (fun _ => 518), (fun _ => 529)⟩
def sched7_v2 : ViewExecutionSchedule := ⟨550, 0, (fun _ => 554), (fun _ => 567), (fun _ => 578)⟩

def sent7_v1 : Sent :=
  runPostGstHonestLeaderView proto7 cfg7 sched7_v1 [] 1 1001 []

def sent7_v2 : Sent :=
  runPostGstHonestLeaderView proto7 cfg7 sched7_v2 sent7_v1 2 2002 [.block 1 1001]

example : proto7.quorum = 5 := rfl
example : (honestMembers proto7).length = 5 := rfl
example : (extractFinCert? proto7 sent7_v1 1 [.block 1 1001]).isSome = true := by decide
example : (extractFinCert? proto7 sent7_v2 2 [.block 1 1001, .block 2 2002]).isSome = true := by decide
example : [0, 1, 2, 3, 4].all (fun n => !voted sent7_v1 n 1 (.dummy 1)) = true := by decide
example : [0, 1, 2, 3, 4].all (fun n => !voted sent7_v2 n 2 (.dummy 2)) = true := by decide
example : [0, 1, 2, 3, 4].all (fun n => finalizeVoted sent7_v2 n 2 [.block 1 1001, .block 2 2002]) = true := by decide

theorem proto7_v1_sync : PostGstHonestViewSync proto7 cfg7 sched7_v1 1 where
  postGst := by decide
  honestLeader := ⟨by decide, by decide⟩
  honestEnterBound := fun _ _ => ⟨by dsimp [sched7_v1]; omega, by dsimp [sched7_v1, cfg7]; omega⟩
  proposalDelivery := fun _ _ => by dsimp [sched7_v1, cfg7]; omega
  notarDelivery := fun _ _ => by dsimp [sched7_v1, cfg7]; omega
  timerMargin := by decide

example : Finalized proto7 sent7_v1 1 [.block 1 1001] :=
  (@gst_honest_leader_finalizes proto7 cfg7 sched7_v1 [] 1 1001 []
    Reach.nil (by decide) rfl (fun _ hk => by simp at hk)
    (fun _ _ => rfl) proto7_v1_sync).2.2.2.2.2.2.1

/-! ## 2. Authenticated `SignedSimplexMsg` & Constructive EUF-CMA / Collision Extraction -/

/-- Constant 32-byte collision-exhibiting test hash (used strictly to trigger the constructive
    `.inr` collision-extraction branch of `forgedVoteSignature_reduces_to_hashCollision`). -/
def collidingSlotHash : HashBytes.Hash :=
  fun _ => List.replicate 32 0x5A

def saltHonest : ByteArray := bytesOfList (List.replicate 32 0x11)
def saltForged : ByteArray := bytesOfList (List.replicate 32 0x22)

/-- `proto4.leader 1 = 0` (`committee[(1 - 1) % 4] = 0`). -/
def honestLeaderProposal : Msg := ⟨0, 1, .propose, .block [.block 1 777]⟩
def forgedHonestVote : Msg := ⟨0, 1, .vote, .block [.block 1 999]⟩
def faultyEquivocation : Msg := ⟨3, 1, .vote, .block [.block 1 888]⟩

def slotKeys4 : KeyDirectory where
  pubKey n :=
    if n == 3 then
      deriveSlotPubKey collidingSlotHash (signableByteArray 0#256 faultyEquivocation) saltHonest
    else
      deriveSlotPubKey collidingSlotHash (signableByteArray 0#256 honestLeaderProposal) saltHonest

def signedHonestProp : SignedSimplexMsg where
  msg := honestLeaderProposal
  signerPk := slotKeys4.pubKey 0
  signature := saltHonest

def signedFaultyEquiv : SignedSimplexMsg where
  msg := faultyEquivocation
  signerPk := slotKeys4.pubKey 3
  signature := saltHonest

def signedForgedHonestVote : SignedSimplexMsg where
  msg := forgedHonestVote
  signerPk := slotKeys4.pubKey 0
  signature := saltForged

/-- Valid authenticated trace containing an honest proposal + a faulty node's equivocation under its own key. -/
def authValidTrace : SignedSent := [signedHonestProp, signedFaultyEquiv]

/-- Adversarially forged trace injecting an unauthorized honest vote (`sender = 0`) without oracle query. -/
def authForgedTrace : SignedSent := [signedForgedHonestVote]

example : verifySignedSent (commitSlotSigScheme collidingSlotHash 512) slotKeys4
            proto4.committee authValidTrace = true := by decide

example : verifySignedSent (commitSlotSigScheme collidingSlotHash 512) slotKeys4
            proto4.committee authForgedTrace = true := by decide

def isExtractedReach {α β} : PSum α β → Bool
  | .inl _ => true
  | .inr _ => false

theorem authValidTrace_ver :
    verifySignedSent (commitSlotSigScheme collidingSlotHash 512) slotKeys4
      proto4.committee authValidTrace = true := by decide

theorem authValidTrace_oracle :
    HonestSigningOracle proto4 [] [honestLeaderProposal] authValidTrace := by
  intro pre sm suf hEq hHon _
  cases pre with
  | nil =>
    simp [authValidTrace] at hEq
    rcases hEq with ⟨rfl, _⟩
    decide
  | cons p ps =>
    cases ps with
    | nil =>
      simp [authValidTrace] at hEq
      rcases hEq with ⟨_, rfl, _⟩
      have hF : proto4.faulty signedFaultyEquiv.msg.sender = true := rfl
      exact False.elim (Bool.false_ne_true (hHon.2.symm.trans hF))
    | cons q qs =>
      simp [authValidTrace] at hEq

/-- Constructive `.inl` branch: `extractForgedVoteSignature` certifies `Reach` on `authValidTrace`! -/
example :
    isExtractedReach
      (extractForgedVoteSignature (commitSlotSigScheme collidingSlotHash 512) slotKeys4
        proto4 [honestLeaderProposal] authValidTrace
        authValidTrace_ver authValidTrace_oracle) = true := by
  decide

/-- Constructive `.inr` branch + `forgedVoteSignature_reduces_to_hashCollision`:
    deterministically extracts a genuine `HashCollisionWitness` (`msgA ≠ msgB` with identical digest)! -/
def singleHonestProto : Protocol :=
  ⟨[0], 0, (fun _ => false), by decide, by decide, by decide⟩

def singleHonestKeys : KeyDirectory where
  pubKey _ :=
    let dummyPk := BitVec.ofNat 256 (HashBytes.ofBE (List.replicate 32 0x5A))
    deriveSlotPubKey collidingSlotHash (signableByteArray dummyPk honestLeaderProposal) saltHonest

def singleSignedForged : SignedSimplexMsg where
  msg := forgedHonestVote
  signerPk := singleHonestKeys.pubKey 0
  signature := saltForged

example :
    let hVer : verifySignedSent (commitSlotSigScheme collidingSlotHash 512) singleHonestKeys
                 singleHonestProto.committee [singleSignedForged] = true := by decide
    have hOracle : HonestSigningOracle singleHonestProto [] [honestLeaderProposal] [singleSignedForged] := by
      intro _ sm _ hEq _ hIn
      have hMem : sm ∈ [singleSignedForged] := by rw [hEq]; simp
      simp [singleSignedForged] at hMem
      subst hMem
      simp [forgedHonestVote, honestLeaderProposal] at hIn
    match extractForgedVoteSignature (commitSlotSigScheme collidingSlotHash 512) singleHonestKeys
            singleHonestProto [honestLeaderProposal] [singleSignedForged] hVer hOracle with
    | .inl _ => False
    | .inr w =>
      let col := forgedVoteSignature_reduces_to_hashCollision collidingSlotHash 512
        singleHonestKeys singleHonestProto honestLeaderProposal saltHonest
        (by decide) (by decide) (by decide) (by decide)
        (fun n hn => by
          rcases hn with ⟨hmem, _⟩
          simp [singleHonestProto] at hmem
          subst hmem
          exact ⟨rfl, rfl⟩)
        w
      col.msgA ≠ col.msgB ∧
      HashBytes.ofBE (collidingSlotHash col.msgA) = HashBytes.ofBE (collidingSlotHash col.msgB) := by
  dsimp only
  split
  · rename_i w _
    exfalso
    have hRuleFalse : checkHonestProtocolRule singleHonestProto [] singleSignedForged.msg = false := by decide
    have hFault := w.down.2.2.faultyOnlyInject [] singleSignedForged [] rfl hRuleFalse
    exact Bool.false_ne_true hFault.1
  · rename_i forgery _
    exact ⟨(forgedVoteSignature_reduces_to_hashCollision collidingSlotHash 512
              singleHonestKeys singleHonestProto honestLeaderProposal saltHonest
              (by decide) (by decide) (by decide) (by decide)
              (fun n hn => by
                rcases hn with ⟨hmem, _⟩
                simp [singleHonestProto] at hmem
                subst hmem
                exact ⟨rfl, rfl⟩)
              forgery).distinct,
           (forgedVoteSignature_reduces_to_hashCollision collidingSlotHash 512
              singleHonestKeys singleHonestProto honestLeaderProposal saltHonest
              (by decide) (by decide) (by decide) (by decide)
              (fun n hn => by
                rcases hn with ⟨hmem, _⟩
                simp [singleHonestProto] at hmem
                subst hmem
                exact ⟨rfl, rfl⟩)
              forgery).sameDigest⟩

/-! ## 3. Pillar-6 `IrreversibleOutbox` Settlement, TOCTOU Immunity & Refusal Suite -/

def checkOutboxErr (res : Except OutboxRefusal OutboxState) (expected : OutboxRefusal) : Bool :=
  match res with
  | .error r => r == expected
  | .ok _ => false

def checkOutboxOk (res : Except OutboxRefusal OutboxState) (p : OutboxState → Bool) : Bool :=
  match res with
  | .ok st => p st
  | .error _ => false

def actPayloadV1 : ByteArray := bytesOfList [0xDE, 0xAD, 0xBE, 0xEF]
def actPayloadV3 : ByteArray := bytesOfList [0xCA, 0xFE, 0x01, 0x02]
def dmaTamperedBytes : ByteArray := bytesOfList [0xFF, 0x00, 0xFF, 0x00]
def escrowPayloadV2 : ByteArray := bytesOfList [0x77, 0x88]

def commitV1 : Nat := effectCommitNat 10 .irreversibleActuation actPayloadV1
def commitV3 : Nat := effectCommitNat 30 .irreversibleActuation actPayloadV3

/-- View-1 post-GST finalized consensus trace committing to `(10, .irreversibleActuation, actPayloadV1)`. -/
def sentOutboxV1 : Sent :=
  runPostGstHonestLeaderView proto4 cfg4 sched4_v1 [] 1 commitV1 []

/-- View-2 timeout dummy extension `[.block 1 commitV1, .dummy 2]` (orphaning competing branch `.block 2 999999`). -/
def sentOutboxV2Dummy : Sent :=
  scheduleHonestVotes proto4 2 (.dummy 2) proto4.committee sentOutboxV1

/-- View-3 post-GST finalized consensus trace committing to `(30, .irreversibleActuation, actPayloadV3)`
    on canonical chain `[.block 1 commitV1, .dummy 2, .block 3 commitV3]`
    (`proto4.leader 3 = committee[(3 - 1) % 4] = 2`, honest!). -/
def chainOutboxV1 : Chain := [.block 1 commitV1]
def chainOutboxV3 : Chain := [.block 1 commitV1, .dummy 2, .block 3 commitV3]

def sched4_v3 : ViewExecutionSchedule := ⟨200, 0, (fun _ => 201), (fun _ => 210), (fun _ => 218)⟩

def sentOutboxV3 : Sent :=
  runPostGstHonestLeaderView proto4 cfg4 sched4_v3 sentOutboxV2Dummy 3 commitV3
    [.block 1 commitV1, .dummy 2]

def finCertV1 : FinCert :=
  (extractFinCert? proto4 sentOutboxV1 1 chainOutboxV1).getD ⟨1, [], []⟩

def finCertV3 : FinCert :=
  (extractFinCert? proto4 sentOutboxV3 3 chainOutboxV3).getD ⟨3, [], []⟩

example : finCertV1.checks proto4 sentOutboxV1 = true := by decide
example : finCertV3.checks proto4 sentOutboxV3 = true := by decide

def initOutboxSt : OutboxState where
  gatekeeperPd         := 3
  highWaterNullifier   := 0
  escrowVaultBalance   := 500
  readAuditCount       := 0
  activeEscrows        := []
  settledEscrowTotal   := 0
  dispatchedActuations := []

/-- Turn 1: Pre-finality `.idempotentRead` admitted on empty `sent = []`. -/
def reqTurn1Read : OutboxEffectReq where
  nullifierId   := 1
  effectClass   := .idempotentRead
  targetView    := 1
  proposedChain := []
  finCert?      := none
  escrowBond?   := none
  spsc          := ⟨0, bytesOfList [0x01], bytesOfList [0x02]⟩

/-- Turn 2: `.irreversibleActuation` (`nullifierId = 10`) WITH concurrent post-copy shared-ring
    DMA TOCTOU overwrite (`sharedRingAfterVerify = dmaTamperedBytes ≠ actPayloadV1`). -/
def reqTurn2ActToctou : OutboxEffectReq where
  nullifierId   := 10
  effectClass   := .irreversibleActuation
  targetView    := 1
  proposedChain := chainOutboxV1
  finCert?      := some finCertV1
  escrowBond?   := none
  spsc          := ⟨0, actPayloadV1, dmaTamperedBytes⟩

/-- Turn 3: Optimistic `.compensatableEscrow` (`nullifierId = 20`, deposit `100`, rollbackCost `25`)
    placed on an unfinalized view-2 branch `[.block 1 commitV1, .block 2 999999]` that will be orphaned! -/
def reqTurn3EscrowOrphan : OutboxEffectReq where
  nullifierId   := 20
  effectClass   := .compensatableEscrow
  targetView    := 2
  proposedChain := [.block 1 commitV1, .block 2 999999]
  finCert?      := none
  escrowBond?   := some ⟨100, 25⟩
  spsc          := ⟨0, escrowPayloadV2, dmaTamperedBytes⟩

/-- Turn 4: `.irreversibleActuation` (`nullifierId = 30`) on view-3 canonical finalized chain
    after view-2 timeout skip, paired with escrow rollback reconciliation! -/
def reqTurn4ActV3 : OutboxEffectReq where
  nullifierId   := 30
  effectClass   := .irreversibleActuation
  targetView    := 3
  proposedChain := chainOutboxV3
  finCert?      := some finCertV3
  escrowBond?   := none
  spsc          := ⟨0, actPayloadV3, dmaTamperedBytes⟩

/-- **TOCTOU Immunity Verification**: post-copy DMA mutation `dmaTamperedBytes` is completely ignored;
    dispatched payload equals `actPayloadV1`! -/
example :
    checkOutboxOk
      (auditOutboxStep proto4 sampleValidPartition sentOutboxV1 initOutboxSt reqTurn2ActToctou)
      (fun st' =>
        st'.dispatchedActuations.map DispatchedActuation.dispatchedPayload == [actPayloadV1] &&
        st'.dispatchedActuations.map DispatchedActuation.dispatchedPayload != [dmaTamperedBytes]) = true := by
  decide

/-- **TOCTOU Pre-Copy Tamper Refusal**: if shared ring was corrupted *before* copy so `privateCopy = dmaTamperedBytes`,
    the 256-bit cSHAKE256 block commitment check refuses with `.unfinalizedOrMismatchedBlockCommit 10 1`! -/
def reqPreCopyTampered : OutboxEffectReq :=
  { reqTurn2ActToctou with spsc := ⟨0, dmaTamperedBytes, dmaTamperedBytes⟩ }

example :
    checkOutboxErr
      (auditOutboxStep proto4 sampleValidPartition sentOutboxV1 initOutboxSt reqPreCopyTampered)
      (.unfinalizedOrMismatchedBlockCommit 10 1) = true := by
  decide

/-- **Unfinalized-Block Irreversible Actuation Refusal 1**: missing `FinCert` refused! -/
example :
    checkOutboxErr
      (auditOutboxStep proto4 sampleValidPartition sentOutboxV1 initOutboxSt
        { reqTurn2ActToctou with finCert? := none })
      (.missingFinalityCert 10) = true := by
  decide

/-- **Unfinalized-Block Irreversible Actuation Refusal 2**: notarized-only / proposal-only trace
    lacking `2f + 1` `.finalize` votes refused with `.invalidFinalityCert 10 1`! -/
def sentUnfinalizedOnlyVotes : Sent :=
  scheduleHonestVotes proto4 1 (.block chainOutboxV1) proto4.committee
    [⟨0, 1, .propose, .block chainOutboxV1⟩]

example :
    checkOutboxErr
      (auditOutboxStep proto4 sampleValidPartition sentUnfinalizedOnlyVotes initOutboxSt reqTurn2ActToctou)
      (.invalidFinalityCert 10 1) = true := by
  decide

/-- **Duplicate & Stale Outbox Nullifier Refusals**: replaying `nullifierId = 10` or stale `5`
    after `highWaterNullifier = 10` is deterministically refused! -/
example :
    (match stepOutbox proto4 sampleValidPartition sentOutboxV1 initOutboxSt reqTurn2ActToctou with
     | none => false
     | some stAfter10 =>
       checkOutboxErr
         (auditOutboxStep proto4 sampleValidPartition sentOutboxV1 stAfter10 reqTurn2ActToctou)
         (.staleOrDuplicateNullifier 10 10) &&
       checkOutboxErr
         (auditOutboxStep proto4 sampleValidPartition sentOutboxV3 stAfter10
           { reqTurn4ActV3 with nullifierId := 5 })
         (.staleOrDuplicateNullifier 5 10)) = true := by
  decide

/-! ### Multi-Turn / Multi-View `ValidOutboxTrace` & Pillar-6 Apex Theorem Instantiation -/

private theorem step_to_sentSteps {P : Protocol} {s₁ s₂ : Sent} (h : Step P s₁ s₂) :
    SentSteps P s₁ s₂ :=
  SentSteps.step (SentSteps.refl s₁) h

private theorem scheduleVotes_sentSteps {P : Protocol} {v : Nat} {t : Target} :
    ∀ (nodes : List NodeId) {sent : Sent},
      SentSteps P sent (scheduleHonestVotes P v t nodes sent)
  | [], _ => SentSteps.refl _
  | n :: ns, sent => by
    unfold scheduleHonestVotes
    split
    · rename_i hCond
      simp only [Bool.and_eq_true, List.contains_iff_mem] at hCond
      have hNf : P.faulty n = false := by cases hf : P.faulty n <;> simp_all
      have hAv : votedAny sent n v = false := by cases hv : votedAny sent n v <;> simp_all
      have hStep := Step.vote sent n v t ⟨hCond.1.1.2, hNf⟩ hAv
        (Obend.Consensus.SimplexTrace.voteRuleB_sound hCond.2)
      exact sentSteps_trans (step_to_sentSteps hStep) (scheduleVotes_sentSteps ns)
    · exact scheduleVotes_sentSteps ns

private theorem scheduleFinalizes_sentSteps {P : Protocol} {v : Nat} {c : Chain} :
    ∀ (nodes : List NodeId) {sent : Sent},
      SentSteps P sent (scheduleHonestFinalizes P v c nodes sent)
  | [], _ => SentSteps.refl _
  | n :: ns, sent => by
    unfold scheduleHonestFinalizes
    split
    · rename_i hCond
      simp only [Bool.and_eq_true, List.contains_iff_mem, decide_eq_true_eq] at hCond
      have hNf : P.faulty n = false := by cases hf : P.faulty n <;> simp_all
      have hStep := Step.finalize sent n v c ⟨hCond.1.1.1.2, hNf⟩ hCond.1.2 hCond.2
      exact sentSteps_trans (step_to_sentSteps hStep) (scheduleFinalizes_sentSteps ns)
    · exact scheduleFinalizes_sentSteps ns

private theorem postGstView_sentSteps {P : Protocol} (cfg : PartialSyncConfig)
    (sched : ViewExecutionSchedule) (sent₀ : Sent) (v payload : Nat) (p : Chain)
    (hHonLeader : P.honest (P.leader v)) :
    SentSteps P sent₀ (runPostGstHonestLeaderView P cfg sched sent₀ v payload p) := by
  unfold runPostGstHonestLeaderView
  have hProp : Step P sent₀ (⟨P.leader v, v, .propose, .block (p ++ [.block v payload])⟩ :: sent₀) :=
    Step.propose sent₀ (P.leader v) v (p ++ [.block v payload]) hHonLeader rfl
  exact sentSteps_trans (step_to_sentSteps hProp)
    (sentSteps_trans (scheduleVotes_sentSteps P.committee) (scheduleFinalizes_sentSteps P.committee))

def st1 : OutboxState :=
  (stepOutbox proto4 sampleValidPartition [] initOutboxSt reqTurn1Read).getD initOutboxSt

def st2 : OutboxState :=
  (stepOutbox proto4 sampleValidPartition sentOutboxV1 st1 reqTurn2ActToctou).getD initOutboxSt

def st3 : OutboxState :=
  (stepOutbox proto4 sampleValidPartition sentOutboxV1 st2 reqTurn3EscrowOrphan).getD initOutboxSt

def st4Mid : OutboxState :=
  (stepOutbox proto4 sampleValidPartition sentOutboxV3 st3 reqTurn4ActV3).getD initOutboxSt

def st4Final : OutboxState :=
  (reconcileEscrowsWithCert proto4 sentOutboxV3 finCertV3 st4Mid).getD initOutboxSt

/-- Verify multi-turn state outcomes:
    - Both irreversible actuations `[30, 10]` dispatched with exact pre-TOCTOU private snapshots,
    - Orphaned view-2 optimistic escrow rolled back (`escrowVaultBalance = 475`, `settledEscrowTotal = 25`,
      `activeEscrows = []`, total `475 + 0 + 25 = 500` conserved!). -/
example : st4Final.dispatchedActuations.map DispatchedActuation.nullifierId = [30, 10] := by decide
example : st4Final.dispatchedActuations.map DispatchedActuation.dispatchedPayload =
            [actPayloadV3, actPayloadV1] := by decide
example : st4Final.escrowVaultBalance = 475 := by decide
example : st4Final.settledEscrowTotal = 25 := by decide
example : st4Final.activeEscrows = [] := by decide

def multiTurnTrace : List OutboxTurn :=
  [ ⟨[], reqTurn1Read, none⟩
  , ⟨sentOutboxV1, reqTurn2ActToctou, none⟩
  , ⟨sentOutboxV1, reqTurn3EscrowOrphan, none⟩
  , ⟨sentOutboxV3, reqTurn4ActV3, some finCertV3⟩ ]

theorem multiTurnTrace_valid :
    ValidOutboxTrace proto4 sampleValidPartition [] initOutboxSt multiTurnTrace sentOutboxV3 st4Final := by
  have hStep1 : stepOutbox proto4 sampleValidPartition [] initOutboxSt reqTurn1Read = some st1 := by decide
  have hStep2 : stepOutbox proto4 sampleValidPartition sentOutboxV1 st1 reqTurn2ActToctou = some st2 := by decide
  have hStep3 : stepOutbox proto4 sampleValidPartition sentOutboxV1 st2 reqTurn3EscrowOrphan = some st3 := by decide
  have hStep4 : stepOutbox proto4 sampleValidPartition sentOutboxV3 st3 reqTurn4ActV3 = some st4Mid := by decide
  have hRec4  : reconcileEscrowsWithCert proto4 sentOutboxV3 finCertV3 st4Mid = some st4Final := by decide
  have hIso   : checkMicrokitIsolation sampleValidPartition = true := by decide
  have hHon0  : proto4.honest (proto4.leader 1) := ⟨by decide, by decide⟩
  have hHon2  : proto4.honest (proto4.leader 3) := ⟨by decide, by decide⟩
  have hNet01 : SentSteps proto4 [] sentOutboxV1 :=
    postGstView_sentSteps cfg4 sched4_v1 [] 1 commitV1 [] hHon0
  have hNet13 : SentSteps proto4 sentOutboxV1 sentOutboxV3 :=
    sentSteps_trans (scheduleVotes_sentSteps proto4.committee)
      (postGstView_sentSteps cfg4 sched4_v3 sentOutboxV2Dummy 3 commitV3
        [.block 1 commitV1, .dummy 2] hHon2)
  have hReachV1 : Reach proto4 sentOutboxV1 := sentSteps_reach Reach.nil hNet01
  have hReachV3 : Reach proto4 sentOutboxV3 := sentSteps_reach hReachV1 hNet13
  exact ⟨Reach.nil, SentSteps.refl [], st1, st1, hStep1, rfl,
    ⟨Reach.nil, hNet01, st2, st2, hStep2, rfl,
      ⟨hReachV1, SentSteps.refl sentOutboxV1, st3, st3, hStep3, rfl,
        ⟨hReachV1, hNet13, st4Mid, st4Final, hStep4, hRec4,
          ⟨rfl, rfl, hReachV3, hIso⟩⟩⟩⟩⟩

/-- Concrete instantiation of Pillar-6 apex theorem `firmament_sel4_copy_before_verify_and_irreversible_outbox_safe`
    and `irreversible_at_most_once_and_never_rolled_back` on `multiTurnTrace`! -/
example :
    (st4Final.dispatchedActuations.map DispatchedActuation.nullifierId).Nodup ∧
    st4Final.escrowVaultBalance + lockedEscrowDeposits st4Final.activeEscrows + st4Final.settledEscrowTotal = 500 ∧
    (∀ a₁ ∈ st4Final.dispatchedActuations, ∀ a₂ ∈ st4Final.dispatchedActuations,
      a₁.chain <+: a₂.chain ∨ a₂.chain <+: a₁.chain) := by
  have hApex := firmament_sel4_copy_before_verify_and_irreversible_outbox_safe rfl multiTurnTrace_valid
  have hOnce := irreversible_at_most_once_and_never_rolled_back rfl multiTurnTrace_valid
  exact ⟨hApex.2.2.1, hApex.2.2.2.1, hOnce.2.1⟩

/-! ## 4. Mutation-Sensitivity Witnesses (`#tooth`, 7 Kills) & Kernel Axiom Audit -/

-- Kill 1: Bypassing sender signature verification breaks `verifySignedSent_projects_to_reach`
#tooth Obend.Consensus.SimplexLiveness.verifySignedSent_projects_to_reach by mutation
  Obend.Consensus.SimplexLiveness.verifySignedMsg := fun _ _ _ _ => true

-- Kill 2: Voting `.dummy v` unconditionally even before view timeout breaks post-GST finalization
#tooth Obend.Consensus.SimplexLiveness.gst_honest_leader_finalizes by mutation
  Obend.Consensus.SimplexLiveness.selectTimedVoteTarget := fun _ _ v _ _ => .dummy v

-- Kill 3: Suppressing `.finalize` votes breaks single-view `FinCert` formation
#tooth Obend.Consensus.SimplexLiveness.gst_honest_leader_finalizes by mutation
  Obend.Consensus.SimplexLiveness.scheduleHonestFinalizes := fun _ _ _ _ sent => sent

-- Kill 4: Suppressing honest timeout `.dummy` votes breaks `pre_gst_or_faulty_leader_advances_view`
#tooth Obend.Consensus.SimplexLiveness.pre_gst_or_faulty_leader_advances_view by mutation
  Obend.Consensus.SimplexLiveness.scheduleHonestVotes := fun _ _ _ _ sent => sent

-- Kill 5: Double-fetch SPSC TOCTOU bug (reading `sharedRingAfterVerify` instead of `privateSnapshot`!)
#tooth Obend.Vault.IrreversibleOutbox.firmament_sel4_copy_before_verify_and_irreversible_outbox_safe by mutation
  Obend.Vault.IrreversibleOutbox.selectActuationSource := fun _priv sharedAfter => sharedAfter

-- Kill 6: Accepting mismatched / unverified block payload commitments breaks Pillar-6 apex safety
#tooth Obend.Vault.IrreversibleOutbox.firmament_sel4_copy_before_verify_and_irreversible_outbox_safe by mutation
  Obend.Vault.IrreversibleOutbox.checkChainTipCommit := fun _ _ _ => true

-- Kill 7: Minting unbacked escrow refunds during branch rollback breaks vault conservation
#tooth Obend.Vault.IrreversibleOutbox.reconcileEscrowsWithCert_conserves by mutation
  Obend.Vault.IrreversibleOutbox.reconcileEscrowList := fun _ _ _ => ([], 999, 0)

#assert_axioms_tree

end Obend.Tests.SimplexLivenessAndOutbox
end
