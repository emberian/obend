module
public import Obend.Crypto.BinaryTower256
public import Obend.Judge.DecoAndCallTree
import all Init.Data.String.Defs
import all Obend.Crypto.BinaryTower256
import all Obend.Judge.DecoAndCallTree
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
import all Obend.Crypto.DualSpine
import all Obend.Crypto.Multilinear
import all Obend.Crypto.PCS
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
import all Obend.Intention
import all Obend.Judge.AutomataConfinement
import all Obend.Judge.Class
import all Obend.Judge.Clearing
import all Obend.Judge.Computational
import all Obend.Judge.TranscriptPolicy
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
import all Obend.Ledger.Book
import all Obend.Ledger.Floors
import all Obend.Ledger.Register
import all Obend.Ledger.Seat
import all Obend.Logic.Claim
import all Obend.Logic.LateBinding
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
import all Obend.Spec.Proofs.C4
import all Obend.Tactic.Cases
import all Obend.Tactic.MonadicReduction
import all Obend.Tactic.Tooth

public section
namespace Obend.Tests.BinaryTowerDecoCallTree
open Obend.Crypto Obend.Crypto.BinaryTower256 Obend.Judge.DecoAndCallTree
set_option autoImplicit false
set_option Elab.async false

example (a : Tower256) : ofExec256 (toExec256 a) = a := ofExec256_toExec256 a
example (a : Tower256Exec) : ofBytes32 (toBytes32 a) = some a := ofBytes32_toBytes32 a
example (a b : TowerElem 3) (h : embedTowerChain 3 5 a = embedTowerChain 3 5 b) : a = b :=
  embedTowerChain_injective 3 5 a b h
example (a : Tower128) (ha : a ≠ towerZero 7) : towerMul 7 a (towerInv 7 a) = towerOne 7 :=
  towerMul_inv 7 a ha
example : towerMul 1 (false, true) (false, true) = (true, true) := by rfl
example : mulExec 3 0x53 0xca = packTower 3 (towerMul 3 (unpackTower 3 0x53) (unpackTower 3 0xca)) := by
  simpa only [packTower_unpackTower] using mulExec_refines 3 (unpackTower 3 0x53) (unpackTower 3 0xca)
example : Simulates 8 (towerAdd 8 (unpackTower 8 0x123456789abcdef) (unpackTower 8 0x10000000000000000))
    (0x123456789abcdef ^^^ 0x10000000000000000) :=
  Simulates.add 8 (packTower_unpackTower 8 _) (packTower_unpackTower 8 _)

example : mulExec 7 (packTower 7 (towerOne 7)) (packTower 7 (towerOne 7)) =
    packTower 7 (towerOne 7) := by rw [mulExec_refines, towerMul_one]
example : mulExec 8 (packTower 8 (towerOne 8)) (packTower 8 (towerOne 8)) =
    packTower 8 (towerOne 8) := by rw [mulExec_refines, towerMul_one]
example : ofBytes32 (toBytes32 (0x8000000000000000000000000000000000000000000000000000000000000001 : Tower256Exec)) =
    some 0x8000000000000000000000000000000000000000000000000000000000000001 := ofBytes32_toBytes32 _

example (H : Tower128) : ghashPoly H [] = ghashPoly H [towerZero 7] := ghashPoly_leading_zero H
example : ghashPoly (towerOne 7) [towerOne 7] ≠ ghashPoly (towerOne 7) [towerZero 7] := by
  simpa [ghashPoly, RoundPoly.evalCoeffs, CommRingOps.zero, CommRingOps.add, CommRingOps.mul] using towerOne_ne_zero 7

example : (1 : Nat) ≤ 1 :=
  ghashDiff_roots_bound [towerOne 7] [towerZero 7] 1 [towerZero 7]
    (by decide +kernel) (by decide +kernel) (by simp)
    ⟨towerOne 7, by simpa [ghashPoly, RoundPoly.evalCoeffs,
      CommRingOps.zero, CommRingOps.add, CommRingOps.mul] using towerOne_ne_zero 7⟩
    (by intro H h; simp only [List.mem_singleton] at h; subst H
        simp [ghashPoly, RoundPoly.evalCoeffs, CommRingOps.zero, CommRingOps.add, CommRingOps.mul])

example : decList (encList [[], [0], [255, 128, 0]]) = some [[], [0], [255, 128, 0]] := decList_encList _
example : encList [[1, 2], [3]] ≠ encList [[1], [2, 3]] := by
  intro h
  have := encList_injective _ _ h
  contradiction

/-- Bytes are literal fixtures; hash equality is proved symbolically, without evaluating the sponge in the kernel. -/
def paymentRequest : ByteArray := "Authorization: Bearer sk_live_secret_99\r\n\r\npi_3Q9x77".toUTF8
def paymentResponse : ByteArray := "HTTP/1.1 200 OK\r\n\r\n{\"id\":\"pi_3Q9x77\",\"status\":\"succeeded\",\"amount\":4200}".toUTF8
def paymentRecord : SessionRecord :=
  { host := "api.payments.example".toUTF8, notary := "notary-key-256".toUTF8,
    time := 100, request := paymentRequest, response := paymentResponse,
    ghashTag := towerOne 7, verifierNonce := "nonce-payment-1".toUTF8,
    paymentIntentId := "pi_3Q9x77".toUTF8 }
def zeroMask (b : ByteArray) : ByteArray := ⟨Array.replicate b.size 0⟩
def paymentRequestMask : ByteArray :=
  ⟨((List.replicate 22 (0 : UInt8)) ++ List.replicate 17 255 ++ List.replicate (paymentRequest.size - 39) 0).toArray⟩
def payment : DecoAttestation :=
  { record := paymentRecord, recordTranscriptCommit := recordCommit paymentRecord,
    requestMask := paymentRequestMask, responseMask := zeroMask paymentResponse,
    requestFacts := [⟨43, "pi_3Q9x77".toUTF8⟩],
    responseFacts := [⟨26, "pi_3Q9x77".toUTF8⟩, ⟨47, "succeeded".toUTF8⟩] }
def paymentPolicy : DecoPolicy :=
  { authenticatedRecords := [paymentRecord], notaries := [paymentRecord.notary],
    hosts := [paymentRecord.host], minTime := 90, maxTime := 110,
    secretRequestOffsets := List.range 17 |>.map (· + 22) }
def emptyLedger : SessionLedger := ⟨[], []⟩

example : checkMask paymentRecord.request payment.requestMask = true := by decide +kernel
example : checkSpan paymentRecord.response payment.responseMask ⟨26, "pi_3Q9x77".toUTF8⟩ = true := by decide +kernel
example : checkSpan paymentRecord.response payment.responseMask ⟨26, "pi_TAMPER".toUTF8⟩ = false := by decide +kernel
example : checkSpan paymentRecord.request payment.requestMask ⟨22, "sk_live_secret_99".toUTF8⟩ = false := by decide +kernel

example : checkDecoAttestation paymentPolicy emptyLedger payment = true := by
  unfold checkDecoAttestation payment
  simp only [decide_true, Bool.true_and]
  decide +kernel

private theorem paymentRelation : DecoRelation paymentPolicy emptyLedger payment := by
  apply (checkDecoAttestation_iff_relation _ _ _).mp
  unfold checkDecoAttestation payment
  simp only [decide_true, Bool.true_and]
  decide +kernel

example : checkDecoTrace paymentPolicy emptyLedger [payment, payment] = false := by
  have hr : checkDecoAttestation paymentPolicy (consume emptyLedger payment) payment = false :=
    replay_nonce_rejected paymentPolicy (consume emptyLedger payment) (consume emptyLedger payment) []
      (.nil _) payment (.head _)
  simp only [checkDecoTrace, hr, Bool.false_and, Bool.and_false]

example : checkFresh (consume emptyLedger payment) payment = false := by decide +kernel
example : checkPolicy { paymentPolicy with minTime := 101 } payment = false := by decide +kernel
example : checkPolicy { paymentPolicy with notaries := [] } payment = false := by decide +kernel
example : checkPolicy { paymentPolicy with hosts := [] } payment = false := by decide +kernel

example : bindAdv (shareRecord paymentRecord) = 0 := deco_sameOpening_bindAdv_zero _
example : OpeningRelation (recordCommit paymentRecord) paymentRecord := by rfl

/-- Three authenticated network hops under one deterministic orchestrator. -/
def settlementRecord : SessionRecord :=
  { paymentRecord with
    request := "pi_3Q9x77".toUTF8, response := "settled".toUTF8,
    verifierNonce := "nonce-settlement-3".toUTF8, paymentIntentId := "settlement:pi_3Q9x77".toUTF8 }
def settlement : DecoAttestation :=
  { record := settlementRecord, recordTranscriptCommit := recordCommit settlementRecord,
    requestMask := zeroMask settlementRecord.request, responseMask := zeroMask settlementRecord.response,
    requestFacts := [], responseFacts := [] }
def settlementTree : HttpsCallTree := .node ⟨.leafHttpsHop, settlement, 0⟩ []
def recursiveRecord : SessionRecord :=
  { paymentRecord with
    request := "pi_3Q9x77".toUTF8,
    response := "HTTP/1.1 200 OK\r\n\r\n".toUTF8 ++ rootField (mrootC [treeRoot settlementTree]),
    verifierNonce := "nonce-recorder-2".toUTF8, paymentIntentId := "recorder:pi_3Q9x77".toUTF8 }
def recursiveAttestation : DecoAttestation :=
  { record := recursiveRecord, recordTranscriptCommit := recordCommit recursiveRecord,
    requestMask := zeroMask recursiveRecord.request, responseMask := zeroMask recursiveRecord.response,
    requestFacts := [], responseFacts := [] }
def recursiveTree : HttpsCallTree := .node ⟨.recursiveHttpsCallee, recursiveAttestation, 19⟩ [settlementTree]
def orchestrator : DecoAttestation :=
  { payment with record := { paymentRecord with request := "start".toUTF8, response := "scheduled".toUTF8 } }
def threeHopTree : HttpsCallTree := .node ⟨.localComputation, orchestrator, 0⟩
  [.node ⟨.leafHttpsHop, payment, 0⟩ [], recursiveTree]
def threeHopPolicy : CallTreePolicy :=
  { deco := { paymentPolicy with
        authenticatedRecords := [paymentRecord, recursiveRecord, settlementRecord],
        secretRequestOffsets := [] },
    ledger := emptyLedger, recorders := [paymentRecord.host], localEval := fun _ => "scheduled".toUTF8 }
def paymentEdge : DataflowEdge := ⟨1, 2, 26, 0, "pi_3Q9x77".toUTF8⟩
def threeHopClaim : CallTreeClaim :=
  ⟨threeHopPolicy, threeHopTree, treeRoot threeHopTree, [paymentEdge]⟩

theorem zeroMask_size (bs : ByteArray) : (zeroMask bs).size = bs.size := by
  change (Array.replicate bs.size (0 : UInt8)).size = bs.size
  exact Array.size_replicate

theorem zeroMask_get (bs : ByteArray) (i : Nat) (hi : i < bs.size) : (zeroMask bs)[i]! = 0 := by
  have hm : i < (zeroMask bs).size := by rw [zeroMask_size]; exact hi
  rw [getElem!_pos (zeroMask bs) i hm]
  exact Array.getElem_replicate (by simpa only [Array.size_replicate] using hi)

theorem checkMask_zero (bs : ByteArray) : checkMask bs (zeroMask bs) = true := by
  apply (checkMask_iff _ _).mpr
  exact ⟨(zeroMask_size bs).symm, fun i hi => Or.inl (zeroMask_get bs i hi)⟩

theorem checkSpan_suffix (lead bs : ByteArray) (hn : 0 < bs.size) :
    checkSpan (lead ++ bs) (zeroMask (lead ++ bs)) ⟨lead.size, bs⟩ = true := by
  apply (checkSpan_iff _ _ _).mpr
  refine ⟨hn, by simp, zeroMask_size _, ?_⟩
  intro j hj
  change j < bs.size at hj
  have hfull : lead.size + j < (lead ++ bs).size := by rw [ByteArray.size_append]; omega
  refine ⟨zeroMask_get _ _ hfull, ?_⟩
  change (lead ++ bs)[lead.size + j]! = bs[j]!
  rw [getElem!_pos (lead ++ bs) _ hfull, ByteArray.getElem_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left, getElem!_pos bs j hj]

theorem prefix_get (lead bs : ByteArray) (i : Nat) (hi : i < lead.size) :
    (lead ++ bs)[i]! = lead[i]! := by
  have hfull : i < (lead ++ bs).size := by rw [ByteArray.size_append]; omega
  rw [getElem!_pos (lead ++ bs) _ hfull, ByteArray.getElem_append_left hi, getElem!_pos lead i hi]

def httpHeader : ByteArray := "HTTP/1.1 200 OK\r\n\r\n".toUTF8

theorem bodyStart_header (bs : ByteArray) : bodyStart (httpHeader ++ bs) = some 19 := by
  have hs : httpHeader.size = 19 := by decide +kernel
  unfold bodyStart
  rw [ByteArray.size_append, hs, List.range_add, List.find?_append]
  have hf : (List.range 19).find? (fun i => decide (i + 4 ≤ (httpHeader ++ bs).size) &&
      (httpHeader ++ bs)[i]! == 13 && (httpHeader ++ bs)[i+1]! == 10 &&
      (httpHeader ++ bs)[i+2]! == 13 && (httpHeader ++ bs)[i+3]! == 10) = some 15 := by
    have hg (i : Nat) (hi : i < 19) : (httpHeader ++ bs)[i]! = httpHeader[i]! :=
      prefix_get _ _ _ (by rw [hs]; exact hi)
    have hb (i : Nat) (hi : i ≤ 15) : decide (i + 4 ≤ (httpHeader ++ bs).size) = true := by
      rw [ByteArray.size_append, hs]
      exact decide_eq_true (by omega)
    simp only [show List.range 19 = [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18] from rfl,
      List.find?_cons]
    simp only [hg 0 (by decide), hg 1 (by decide), hg 2 (by decide), hg 3 (by decide),
      hg 4 (by decide), hg 5 (by decide), hg 6 (by decide), hg 7 (by decide), hg 8 (by decide),
      hg 9 (by decide), hg 10 (by decide), hg 11 (by decide), hg 12 (by decide), hg 13 (by decide),
      hg 14 (by decide), hg 15 (by decide), hg 16 (by decide), hg 17 (by decide), hg 18 (by decide),
      hb 0 (by decide), hb 1 (by decide), hb 2 (by decide), hb 3 (by decide),
      hb 4 (by decide), hb 5 (by decide), hb 6 (by decide), hb 7 (by decide), hb 8 (by decide),
      hb 9 (by decide), hb 10 (by decide), hb 11 (by decide), hb 12 (by decide), hb 13 (by decide),
      hb 14 (by decide), hb 15 (by decide)]
    rfl
  simp only [ByteArray.size_append, hs] at hf
  rw [hf]
  rfl

theorem rootField_size (root : Hash256) : (rootField root).size = 81 := by
  change (("\"subtree_root\":\"".toUTF8.data.toList ++ hex64 root ++ "\"".toUTF8.data.toList).toArray).size = 81
  rw [List.size_toArray, List.length_append, List.length_append, hex64_length]
  decide +kernel

private theorem recursiveRootAccepted :
    checkSubtreeRoot recursiveAttestation 19 (mrootC [treeRoot settlementTree]) = true := by
  apply (checkSubtreeRoot_iff _ _ _).mpr
  refine ⟨19, bodyStart_header _, Nat.le_refl _, ?_⟩
  apply (checkSpan_iff _ _ _).mp
  have hs : httpHeader.size = 19 := by decide +kernel
  have h := checkSpan_suffix httpHeader (rootField (mrootC [treeRoot settlementTree]))
    (by rw [rootField_size]; decide)
  rw [hs] at h
  exact h

example : checkDataflowEdge (treeHops threeHopTree).toArray paymentEdge = true := by decide +kernel
example : checkDataflowEdge (treeHops threeHopTree).toArray { paymentEdge with dstOff := 1 } = false := by decide +kernel

private theorem paymentRelationAt (ledger : SessionLedger) (hf : Fresh ledger payment) :
    DecoRelation threeHopPolicy.deco ledger payment := by
  obtain ⟨hc, _, _, hm, hr, hq, hs⟩ := paymentRelation
  refine ⟨hc, hf, ?_, hm, hr, hq, hs⟩
  refine ⟨.head _, .head _, .head _, ?_, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
  · intro i hi; cases hi

private theorem settlementRelationAt (ledger : SessionLedger) (hf : Fresh ledger settlement) :
    DecoRelation threeHopPolicy.deco ledger settlement := by
  refine ⟨rfl, hf, ?_, (checkMask_iff _ _).mp (checkMask_zero _),
    (checkMask_iff _ _).mp (checkMask_zero _), ?_, ?_⟩
  · refine ⟨.tail _ (.tail _ (.head _)), .head _, .head _, ?_, ?_, ?_⟩
    · decide +kernel
    · decide +kernel
    · intro i hi; cases hi
  · intro s hs; cases hs
  · intro s hs; cases hs

private theorem recursiveRelationAt (ledger : SessionLedger) (hf : Fresh ledger recursiveAttestation) :
    DecoRelation threeHopPolicy.deco ledger recursiveAttestation := by
  refine ⟨rfl, hf, ?_, (checkMask_iff _ _).mp (checkMask_zero _),
    (checkMask_iff _ _).mp (checkMask_zero _), ?_, ?_⟩
  · refine ⟨.tail _ (.head _), .head _, .head _, ?_, ?_, ?_⟩
    · decide +kernel
    · decide +kernel
    · intro i hi; cases hi
  · intro s hs; cases hs
  · intro s hs; cases hs

private theorem threeHopMeaning :
    CallTreeMeaning threeHopPolicy threeHopTree (treeRoot threeHopTree) [paymentEdge] := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · change _ ∧ (_ ∧ (_ ∧ True))
    refine ⟨?_, ?_, ?_, trivial⟩
    · rfl
    · change (true = true ∧ DecoRelation _ _ payment) ∧ True
      exact ⟨⟨rfl, paymentRelationAt _ (by apply (checkFresh_iff _ _).mp; decide +kernel)⟩, trivial⟩
    · change (_ ∧ _ ∧ SubtreeRootMeaning recursiveAttestation 19 (mrootC [treeRoot settlementTree])) ∧
        (((true = true ∧ DecoRelation _ _ settlement) ∧ True) ∧ True)
      exact ⟨⟨recursiveRelationAt _ (by apply (checkFresh_iff _ _).mp; decide +kernel),
        .head _, (checkSubtreeRoot_iff _ _ _).mp recursiveRootAccepted⟩,
        ⟨⟨⟨rfl, settlementRelationAt _ (by apply (checkFresh_iff _ _).mp; decide +kernel)⟩, trivial⟩, trivial⟩⟩
  · refine ⟨_, ValidDecoTrace.cons (paymentRelationAt _ ?_)
        (ValidDecoTrace.cons (recursiveRelationAt _ ?_)
          (ValidDecoTrace.cons (settlementRelationAt _ ?_) (ValidDecoTrace.nil _)))⟩ <;>
      apply (checkFresh_iff _ _).mp <;> decide +kernel
  · intro e he
    have heq : e = paymentEdge := List.mem_singleton.mp he
    subst e
    apply (checkDataflowEdge_iff _ _).mp
    decide +kernel

example : callTreeVerify threeHopPolicy threeHopTree (treeRoot threeHopTree) [paymentEdge] = true :=
  (callTreeVerify_iff _ _ _ _).mpr threeHopMeaning

example : callTreeJudge.check 0 threeHopClaim ⟨0⟩ = .ok := by
  change (if callTreeVerify threeHopPolicy threeHopTree (treeRoot threeHopTree) [paymentEdge] then _ else _) = _
  rw [(callTreeVerify_iff _ _ _ _).mpr threeHopMeaning]
  rfl

#guard callTreeVerify threeHopPolicy threeHopTree (treeRoot threeHopTree) [paymentEdge]
#guard !(checkSubtreeRoot recursiveAttestation 19 (recordCommit paymentRecord))
#guard !(checkDataflowEdge (treeHops threeHopTree).toArray { paymentEdge with dstOff := 1 })
#guard match callTreeJudge.check 0 threeHopClaim ⟨0⟩ with | .ok => true | _ => false
#guard match callTreeJudge.check 0 { threeHopClaim with requiredEdges := [{ paymentEdge with dstOff := 1 }] } ⟨0⟩ with
  | .refused _ [] => true | _ => false

example : checkFresh ⟨[paymentRecord.verifierNonce], []⟩ payment = false := by decide +kernel
example : checkFresh ⟨[], [paymentRecord.paymentIntentId]⟩ payment = false := by decide +kernel

#tooth checkDecoAttestation_iff_relation by mutation checkDecoAttestation := fun _ _ _ => true
#tooth callTreeVerify_sound_or_collision by mutation callTreeVerify := fun _ _ _ _ => true
#tooth towerScaleX_eq_mul by mutation towerScaleX := fun k _ => towerZero k
#tooth towerKaratsuba_eq by mutation towerKaratsuba := fun k a b => towerAdd k a b
#tooth towerMul_add_distrib by mutation towerMul := fun k _ _ => towerOne k
#tooth checkSpan_iff by mutation checkSpan := fun _ _ _ => true
#tooth checkFresh_iff by mutation checkFresh := fun _ _ => true
#tooth checkPolicy_iff by mutation checkPolicy := fun _ _ => true
#tooth checkSubtreeRoot_iff by mutation checkSubtreeRoot := fun _ _ _ => true
#tooth checkDataflowEdge_iff by mutation checkDataflowEdge := fun _ _ => true
#tooth encList_injective by mutation encList := fun _ => []

#print axioms towerMul_add_distrib
#print axioms embedTower_injective
#print axioms towerMul_inv
#print axioms ghashDiff_roots_bound
#print axioms checkDecoAttestation_iff_relation
#print axioms deco_binds_disclosed_facts_or_collision
#print axioms encList_injective
#print axioms callTreeVerify_sound_or_collision
#assert_axioms_tree

end Obend.Tests.BinaryTowerDecoCallTree
