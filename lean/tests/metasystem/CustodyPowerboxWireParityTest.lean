module
public import Obend.Polis.GrainCustodyHost
import all Obend.Vault.Escrow
import all Obend.Vault.Replay
import all Obend.Vault.WorldTree
import all Obend.Polis.GrainCustodyHost
import Obend.Tactic.Tooth
import all Obend.Polis.GrainPowerbox
import all Obend.Apps.ZkNtt.Goldilocks
import all Obend.AssertAxioms
import all Obend.Core.AliasExposure
import all Obend.Core.Assumptions
import all Obend.Core.Bidirectional
import all Obend.Core.Brand
import all Obend.Core.Check
import all Obend.Core.Data
import all Obend.Core.Digest
import all Obend.Core.EquiRecursiveAgreement
import all Obend.Core.FieldCongruence
import all Obend.Core.FiniteBisimulation
import all Obend.Core.FinitePresentation
import all Obend.Core.FiniteRowLaws
import all Obend.Core.Invariant
import all Obend.Core.Machine
import all Obend.Core.MachineFast
import all Obend.Core.MachineTyping
import all Obend.Core.Proofs.Substitution.Defs
import all Obend.Core.Proofs.Substitution.Uses
import all Obend.Core.Proofs.TypedSubstitution
import all Obend.Core.RecursiveAgreement
import all Obend.Core.RecursiveRows
import all Obend.Core.ResourceSemantics
import all Obend.Core.RowCongruence
import all Obend.Core.RowExposureInvariance
import all Obend.Core.RowHit
import all Obend.Core.Term
import all Obend.Core.TermTraverse
import all Obend.Core.Traverse
import all Obend.Core.Ty
import all Obend.Core.TypeGraph
import all Obend.Core.TypeGraphAlias
import all Obend.Core.TypeGraphHead
import all Obend.Core.TypeGraphResource
import all Obend.Crypto.Multilinear
import all Obend.Crypto.Transcript
import all Obend.Digest.Cshake256
import all Obend.Digest.Cshake256.Fast
import all Obend.Digest.Cshake256.Seam
import all Obend.Digest.Cshake256.Spec
import all Obend.Digest.HashBytes
import all Obend.Doc
import all Obend.Doc.Backlinks
import all Obend.Doc.Graph
import all Obend.Doc.Merge
import all Obend.Doc.Patch
import all Obend.Doc.Render
import all Obend.Doc.Section
import all Obend.Doc.Structured
import all Obend.Intention
import all Obend.Judge.Class
import all Obend.Judge.Computational
import all Obend.Law.Claim
import all Obend.Law.Inherit
import all Obend.Law.Proofs.Claim
import all Obend.Law.Proofs.Eval
import all Obend.Law.Proofs.Inherit
import all Obend.Law.Proofs.Run
import all Obend.Law.Proofs.Std
import all Obend.Law.Proofs.Typing
import all Obend.Law.Run
import all Obend.Law.Std
import all Obend.Law.Syntax
import all Obend.Polis.CapTP
import all Obend.Polis.EvidencedOcap
import all Obend.Polis.BlumRam
import all Obend.Polis.ZkBiscuit
import all Obend.Run.Core4
import all Obend.Run.Runner
import all Obend.Slot
import all Obend.Slot.Integrity
import all Obend.Slot.Protocol
import all Obend.Slot.World
import all Obend.Spec.C4
import all Obend.Spec.DataWire
import all Obend.Spec.Law
import all Obend.Spec.LawCompile
import all Obend.Spec.LawDial
import all Obend.Spec.Proofs.C4
import all Obend.Spec.Proofs.LawCompile
import all Obend.Tactic.Cases
import all Obend.Tactic.Tooth
import all Obend.Vault.Affordance
import all Obend.Vault.Law
import all Obend.Vault.Mandate
import all Obend.Vault.Page
import all Obend.Vault.Rehydration
public section
namespace Obend.Polis.Custody.WireTests
open Obend.Crypto
set_option autoImplicit false

def bytes (n : UInt8) : ByteArray := ⟨(List.replicate 32 n).toArray⟩
def hex (b : ByteArray) : String :=
  String.ofList (b.data.toList.flatMap fun x =>
    let digits := "0123456789abcdef".toList.toArray
    [digits[x.toNat / 16]!, digits[x.toNat % 16]!])

def lease : PrepaidLease := openLease 257 128 10 100
def pkg : SignedGrainPackage := ⟨bytes 7, ⟨#[0,255,128]⟩, ByteArray.empty, bytes 9⟩
def session : ConfinedSession :=
  let mind := hash "OBEND.CUSTODY.MIND/v1" [leb128 257, []]
  let auth := authorityRoot ["z", "api:443"] [128,1] [129,2,2] [8,3] true
  let head := forkGenesis (bytes 0) 257 mind (leaseStateRoot lease) auth
  ⟨257, lease, mind, ["z", "api:443"], [128,1], head, head, ⟨257, #[]⟩,
    [129,2,2], [8,3], true, []⟩
def ingress : IngressMmr := (IngressMmr.empty.append (bytes 1)).append (bytes 2)
def archive : GrainArchive :=
  let ledger := settleOrReplay ⟨lease, []⟩ 128
  let entries := [⟨[120], "abc".toUTF8⟩]
  ⟨pkg, entries, ⟨129, packageDigest pkg, computeVarDataRoot entries, bytes 0,
    leaseStateRoot ledger.lease, ingress.root⟩, bytes 6, ⟨257, #[]⟩,
    ledger.lease, ledger, ingress, [(0,bytes 1,bytes 5)], ByteArray.empty⟩

-- Identical fixture fields and hex strings in cloud_custody::tests::custody_wire_vectors.
#guard hex (authorityRoot ["z", "api:443"] [128,1] [129,2,2] [8,3] true) ==
  "073cd30c52c70354069f7752ce084f869bab1a22418b931297fdce2f726d0ed9"
#guard hex (packageDigest pkg) ==
  "cb7bfdba43c79d62764d185088fe2340325237b8fc86626c04694e3b75170bd7"
#guard hex (sessionCheckpoint session) ==
  "68e2cbe03a4dfe7e41fed63a8de29df8edb6905b2ed9398e8c3b354608978a56"
#guard hex (transitionHead archive) ==
  "2304c16c0e41ca4b4a7c4e33fb3f31759efd64c0cab5851785645e4918290a62"
#guard hex ingress.root ==
  "1825228bfbbed2ea44769b36f726113a6a7c9f4a9cfea136f5cf7746726aec75"
#guard authorityRoot ["z","api:443","z"] [1,128,1] [2,129] [3,8,3] true ==
  authorityRoot ["api:443","z"] [128,1] [129,2,2] [8,3] true

-- A finite authentication fixture pins the signed message rather than trusting public roots.
def base : GrainCustodyAnchor := { archive.anchor with generation := 128, receiptHead := bytes 6 }
def signed : GrainArchive := sealArchive (fun _ => bytes 42) archive
def verify (msg sig : ByteArray) : Bool := msg == transitionHead signed && sig == bytes 42
def auth (p : SignedGrainPackage) : Bool := p == pkg
#guard reopenCustody auth verify (some signed) (some base) == .recoveryRequired
#guard recoverOneAhead auth verify signed (some base) == some signed.anchor
#guard reopenCustody auth verify (some signed) (some signed.anchor) == .ready

def rehead (a : GrainArchive) : GrainArchive :=
  {a with anchor := {a.anchor with receiptHead := transitionHead a}}
def changedVar : GrainArchive :=
  let entries := [⟨[120], "attacker".toUTF8⟩]
  rehead {signed with
    entries := entries
    anchor := {signed.anchor with varDataRoot := computeVarDataRoot entries}}
def changedFrozen : GrainArchive :=
  rehead {signed with frozenGrain := ⟨258, #[]⟩}
def changedLease : GrainArchive :=
  rehead {signed with anchor := {signed.anchor with leaseRoot := bytes 99}}
#guard reopenCustody auth verify (some changedVar) (some base) == .poisoned .signature
#guard reopenCustody auth verify (some changedFrozen) (some base) == .poisoned .signature
#guard reopenCustody auth verify (some changedLease) (some base) == .poisoned .lease
#guard reopenCustody auth verify (some {signed with transitionSignature := ByteArray.empty}) (some base) ==
  .poisoned .signature

def children : ForkTwoSpec := ⟨⟨2,20,[],[],[],[],false⟩, ⟨3,20,[],[],[],[],false⟩⟩
#guard match forkTwo session children with
  | .error _ => false
  | .ok (p,a,b) =>
    (match forkTwo p children with | .error .duplicateIdentity => true | _ => false) &&
    (match forkTwo a ⟨⟨257,1,[],[],[],[],false⟩,⟨4,1,[],[],[],[],false⟩⟩ with | .error .duplicateIdentity => true | _ => false) &&
    (match forkTwo a ⟨⟨3,1,[],[],[],[],false⟩,⟨4,1,[],[],[],[],false⟩⟩ with | .error .duplicateIdentity => true | _ => false) &&
    (match forkFrontier [b] [] a ⟨⟨3,1,[],[],[],[],false⟩,⟨4,1,[],[],[],[],false⟩⟩ with
      | .error .duplicateIdentity => true | _ => false)

def host : GrainCustodyHost := ⟨signed, none, some changedVar⟩
#guard (custodyEvent auth verify host .crash).volatile.isNone
#guard ((custodyEvent auth verify (custodyEvent auth verify host .crash) .restart).volatile.map
  (fun a => computeVarDataRoot a.entries)) == some signed.anchor.varDataRoot
#guard ((custodyEvent auth verify ⟨signed, some changedVar, none⟩ .restart).volatile).isNone

-- A real powerbox grant survives custody sealing and restoration; unmapped slots do not.
#guard match GrainPowerbox.runPowerbox
    (GrainPowerbox.genesis [1] (fun _ => .unbound3))
    #[.spawn, .grant 1 0 "read" ⟨7, .const true, "holder".toUTF8, "channel".toUTF8⟩ (some 129)] with
  | none => false
  | some h => match GrainPowerbox.freezeGrain h 0 with
    | none => false
    | some frozen =>
      let a := sealArchive (fun b => b) {archive with frozenGrain := frozen}
      let s := {session with frozenGrain := frozen, caps := [0]}
      (restorePowerbox h a).clist.size == 1 && (resolveSessionCap s 0).isSome &&
        (resolveSessionCap s 1).isNone &&
        reopenCustody auth (fun msg sig => msg == sig) (some a) (some a.anchor) == .ready

-- A settlement becomes durable only after preparing a signed WAL; crash/restart installs it once.
#guard let trusted := sealArchive (fun b => b) archive
       let h : GrainCustodyHost := ⟨trusted, none, some trusted⟩
       let verify := fun msg sig => msg == sig
       let work := custodyEvent auth verify h (.settle 129)
       match prepareCustody auth verify (fun b => b) work with
       | none => false
       | some pending =>
         let recovered := custodyEvent auth verify (custodyEvent auth verify pending .crash) .restart
         recovered.durable.lease.drawn == 20 && recovered.durable.lease.remaining == 80 &&
           recovered.wal.isNone && recovered.volatile.isSome

#tooth ungranted_slot_refused by
  mutation resolveSessionCap := fun s slot => s.frozenGrain.refs[slot.toNat]?
#tooth child_cap_resolves_in_parent by
  mutation resolveSessionCap := fun s slot => s.frozenGrain.refs[slot.toNat + s.caps.length]?

#tooth issued_identity_rejected by
  mutation forkTwo := fun p s =>
    if s.left.id = s.right.id ∨ s.left.id = p.lease.leaseId ∨ s.right.id = p.lease.leaseId then
      .error .duplicateIdentity
    else if ¬ (attenuates p s.left ∧ attenuates p s.right) then .error .amplifiedAuthority
    else if p.lease.remaining < s.left.budget + s.right.budget then .error .budgetOverdraw
    else if childMind p s.left = childMind p s.right then .error .namespaceCollision
    else .ok (retainedParent p s, makeChild p s.left [s.right.id], makeChild p s.right [s.left.id])
#tooth forkTwo_inherits_ids by
  mutation makeChild := fun p s _ => {p with sessionId := s.id, issuedIds := []}
#tooth forkFrontier_success by
  mutation forkFrontier := fun _ _ p s => forkTwo p s
#tooth crash_erases_volatile by
  mutation custodyEvent := fun _ _ s _ => s
#tooth restart_ignores_uncommitted by
  mutation custodyEvent := fun _ _ s _ => s

#tooth unsigned_archive_refused by
  mutation reopenCustody := fun authenticate verify archive anchor =>
    match archive, anchor with
    | none, none => .empty
    | none, some _ => .poisoned .missingArchive
    | some a, base =>
      if authenticate a.package = false ∨ packageDigest a.package ≠ a.anchor.packageDigest then .poisoned .package
      else if computeVarDataRoot a.entries ≠ a.anchor.varDataRoot then .poisoned .varData
      else if transitionHead a ≠ a.anchor.receiptHead then .poisoned .brokenReceipt
      else if a.anchor.leaseRoot ≠ leaseStateRoot a.lease ∨ a.settlements.lease ≠ a.lease then .poisoned .lease
      else if a.anchor.ingressRoot ≠ a.ingress.root then .poisoned .ingress
      else match base with
        | none => if a.anchor.generation = 0 then .recoveryRequired else .poisoned .divergence
        | some b =>
          if a.anchor.packageDigest ≠ b.packageDigest then .poisoned .package
          else if a.anchor = b then .ready
          else if a.anchor.generation < b.generation then .poisoned .rollback
          else if a.anchor.generation = b.generation + 1 ∧ a.previousHead = b.receiptHead then .recoveryRequired
          else .poisoned .divergence

#tooth lease_mismatch_refused by
  mutation reopenCustody := fun authenticate verify archive anchor =>
    match archive, anchor with
    | none, none => .empty
    | none, some _ => .poisoned .missingArchive
    | some a, base =>
      if authenticate a.package = false ∨ packageDigest a.package ≠ a.anchor.packageDigest then .poisoned .package
      else if computeVarDataRoot a.entries ≠ a.anchor.varDataRoot then .poisoned .varData
      else if transitionHead a ≠ a.anchor.receiptHead then .poisoned .brokenReceipt
      else if a.anchor.ingressRoot ≠ a.ingress.root then .poisoned .ingress
      else if verify (transitionHead a) a.transitionSignature = false then .poisoned .signature
      else match base with
        | none => if a.anchor.generation = 0 then .recoveryRequired else .poisoned .divergence
        | some b =>
          if a.anchor.packageDigest ≠ b.packageDigest then .poisoned .package
          else if a.anchor = b then .ready
          else if a.anchor.generation < b.generation then .poisoned .rollback
          else if a.anchor.generation = b.generation + 1 ∧ a.previousHead = b.receiptHead then .recoveryRequired
          else .poisoned .divergence

#tooth transitionHead_binds by
  mutation transitionHead := fun a =>
    hash "OBEND.CUSTODY.ARCHIVE/v1" [a.previousHead.data.toList, leb128 a.anchor.generation,
      a.anchor.packageDigest.data.toList, a.anchor.varDataRoot.data.toList,
      a.anchor.leaseRoot.data.toList, (settlementRoot a.settlements).data.toList,
      a.anchor.ingressRoot.data.toList, (executionRoot a.executions).data.toList]

#tooth prepared_wal_authenticated by
  mutation prepareCustody := fun _ _ sign s => some {s with wal := some (sealArchive sign s.durable)}
#tooth sealed_one_ahead_recovers by
  mutation sealArchive := fun _ a => a

#print axioms multi_fork_tree_distinct
#print axioms recovery_facts
end Obend.Polis.Custody.WireTests

namespace EqualCustodyPlacementAudit
open Obend.Run.VaultDurableBridge

def swappedPlacementRefused : Bool :=
  let original : TVal := .record [("a", .cap 10 1), ("b", .cap 20 1)]
  match dehydrate sampleIdentityHash sampleSealKey 9 1
      ⟨[⟨10, 1, []⟩, ⟨20, 1, []⟩]⟩ original with
  | .error _ => false
  | .ok (_, frame) =>
    match rehydrate sampleIdentityHash sampleSealKey 9
        (.record [("a", .sealedCap 1 1), ("b", .sealedCap 0 1)]) frame with
    | .error .unsealedFrame => true
    | _ => false

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
theorem equal_custody_placement_tamper_refused : swappedPlacementRefused = true := by
  simp [swappedPlacementRefused, dehydrate, sampleSealKey, ByteArray.size, -ByteArray.size_data,
    dehydrateVal, dehydrateFields, takeCapAtSlot, duplicateSlot, rehydrate, CapSealFrame.sealValid,
    computeCapFrameSeal, capFramePreimage, encodeCapTableBytes, frameBytes, dataWireBytes,
    sampleIdentityHash] <;> decide +kernel

#tooth equal_custody_placement_tamper_refused by mutation
  Obend.Run.VaultDurableBridge.dataWireBytes := fun _ => []

end EqualCustodyPlacementAudit
