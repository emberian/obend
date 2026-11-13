import Obend.Vault.Escrow
import Obend.Polis.GrainCustodyHost
import Obend.Tactic.Tooth
import Obend.AssertAxioms

namespace Obend.Polis.Custody.Tests
open Obend.Crypto
set_option autoImplicit false

private def lease : PrepaidLease := openLease 1 0 10 100
private def once : PrepaidLease := advanceLease lease
private def twice : PrepaidLease := advanceLease once
example : ReachableLease 1 0 10 100 2 twice := by
  apply ReachableLease.step (l := once) (p := 1) (a := 10)
  · apply ReachableLease.step (l := lease) (p := 0) (a := 10)
    · exact ReachableLease.initial
    · rfl
  · rfl
example : twice.remaining = 80 ∧ twice.drawn = 20 ∧ twice.nextDue = 2 := by decide
example : dischargePeriod twice 1 10 = .error .replay := by rfl
example : dischargePeriod twice 3 10 = .error .offSchedule := by rfl
example : dischargePeriod twice 2 11 = .error .overDraw := by rfl
example : dischargePeriod (openLease 1 0 10 9) 0 10 = .error .insufficientBudget := by rfl
example : leaseStateRoot lease = leaseStateRoot lease := rfl

private def parent : ConfinedSession :=
  let root := leaseStateRoot twice
  let p : ConfinedSession := ⟨1, twice, root, ["api:443", "store:443"], [1,2], root, root, ⟨1, #[]⟩, [], [], false, []⟩
  {p with checkpointRoot := sessionCheckpoint p}
private def childA : ForkChildSpec := ⟨2, 30, ["api:443"], [1], [], [], false⟩
private def childB : ForkChildSpec := ⟨3, 20, [], [], [], [], false⟩
private def forkSpec : ForkTwoSpec := ⟨childA, childB⟩

-- Compiled concrete cryptographic witnesses complement the universally quantified kernel proofs.
#guard match forkTwo parent forkSpec with
  | .ok (p,a,b) => p.lease.remaining == 30 && a.lease.remaining == 30 && b.lease.remaining == 20 &&
    verifyForkGenesis parent.checkpointRoot a && verifyForkGenesis parent.checkpointRoot b &&
    decide (a.mindRoot ≠ b.mindRoot)
  | .error _ => false
example : forkTwo parent ⟨childA, {childB with id := 2}⟩ = .error .duplicateIdentity := by
  rfl
example : forkTwo parent ⟨{childA with doors := ["ungranted:443"]}, childB⟩ = .error .amplifiedAuthority := by
  rfl
example : forkTwo parent ⟨{childA with caps := [9]}, childB⟩ = .error .amplifiedAuthority := by rfl
example : forkTwo parent ⟨{childA with budget := 81}, childB⟩ = .error .budgetOverdraw := by rfl

private def package : SignedGrainPackage := ⟨ByteArray.empty, ByteArray.empty, ByteArray.empty, ByteArray.empty⟩
private def archive (n : Nat) (prev : ByteArray) : GrainArchive :=
  let a : GrainArchive := ⟨package, [],
    ⟨n, packageDigest package, computeVarDataRoot [], ByteArray.empty, leaseStateRoot lease, IngressMmr.empty.root⟩, prev, ⟨1, #[]⟩, lease, ⟨lease, []⟩,
    IngressMmr.empty, [], ByteArray.empty⟩
  sealArchive (fun x => x) a
private def genesis : GrainArchive := archive 0 ByteArray.empty
private def second : GrainArchive := archive 1 genesis.anchor.receiptHead
private def authenticate (p : SignedGrainPackage) : Bool := decide (p = package)

#guard reopenCustody authenticate (fun msg sig => msg == sig) none none == .empty
#guard reopenCustody authenticate (fun msg sig => msg == sig) (some genesis) (some genesis.anchor) == .ready
#guard reopenCustody authenticate (fun msg sig => msg == sig) (some second) (some genesis.anchor) == .recoveryRequired
#guard recoverOneAhead authenticate (fun msg sig => msg == sig) second (some genesis.anchor) == some second.anchor
#guard reopenCustody authenticate (fun msg sig => msg == sig) (some second) (some second.anchor) == .ready
#guard match reopenCustody authenticate (fun msg sig => msg == sig) (some (archive 2 genesis.anchor.receiptHead)) (some genesis.anchor) with
  | .poisoned .divergence => true
  | _ => false
#guard match reopenCustody authenticate (fun msg sig => msg == sig)
    (some {second with entries := [⟨[1], "tamper".toUTF8⟩]}) (some genesis.anchor) with
  | .poisoned .varData => true
  | _ => false
#guard match reopenCustody authenticate (fun msg sig => msg == sig)
    (some {second with package := {package with code := "swapped".toUTF8}}) (some genesis.anchor) with
  | .poisoned .package => true
  | _ => false

private def events : List CustodyHostEvent :=
  [.settle 0, .crash, .restart, .settle 0, .settle 1, .crash, .restart, .settle 1, .settle 2]
#guard let s := runSettlementEvents ⟨lease, []⟩ events
       s.lease.remaining == 70 && s.lease.drawn == 30 && s.records.length == 3
#guard let s := settleOrReplay ⟨lease, []⟩ 0
       settlementReceipt (settleOrReplay s 0) (1,0) == settlementReceipt s (1,0)

#guard let es : List WalEvent := [.request 0, .crashRestart, .request 0, .install, .request 1, .crashRestart]
       let w := es.foldl walEvent ⟨⟨lease, []⟩, none⟩
       w.recover.durable.lease.remaining == 80 && w.recover.durable.records.length == 2

def requestOne : ByteArray := ⟨(List.replicate 32 (1 : UInt8)).toArray⟩
def requestTwo : ByteArray := ⟨(List.replicate 32 (2 : UInt8)).toArray⟩
def ticketed : IngressMmr × AriadneTicket :=
  ariadneCommitTurn (fun b => b) IngressMmr.empty requestOne
def later : IngressMmr := ticketed.1.append requestTwo
#guard verifyNonOmission ticketed.2 ticketed.1 later later.openings
#guard !verifyNonOmission ticketed.2 ticketed.1 later [(1,requestTwo)]
#guard !verifyNonOmission ticketed.2 ticketed.1 later [(0,"replaced".toUTF8),(1,requestTwo)]
#guard ticketMessage ticketed.2 == ticketed.2.signature &&
  ticketed.1.root == ticketed.2.mmrRoot &&
  ticketed.1.openings[ticketed.2.seqNo]? == some (ticketed.2.seqNo, ticketed.2.reqDigest)

example (s : IngressMmr) (req : ByteArray) (hs : ReachableIngress s) :
    ValidTicket (fun msg sig => decide (msg = sig))
      (ariadneCommitTurn (fun b => b) s req).2 (ariadneCommitTurn (fun b => b) s req).1 := by
  exact ariadneCommitTurn_complete _ _ (fun _ => by simp) s req hs

-- Each mutation attacks a universal operational theorem, not a closed fixture.
#tooth no_advance_without_draw_rejected by
  mutation advanceLease := fun l => { l with nextDue := l.nextDue + 1, remaining := l.remaining - l.rent }

#tooth forkTwo_attenuates_confinement by
  mutation forkTwo := fun p s =>
    if s.left.id = s.right.id ∨ s.left.id = p.lease.leaseId ∨ s.right.id = p.lease.leaseId then .error .duplicateIdentity
    else if p.lease.remaining < s.left.budget + s.right.budget then .error .budgetOverdraw
    else if childMind p s.left = childMind p s.right then .error .namespaceCollision
    else .ok (retainedParent p s, makeChild p s.left, makeChild p s.right)

#tooth forkTwo_conserves_budget by
  mutation forkTwo := fun p s =>
    if s.left.id = s.right.id ∨ s.left.id = p.lease.leaseId ∨ s.right.id = p.lease.leaseId then .error .duplicateIdentity
    else if ¬ (attenuates p s.left ∧ attenuates p s.right) then .error .amplifiedAuthority
    else if p.lease.remaining < s.left.budget then .error .budgetOverdraw
    else if childMind p s.left = childMind p s.right then .error .namespaceCollision
    else .ok (retainedParent p s, makeChild p s.left, makeChild p s.right)

#tooth var_mismatch_poisoned by
  mutation reopenCustody := fun _ _ a b => match a,b with
    | none, none => .empty
    | some _, some _ => .ready
    | _, _ => .poisoned .divergence

#tooth two_ahead_poisoned by
  mutation reopenCustody := fun _ _ a b => match a,b with
    | some x, some y => if y.generation < x.anchor.generation then .recoveryRequired else .ready
    | none, none => .empty
    | _, _ => .poisoned .divergence

#tooth settle_replay_unchanged by
  mutation settleOrReplay := fun s p =>
    match dischargePeriod s.lease p s.lease.rent with
    | .error _ => s
    | .ok l => ⟨l, ((s.lease.leaseId,p),leaseStateRoot l) :: s.records⟩

#tooth IngressMmr.append_openings by
  mutation appendMountain := fun m _ => [m]

#tooth host_cannot_omit_committed_turn_or_collision by
  mutation verifyNonOmission := fun _ _ _ _ => true

-- These byte vectors are also checked against the Rust implementation.
#guard (leaseStateRoot (openLease 1 0 10 100)).data.toList ==
  [10, 109, 57, 143, 13, 113, 96, 249, 210, 40, 202, 84, 43, 89, 143, 81, 156, 102, 184, 77, 112, 182, 82, 234, 220, 103, 77, 21, 228, 173, 25, 61]
#guard (computeVarDataRoot [⟨[120], "abc".toUTF8⟩]).data.toList ==
  [240, 65, 64, 145, 126, 136, 96, 128, 102, 23, 43, 57, 253, 74, 196, 95, 211, 8, 126, 209, 72, 102, 18, 184, 210, 8, 75, 23, 249, 237, 46, 115]
#guard ((IngressMmr.empty.append requestOne).append requestTwo).root.data.toList ==
  [24,37,34,139,251,190,210,234,68,118,155,54,247,38,17,58,106,124,159,74,156,254,161,54,245,207,119,70,114,106,236,117]
#tooth merkle_exec_eq by
  mutation merkleExec := fun _ => hash "OBEND.CUSTODY.MERKLE.EMPTY/v1" []

#tooth leaseFields_inj by
  mutation leaseFields := fun l =>
    [leb128 l.leaseId.toNat, leb128 l.startPeriod, leb128 l.nextDue, leb128 l.rent,
      leb128 l.initialBudget, leb128 l.remaining]

#tooth forkTwo_anchors_receipt_chains_or_collision by
  mutation verifyForkGenesis := fun _ _ => true

#tooth double_charge_impossible_across_crash by
  mutation settleOrReplay := fun s p =>
    match dischargePeriod s.lease s.lease.nextDue s.lease.rent with
    | .error _ => s
    | .ok l => ⟨l, ((s.lease.leaseId,p),leaseStateRoot l) :: s.records⟩

#tooth double_charge_impossible_during_wal_recovery by
  mutation SettlementWal.recover := fun w =>
    let s := w.pending.getD w.durable
    ⟨{s with lease := advanceLease s.lease}, none⟩

-- Non-vacuity witnesses: finite trace call sets are decidably collision-free on real cSHAKE256!
#guard cshakeCollisionFree (leaseStateRootCalls lease ++ leaseStateRootCalls twice)
#guard cshakeCollisionFree (ticketed.1.rootCalls ++ later.rootCalls)

theorem concrete_non_omission_unconditional :
    verifyNonOmission ticketed.2 ticketed.1 later [(1, requestTwo)] = false := by
  have hVt : ValidTicket (fun msg sig => decide (msg = sig)) ticketed.2 ticketed.1 :=
    ariadneCommitTurn_complete _ _ (fun _ => by simp) IngressMmr.empty requestOne .empty
  rcases host_cannot_omit_committed_turn_or_collision
      (fun msg sig => decide (msg = sig)) ticketed.2 ticketed.1 ticketed.1 later
      [(1, requestTwo)] hVt (by decide) with hRefused | hCol
  · exact hRefused
  · obtain ⟨w⟩ := hCol
    have hm1 : (w.domain, w.leftFields) ∈ ticketed.1.rootCalls := by
      rcases List.mem_append.1 w.leftMem with h | h <;> exact h
    have hm2 : (w.domain, w.rightFields) ∈ ticketed.1.rootCalls := by
      rcases List.mem_append.1 w.rightMem with h | h <;> exact h
    simp only [ticketed, ariadneCommitTurn, IngressMmr.empty, IngressMmr.append, appendMountain,
      IngressMmr.rootCalls, peaksRootCalls, List.append_nil,
      IngressMountain.rootCalls, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm1 hm2
    rcases hm1 with ⟨hd1, hf1⟩ | ⟨hd1, hf1⟩ <;> rcases hm2 with ⟨hd2, hf2⟩ | ⟨hd2, hf2⟩
    · exact False.elim (w.distinct (by rw [hf1, hf2]))
    · rw [hd1] at hd2; exact False.elim ((by decide : "OBEND.CUSTODY.MMR.ROOT/v1" ≠ "OBEND.CUSTODY.MOUNTAIN/v1") hd2)
    · rw [hd1] at hd2; exact False.elim ((by decide : "OBEND.CUSTODY.MOUNTAIN/v1" ≠ "OBEND.CUSTODY.MMR.ROOT/v1") hd2)
    · exact False.elim (w.distinct (by rw [hf1, hf2]))

#print axioms double_charge_impossible_during_wal_recovery
#print axioms fork_receipt_chain_binds_anchor_or_collision
#print axioms metered_equals_drawn
#print axioms equal_roots_bind_cursor_remaining_drawn_or_collision
#print axioms forkTwo_sovereign_isolation
#print axioms forkTwo_attenuates_confinement
#print axioms forkTwo_conserves_budget
#print axioms forkTwo_anchors_receipt_chains_or_collision
#print axioms tampered_var_or_package_poisoned_or_collision
#print axioms double_charge_impossible_across_crash
#print axioms host_cannot_omit_committed_turn_or_collision
#assert_axioms_tree
end Obend.Polis.Custody.Tests

#tooth Obend.Vault.Escrow.escrowCellContract_conserves_funded_value by
  mutation Obend.Vault.Escrow.escrowCondT := Obend.Law.trueT

#tooth Obend.Vault.Escrow.escrowCellContract_refuses_unfunded_payout by
  mutation Obend.Vault.Escrow.escrowBalanceT := fun _ => Obend.Law.trueT

namespace Obend.Vault.Escrow.Tests

def mintedPayout : EscrowState :=
  { openedEscrow with paid := fun _ => 100 }

example : escrowVerdictBool openedEscrow mintedPayout = false := by decide
example : escrowVerdictBool openedEscrow
    { openedEscrow with status := upd openedEscrow.status .A .deposited, amount := upd openedEscrow.amount .A 7 } = true := by decide

end Obend.Vault.Escrow.Tests

#tooth Obend.Vault.Escrow.escrowCellContract_refuses_skipped_deposit by
  mutation Obend.Vault.Escrow.fundedLegT := fun _ _ _ _ => Obend.Law.trueT

open Obend.Vault.Escrow in
example : escrowVerdictBool openedEscrow
    { status := fun _ => .consumed, amount := fun _ => 100, recv := fun _ => 100, paid := fun _ => 100 } = false := by decide
