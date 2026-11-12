module
public import Obend.Polis.CapTP
public import Obend.Polis.HouyhnhnmTurn
public import Obend.Polis.HouyhnhnmMonitor
import all Obend.Polis.CapTP
import all Obend.Polis.HouyhnhnmTurn
import all Obend.Polis.HouyhnhnmMonitor
import Obend.Tactic.Tooth

public section
namespace Obend.Tests.HouyhnhnmCapTpMonitor
open Obend.Polis.CapTP Obend.Polis.HouyhnhnmTurn Obend.Polis.HouyhnhnmMonitor
open Obend.Vault.Mandate Obend.Crypto

@[expose] def alice : Principal := ⟨"Alice", 1⟩
@[expose] def carol : Principal := ⟨"Carol", 3⟩
@[expose] def held : Mandate :=
  ⟨1, .root alice "Bob", alice, "Bob", [.read, .call], 20, [1,2], 100, .any⟩
@[expose] def entry (key : UInt64) (expires : Nat) (revoked : Bool) : SturdyEntry :=
  ⟨key, held, 42, expires, revoked⟩
@[expose] def table : SwissTableExec := ⟨#[entry 3 100 false, entry 8 5 false, entry 12 100 true], SortedU64Set.empty⟩

example : WFSwissTable table := by
  intro i j hi hj hij
  change i < 3 at hi
  change j < 3 at hj
  have hi3 : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  have hj3 : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  rcases hi3 with hi3 | hi3 | hi3 <;> rcases hj3 with hj3 | hj3 | hj3 <;>
    subst i <;> subst j <;> simp_all [table, entry]

example : lookupSwissExec table 7 10 42 = .denied := by rfl
example : lookupSwissExec table 8 10 42 = .denied := by rfl
example : lookupSwissExec table 12 10 42 = .denied := by rfl
example : lookupSwissExec table 3 10 99 = .denied := by rfl
example : lookupSwissExec { table with seenNonces := SortedU64Set.empty.insert 42 } 3 10 42 = .denied := by rfl
example : lookupSwissExec table 3 10 42 = .granted held := by rfl

@[expose] def request : DelegationRequest := ⟨2, carol, [.call], 7, [1], 90, [5]⟩
@[expose] def identity : HybridIdentity := ⟨⟨#[1,2]⟩, ⟨#[3,4]⟩⟩
@[expose] def signatures : HybridSignature := ⟨⟨#[1,2]⟩, ⟨#[3,4]⟩⟩
/-- Test-only signature adapters exercise the composition, not Ed25519 or ML-DSA. -/
@[expose] def testSignatures : HybridSigVerifier :=
  ⟨fun key _ sig => decide (key = sig), fun key _ sig => decide (key = sig)⟩
@[expose] def cert : HybridHandoffCert :=
  ⟨"Bob".toUTF8, "Alice-Carol".toUTF8, 17, identity, identity, request, signatures, signatures⟩

example : attenuates (request.granted held) held := delegate_child_attenuates _ _ _ _ _ _ _ _
example : verifyBoth testSignatures identity ByteArray.empty signatures = true := by rfl
example : verifyBoth { testSignatures with classical := fun _ _ _ => false }
    identity ByteArray.empty signatures = false := by rfl
example : verifyBoth { testSignatures with mlDsa65 := fun _ _ _ => false }
    identity ByteArray.empty signatures = false := by rfl
example : requestFits { request with quota := 21 } held = false := by rfl
example : requestFits { request with rights := [.control] } held = false := by rfl

example : verifyHybridHandoff testSignatures held ByteArray.empty
    (hybridIdentityDigest identity) (hybridIdentityDigest identity) SortedU64Set.empty cert = true := by
  simp only [verifyHybridHandoff, cert, eq_self, decide_true, Bool.true_and, verifyBoth, testSignatures,
    identity, signatures, Bool.and_true]
  rfl

example : verifyHybridHandoff testSignatures held ByteArray.empty
    (hybridIdentityDigest identity) (hybridIdentityDigest identity)
    (SortedU64Set.empty.insert 17) cert = false :=
  verifyHybridHandoff_no_replay _ _ _ _ _ _ _

@[expose] def holes : GuardedHole := ⟨SortedU64Set.empty, SortedU64Set.empty⟩
example : countResolved holes [.allocate 7, .deliver 7, .resolve 7,
    .merge (SortedU64Set.empty.insert 7), .allocate 7, .resolve 7] 7 = 1 := by rfl
example : (resolvePromise (pushout (allocatePromise holes 7) (SortedU64Set.empty.insert 7)) 7).isNone = true := by rfl

@[expose] def root32 : ByteArray := ⟨Array.replicate 32 1⟩
@[expose] def cell : CellState := ⟨#[10,5], root32, root32, root32, 1, SortedU64Set.empty, #[request.granted held]⟩
@[expose] def invocation : InvocationWithProvenance :=
  ⟨0, ⟨carol, "Bob", 1, 5, [.call], 1, 20⟩, [2,7,11], 90⟩
@[expose] def turn : StructuredTurn := ⟨#[-3,3], #[invocation], #[], ⟨#[0,0,0]⟩⟩
example : execTurnSymbolic (fun _ _ _ => false) cell turn = true := by
  simp [execTurnSymbolic, nextBalances, cell, turn, checkAllRowsNonVacuous] <;> decide
example : execTurnSymbolic (fun _ _ _ => false) cell { turn with deltas := #[-3,4] } = false := by
  simp [execTurnSymbolic, nextBalances, cell, turn, checkAllRowsNonVacuous] <;> decide
example : execTurnSymbolic (fun _ _ _ => false) cell { turn with deltas := #[-11,11] } = false := by
  simp [execTurnSymbolic, nextBalances, cell, turn, checkAllRowsNonVacuous] <;> decide
example : execTurnSymbolic (fun _ _ _ => false) cell { turn with rows := ⟨#[0,0,1]⟩ } = false := by
  simp [execTurnSymbolic, nextBalances, cell, turn, checkAllRowsNonVacuous] <;> decide
example : execTurnSymbolic (fun _ _ _ => false) { cell with revoked := cell.revoked.insert 7 } turn = false := by
  simp [execTurnSymbolic, nextBalances, cell, turn, checkAllRowsNonVacuous] <;> decide
example : execTurnSymbolic (fun _ _ _ => true) cell
    { turn with effects := #[⟨1, ByteArray.empty, root32, root32⟩] } = false := by
  simp [execTurnSymbolic, nextBalances, cell, turn, checkAllRowsNonVacuous] <;> decide
example : liveRevokedRoot emptyRevokedRoot32 = false := by decide

/-- End-to-end theorem is quantified over an actual sound/complete receipt backend.
No test manufactures a Boolean "proof verified" witness. -/
example {c : TurnCommitments} {v : InnerVerifier} (ps : TurnProofSystem c v)
    (s : CellState) (t : StructuredTurn) (height : Nat)
    (hs : execTurnSymbolic v s t = true) (hr : RootBindings c s) :
    verifyCipherclerkBundle ps (collapseTurn ps s t height hs hr) = true :=
  (symbolic_collapse_refines ps s t height hs hr).1

@[expose] def rt : ReversibleTurn := ⟨#[-3,3]⟩
example : applyTurn rt.invert (applyTurn rt (fun _ => 10)) 0 = 10 := by
  rw [invert_cancel]
@[expose] def history : ReversibleHistory := ⟨#[rt,rt], 2, by decide, #[]⟩
example : (forkAt history 1 (by decide)).backing = history.backing := by
  exact prefixSlice_eq _ _ _
example : historySpec (forkAt history 1 (by decide)) = [rt] := by rfl
example : rollback [rt,rt] (applyHistory [rt,rt] (fun _ => 10)) = (fun _ => 10) :=
  rollbackTo_recovers_checkpoint _ _

@[expose] def brokenSubsystem : MonitoredSubsystem Nat Nat :=
  ⟨fun n => .recovered n root32, id, fun _ => .degraded⟩
example : detectDivergence brokenSubsystem 2 =
    some (.divergentArtifact (.recovered 2 root32) .degraded) := by rfl
example : detectDivergence (monitorTower brokenSubsystem 2) ⟨⟨(2 : Nat), none⟩, none⟩ =
    some (.divergentArtifact (.healthy ByteArray.empty) .degraded) := by rfl

@[expose] def framingVector : FullPinnedPublicInputs :=
  ⟨⟨Array.replicate 32 1⟩, ⟨Array.replicate 32 2⟩, ⟨Array.replicate 32 3⟩,
   ⟨Array.replicate 32 4⟩, ⟨Array.replicate 32 5⟩, ⟨Array.replicate 32 6⟩,
   300, ⟨Array.replicate 32 8⟩⟩

set_option maxRecDepth 4096 in
/-- The same independent byte vector is checked by the Rust crate. -/
example : (encodePublicInputs framingVector).data =
    #[99,32] ++ Array.replicate 32 1 ++ #[32] ++ Array.replicate 32 2 ++
    #[32] ++ Array.replicate 32 3 ++ #[99,32] ++ Array.replicate 32 4 ++
    #[32] ++ Array.replicate 32 5 ++ #[32] ++ Array.replicate 32 6 ++
    #[37,2,172,2,32] ++ Array.replicate 32 8 ++ #[0] := by decide

#tooth lookupSwissExec_eq_spec by mutation search := fun _ _ _ _ _ _ => none
#tooth pushout_refuses_replay by mutation mergeNullifierSets := fun a _ => a
#tooth invert_cancel by mutation ReversibleTurn.invert := fun t => t

#tooth swissTable_no_membership_oracle by mutation authorizeEntry :=
  fun _ nonce replayed entry => match entry with
  | none => .denied
  | some e => if !replayed && nonce == e.expectedNonce then .granted e.mandate else .denied

#tooth hybridHandoff_fails_closed_classical_or_pq by mutation verifyBoth :=
  fun v id msg sig => v.classical id.classicalKey msg sig.classical ||
    v.mlDsa65 id.mlDsa65Key msg sig.mlDsa65

#tooth guardedHole_resolve_at_most_once by mutation resolvePromise :=
  fun s k => if !s.openPromises.contains k then none else some s

#tooth fenzi_pi_injective by mutation encodePublicInputs :=
  fun p => encodeFrame (encodeFrame p.circuitDescDigest p.actorVkDigest p.preStateRoot)
    (encodeFrame p.postStateRoot p.capRoot p.revokedRoot)
    (encodeFrame (natBytes p.height) ByteArray.empty ByteArray.empty)

#tooth fenzi_pi_injective by mutation encodePublicInputs :=
  fun p => encodeFrame (encodeFrame p.circuitDescDigest p.actorVkDigest p.preStateRoot)
    (encodeFrame p.postStateRoot p.capRoot ByteArray.empty)
    (encodeFrame (natBytes p.height) p.turnHash ByteArray.empty)

#tooth empty_revoked_root_refused by mutation liveRevokedRoot := fun _ => true

#tooth lastRowGateGuard by mutation checkAllRowsNonVacuous :=
  fun t => (t.residuals.toList.take (t.residuals.size - 1)).all (· == 0)

#tooth monitor_catches_false_claim by mutation auditSubsystem := fun m s => m.selfClaim s

end Obend.Tests.HouyhnhnmCapTpMonitor
