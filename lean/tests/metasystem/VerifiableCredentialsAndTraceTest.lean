module
public import Obend.Polis.VerifiableCredentials
public import Obend.Polis.HouyhnhnmTurn
public import Obend.Polis.HouyhnhnmMonitor
public import Obend.Tactic.Tooth
public import Obend.AssertAxioms
import all Obend.Apps.ZkNtt.Goldilocks
import all Obend.AssertAxioms
import all Obend.Codec.DetCbor
import all Obend.Core.Digest
import all Obend.Core.Term
import all Obend.Crypto.DualSpine
import all Obend.Crypto.Multilinear
import all Obend.Crypto.PCS
import all Obend.Crypto.Sumcheck
import all Obend.Crypto.Transcript
import all Obend.Digest.Cshake256
import all Obend.Digest.Cshake256.Fast
import all Obend.Digest.Cshake256.Seam
import all Obend.Digest.Cshake256.Spec
import all Obend.Digest.HashBytes
import all Obend.Judge.Class
import all Obend.Judge.Computational
import all Obend.Polis.CapTP
import all Obend.Polis.EvidencedOcap
import all Obend.Polis.HouyhnhnmMonitor
import all Obend.Polis.HouyhnhnmTurn
import all Obend.Polis.VerifiableCredentials
import all Obend.Polis.VerkleUmem
import all Obend.Polis.ZkBiscuit
import all Obend.Reasons
import all Obend.Reasons.UnifiedEquilibrium
import all Obend.SymbolicZk.LinMem
import all Obend.SymbolicZk.RankedFixpointArith
import all Obend.Tactic.Tooth
import all Obend.Vault.Lsafe
import all Obend.Vault.Mandate
meta import Obend.Polis.VerifiableCredentials
meta import Obend.Polis.HouyhnhnmTurn
meta import Obend.Polis.HouyhnhnmMonitor
meta import Obend.Polis.CapTP
meta import Obend.Polis.ZkBiscuit
meta import Obend.Vault.Lsafe
meta import Obend.Vault.Mandate
meta import Obend.Codec.DetCbor
meta import Obend.SymbolicZk.LinMem
meta import Obend.SymbolicZk.RankedFixpointArith
meta import Obend.Crypto.DualSpine
meta import Obend.Digest.Cshake256

/-!
# `tests/metasystem/VerifiableCredentialsAndTraceTest.lean`

Runs `Obend.Polis.VerifiableCredentials` and the session layer of `Obend.Polis.HouyhnhnmTurn` on
one credential, one policy and one session, and aims a `#tooth` at each check a universal theorem
depends on.

* §1 a credential, its commitment, and an accepted evaluation; then the same evaluation with the
  credential tampered, a fact left unread, a revocation fact omitted, a hop that amplifies, a
  revoked grant, an unsafe redaction: each refused.
* §2 the honest receipt, its wire form, the inner verifier, and a turn admitted with it; then a
  wrong key, a rebound statement, a table with a violation, a trailing byte: each refused.
* §3 a three-turn session over three handles (two initial, one delegated): accepted, with
  balances, budgets and height as the trace theorems say; then a replayed channel nullifier, an
  invocation under a credential revoked mid-session, an exhausted budget: each refused. A
  monitor over session states stays quiet along every valid trace and reports a forged root.
* §4 teeth, and the axiom audit over the two modules.

The `#guard` lines run compiled code, cSHAKE256 included. The kernel does not evaluate the hash,
so the existence of this particular trace is evidence by execution; what holds of every trace is
in the theorems, which the `example`s apply to it.
-/

public section
namespace Obend.Tests.VerifiableCredentialsAndTrace

open Obend.Polis Obend.Polis.VerifiableCredentials Obend.Polis.HouyhnhnmTurn
open Obend.Polis.HouyhnhnmMonitor Obend.Polis.CapTP
open Obend.Crypto Obend.Codec.DetCbor Obend.Vault.Lsafe
open Obend.SymbolicZk Obend.SymbolicZk.Ranked

-- ============================================================================
-- 1. Credential, commitment, evaluation
-- ============================================================================

def root32 : ByteArray := ⟨Array.replicate 32 1⟩
def subject : ByteArray := "did:obend:carol".toByteArray
def statusPred : UInt64 := 7
def issuerAuth : ByteArray := ⟨Array.replicate 32 9⟩

/-- The root grant carries rights `0b111` under the caveat "atom 2 holds": the policy's goal. -/
def grant : Block := ⟨7, Obend.Polis.Caveat.atom 2, "issuer".toByteArray, "chan-0".toByteArray⟩
/-- One hop narrows to `0b011`. -/
def hop : Block := ⟨3, Obend.Polis.Caveat.const true, "carol".toByteArray, "chan-1".toByteArray⟩

def evidence : ByteArray := "{\"a\":\"secret\",\"b\":1}".toByteArray

def credential : IssuerCredential :=
  ⟨"issuer".toByteArray, subject, "schema/v1".toByteArray,
    .array [.uint 42, CborVal.ofString "member"], evidence, lineageOf grant [hop], 7⟩

/-- Atom 0: member. Atom 1: revoked. Atom 2, the goal: member and not revoked. -/
def policy : StatusPolicy := ⟨⟨3, #[⟨2, #[0], #[1]⟩]⟩, 2, 1, statusPred, issuerAuth⟩

def memberEdge : KgEdge := ⟨statusPred, subject, ⟨#[0]⟩⟩
def revokedEdge : KgEdge := ⟨statusPred, subject, ⟨#[1]⟩⟩

def tokenFor (edges : Array KgEdge) : CompletenessToken :=
  let body : CompletenessToken :=
    ⟨root32, statusPred, subject, edgesDigest cshakeHasher edges, ByteArray.empty⟩
  { body with issuerTag32 := tokenMac cshakeHasher issuerAuth body }

/-- The trace that reads the one committed fact once. -/
def memory : LinMemTrace := ⟨#[⟨0, 0, 0⟩], #[], #[⟨⟨0, 0, 0⟩, 1⟩], #[]⟩

def cert : ArrayCert :=
  ⟨#[0, 0, 1], #[0, 0, 1], #[0, 0, 1], #[1, 0, 0], #[1, 0, 0], #[(false, 0), (false, 0)]⟩

def witness : CredentialWitness :=
  ⟨credential, grant, #[hop], RevokedSet.empty, #[memberEdge], tokenFor #[memberEdge], memory,
    #[true, false, true], #[true, false, true], cert, 6, 12, "XXXX".toByteArray⟩

def view : DisclosureView :=
  ⟨credentialCommitment credential, RevokedSet.empty.root, root32,
    spliceByteArray evidence 6 12 "XXXX".toByteArray⟩

#guard (credentialCommitment credential).size == 32
#guard checkCredentialEval policy view witness

-- A tampered credential does not open the digest.
#guard credentialCommitment { credential with epoch := 8 } != credentialCommitment credential
#guard !checkCredentialEval policy view { witness with credential := { credential with epoch := 8 } }
#guard !checkCredentialEval policy view
  { witness with credential := { credential with attributes := .array [.uint 43] } }

-- A fact left unread, and a fact never loaded, are both refused by the memory check.
#guard !checkCredentialEval policy view { witness with memory := ⟨#[⟨0, 0, 0⟩], #[], #[], #[⟨0, 0, 0⟩]⟩ }
#guard !checkCredentialEval policy view { witness with memory := ⟨#[], #[], #[], #[]⟩ }

/-- The issuer's slice also says "revoked". -/
def revokedSlice : Array KgEdge := #[memberEdge, revokedEdge]

-- The prover drops the revocation fact from what it reads: refused.
#guard !checkCredentialEval policy view
  { witness with edges := revokedSlice, token := tokenFor revokedSlice }
-- The prover reads both facts and keeps the model in which the goal holds: refused.
#guard !checkCredentialEval policy view
  { witness with edges := revokedSlice, token := tokenFor revokedSlice,
                 memory := ⟨#[⟨0, 0, 0⟩, ⟨1, 0, 1⟩], #[], #[⟨⟨0, 0, 0⟩, 1⟩, ⟨⟨1, 0, 1⟩, 1⟩], #[]⟩ }
-- A token for another slice does not cover the presented one.
#guard !checkCredentialEval policy view { witness with token := tokenFor revokedSlice }

-- A hop may not amplify, the chain must carry the needed rights, a revoked grant folds no chain.
#guard !checkCredentialEval policy view { witness with hops := #[{ hop with rights := 15 }] }
#guard !checkCredentialEval { policy with need := 4 } view witness
#guard !checkCredentialEval policy
  { view with revokedRoot := (RevokedSet.empty.insert (credNul (rootLineage grant))).root }
  { witness with revoked := RevokedSet.empty.insert (credNul (rootLineage grant)) }

-- A redaction that writes a backslash, and a disclosure that is not the redaction, are refused.
#guard !checkCredentialEval policy view { witness with replacement := "XX\\".toByteArray }
#guard !checkCredentialEval policy { view with disclosed := evidence } witness

/-- The universal theorem at this evaluation: whatever accepted model the prover presents, the
member fact is true in it and the goal's rule negates nothing that is committed. -/
example (w : CredentialWitness) (h : checkCredentialEval policy view w = true) :
    ∀ e ∈ w.edges.toList, bit w.modelTrue (factAtom e).toNat = true :=
  (no_forged_negative_by_omission policy view w h).1

-- ============================================================================
-- 2. The receipt, the wire form, the inner verifier
-- ============================================================================

def policyDigest : ByteArray := ⟨Array.replicate 32 5⟩
def vk : ByteArray := root32

def table : List Goldilocks := complianceTable policy view witness
def statement : CredentialStatement :=
  statementOf policyDigest view (commitTable deployedReceiptParams table)
def receipt : ExPostReceipt :=
  proveExPostCredentialReceipt deployedReceiptParams vk statement table

#guard verifyExPostCredentialReceipt deployedReceiptParams vk statement receipt

-- What the receipt does not bind. The table of an accepted evaluation is all zeros, so its round
-- polynomials are zero and its opening is of a public constant: the same receipt is accepted
-- under another verifier key and for another statement with that table commitment. A receipt is
-- evidence about the committed table, not about a credential; what ties an effect to a statement
-- is the digest check of the inner verifier below. These two lines record that, so that a
-- stronger binding shows up here as a change.
#guard verifyExPostCredentialReceipt deployedReceiptParams ⟨Array.replicate 32 2⟩ statement receipt
#guard verifyExPostCredentialReceipt deployedReceiptParams vk
  { statement with disclosed := evidence } receipt

/-- A witness whose credential does not open the digest: its table has a nonzero row. -/
def badWitness : CredentialWitness :=
  { witness with credential := { credential with epoch := 8 } }
def badTable : List Goldilocks := complianceTable policy view badWitness
def badStatement : CredentialStatement :=
  statementOf policyDigest view (commitTable deployedReceiptParams badTable)

-- Neither the honest prover run on the violating table nor the good receipt replayed is accepted.
#guard !verifyExPostCredentialReceipt deployedReceiptParams vk badStatement
  (proveExPostCredentialReceipt deployedReceiptParams vk badStatement badTable)
#guard !verifyExPostCredentialReceipt deployedReceiptParams vk badStatement receipt

def proofBytes : ByteArray := encodeReceiptBytes statement receipt

#guard (decodeReceiptBytes proofBytes).isSome
#guard verifiableCredentialInnerVerifier deployedReceiptParams policyDigest vk
  (statementDigest statement) proofBytes
-- A trailing byte, another policy, another statement digest.
#guard !verifiableCredentialInnerVerifier deployedReceiptParams policyDigest vk
  (statementDigest statement) (proofBytes.push 0)
#guard !verifiableCredentialInnerVerifier deployedReceiptParams root32 vk
  (statementDigest statement) proofBytes
#guard !verifiableCredentialInnerVerifier deployedReceiptParams policyDigest vk
  (statementDigest badStatement) proofBytes

/-- The inner verifier of every turn below. -/
def verifier : InnerVerifier := vcInnerVerifier deployedReceiptParams policyDigest

def actorCell : CellState := ⟨#[10, 5], root32, root32, vk, 1, SortedU64Set.empty, #[]⟩
def effect : EffectCustom :=
  credentialEffect deployedReceiptParams policyDigest actorCell policy view witness
def effectTurn : StructuredTurn := ⟨#[-3, 3], #[], #[effect], ⟨#[0, 0, 0]⟩⟩

#guard execTurnSymbolic verifier actorCell effectTurn
#guard !execTurnSymbolic verifier actorCell
  { effectTurn with effects := #[{ effect with proof := ByteArray.empty }] }
#guard !execTurnSymbolic verifier actorCell { effectTurn with effects := #[{ effect with actorId := 2 }] }

-- ============================================================================
-- 3. A session over several handles
-- ============================================================================

open Obend.Vault.Mandate in
def alice : Principal := ⟨"Alice", 1⟩
open Obend.Vault.Mandate in
def carol : Principal := ⟨"Carol", 3⟩
open Obend.Vault.Mandate in
def dave : Principal := ⟨"Dave", 4⟩

open Obend.Vault.Mandate in
/-- Carol's handle, budget 7. -/
def handleA : Mandate := ⟨1, .root alice "Bob", carol, "Bob", [.read, .call], 7, [1, 2], 100, .any⟩
open Obend.Vault.Mandate in
/-- Dave's handle, budget 9. -/
def handleB : Mandate := ⟨2, .root alice "Bob", dave, "Bob", [.read, .call], 9, [1, 2], 100, .any⟩

def commitments : TurnCommitments where
  stateRoot s := cshake32ByteArray "test.state".toUTF8.data.toList
    (CapTP.encodeNats (s.balances.toList.map Int.toNat)).data.toList
  turnHash t := cshake32ByteArray "test.turn".toUTF8.data.toList
    (CapTP.encodeNats (t.deltas.toList.map Int.natAbs)).data.toList
  circuitDigest := root32
  capabilityRoot caps := cshake32ByteArray "test.caps".toUTF8.data.toList
    (CapTP.encodeNats (caps.toList.map (·.budget))).data.toList
  stateRoot_size _ := cshake32ByteArray_size _ _
  turnHash_size _ := cshake32ByteArray_size _ _
  circuitDigest_size := by decide

def cell0 : CellState :=
  ⟨#[10, 5], commitments.capabilityRoot #[handleA, handleB],
    revokedCommitment SortedU64Set.empty, vk, 1, SortedU64Set.empty, #[handleA, handleB]⟩

def session0 : HouyhnhnmSessionState := openSession cell0

open Obend.Vault.Mandate in
def invoke (handle : Nat) (who : Principal) (cost : Nat) (cone : List UInt64) (chan : UInt64) :
    InvocationWithProvenance :=
  ⟨handle, ⟨who, "Bob", 1, 5, [.call], cost, 20⟩, cone, chan⟩

/-- Carol spends 5 on handle 0 and attaches the credential receipt. -/
def turn1 : HouyhnhnmTurn :=
  ⟨⟨#[-3, 3], #[invoke 0 carol 5 [2, 7] 90],
      #[credentialEffect deployedReceiptParams policyDigest cell0 policy view witness], ⟨#[0]⟩⟩,
    [], none⟩

open Obend.Vault.Mandate in
/-- Dave spends 4 on handle 1, delegates a child of budget 3 to Carol, and revokes credential 7,
an ancestor of handle 0. -/
def turn2 : HouyhnhnmTurn :=
  ⟨⟨#[1, -1], #[invoke 1 dave 4 [3, 8] 91], #[], ⟨#[0]⟩⟩, [7],
    some ⟨1, ⟨5, carol, [.call], 3, [1], 90, [5]⟩⟩⟩

/-- Carol spends 1 on the delegated handle 2. -/
def turn3 : HouyhnhnmTurn :=
  ⟨⟨#[0, 0], #[invoke 2 carol 1 [3, 8, 9] 92], #[], ⟨#[0]⟩⟩, [], none⟩

def run (turns : List HouyhnhnmTurn) : Option HouyhnhnmSessionState :=
  runHouyhnhnmSession commitments verifier session0 turns

#guard (run [turn1, turn2, turn3]).isSome
#guard (run [turn1, turn2, turn3]).any fun s =>
  s.turnHeight == 3 && s.cell.capabilities.size == 3 && s.cell.balances.toList.sum == 15 &&
    budgetSum s.cell.capabilities + traceCost [turn1, turn2, turn3] == 16 &&
    s.lineage.toList == [0, 1, 1] && s.postRoots.length == 3

-- A channel nullifier is spent once.
#guard (run [turn1, turn1]).isNone
#guard (run [turn1, turn2, { turn3 with structured :=
  { turn3.structured with invocations := #[invoke 2 carol 1 [3, 8, 9] 91] } }]).isNone

/-- Carol again on handle 0, a fresh channel, one unit. -/
def coneTurn : HouyhnhnmTurn :=
  ⟨⟨#[0, 0], #[invoke 0 carol 1 [2, 7] 93], #[], ⟨#[0]⟩⟩, [], none⟩

-- Admitted before credential 7 is revoked, refused after: one revocation kills the cone.
#guard (run [turn1, coneTurn]).isSome
#guard (run [turn1, turn2, coneTurn]).isNone

-- Handle 0 has 7: a second spend of 5 is refused, across turns and inside one turn, although
-- each invocation alone is within the mandate.
#guard (run [turn1, ⟨⟨#[0, 0], #[invoke 0 carol 5 [2, 7] 94], #[], ⟨#[0]⟩⟩, [], none⟩]).isNone
def doubleSpend : HouyhnhnmTurn :=
  ⟨⟨#[0, 0], #[invoke 0 carol 4 [2, 7] 95, invoke 0 carol 4 [2, 7] 96], #[], ⟨#[0]⟩⟩, [], none⟩
#guard execTurnSymbolic verifier cell0 doubleSpend.structured
#guard (run [doubleSpend]).isNone

-- A delegation the parent cannot fit is refused.
open Obend.Vault.Mandate in
def overreach : HandleDelegation := ⟨1, ⟨5, carol, [.control], 3, [1], 90, [5]⟩⟩
#guard (run [turn1, { turn2 with delegation := some overreach }]).isNone

/-- The trace theorems at this trace: whatever state it ends in, the total is 15. -/
example (st' : HouyhnhnmSessionState)
    (h : ValidHouyhnhnmTrace commitments verifier session0 [turn1, turn2, turn3] st') :
    st'.cell.balances.toList.sum = 15 := by
  rw [(validHouyhnhnmTrace_conserves_balances _ _ _ _ _ h).1]
  decide

/-- After any trace from `session0`, the three handles of this trace attenuate the two initial
ones, and what is left plus what was spent is the initial 16. -/
example (turns : List HouyhnhnmTurn) (st' : HouyhnhnmSessionState)
    (h : ValidHouyhnhnmTrace commitments verifier session0 turns st') :
    budgetSum st'.cell.capabilities + traceCost turns = budgetSum cell0.capabilities ∧
      HandleLineage cell0.capabilities st' :=
  let r := validHouyhnhnmTrace_budget_and_lineage commitments verifier cell0.capabilities turns
    session0 st' h (handleLineage_openSession cell0) ⟨rfl, rfl⟩
  ⟨r.1, r.2.1⟩

/-- A session as a monitored subsystem: it claims its state root, and the probe recomputes the
two cached roots from the stores. -/
def sessionMonitor (c : TurnCommitments) :
    MonitoredSubsystem HouyhnhnmSessionState HouyhnhnmSessionState where
  selfClaim st := .healthy (c.stateRoot st.cell)
  extractArtifact st := st
  probeArtifact st := if RootBindings c st.cell then .healthy (c.stateRoot st.cell) else .degraded

/-- **The monitor is quiet along every valid trace** that starts with bound roots. -/
theorem sessionMonitor_quiet (c : TurnCommitments) (v : InnerVerifier)
    (turns : List HouyhnhnmTurn) (st st' : HouyhnhnmSessionState)
    (h : ValidHouyhnhnmTrace c v st turns st') (hr : RootBindings c st.cell) :
    detectDivergence (sessionMonitor c) st' = none := by
  have hr' : RootBindings c st'.cell :=
    validHouyhnhnmTrace_invariant (fun s => RootBindings c s.cell)
      (fun s turn s' _ hs => by
        obtain ⟨_, _, spent, debited, caps, lineage, _, _, _, rfl⟩ :=
          (stepHouyhnhnmSession_eq_some_iff c v s turn s').mp hs
        exact ⟨rfl, rfl⟩) turns st st' h hr
  simp [detectDivergence, compareClaims, auditSubsystem, sessionMonitor, hr']

/-- **The monitor reports a state whose cached roots are not those of its stores.** -/
theorem sessionMonitor_catches_unbound_root (c : TurnCommitments) (st : HouyhnhnmSessionState)
    (h : ¬ RootBindings c st.cell) :
    detectDivergence (sessionMonitor c) st =
      some (.divergentArtifact (.healthy (c.stateRoot st.cell)) .degraded) := by
  simp [detectDivergence, compareClaims, auditSubsystem, sessionMonitor, h]

#guard (run [turn1, turn2, turn3]).any fun s =>
  decide (detectDivergence (sessionMonitor commitments) s = none)
#guard decide (detectDivergence (sessionMonitor commitments)
  { session0 with cell := { cell0 with revokedRoot := root32 } } ≠ none)

-- ============================================================================
-- 4. Teeth and the axiom audit
-- ============================================================================

-- The memory check: without it, nothing says the facts were read.
#tooth stratified_credential_eval_sound by mutation checkFacts :=
  fun pol pub w =>
    verifyCompletenessToken cshakeHasher pub.graphDigest pol.issuerAuth pol.statusPred
        w.credential.subject w.edges w.token &&
      decide (w.memory.produced.size = 0) && decide (w.memory.finalCells.size = 0) &&
      decide (w.memory.init.toList.map LinCell.payload = w.edges.toList.map factAtom)

-- The rank check: a model nobody checked supports no claim about negation.
#tooth no_forged_negative_by_omission by mutation checkModel :=
  fun pol w => bit w.modelTrue pol.goal

-- The redaction check: a splice alone confines nothing.
#tooth disclosure_noninterference by mutation checkDisclosure :=
  fun pub w => decide (pub.disclosed =
    spliceByteArray w.credential.evidence w.spanStart w.spanEnd w.replacement)

-- A dropped field: the evidence leaves the committed payload.
#tooth credentialCommitment_binding by mutation credentialPayload :=
  fun c => encodeFrame (encodeFrame c.issuer c.subject c.schema)
    (encodeFrame (encodeDetCbor c.attributes) ByteArray.empty c.lineage) (natField c.epoch)

-- The receipt verifier without the opening: the sumcheck rounds alone.
#tooth verifyExPostCredentialReceipt_sound by mutation verifyExPostCredentialReceipt :=
  fun _ vk s rc => (receiptSumcheck vk s rc).isSome

-- An inner verifier that accepts every proof.
#tooth execTurnSymbolic_vc_sound by mutation verifiableCredentialInnerVerifier :=
  fun _ _ _ _ _ => true

-- Revocation that inserts nothing.
#tooth validHouyhnhnmTrace_spent_revoked by mutation revokeAll := fun r _ => r

-- A provenance check that ignores the revoked set.
#tooth validHouyhnhnmTrace_no_nullifier_replay by mutation provenanceLive := fun _ _ _ => true

-- A debit that debits nothing.
#tooth validHouyhnhnmTrace_budget_and_lineage by mutation debitHandle := fun caps _ => some caps

-- A step that takes every turn the admission check admits, skipping spends and debits.
#tooth stepHouyhnhnmSession_eq_none_iff by mutation stepHouyhnhnmSession :=
  fun c v st turn =>
    if decide (RootBindings c st.cell) && execTurnSymbolic v st.cell turn.structured then
      some (nextSession c st turn st.cell.revoked st.cell.capabilities st.lineage)
    else none

open Lean Elab Command in
/-- Every constant of the two modules rests on Lean's three axioms at most, and the four extractors
are computable. `credentialCommitmentExtract` and `issuerSliceExtract` rest on no choice at all.
`dualOpeningExtract` and `exPostReceiptExtract` return data computed without choice, but their
proof fields cite `Obend.Crypto.extractCanopyOpenMerkleCollision` and
`gadgetRecomposeTable_decompose`, whose own proofs carry `Classical.choice`, so `collectAxioms`
lists it for them. The package-wide `#assert_axioms_tree` needs every body in view, which a
`module` file does not have for its transitive imports; `Obend/Census.lean` runs it over the
library. -/
elab "#assert_credential_axioms" : command => do
  let env ← getEnv
  let owned : List Name := [`Obend.Polis.VerifiableCredentials, `Obend.Polis.HouyhnhnmTurn]
  for (constant, info) in env.constants.map₁.toList do
    let some index := env.getModuleIdxFor? constant | continue
    let some module := env.header.moduleNames[index.toNat]? | continue
    unless owned.contains module do continue
    if info matches .axiomInfo _ then throwError "{constant} is an axiom or a hidden body"
    for a in ← liftCoreM <| collectAxioms constant do
      unless Obend.AssertAxioms.standard.contains a do throwError "{constant} rests on {a}"
  for extractor in [``credentialCommitmentExtract, ``issuerSliceExtract, ``dualOpeningExtract,
      ``exPostReceiptExtract] do
    if Lean.isNoncomputable env extractor then throwError "{extractor} is noncomputable"
  let mut withChoice : List Name := []
  for extractor in [``credentialCommitmentExtract, ``issuerSliceExtract] do
    if (← liftCoreM <| collectAxioms extractor).contains ``Classical.choice then
      withChoice := extractor :: withChoice
  unless withChoice.isEmpty do throwError "extractors using Classical.choice: {withChoice}"
  logInfo m!"axiom audit passed: both modules rest on propext, Classical.choice and Quot.sound at most; the extractors are computable, and the commitment and slice extractors use no choice"

#assert_credential_axioms
#assert_axioms_tree

end Obend.Tests.VerifiableCredentialsAndTrace
