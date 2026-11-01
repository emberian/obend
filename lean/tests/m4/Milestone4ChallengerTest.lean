import Obend.Consensus.Simplex
import Obend.Consensus.Finality
import Obend.Consensus.Epistemic
import Obend.Fold.Collapse
import Obend.Vault.Hyperedge
import Obend.Core.Digest
import Obend.Receipt.Merkle

open Obend.Consensus.Simplex
open Obend.Consensus.Finality
open Obend.Consensus.Epistemic
open Obend.Fold.Collapse
open Obend.Vault

set_option autoImplicit false
set_option linter.unusedVariables false

def assertChallenger (what : String) (ok : Bool) : IO Unit :=
  if ok then
    IO.println s!"[PASS] {what}"
  else
    throw (IO.userError s!"[FAIL] EMPIRICAL CHALLENGE FAILURE: {what}")

/-! =========================================================================
    Suite 1: Simplex Consensus Committee Configurations ($f = 0, 1, 2, 5$)
    ========================================================================= -/

def testCommitteeConfigurations : IO Unit := do
  IO.println "=== Suite 1: Simplex Committee Configurations (f = 0, 1, 2, 5) ==="

  -- Configurations matching n = 3f + 1
  let cfg0 : Config := { parties := 1, faults := 0, timeout := 100, pumpBudget := 64, backoffCap := 4 }
  let cfg1 : Config := { parties := 4, faults := 1, timeout := 100, pumpBudget := 64, backoffCap := 4 }
  let cfg2 : Config := { parties := 7, faults := 2, timeout := 100, pumpBudget := 64, backoffCap := 4 }
  let cfg5 : Config := { parties := 16, faults := 5, timeout := 100, pumpBudget := 64, backoffCap := 4 }

  -- 1.1 Well-formedness checks
  assertChallenger "cfg0 (f=0, n=1) is well-formed" (cfg0.wellFormed == true)
  assertChallenger "cfg1 (f=1, n=4) is well-formed" (cfg1.wellFormed == true)
  assertChallenger "cfg2 (f=2, n=7) is well-formed" (cfg2.wellFormed == true)
  assertChallenger "cfg5 (f=5, n=16) is well-formed" (cfg5.wellFormed == true)

  -- 1.2 Exact quorum thresholds: 2f + 1
  assertChallenger "cfg0 quorum = 1 (2*0 + 1)" (cfg0.quorum == 1)
  assertChallenger "cfg1 quorum = 3 (2*1 + 1)" (cfg1.quorum == 3)
  assertChallenger "cfg2 quorum = 5 (2*2 + 1)" (cfg2.quorum == 5)
  assertChallenger "cfg5 quorum = 11 (2*5 + 1)" (cfg5.quorum == 11)

  -- 1.3 Leader rotation across views
  -- Leader is (view - 1) % parties
  assertChallenger "cfg0 leader is always 0"
    (cfg0.leader 1 == 0 && cfg0.leader 2 == 0 && cfg0.leader 10 == 0)
  assertChallenger "cfg1 leader cycles 0, 1, 2, 3, 0"
    (cfg1.leader 1 == 0 && cfg1.leader 2 == 1 && cfg1.leader 3 == 2 && cfg1.leader 4 == 3 && cfg1.leader 5 == 0)
  assertChallenger "cfg2 leader cycles 0..6"
    (cfg2.leader 1 == 0 && cfg2.leader 7 == 6 && cfg2.leader 8 == 0)
  assertChallenger "cfg5 leader cycles 0..15"
    (cfg5.leader 1 == 0 && cfg5.leader 16 == 15 && cfg5.leader 17 == 0)

  -- 1.4 Ill-formed configurations strictly rejected
  let badSize1 : Config := { parties := 3, faults := 1, timeout := 100, pumpBudget := 64 } -- 3 != 3*1+1
  let badSize2 : Config := { parties := 5, faults := 1, timeout := 100, pumpBudget := 64 } -- 5 != 3*1+1
  let badTimeout : Config := { parties := 4, faults := 1, timeout := 0, pumpBudget := 64 }
  let badBudget : Config := { parties := 4, faults := 1, timeout := 100, pumpBudget := 0 }
  assertChallenger "undersized committee n=3 for f=1 is not well-formed" (badSize1.wellFormed == false)
  assertChallenger "oversized committee n=5 for f=1 is not well-formed" (badSize2.wellFormed == false)
  assertChallenger "zero timeout configuration is not well-formed" (badTimeout.wellFormed == false)
  assertChallenger "zero pump budget configuration is not well-formed" (badBudget.wellFormed == false)

/-! =========================================================================
    Suite 2: Equivocation Attempts and Voter Deduplication
    ========================================================================= -/

def testEquivocationAndDeduplication : IO Unit := do
  IO.println "=== Suite 2: Equivocation Detection & Voter Deduplication ==="

  let bA : Block := [{ turnId := ByteArray.mk #[1], turn := none }]
  let bB : Block := [{ turnId := ByteArray.mk #[2], turn := none }]

  -- 2.1 Local state machine: duplicate voting refused
  let s0 : State := { self := 0, deadline := 1000 }
  let s1 := castVote s0 1 bA
  assertChallenger "First vote marks view as voted" ((viewAt s1 1).voted == true)
  assertChallenger "First vote emits message to outbox" (s1.outbox.length == 1)

  -- Attempting second vote for different block in same view
  let s2 := castVote s1 1 bB
  assertChallenger "Second vote for different block in same view is ignored"
    (s2 == s1 && s2.outbox.length == 1)

  -- 2.2 Network view record: equivocation detection
  -- Node 3 sends two distinct votes in view 1
  let msgA : Message := { sender := 3, view := 1, kind := .vote, value := some bA }
  let msgB : Message := { sender := 3, view := 1, kind := .vote, value := some bB }
  let vEmpty : ViewRecord := { number := 1 }
  let vOne := { vEmpty with received := [msgA] }
  let vTwo := { vEmpty with received := [msgA, msgB] }

  assertChallenger "Single vote is not an equivocation" (voteEquivocator vOne 3 == false)
  assertChallenger "Two distinct votes in same view detected as equivocation" (voteEquivocator vTwo 3 == true)

  -- Duplicate identical vote from node 3 is NOT equivocation
  let vDupSame := { vEmpty with received := [msgA, msgA] }
  assertChallenger "Duplicate identical vote messages are not an equivocation" (voteEquivocator vDupSame 3 == false)

  -- 2.3 Equivocator exclusion from quorum count
  -- In a committee of 4 nodes, node 0 and 1 vote for block A, node 3 equivocates (votes A and B)
  let msg0 : Message := { sender := 0, view := 1, kind := .vote, value := some bA }
  let msg1 : Message := { sender := 1, view := 1, kind := .vote, value := some bA }
  let vQuorumCheck : ViewRecord := { number := 1, received := [msg0, msg1, msgA, msgB] }

  let countA := count vQuorumCheck .vote (some bA)
  let countB := count vQuorumCheck .vote (some bB)
  assertChallenger "Equivocator node 3 is purged from block A vote count (count = 2)" (countA == 2)
  assertChallenger "Equivocator node 3 is purged from block B vote count (count = 0)" (countB == 0)

  -- For f=1 (quorum = 3), countA is 2 < 3, so equivocation prevents false quorum!
  let cfg1 : Config := { parties := 4, faults := 1, timeout := 100 }
  assertChallenger "Block A fails to reach quorum due to equivocator purging (2 < 3)"
    (countA < cfg1.quorum)

/-! =========================================================================
    Suite 3: Sub-Quorum QC Forgery & Duplicate Signer Sybil Attacks
    ========================================================================= -/

/-- Verifier checking that a list of signers constitutes a valid quorum for a config. -/
def verifyQuorum (cfg : Config) (signers : List NodeId) : Bool :=
  signers.eraseDups.length >= cfg.quorum

def testSubQuorumAndSybilAttacks : IO Unit := do
  IO.println "=== Suite 3: Sub-Quorum Forgery & Duplicate Signer Attacks ==="

  let bA : Block := [{ turnId := ByteArray.mk #[1], turn := none }]

  -- 3.1 Sub-quorum forgery across committee sizes
  let cfgs : List (Config × List (List NodeId)) := [
    ({ parties := 1, faults := 0, timeout := 100 }, [[]]),
    ({ parties := 4, faults := 1, timeout := 100 }, [[], [0], [1], [0, 1], [1, 2], [2, 3]]),
    ({ parties := 7, faults := 2, timeout := 100 }, [[], [0], [0, 1], [0, 1, 2], [0, 1, 2, 3]]),
    ({ parties := 16, faults := 5, timeout := 100 }, [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9]]) -- 10 signers < 11
  ]

  for (cfg, subQuorums) in cfgs do
    for sq in subQuorums do
      assertChallenger s!"Sub-quorum of size {sq.length} rejected for f={cfg.faults} (quorum={cfg.quorum})"
        (verifyQuorum cfg sq == false)

  -- Valid quorums pass
  assertChallenger "Valid quorum of size 1 passes for f=0" (verifyQuorum { parties := 1, faults := 0, timeout := 100 } [0] == true)
  assertChallenger "Valid quorum of size 3 passes for f=1" (verifyQuorum { parties := 4, faults := 1, timeout := 100 } [0, 1, 2] == true)
  assertChallenger "Valid quorum of size 5 passes for f=2" (verifyQuorum { parties := 7, faults := 2, timeout := 100 } [0, 1, 2, 3, 4] == true)
  assertChallenger "Valid quorum of size 11 passes for f=5" (verifyQuorum { parties := 16, faults := 5, timeout := 100 } (List.range 11) == true)

  -- 3.2 Duplicate Signer Sybil Attack
  -- Node 2 injects 10 identical votes
  let sybilSigners := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
  assertChallenger "10 duplicate votes from node 2 fail quorum for f=1 (eraseDups length = 1 < 3)"
    (verifyQuorum { parties := 4, faults := 1, timeout := 100 } sybilSigners == false)

  -- Node 1 and Node 2 (with Node 2 repeated 5 times)
  let mixedSybil := [1, 2, 2, 2, 2, 2]
  assertChallenger "1 honest vote + 5 duplicate votes fail quorum for f=1 (unique signers = 2 < 3)"
    (verifyQuorum { parties := 4, faults := 1, timeout := 100 } mixedSybil == false)

  -- In state machine count function:
  let msgsSybil := (List.range 10).map fun _ =>
    ({ sender := 2, view := 1, kind := .vote, value := some bA } : Message)
  let msgHonest : Message := { sender := 1, view := 1, kind := .vote, value := some bA }
  let vSybil : ViewRecord := { number := 1, received := msgHonest :: msgsSybil }
  let countSybil := count vSybil .vote (some bA)
  assertChallenger "count function collapses 10 duplicate votes from node 2 to 1 (total count = 2)"
    (countSybil == 2)

/-! =========================================================================
    Suite 4: Exponential View Backoff Across Timeout Epochs
    ========================================================================= -/

def testExponentialBackoff : IO Unit := do
  IO.println "=== Suite 4: Exponential View Backoff Stress Tests ==="

  let base := 50

  -- 4.1 Cap = 0: constant timeout regardless of epoch
  for v in [0, 1, 2, 5, 10, 50, 100] do
    assertChallenger s!"Cap 0: timeout at epoch {v} remains {base}"
      (viewTimeout base v 0 == base)

  -- 4.2 Cap = 3: powers of 2 up to 2^3 = 8
  assertChallenger "Cap 3: epoch 0 = 50 * 1 = 50" (viewTimeout base 0 3 == 50)
  assertChallenger "Cap 3: epoch 1 = 50 * 2 = 100" (viewTimeout base 1 3 == 100)
  assertChallenger "Cap 3: epoch 2 = 50 * 4 = 200" (viewTimeout base 2 3 == 200)
  assertChallenger "Cap 3: epoch 3 = 50 * 8 = 400" (viewTimeout base 3 3 == 400)
  assertChallenger "Cap 3: epoch 4 clamped at 400" (viewTimeout base 4 3 == 400)
  assertChallenger "Cap 3: epoch 100 clamped at 400" (viewTimeout base 100 3 == 400)

  -- 4.3 Cap = 6: powers of 2 up to 2^6 = 64
  let expected6 : List (Nat × Nat) := [
    (0, base * 1),
    (1, base * 2),
    (2, base * 4),
    (3, base * 8),
    (4, base * 16),
    (5, base * 32),
    (6, base * 64),
    (7, base * 64),
    (20, base * 64)
  ]
  for (ep, exp) in expected6 do
    assertChallenger s!"Cap 6: epoch {ep} matches expected {exp}"
      (viewTimeout base ep 6 == exp)

  -- 4.4 Monotonicity test: viewTimeout is monotonic in view count
  let mut prev := 0
  let mut monoOk := true
  for v in List.range 15 do
    let cur := viewTimeout base v 5
    if cur < prev then monoOk := false
    prev := cur
  assertChallenger "viewTimeout is monotonically non-decreasing across epochs" (monoOk == true)

/-! =========================================================================
    Suite 5: Finality Ladder Downgrade Refutation & Permission Boundary
    ========================================================================= -/

def testFinalityTransitionsAndPermissions : IO Unit := do
  IO.println "=== Suite 5: Finality Ladder Transitions & Permissions ==="

  let s := FinalityTier.speculative
  let a := FinalityTier.attested
  let q := FinalityTier.quorum_final
  let c := FinalityTier.collapsed

  -- 5.1 Backward transitions (downgrades) strictly fail
  assertChallenger "s ≤ a is true" (s ≤ a)
  assertChallenger "a ≤ q is true" (a ≤ q)
  assertChallenger "q ≤ c is true" (q ≤ c)

  -- Downgrades evaluated by LE
  assertChallenger "attested ≤ speculative is false" (!(a ≤ s))
  assertChallenger "quorum_final ≤ speculative is false" (!(q ≤ s))
  assertChallenger "quorum_final ≤ attested is false" (!(q ≤ a))
  assertChallenger "collapsed ≤ speculative is false" (!(c ≤ s))
  assertChallenger "collapsed ≤ attested is false" (!(c ≤ a))
  assertChallenger "collapsed ≤ quorum_final is false" (!(c ≤ q))

  -- 5.2 promoteStep rejects regressions and out-of-order jumps
  let dummyId := ByteArray.mk #[1]
  assertChallenger "promoteStep(q, attestTurn) = none (cannot re-attest or regress)"
    (promoteStep q (.attestTurn dummyId) == none)
  assertChallenger "promoteStep(c, formQC) = none (collapsed cannot regress)"
    (promoteStep c (.formQC dummyId) == none)
  assertChallenger "promoteStep(s, formQC) = none (cannot skip attested tier)"
    (promoteStep s (.formQC dummyId) == none)
  assertChallenger "promoteStep(s, collapseRoot) = none (cannot skip directly to collapsed)"
    (promoteStep s (.collapseRoot dummyId) == none)
  assertChallenger "promoteStep(a, collapseRoot) = none (cannot skip quorum_final)"
    (promoteStep a (.collapseRoot dummyId) == none)

  -- 5.3 Exhaustive 4x4 Operation Permission Matrix
  let ops : List Operation := [.readUncommitted, .executeReadOnly, .stateWrite, .immutableArchive]

  -- Tier speculative: only readUncommitted
  assertChallenger "speculative admits readUncommitted" (admitsOp s .readUncommitted == true)
  assertChallenger "speculative refuses executeReadOnly" (admitsOp s .executeReadOnly == false)
  assertChallenger "speculative refuses stateWrite" (admitsOp s .stateWrite == false)
  assertChallenger "speculative refuses immutableArchive" (admitsOp s .immutableArchive == false)

  -- Tier attested: readUncommitted, executeReadOnly
  assertChallenger "attested admits readUncommitted" (admitsOp a .readUncommitted == true)
  assertChallenger "attested admits executeReadOnly" (admitsOp a .executeReadOnly == true)
  assertChallenger "attested refuses stateWrite" (admitsOp a .stateWrite == false)
  assertChallenger "attested refuses immutableArchive" (admitsOp a .immutableArchive == false)

  -- Tier quorum_final: readUncommitted, executeReadOnly, stateWrite
  assertChallenger "quorum_final admits readUncommitted" (admitsOp q .readUncommitted == true)
  assertChallenger "quorum_final admits executeReadOnly" (admitsOp q .executeReadOnly == true)
  assertChallenger "quorum_final admits stateWrite" (admitsOp q .stateWrite == true)
  assertChallenger "quorum_final refuses immutableArchive" (admitsOp q .immutableArchive == false)

  -- Tier collapsed: admits all 4
  assertChallenger "collapsed admits readUncommitted" (admitsOp c .readUncommitted == true)
  assertChallenger "collapsed admits executeReadOnly" (admitsOp c .executeReadOnly == true)
  assertChallenger "collapsed admits stateWrite" (admitsOp c .stateWrite == true)
  assertChallenger "collapsed admits immutableArchive" (admitsOp c .immutableArchive == true)

/-! =========================================================================
    Suite 6: Multi-Cell Turn Lattice Join Commit Tiers
    ========================================================================= -/

def testMultiCellTurnLatticeJoins : IO Unit := do
  IO.println "=== Suite 6: Multi-Cell Turn Lattice Join Commit Tiers ==="

  let s := FinalityTier.speculative
  let a := FinalityTier.attested
  let q := FinalityTier.quorum_final
  let c := FinalityTier.collapsed

  -- 6.1 Floor rule: empty and below-quorum lists commit at quorum_final
  assertChallenger "turnCommitTier [] = quorum_final" (turnCommitTier [] == q)
  assertChallenger "turnCommitTier [s] = quorum_final" (turnCommitTier [s] == q)
  assertChallenger "turnCommitTier [s, s, s] = quorum_final" (turnCommitTier [s, s, s] == q)
  assertChallenger "turnCommitTier [s, a] = quorum_final" (turnCommitTier [s, a] == q)
  assertChallenger "turnCommitTier [a, a] = quorum_final" (turnCommitTier [a, a] == q)
  assertChallenger "turnCommitTier [a, q] = quorum_final" (turnCommitTier [a, q] == q)
  assertChallenger "turnCommitTier [q, q] = quorum_final" (turnCommitTier [q, q] == q)

  -- 6.2 Collapsed promotion: any collapsed cell lifts entire turn to collapsed
  assertChallenger "turnCommitTier [c] = collapsed" (turnCommitTier [c] == c)
  assertChallenger "turnCommitTier [s, c] = collapsed" (turnCommitTier [s, c] == c)
  assertChallenger "turnCommitTier [c, s] = collapsed" (turnCommitTier [c, s] == c)
  assertChallenger "turnCommitTier [a, c] = collapsed" (turnCommitTier [a, c] == c)
  assertChallenger "turnCommitTier [q, c] = collapsed" (turnCommitTier [q, c] == c)
  assertChallenger "turnCommitTier [s, a, q, c] = collapsed" (turnCommitTier [s, a, q, c] == c)

  -- 6.3 Commutativity and order invariance
  let p1 := [s, a, c]
  let p2 := [c, a, s]
  let p3 := [a, c, s]
  assertChallenger "turnCommitTier is order-invariant across cell permutations"
    (turnCommitTier p1 == turnCommitTier p2 && turnCommitTier p2 == turnCommitTier p3)

  -- 6.4 State write admission invariant: all turnCommitTier results admit stateWrite
  let testLists := [[], [s], [a], [q], [c], [s, a], [s, q], [s, c], [a, q, c]]
  for cellList in testLists do
    let tier := turnCommitTier cellList
    assertChallenger s!"turnCommitTier admits stateWrite for tier {tier.rank}"
      (admitsOp tier .stateWrite == true)

/-! =========================================================================
    Suite 7: Finality Gate Lifecycle & WellFormed Invariant Preservation
    ========================================================================= -/

/-- Boolean check corresponding to FinalityGate.WellFormed. -/
def isGateWellFormed (g : FinalityGate) : Bool :=
  (g.currentTier.rank < 1 || !g.attestations.isEmpty) &&
  (g.currentTier.rank < 2 || g.qc.isSome) &&
  (g.currentTier.rank < 3 || g.merkleRoot.isSome)

def testFinalityGateLifecycle : IO Unit := do
  IO.println "=== Suite 7: Finality Gate Lifecycle & Invariants ==="

  let tid := ByteArray.mk #[0xAA, 0xBB]
  let signer := ByteArray.mk #[0x11]
  let qcd := ByteArray.mk #[0x22]
  let root := ByteArray.mk #[0x33]

  -- 7.1 Fresh gate initialization
  let g0 := FinalityGate.init tid
  assertChallenger "Fresh gate tier is speculative" (g0.currentTier == .speculative)
  assertChallenger "Fresh gate attestations is empty" (g0.attestations == [])
  assertChallenger "Fresh gate qc is none" (g0.qc == none)
  assertChallenger "Fresh gate merkleRoot is none" (g0.merkleRoot == none)
  assertChallenger "Fresh gate is WellFormed" (isGateWellFormed g0 == true)

  -- 7.2 Advance to attested
  let g1Opt := advanceGate g0 (.attestTurn signer)
  assertChallenger "advanceGate with attestTurn succeeds" (g1Opt.isSome == true)
  match g1Opt with
  | none => throw (IO.userError "Expected some g1")
  | some g1 =>
    assertChallenger "g1 tier is attested" (g1.currentTier == .attested)
    assertChallenger "g1 records signer attestation" (g1.attestations == [signer])
    assertChallenger "g1 preserves turnId" (g1.turnId == tid)
    assertChallenger "g1 is WellFormed" (isGateWellFormed g1 == true)

    -- 7.3 Advance to quorum_final
    let g2Opt := advanceGate g1 (.formQC qcd)
    assertChallenger "advanceGate with formQC succeeds" (g2Opt.isSome == true)
    match g2Opt with
    | none => throw (IO.userError "Expected some g2")
    | some g2 =>
      assertChallenger "g2 tier is quorum_final" (g2.currentTier == .quorum_final)
      assertChallenger "g2 records QC digest" (g2.qc == some qcd)
      assertChallenger "g2 preserves attestations" (g2.attestations == [signer])
      assertChallenger "g2 is WellFormed" (isGateWellFormed g2 == true)

      -- 7.4 Advance to collapsed
      let g3Opt := advanceGate g2 (.collapseRoot root)
      assertChallenger "advanceGate with collapseRoot succeeds" (g3Opt.isSome == true)
      match g3Opt with
      | none => throw (IO.userError "Expected some g3")
      | some g3 =>
        assertChallenger "g3 tier is collapsed" (g3.currentTier == .collapsed)
        assertChallenger "g3 records merkleRoot" (g3.merkleRoot == some root)
        assertChallenger "g3 preserves attestations and qc" (g3.attestations == [signer] && g3.qc == some qcd)
        assertChallenger "g3 is WellFormed" (isGateWellFormed g3 == true)

        -- 7.5 Adversarial out-of-order attempts
        assertChallenger "Skip attestation: g0 cannot formQC" ((advanceGate g0 (.formQC qcd)).isNone == true)
        assertChallenger "Skip attestation and QC: g0 cannot collapseRoot" ((advanceGate g0 (.collapseRoot root)).isNone == true)
        assertChallenger "Skip QC: g1 cannot collapseRoot" ((advanceGate g1 (.collapseRoot root)).isNone == true)
        assertChallenger "Redundant attestation: g1 cannot attestTurn again" ((advanceGate g1 (.attestTurn signer)).isNone == true)
        assertChallenger "Regression: g2 cannot attestTurn" ((advanceGate g2 (.attestTurn signer)).isNone == true)
        assertChallenger "Terminal state: g3 cannot collapseRoot again" ((advanceGate g3 (.collapseRoot root)).isNone == true)
        assertChallenger "Terminal state: g3 cannot regress to attestTurn" ((advanceGate g3 (.attestTurn signer)).isNone == true)
        assertChallenger "Terminal state: g3 cannot regress to formQC" ((advanceGate g3 (.formQC qcd)).isNone == true)


/-! =========================================================================
    Main Execution Harness
    ========================================================================= -/

def main : IO Unit := do
  IO.println "=========================================================="
  IO.println "=== [Milestone 4 Empirical Challenger Test Suite]      ==="
  IO.println "=========================================================="
  testCommitteeConfigurations
  testEquivocationAndDeduplication
  testSubQuorumAndSybilAttacks
  testExponentialBackoff
  testFinalityTransitionsAndPermissions
  testMultiCellTurnLatticeJoins
  testFinalityGateLifecycle
  IO.println ""
  IO.println "=========================================================="
  IO.println "=== [ALL 7 EMPIRICAL CHALLENGE SUITES PASSED CLEANLY]  ==="
  IO.println "=========================================================="
