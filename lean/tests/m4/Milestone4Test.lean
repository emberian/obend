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
open Obend.Core.Digest (deployed)

set_option autoImplicit false

/-! # Milestone 4 Unit Test Suite -/

-- 1. Unit Test: Feature 30 Simplex BFT Consensus Configuration and Backoff
def test_simplex_config_and_backoff : Bool :=
  let cfg : Config := { parties := 4, faults := 1, timeout := 100, backoffCap := 3 }
  let q := cfg.quorum
  let l1 := cfg.leader 1
  let l2 := cfg.leader 2
  let t0 := viewTimeout 100 0 3
  let t1 := viewTimeout 100 1 3
  let t2 := viewTimeout 100 2 3
  let t5 := viewTimeout 100 5 3
  (cfg.wellFormed == true) &&
  (q == 3) &&
  (l1 == 0) &&
  (l2 == 1) &&
  (t0 == 100) &&
  (t1 == 200) &&
  (t2 == 400) &&
  (t5 == 800) -- capped at 2^3 = 8 * 100

#guard test_simplex_config_and_backoff == true

-- 2. Unit Test: Feature 30 Simplex State Machine Voting & Equivocation
def test_simplex_voting : Bool :=
  let s0 : State := { self := 0, deadline := 1000 }
  let b1 : Block := [{ turnId := ByteArray.empty, turn := none }]
  let s1 := castVote s0 1 b1
  let v1 := viewAt s1 1
  -- Double vote in same view is ignored
  let s2 := castVote s1 1 b1
  (v1.voted == true) &&
  (s2.outbox.length == s1.outbox.length)

#guard test_simplex_voting == true

-- 3. Unit Test: Feature 31 4-Tier Finality Ladder Transitions & Permissions
def test_finality_ladder : Bool :=
  let s := FinalityTier.speculative
  let a := FinalityTier.attested
  let q := FinalityTier.quorum_final
  let c := FinalityTier.collapsed
  -- Order
  (s ≤ a) && (a ≤ q) && (q ≤ c) && !(c ≤ s) &&
  -- Permissions
  (admitsOp s .readUncommitted == true) &&
  (admitsOp s .executeReadOnly == false) &&
  (admitsOp a .executeReadOnly == true) &&
  (admitsOp a .stateWrite == false) &&
  (admitsOp q .stateWrite == true) &&
  (admitsOp q .immutableArchive == false) &&
  (admitsOp c .immutableArchive == true) &&
  -- Promotion step machine
  (promoteStep s (.attestTurn ByteArray.empty) == some a) &&
  (promoteStep a (.formQC ByteArray.empty) == some q) &&
  (promoteStep q (.collapseRoot ByteArray.empty) == some c) &&
  (promoteStep q (.attestTurn ByteArray.empty) == none) &&
  -- Multi-cell turn commit lattice join
  (turnCommitTier [s, a] == q) &&
  (turnCommitTier [s, c] == c)

#guard test_finality_ladder == true

-- 4. Unit Test: Feature 31 FinalityGate Lifecycle
def test_finality_gate_lifecycle : Bool :=
  let tid := ByteArray.mk #[1, 2, 3]
  let g0 := FinalityGate.init tid
  let g1 := advanceGate g0 (.attestTurn (ByteArray.mk #[9]))
  let g2 := g1.bind (fun g => advanceGate g (.formQC (ByteArray.mk #[8])))
  let g3 := g2.bind (fun g => advanceGate g (.collapseRoot (ByteArray.mk #[7])))
  match g0.currentTier, g1.map (·.currentTier), g2.map (·.currentTier), g3.map (·.currentTier) with
  | .speculative, some FinalityTier.attested, some FinalityTier.quorum_final, some FinalityTier.collapsed => true
  | _, _, _, _ => false

#guard test_finality_gate_lifecycle == true

-- 5. Unit Test: Feature 32 Epistemic Consensus Lexical Ordering & Tie-Breaking
structure TestCert where
  id : Nat
  costVal : Nat
  hashVal : ByteArray
  validVal : Bool
  deriving BEq

instance : VerifiableRace Nat TestCert where
  isValid _ c := c.validVal
  cost _ c := c.costVal
  digest c := c.hashVal

def test_epistemic_consensus : Bool :=
  let cA : TestCert := { id := 1, costVal := 10, hashVal := ByteArray.mk #[1], validVal := true }
  let cB : TestCert := { id := 2, costVal := 20, hashVal := ByteArray.mk #[0], validVal := true }
  let cC : TestCert := { id := 3, costVal := 10, hashVal := ByteArray.mk #[2], validVal := true }
  let cBad : TestCert := { id := 4, costVal := 1, hashVal := ByteArray.mk #[0], validVal := false }
  let winnerAB := selectWinner 0 [cA, cB]
  let winnerBA := selectWinner 0 [cB, cA]
  let winnerAC := selectWinner 0 [cA, cC]
  let winnerWithBad := selectWinner 0 [cBad, cA]
  (winnerAB == some cA) &&
  (winnerBA == some cA) && -- order-insensitive
  (winnerAC == some cA) && -- equal cost, lower byte digest wins
  (winnerWithBad == some cA) -- invalid rejected

#guard test_epistemic_consensus == true

-- 6. Unit Test: Feature 33 Merkle Trace Fold & Pruning
def test_merkle_trace_collapse : Bool :=
  let s₀ : VaultStore := fun c =>
    if c == "cellA" then some (.label "initA")
    else if c == "cellB" then some (.label "initB")
    else none
  let schema := ["cellA", "cellB"]
  let val : StoreValuation := fun st c =>
    match st c with
    | some (.label "initA") => 10
    | some (.label "initB") => 20
    | some (.label "postA") => 100
    | _ => 0
  let tA : VaultTurn := {
    turnId := ByteArray.empty,
    readPins := [],
    writeCells := [{ cell := "cellA", preState := .label "initA", postState := .label "postA" }],
    occasion := .record [],
    agree := by intro d hd; cases hd; rfl; contradiction,
    balanced := fun _ => rfl,
    nodup_cells := by decide
  }
  let b1 : CommittedBlock := { height := 1, view := 1, turn := some tA }
  let b2_empty : CommittedBlock := { height := 2, view := 2, turn := none }
  let trace : Trace := [b1, b2_empty]
  let s_folded := foldTrace s₀ trace
  let root_full := collapseTrace deployed schema val s₀ trace
  let root_pruned := collapseTrace deployed schema val s₀ (filterActive trace)
  let cellCheck := match s_folded "cellA", s_folded "cellB" with
    | some (.label "postA"), some (.label "initB") => true
    | _, _ => false
  cellCheck &&
  (val s_folded "cellA" == 100) &&
  (val s_folded "cellB" == 20) &&
  (root_full == root_pruned)

#guard test_merkle_trace_collapse == true

def main : IO Unit := do
  IO.println "[PASS] Milestone4Test: All unit tests succeeded."
