import Obend.Consensus.Simplex
import Obend.Consensus.Finality
import Obend.Consensus.Epistemic
import Obend.Fold.Collapse
import Obend.Vault.Hyperedge
import Obend.Core.Digest
import Obend.Receipt.Merkle
import Obend.Judge.Clearing
import Obend.Judge.RealAnalysis
import Obend.Analysis.RealAnalysis

open Obend.Consensus.Simplex
open Obend.Consensus.Finality
open Obend.Consensus.Epistemic
open Obend.Fold.Collapse
open Obend.Vault
open Obend.Core.Digest (deployed)
open Obend.Receipt.Merkle (Opening opens mapOpening mapRoot)
open Obend.Judge
open Obend.Consensus.Epistemic.DrEXRace

set_option autoImplicit false

/-!
# Milestone 4 Challenger 2 Empirical Stress Test Harness

Role: Empirical Challenger (role: critic, specialist)
Features Under Test:
- Feature 32: `EpistemicConsensus` (solver/proof race convergence, canonical tie-breaking, permutation invariance, adversarial injections)
- Feature 33: `Fold.collapse` (symbolic trace folding, Merkle root collapse, associativity, pruning preservation, stranger-checkable openings & tampering rejection)
-/

namespace Obend.Challenger4_2

/-! ## Helper: ByteArray and Permutation Utilities -/

def mkBytes (xs : List Nat) : ByteArray :=
  ByteArray.mk (xs.map Nat.toUInt8).toArray

def permutations {α : Type} : List α → List (List α)
  | [] => [[]]
  | x :: xs =>
    (permutations xs).flatMap (fun p =>
      (List.range (p.length + 1)).map (fun i =>
        (p.take i) ++ [x] ++ (p.drop i)))

-- Deterministic Linear Congruential Generator for pseudo-random stress tests
def lcgNext (seed : Nat) : Nat :=
  (seed * 1103515245 + 12345) % 2147483648

def shuffleStep {α : Type} (rng : Nat) (acc : List α) : List α → List α × Nat
  | [] => (acc, rng)
  | x :: xs =>
    let rng' := lcgNext rng
    let idx := rng' % (acc.length + 1)
    let acc' := (acc.take idx) ++ [x] ++ (acc.drop idx)
    shuffleStep rng' acc' xs

def shuffleWithSeed {α : Type} (seed : Nat) (l : List α) : List α :=
  (shuffleStep seed [] l).1

/-! ## Test Structure for Generic Epistemic Races -/

structure RaceCert where
  id : Nat
  costVal : Nat
  hashVal : ByteArray
  validVal : Bool
  deriving BEq, Inhabited

instance : VerifiableRace Nat RaceCert where
  isValid _ c := c.validVal
  cost _ c := c.costVal
  digest c := c.hashVal

/-! ## §1. Deep Canonical Ordering Tests for `byteArrayLt` -/

def test_byte_array_canonical_order : IO Unit := do
  IO.println "  [Test 1.1] Testing byteArrayLt strict ordering properties..."

  -- 1. Irreflexivity
  let empty := ByteArray.empty
  let b1 := mkBytes [1]
  let b2 := mkBytes [1, 2, 3]
  let b32 := mkBytes (List.replicate 32 0xAA)
  if byteArrayLt empty empty then throw (IO.userError "Irreflexivity failed for empty")
  if byteArrayLt b1 b1 then throw (IO.userError "Irreflexivity failed for b1")
  if byteArrayLt b2 b2 then throw (IO.userError "Irreflexivity failed for b2")
  if byteArrayLt b32 b32 then throw (IO.userError "Irreflexivity failed for b32")

  -- 2. Prefix comparison: shorter prefix strictly less
  let prefixShort := mkBytes [1, 2]
  let prefixLong := mkBytes [1, 2, 0]
  if !byteArrayLt prefixShort prefixLong then
    throw (IO.userError "Prefix ordering failed: [1,2] should be < [1,2,0]")
  if byteArrayLt prefixLong prefixShort then
    throw (IO.userError "Asymmetry failed: [1,2,0] should NOT be < [1,2]")

  -- 3. Differing byte values at index 0 across different lengths
  let bFF := mkBytes [0xFF]
  let b0000 := mkBytes [0x00, 0x00]
  if !byteArrayLt b0000 bFF then
    throw (IO.userError "Byte comparison failed: [0x00, 0x00] should be < [0xFF]")
  if byteArrayLt bFF b0000 then
    throw (IO.userError "Asymmetry failed for [0xFF] vs [0x00, 0x00]")

  -- 4. Deep difference in 32-byte arrays (byte 31 difference)
  let hashA := mkBytes ((List.replicate 31 0x05) ++ [0x10])
  let hashB := mkBytes ((List.replicate 31 0x05) ++ [0x11])
  if !byteArrayLt hashA hashB then
    throw (IO.userError "Deep 32-byte hash comparison failed: hashA < hashB")
  if byteArrayLt hashB hashA then
    throw (IO.userError "Deep 32-byte hash asymmetry failed")

  -- 5. Transitivity check on 10 sequential byte arrays
  let chain := (List.range 10).map (fun i => mkBytes [i.toUInt8.toNat])
  for i in [0:9] do
    for j in [i+1:10] do
      let bi := chain[i]!
      let bj := chain[j]!
      if !byteArrayLt bi bj then
        throw (IO.userError s!"Transitivity check failed: chain[{i}] should be < chain[{j}]")
      if byteArrayLt bj bi then
        throw (IO.userError s!"Asymmetry check failed: chain[{j}] should NOT be < chain[{i}]")

  IO.println "  [PASS] byteArrayLt strict total order, prefix handling, and deep asymmetry verified."

/-! ## §2. Large Candidate Pool Epistemic Solver Race -/

def test_large_pool_solver_race : IO Unit := do
  IO.println "  [Test 1.2] Testing competitive solver races with large candidate pools (120 candidates)..."

  -- Construct 120 candidate certificates:
  -- Solver 42 is crafted as the true optimal winner: valid, cost 10, hash [0, 0, 1]
  let winnerCert : RaceCert := {
    id := 42,
    costVal := 10,
    hashVal := mkBytes [0, 0, 1],
    validVal := true
  }

  let mut pool : List RaceCert := [winnerCert]

  -- Add 30 inferior valid candidates with higher costs (11 to 40)
  for i in [0:30] do
    let c : RaceCert := {
      id := 100 + i,
      costVal := 11 + i,
      hashVal := mkBytes [0, 0, 0], -- even with lower hash, higher cost loses
      validVal := true
    }
    pool := c :: pool

  -- Add 30 invalid candidates with lower costs (0 to 9)
  for i in [0:30] do
    let c : RaceCert := {
      id := 200 + i,
      costVal := i % 10,
      hashVal := mkBytes [0, 0, 0], -- cheat with 0 cost and 0 hash, but invalid!
      validVal := false
    }
    pool := c :: pool

  -- Add 30 valid candidates with equal cost (10) but lexicographically larger hashes
  for i in [1:31] do
    let c : RaceCert := {
      id := 300 + i,
      costVal := 10,
      hashVal := mkBytes [0, 0, 1 + i], -- same cost, but hash [0, 0, 1+i] > [0, 0, 1]
      validVal := true
    }
    pool := c :: pool

  -- Add 29 invalid candidates with various costs and hashes
  for i in [0:29] do
    let c : RaceCert := {
      id := 400 + i,
      costVal := 50 + i,
      hashVal := mkBytes [i, i, i],
      validVal := false
    }
    pool := c :: pool

  if pool.length != 120 then
    throw (IO.userError s!"Expected pool length 120, got {pool.length}")

  -- Run epistemic race winner selection
  let selected := selectWinner 0 pool
  match selected with
  | none => throw (IO.userError "selectWinner returned none on large pool")
  | some w =>
    if w.id != 42 then
      throw (IO.userError s!"Expected winner 42, got {w.id} (cost: {w.costVal}, valid: {w.validVal})")
    if !w.validVal then
      throw (IO.userError "Selected winner is NOT valid!")

  IO.println "  [PASS] 120-candidate pool converged deterministically to optimal winner (ID 42)."

/-! ## §3. Equal-Cost Tie-Breaking Stress Test -/

def test_equal_cost_tie_breaking : IO Unit := do
  IO.println "  [Test 1.3] Testing tie-breaking among 40 equal-cost valid certificates..."

  -- 40 valid certificates all with identical cost = 50
  -- Unique winner should be the one with minimal hash [0, 1]
  let canonicalWinner : RaceCert := {
    id := 999,
    costVal := 50,
    hashVal := mkBytes [0, 1],
    validVal := true
  }

  let mut candidates : List RaceCert := [canonicalWinner]
  for i in [2:41] do
    let c : RaceCert := {
      id := 1000 + i,
      costVal := 50,
      hashVal := mkBytes [0, i], -- strictly greater than [0, 1]
      validVal := true
    }
    candidates := c :: candidates

  let winner := selectWinner 0 candidates
  match winner with
  | none => throw (IO.userError "Tie-break race produced none")
  | some w =>
    if w.id != 999 then
      throw (IO.userError s!"Tie-breaking failed: expected ID 999, got {w.id}")

  IO.println "  [PASS] 40-way equal-cost tie-break strictly selected canonical minimum hash."

/-! ## §4. Candidate Arrival Permutation Invariance Tests -/

def test_permutation_invariance : IO Unit := do
  IO.println "  [Test 1.4] Testing candidate arrival permutation invariance across all 720 orderings..."

  let cWin : RaceCert := { id := 1, costVal := 10, hashVal := mkBytes [1], validVal := true }
  let cEqualLoss : RaceCert := { id := 2, costVal := 10, hashVal := mkBytes [2], validVal := true }
  let cHigherCost : RaceCert := { id := 3, costVal := 20, hashVal := mkBytes [0], validVal := true }
  let cInvalidLow : RaceCert := { id := 4, costVal := 1, hashVal := mkBytes [0], validVal := false }
  let cValidMid : RaceCert := { id := 5, costVal := 15, hashVal := mkBytes [5], validVal := true }
  let cInvalidEqual : RaceCert := { id := 6, costVal := 10, hashVal := mkBytes [0], validVal := false }

  let basePool := [cWin, cEqualLoss, cHigherCost, cInvalidLow, cValidMid, cInvalidEqual]
  let allPerms := permutations basePool

  if allPerms.length != 720 then
    throw (IO.userError s!"Expected 720 permutations, got {allPerms.length}")

  for perm in allPerms do
    let w := selectWinner 0 perm
    match w with
    | none => throw (IO.userError "selectWinner returned none for permutation")
    | some res =>
      if res.id != 1 then
        throw (IO.userError s!"Permutation invariance violated: winner was ID {res.id} instead of 1")

  IO.println "  [PASS] 100% of 720 candidate permutations produced bit-identical winning certificate."

  -- Stress-test larger pool of 25 candidates with 50 pseudo-random shuffles
  IO.println "  [Test 1.4b] Stress testing 50 pseudo-random shuffles of 25-candidate pool..."
  let mut largePool : List RaceCert := [cWin]
  for i in [1:25] do
    largePool := { id := 10 + i, costVal := 12 + i, hashVal := mkBytes [i], validVal := true } :: largePool

  for seed in [1001:1051] do
    let shuffled := shuffleWithSeed seed largePool
    let w := selectWinner 0 shuffled
    match w with
    | some res =>
      if res.id != 1 then
        throw (IO.userError s!"Random shuffle (seed {seed}) selected ID {res.id} instead of 1")
    | none => throw (IO.userError s!"Random shuffle (seed {seed}) returned none")

  IO.println "  [PASS] 50 pseudo-random shuffles of 25-candidate pool strictly preserved winner ID 1."

/-! ## §5. Adversarial Injections and Edge Case Probes -/

def test_adversarial_injections : IO Unit := do
  IO.println "  [Test 1.5] Testing adversarial injection attacks against epistemic winner selection..."

  let honestWinner : RaceCert := { id := 77, costVal := 25, hashVal := mkBytes [10, 20], validVal := true }

  -- 1. Flooding with 50 zero-cost invalid certificates
  let mut floodedPool : List RaceCert := [honestWinner]
  for i in [0:50] do
    floodedPool := { id := 5000 + i, costVal := 0, hashVal := mkBytes [0], validVal := false } :: floodedPool

  match selectWinner 0 floodedPool with
  | some w =>
    if w.id != 77 then throw (IO.userError "Adversary displaced winner with invalid zero-cost certificates!")
  | none => throw (IO.userError "Flooding caused selection to return none")

  -- 2. Flooding with identical duplicate submissions of the winning certificate
  let dupPool := [honestWinner, honestWinner, honestWinner, honestWinner]
  match selectWinner 0 dupPool with
  | some w =>
    if w.id != 77 then throw (IO.userError "Duplicate winner submission altered winner!")
  | none => throw (IO.userError "Duplicate winner returned none")

  -- 3. All-invalid pool edge case: MUST return none
  let allInvalid : List RaceCert := (List.range 20).map (fun i =>
    { id := i, costVal := i, hashVal := mkBytes [i], validVal := false })
  if (selectWinner 0 allInvalid).isSome then
    throw (IO.userError "selectWinner selected a winner from an all-invalid pool!")

  -- 4. Empty candidate list edge case: MUST return none
  if (selectWinner (Cert := RaceCert) 0 []).isSome then
    throw (IO.userError "selectWinner selected a winner from an empty candidate list!")

  IO.println "  [PASS] All adversarial injection vectors (flooding, duplicates, all-invalid, empty) safely handled."

/-! ## §6. Concrete DrEX LP Clearing Race Stress Test -/

def test_drex_clearing_race : IO Unit := do
  IO.println "  [Test 1.6] Testing DrEX certified LP clearing race (Feature 21/32)..."

  let q : ClearingQuery := {
    market := { currency := 1, goods := 2, epsilon := 5 },
    orders := [],
    transfers := []
  }

  -- Cert A: price 100, potentials (10, 10) -> gap divergence 0, cost = 5 + 0 = 5
  let certA : ClearingCert := {
    cert := { price := 100, potentials := (10, 10), slacks := [] },
    turnDigest := mkBytes [0x01]
  }

  -- Cert B: price 100, potentials (10, 12) -> gap divergence 2, cost = 5 + 2 = 7 (inferior)
  let certB : ClearingCert := {
    cert := { price := 100, potentials := (10, 12), slacks := [] },
    turnDigest := mkBytes [0x00]
  }

  -- Cert Invalid: price 0 (illegal in clearing judge), cost 5
  let certBad : ClearingCert := {
    cert := { price := 0, potentials := (10, 10), slacks := [] },
    turnDigest := mkBytes [0x00]
  }

  let candidates := [certB, certBad, certA]
  match selectWinner q candidates with
  | none => throw (IO.userError "DrEX LP race returned none")
  | some win =>
    if win.cert.price != 100 || win.cert.potentials != (10, 10) then
      throw (IO.userError "DrEX LP race selected sub-optimal or invalid clearing certificate!")

  IO.println "  [PASS] DrEX LP clearing race selected certified epsilon-optimal pricing certificate."

open Obend.Consensus.Epistemic.IntervalRace Obend.Analysis Obend.Analysis.CanonicalRat in
def test_interval_bounding_race : IO Unit := do
  IO.println "  [Test 1.7] Testing RealAnalysis certified interval bounding race (Feature 14/32)..."

  let rat0 : CanonicalRat := CanonicalRat.ofInt 0
  let rat10 : CanonicalRat := CanonicalRat.ofInt 10
  let iv0_10 : Interval := { lo := rat0, hi := rat10 }

  let q : IntervalQuery := {
    expr := .const (CanonicalRat.ofInt 5),
    env := [],
    claimedBound := iv0_10
  }

  let certA : IntervalCertWrapper := {
    cert := .direct,
    boundDigest := mkBytes [0x01]
  }

  let certB : IntervalCertWrapper := {
    cert := .direct,
    boundDigest := mkBytes [0x02]
  }

  let certBad : IntervalCertWrapper := {
    cert := .counterexample [],
    boundDigest := mkBytes [0x00]
  }

  let candidates := [certB, certBad, certA]
  match selectWinner q candidates with
  | none => throw (IO.userError "Interval race returned none")
  | some win =>
    if win.boundDigest != mkBytes [0x01] then
      throw (IO.userError "Interval race failed tie-break on boundDigest!")

  IO.println "  [PASS] Interval bounding race validated certified enclosure and resolved tie-break."

/-! ## Helper: Vault Stores and Block Generators -/

def mkBlockWithTurn (h v : Nat) (cell : String) (val : Nat) : CommittedBlock :=
  let t : VaultTurn := {
    turnId := ByteArray.empty,
    readPins := [],
    writeCells := [{ cell := cell, preState := .label "pre", postState := .natural val }],
    occasion := .record [],
    agree := by intro d hd; cases hd; rfl; contradiction,
    balanced := fun _ => rfl,
    nodup_cells := by simp
  }
  { height := h, view := v, turn := some t }

def mkSkipBlock (h v : Nat) : CommittedBlock :=
  { height := h, view := v, turn := none }

/-! ## §7. Large Mixed Trace Folding and Trace Compositionality -/

def test_trace_folding_and_composition : IO Unit := do
  IO.println "  [Test 2.1] Testing symbolic Merkle trace folding & compositionality on 120-block trace..."

  let schema := ["c0", "c1", "c2", "c3", "c4", "c5", "c6", "c7"]

  let s₀ : VaultStore := fun c =>
    if schema.contains c then some (.label "init") else none

  let val : StoreValuation := fun st c =>
    match st c with
    | some (.natural n) => n + 1000
    | some (.label "init") => 42
    | _ => 0

  -- Build a 120-block trace:
  -- 60 active blocks mutating cells, 60 timeout skip blocks
  let mut trace : Trace := []
  for i in [0:60] do
    let cell := schema[i % schema.length]!
    let bActive := mkBlockWithTurn (2 * i + 1) (2 * i + 1) cell (i + 1)
    let bSkip := mkSkipBlock (2 * i + 2) (2 * i + 2)
    trace := bSkip :: bActive :: trace
  trace := trace.reverse

  if trace.length != 120 then
    throw (IO.userError s!"Expected 120 blocks, got {trace.length}")

  -- Fold entire trace
  let s_folded := foldTrace s₀ trace

  -- Metatheorem: Trace Compositionality / Associativity
  -- foldTrace s₀ (T1 ++ T2) = foldTrace (foldTrace s₀ T1) T2
  let splitPoints := [0, 1, 15, 45, 60, 95, 119, 120]
  for k in splitPoints do
    let t1 := trace.take k
    let t2 := trace.drop k
    let s_composed := foldTrace (foldTrace s₀ t1) t2
    -- Check agreement on all schema cells
    for cell in schema do
      if val s_folded cell != val s_composed cell then
        throw (IO.userError s!"Compositionality failed at split {k} for cell {cell}")
    -- Check Merkle root agreement
    let rootFull := collapseTrace deployed schema val s₀ trace
    let rootComp := collapseTrace deployed schema val (foldTrace s₀ t1) t2
    if rootFull != rootComp then
      throw (IO.userError s!"Merkle collapse root divergence under composition at split {k}")

  IO.println "  [PASS] Trace compositionality foldTrace(s, T1++T2) = foldTrace(foldTrace(s,T1),T2) verified at 8 split points."

/-! ## §8. Empty Block Pruning Preservation -/

def test_pruning_preservation : IO Unit := do
  IO.println "  [Test 2.2] Testing empty/timeout block pruning preservation..."

  let schema := ["c0", "c1", "c2", "c3"]
  let s₀ : VaultStore := fun c => if schema.contains c then some (.label "init") else none
  let val : StoreValuation := fun st c =>
    match st c with
    | some (.natural n) => n * 7
    | some (.label "init") => 13
    | _ => 0

  -- Create trace with 40 skip blocks interleaved with 20 active blocks
  let mut trace : Trace := []
  for i in [0:20] do
    let bA := mkBlockWithTurn (3 * i + 1) (3 * i + 1) (schema[i % schema.length]!) (i + 1)
    let bS1 := mkSkipBlock (3 * i + 2) (3 * i + 2)
    let bS2 := mkSkipBlock (3 * i + 3) (3 * i + 3)
    trace := bS2 :: bS1 :: bA :: trace
  trace := trace.reverse

  let pruned := filterActive trace
  if pruned.length != 20 then
    throw (IO.userError s!"Expected 20 active blocks, got {pruned.length}")

  let rootFull := collapseTrace deployed schema val s₀ trace
  let rootPruned := collapseTrace deployed schema val s₀ pruned

  if rootFull != rootPruned then
    throw (IO.userError s!"Pruning preservation failed! Full root {rootFull} != Pruned root {rootPruned}")

  -- Edge case: 30 consecutive empty blocks
  let emptyTrace : Trace := (List.range 30).map (fun i => mkSkipBlock i i)
  let s_empty_folded := foldTrace s₀ emptyTrace
  for cell in schema do
    if val s_empty_folded cell != val s₀ cell then
      throw (IO.userError s!"Empty trace modified state for cell {cell}")

  let rootEmptyFull := collapseTrace deployed schema val s₀ emptyTrace
  let rootEmptyPruned := collapseTrace deployed schema val s₀ (filterActive emptyTrace)
  let rootDirect := collapseRoot deployed schema val s₀

  if rootEmptyFull != rootEmptyPruned || rootEmptyFull != rootDirect then
    throw (IO.userError "Empty trace root does not equal direct root of initial store")

  IO.println "  [PASS] Pruning preservation verified: filtering empty blocks produces bit-identical Merkle roots."

/-! ## §9. Stranger-Checkable Merkle Openings & Adversarial Tampering -/

def test_stranger_checkable_openings_and_tampering : IO Unit := do
  IO.println "  [Test 2.3] Testing stranger-checkable Merkle openings and defeating adversarial tampering..."

  let schema := ["alpha", "beta", "gamma", "delta", "epsilon", "zeta", "eta", "theta"]
  let s₀ : VaultStore := fun c => if schema.contains c then some (.label "init") else none
  let val : StoreValuation := fun st c =>
    match st c with
    | some (.natural n) => n + 500
    | some (.label "init") => 77
    | _ => 0

  -- Mutate all schema cells across 8 blocks
  let mut trace : Trace := []
  for i in [0:schema.length] do
    let cell := schema[i]!
    trace := mkBlockWithTurn i i cell (i * 10 + 3) :: trace
  trace := trace.reverse

  let s_final := foldTrace s₀ trace
  let root := collapseTrace deployed schema val s₀ trace

  -- Metatheorem: Stranger-Checkable Verification Contract (collapseRoot_binds)
  -- A stranger checks:
  --   1. o.size == schema.length
  --   2. o.index < schema.length
  --   3. schema[o.index] == k
  --   4. opens deployed o root == true
  let verifyStranger (k : String) (op : Opening) (r : Nat) : Bool :=
    (op.size == schema.length) &&
    (op.index < schema.length) &&
    (schema[op.index]! == k) &&
    opens deployed op r

  -- Verify honest openings for all cells
  for cell in schema do
    let optO := openCell deployed schema val s_final cell
    match optO with
    | none => throw (IO.userError s!"openCell returned none for existing schema cell {cell}")
    | some o =>
      -- 1. Honest opening must pass full stranger verification
      if !verifyStranger cell o root then
        throw (IO.userError s!"Honest opening failed stranger verification against root for cell {cell}")
      if o.value != val s_final cell then
        throw (IO.userError s!"Opening value {o.value} != true store value {val s_final cell}")

      -- 2. Adversarial Probe A: Tamper Value (lie about state)
      let o_bad_val := { o with value := o.value + 1 }
      if opens deployed o_bad_val root then
        throw (IO.userError s!"CRITICAL: Tampered value opened successfully for cell {cell}!")
      if verifyStranger cell o_bad_val root then
        throw (IO.userError s!"CRITICAL: Tampered value passed stranger verification for cell {cell}!")

      -- 3. Adversarial Probe B: Tamper Sibling Path (forged Merkle path)
      if !o.path.isEmpty then
        let o_bad_path := { o with path := o.path.map (· + 1) }
        if opens deployed o_bad_path root then
          throw (IO.userError s!"CRITICAL: Tampered Merkle sibling path opened successfully for cell {cell}!")
        if verifyStranger cell o_bad_path root then
          throw (IO.userError s!"CRITICAL: Tampered path passed stranger verification for cell {cell}!")

      -- 4. Adversarial Probe C: Tamper Index (cell position spoofing)
      let o_bad_idx := { o with index := (o.index + 1) % schema.length }
      if opens deployed o_bad_idx root then
        throw (IO.userError s!"CRITICAL: Tampered cell index opened successfully for cell {cell}!")
      if verifyStranger cell o_bad_idx root then
        throw (IO.userError s!"CRITICAL: Tampered index passed stranger verification for cell {cell}!")

      -- 5. Adversarial Probe D: Tamper Schema Size
      -- Size 0 or invalid climb size rejected by climb itself
      let o_zero_sz := { o with size := 0 }
      if opens deployed o_zero_sz root then
        throw (IO.userError s!"CRITICAL: Zero-size opening opened successfully for cell {cell}!")
      -- Any size divergence from schema.length is rejected by stranger check
      let o_bad_sz := { o with size := o.size + 1 }
      if verifyStranger cell o_bad_sz root then
        throw (IO.userError s!"CRITICAL: Tampered schema size passed stranger verification for cell {cell}!")

      -- 6. Adversarial Probe E: Check against invalid root
      if opens deployed o (root + 1) then
        throw (IO.userError s!"CRITICAL: Honest opening verified against tampered root for cell {cell}!")
      if verifyStranger cell o (root + 1) then
        throw (IO.userError s!"CRITICAL: Honest opening passed stranger verification against tampered root!")

      -- 7. Adversarial Probe F: Claim opening belongs to wrong cell key
      if verifyStranger "wrong_cell_key" o root then
        throw (IO.userError s!"CRITICAL: Opening verified for wrong cell key!")

  -- 8. Adversarial Probe G: Query non-existent cell
  let optNonExistent := openCell deployed schema val s_final "ghost_cell_not_in_schema"
  if optNonExistent.isSome then
    throw (IO.userError "openCell returned some opening for non-existent cell!")

  IO.println "  [PASS] Stranger-checkable openings verified for all 8 schema positions."
  IO.println "  [PASS] 7 distinct adversarial tampering probes (value, path, index, size, root, wrong key, ghost) REJECTED."

end Obend.Challenger4_2

open Obend.Challenger4_2

def main : IO Unit := do
  IO.println "=========================================================="
  IO.println "=== [Milestone 4 Challenger 2 Empirical Stress Test] ==="
  IO.println "=========================================================="
  test_byte_array_canonical_order
  test_large_pool_solver_race
  test_equal_cost_tie_breaking
  test_permutation_invariance
  test_adversarial_injections
  test_drex_clearing_race
  test_interval_bounding_race
  test_trace_folding_and_composition
  test_pruning_preservation
  test_stranger_checkable_openings_and_tampering
  IO.println "=========================================================="
  IO.println "[PASS] Milestone 4 Challenger 2: ALL EMPIRICAL STRESS TESTS PASSED."
  IO.println "=========================================================="
