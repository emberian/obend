import Obend.Vault.Hyperedge
import Obend.Ledger.Book
import Obend.Ledger.Seat
import Obend.Judge.Clearing
import Obend.Judge.Class
import Obend.Law.Contract
import Obend.Core.Data
import Obend.Core.Term

open Obend.Vault
open Obend.Ledger
open Obend.Judge
open Obend.Law
open Obend.Core.Data
open Obend.Core.Term

set_option linter.unusedVariables false

def assertChallenger (what : String) (ok : Bool) : IO Unit :=
  if ok then
    IO.println s!"[PASS] {what}"
  else
    throw (IO.userError s!"[FAIL] EMPIRICAL CHALLENGE FAILURE: {what}")

def dataEq (o1 o2 : Option Data) : Bool :=
  match o1, o2 with
  | none, none => true
  | some d1, some d2 => Obend.Law.termEq d1.term d2.term
  | _, _ => false

def isDisjointTurns (T₁ T₂ : VaultTurn) : Bool :=
  let acc1 := T₁.accessFootprint
  let acc2 := T₂.accessFootprint
  T₁.writeFootprint.all (fun c => !acc2.contains c) &&
  T₂.writeFootprint.all (fun c => !acc1.contains c)

/-! =========================================================================
    Suite 1: Duplicate Write Cell Attacks & Pin Integrity
    ========================================================================= -/

def testDuplicateWriteCellsAndPins : IO Unit := do
  IO.println "=== Suite 1: Duplicate Write Cells & Pin Integrity ==="

  -- 1.1 checkNodupCells on empty and single
  assertChallenger "checkNodupCells accepts empty cell list"
    (checkNodupCells [] matches .ok ())
  assertChallenger "checkNodupCells accepts single cell"
    (checkNodupCells ["cellX"] matches .ok ())

  -- 1.2 checkNodupCells on distinct 10 elements
  let distinct10 := (List.range 10).map (fun i => s!"cell_{i}")
  assertChallenger "checkNodupCells accepts 10 distinct cells"
    (checkNodupCells distinct10 matches .ok ())

  -- 1.3 Duplicate at head
  assertChallenger "checkNodupCells catches duplicate at head"
    (checkNodupCells ["cA", "cA", "cB"] matches .error (.duplicateWriteCell "cA"))

  -- 1.4 Duplicate at tail
  assertChallenger "checkNodupCells catches duplicate at tail"
    (checkNodupCells ["cA", "cB", "cB"] matches .error (.duplicateWriteCell "cB"))

  -- 1.5 Duplicate across distance
  assertChallenger "checkNodupCells catches distant duplicate"
    (checkNodupCells ["cA", "cB", "cC", "cD", "cA"] matches .error (.duplicateWriteCell "cA"))

  -- 1.6 Injected duplicate in large list of 100 cells
  let base100 := (List.range 100).map (fun i => s!"cell_idx_{i}")
  let dup100 := base100.take 83 ++ ["cell_idx_17"] ++ base100.drop 83
  assertChallenger "checkNodupCells catches duplicate in 101-element list at pos 17 and 83"
    (checkNodupCells dup100 matches .error (.duplicateWriteCell "cell_idx_17"))

  -- 1.7 Footprint Pins: Conflicting pins in a single footprint
  let storeA : VaultStore := fun c =>
    if c == "cellA" then some (.natural 10)
    else if c == "cellB" then some (.natural 20)
    else none

  -- Pin 1 expects 10, Pin 2 expects 99 on same cell
  let fpConflictingValues : Footprint := [
    ⟨"cellA", some (.natural 10)⟩,
    ⟨"cellA", some (.natural 99)⟩
  ]
  assertChallenger "admitFootprint catches conflicting pins for same cell"
    (admitFootprint storeA fpConflictingValues matches .error (.footprintStale "cellA" (some (.natural 99)) (some (.natural 10))))

  -- Pin 1 expects 10, Pin 2 expects none on same cell
  let fpConflictingPresence : Footprint := [
    ⟨"cellA", some (.natural 10)⟩,
    ⟨"cellA", none⟩
  ]
  assertChallenger "admitFootprint catches conflicting presence pin"
    (admitFootprint storeA fpConflictingPresence matches .error (.footprintStale "cellA" none (some (.natural 10))))

  -- Tail stale pin after 30 valid pins
  let longValidPins : Footprint := (List.range 30).map (fun i => ⟨s!"unalloc_{i}", none⟩)
  let longFpWithStaleTail := longValidPins ++ [⟨"cellA", some (.natural 999)⟩]
  assertChallenger "admitFootprint traverses 30 valid pins to catch tail stale pin"
    (admitFootprint storeA longFpWithStaleTail matches .error (.footprintStale "cellA" (some (.natural 999)) (some (.natural 10))))

  -- TOCTOU Race Simulation: concurrent write between authoring and admission
  let s0 := storeA
  let readerPins : Footprint := [⟨"cellA", some (.natural 10)⟩]
  let sAfterConcurrentWrite := updateStore s0 "cellA" (some (.natural 999))
  assertChallenger "TOCTOU simulation: reader turn rejected after concurrent writer modifies cellA"
    (admitFootprint sAfterConcurrentWrite readerPins matches .error (.footprintStale "cellA" (some (.natural 10)) (some (.natural 999))))

/-! =========================================================================
    Suite 2: Bernstein Independence & Concurrency Hazards
    ========================================================================= -/

def testBernsteinIndependenceAndHazards : IO Unit := do
  IO.println "=== Suite 2: Bernstein Independence & Concurrency Hazards ==="

  let store : VaultStore := fun c =>
    if c == "cR" then some (.natural 100)
    else if c == "cW1" then some (.natural 200)
    else if c == "cW2" then some (.natural 300)
    else if c == "cShared" then some (.natural 500)
    else none

  -- 2.1 RAR (Read-After-Read / Read Sharing):
  -- T1 reads cShared, writes cW1 = 201
  -- T2 reads cShared, writes cW2 = 301
  let d1 : CellDelta := { cell := "cW1", preState := .natural 200, postState := .natural 201 }
  let d2 : CellDelta := { cell := "cW2", preState := .natural 300, postState := .natural 301 }

  let t1 : VaultTurn := {
    turnId := ByteArray.empty
    readPins := [⟨"cShared", some (.natural 500)⟩]
    writeCells := [d1]
    occasion := .record []
    agree := by intro _ hd; simp only [List.mem_singleton] at hd; subst hd; rfl
    balanced := by intro _; rfl
  }

  let t2 : VaultTurn := {
    turnId := ByteArray.empty
    readPins := [⟨"cShared", some (.natural 500)⟩]
    writeCells := [d2]
    occasion := .record []
    agree := by intro _ hd; simp only [List.mem_singleton] at hd; subst hd; rfl
    balanced := by intro _; rfl
  }

  assertChallenger "Bernstein independence holds for shared reads and disjoint writes"
    (isDisjointTurns t1 t2 == true)

  let s12 := applyTurn (applyTurn store t1) t2
  let s21 := applyTurn (applyTurn store t2) t1

  let cells := ["cR", "cW1", "cW2", "cShared", "cOther"]
  let commutesRAR := cells.all fun c => dataEq (s12 c) (s21 c)
  assertChallenger "Commutativity holds under shared reads (RAR): s12 == s21" commutesRAR
  assertChallenger "cW1 has postState 201" (dataEq (s12 "cW1") (some (.natural 201)))
  assertChallenger "cW2 has postState 301" (dataEq (s12 "cW2") (some (.natural 301)))
  assertChallenger "cShared is untouched (500)" (dataEq (s12 "cShared") (some (.natural 500)))

  -- Both remain admitted in either order:
  let sAfterT1 := applyTurn store t1
  assertChallenger "T2 readPins admit after T1 execution"
    (admitFootprint sAfterT1 t2.readPins matches .ok ())
  let sAfterT2 := applyTurn store t2
  assertChallenger "T1 readPins admit after T2 execution"
    (admitFootprint sAfterT2 t1.readPins matches .ok ())

  -- 2.2 RAW Hazard (Read-After-Write):
  -- T_raw1 writes cR = 999
  -- T_raw2 reads cR (expected 100) and writes cW2 = 302
  let d_raw1 : CellDelta := { cell := "cR", preState := .natural 100, postState := .natural 999 }
  let t_raw1 : VaultTurn := {
    turnId := ByteArray.empty
    readPins := []
    writeCells := [d_raw1]
    occasion := .record []
    agree := by intro _ hd; simp only [List.mem_singleton] at hd; subst hd; rfl
    balanced := by intro _; rfl
  }

  let d_raw2 : CellDelta := { cell := "cW2", preState := .natural 300, postState := .natural 302 }
  let t_raw2 : VaultTurn := {
    turnId := ByteArray.empty
    readPins := [⟨"cR", some (.natural 100)⟩]
    writeCells := [d_raw2]
    occasion := .record []
    agree := by intro _ hd; simp only [List.mem_singleton] at hd; subst hd; rfl
    balanced := by intro _; rfl
  }

  assertChallenger "RAW hazard is NOT disjoint under Bernstein Independence"
    (isDisjointTurns t_raw1 t_raw2 == false)

  let sAfterRaw1 := applyTurn store t_raw1
  assertChallenger "RAW hazard: T_raw2 readPin fails after T_raw1 write"
    (admitFootprint sAfterRaw1 t_raw2.readPins matches .error (.footprintStale "cR" (some (.natural 100)) (some (.natural 999))))

  -- 2.3 WAR Hazard (Write-After-Read):
  -- T_raw2 reads cR = 100, T_raw1 writes cR = 999
  let sAfterRaw2 := applyTurn store t_raw2
  let sRaw21 := applyTurn sAfterRaw2 t_raw1
  assertChallenger "WAR hazard: execution order changes cR observation"
    (dataEq (sRaw21 "cR") (some (.natural 999)))

  -- 2.4 WAW Hazard (Write-After-Write):
  -- Both turns write to cW1 with different values
  let d_waw1 : CellDelta := { cell := "cW1", preState := .natural 200, postState := .natural 777 }
  let t_waw1 : VaultTurn := {
    turnId := ByteArray.empty
    readPins := []
    writeCells := [d_waw1]
    occasion := .record []
    agree := by intro _ hd; simp only [List.mem_singleton] at hd; subst hd; rfl
    balanced := by intro _; rfl
  }

  let d_waw2 : CellDelta := { cell := "cW1", preState := .natural 200, postState := .natural 888 }
  let t_waw2 : VaultTurn := {
    turnId := ByteArray.empty
    readPins := []
    writeCells := [d_waw2]
    occasion := .record []
    agree := by intro _ hd; simp only [List.mem_singleton] at hd; subst hd; rfl
    balanced := by intro _; rfl
  }

  assertChallenger "WAW hazard is NOT disjoint under Bernstein Independence"
    (isDisjointTurns t_waw1 t_waw2 == false)

  let sWaw12 := applyTurn (applyTurn store t_waw1) t_waw2
  let sWaw21 := applyTurn (applyTurn store t_waw2) t_waw1
  assertChallenger "WAW execution 1 then 2 produces 888" (dataEq (sWaw12 "cW1") (some (.natural 888)))
  assertChallenger "WAW execution 2 then 1 produces 777" (dataEq (sWaw21 "cW1") (some (.natural 777)))
  assertChallenger "WAW conflicting writes strictly DO NOT commute"
    (dataEq (sWaw12 "cW1") (sWaw21 "cW1") == false)

  -- 2.5 Wide Disjoint Turns (10 cells each)
  let w1Deltas : List CellDelta := (List.range 10).map fun i =>
    { cell := s!"w1_cell_{i}", preState := .natural (1000 + i), postState := .natural (2000 + i) }
  let w2Deltas : List CellDelta := (List.range 10).map fun i =>
    { cell := s!"w2_cell_{i}", preState := .natural (3000 + i), postState := .natural (4000 + i) }

  let wideStore : VaultStore := fun c =>
    match (List.range 10).find? (fun i => s!"w1_cell_{i}" == c) with
    | some i => some (.natural (1000 + i))
    | none =>
      match (List.range 10).find? (fun i => s!"w2_cell_{i}" == c) with
      | some i => some (.natural (3000 + i))
      | none => none

  let tWide1 : VaultTurn := {
    turnId := ByteArray.empty
    readPins := (List.range 5).map (fun i => ⟨s!"shared_ro_{i}", none⟩)
    writeCells := w1Deltas
    occasion := .record []
    agree := by intro _ hd; simp only [w1Deltas, List.mem_map, List.mem_range] at hd; rcases hd with ⟨_, _, rfl⟩; rfl
    balanced := by intro _; rfl
  }

  let tWide2 : VaultTurn := {
    turnId := ByteArray.empty
    readPins := (List.range 5).map (fun i => ⟨s!"shared_ro_{i}", none⟩)
    writeCells := w2Deltas
    occasion := .record []
    agree := by intro _ hd; simp only [w2Deltas, List.mem_map, List.mem_range] at hd; rcases hd with ⟨_, _, rfl⟩; rfl
    balanced := by intro _; rfl
  }

  assertChallenger "Wide 10-cell turns are disjoint" (isDisjointTurns tWide1 tWide2 == true)
  let sWide12 := applyTurn (applyTurn wideStore tWide1) tWide2
  let sWide21 := applyTurn (applyTurn wideStore tWide2) tWide1

  let allWideCheck :=
    ((List.range 10).all fun i => dataEq (sWide12 s!"w1_cell_{i}") (some (.natural (2000 + i)))) &&
    ((List.range 10).all fun i => dataEq (sWide12 s!"w2_cell_{i}") (some (.natural (4000 + i)))) &&
    ((List.range 10).all fun i => dataEq (sWide12 s!"w1_cell_{i}") (sWide21 s!"w1_cell_{i}")) &&
    ((List.range 10).all fun i => dataEq (sWide12 s!"w2_cell_{i}") (sWide21 s!"w2_cell_{i}"))

  assertChallenger "Wide 10-cell turns commute identically across all 20 cells" allWideCheck

/-! =========================================================================
    Suite 3: Store Post-Invariants & Multi-Cell Transitions
    ========================================================================= -/

def testStorePostInvariantsAndTransitions : IO Unit := do
  IO.println "=== Suite 3: Store Post-Invariants & Multi-Cell Transitions ==="

  -- Setup multi-cell store: 5 cells
  let sInit : VaultStore := fun c =>
    if c == "cellVaultA" then some (.natural 500)
    else if c == "cellVaultB" then some (.natural 200)
    else if c == "cellVaultC" then some (.natural 100)
    else if c == "cellVaultD" then some (.natural 50)
    else if c == "cellVaultE" then some (.natural 25)
    else none

  -- Multi-cell turn mutating 3 cells:
  let deltaA : CellDelta := {
    cell := "cellVaultA"
    preState := .natural 500
    postState := .natural 350
  }
  let deltaB : CellDelta := {
    cell := "cellVaultB"
    preState := .natural 200
    postState := .natural 300
  }
  let deltaC : CellDelta := {
    cell := "cellVaultC"
    preState := .natural 100
    postState := .natural 150
  }

  let turnABC : VaultTurn := {
    turnId := ByteArray.empty
    readPins := [⟨"cellVaultA", some (.natural 500)⟩, ⟨"cellVaultB", some (.natural 200)⟩, ⟨"cellVaultC", some (.natural 100)⟩]
    writeCells := [deltaA, deltaB, deltaC]
    occasion := .record []
    agree := by intro _ hd; simp only [List.mem_cons, List.not_mem_nil, or_false] at hd; rcases hd with rfl | rfl | rfl <;> rfl
    balanced := by intro _; rfl
    nodup_cells := by decide
  }

  let sPost := applyTurn sInit turnABC

  -- Verify each mutated cell receives exact postState
  assertChallenger "applyTurn updates cellVaultA to postState (350)"
    (dataEq (sPost "cellVaultA") (some (.natural 350)))
  assertChallenger "applyTurn updates cellVaultB to postState (300)"
    (dataEq (sPost "cellVaultB") (some (.natural 300)))
  assertChallenger "applyTurn updates cellVaultC to postState (150)"
    (dataEq (sPost "cellVaultC") (some (.natural 150)))

  -- Verify untouched cells are strictly preserved (applyTurn_frame)
  assertChallenger "applyTurn preserves untouched cellVaultD (50)"
    (dataEq (sPost "cellVaultD") (some (.natural 50)))
  assertChallenger "applyTurn preserves untouched cellVaultE (25)"
    (dataEq (sPost "cellVaultE") (some (.natural 25)))
  assertChallenger "applyTurn preserves untouched unallocated cellGhost (none)"
    (dataEq (sPost "cellGhost") none)

  -- Net asset conservation across the turn
  let dEth1 : CellDelta := { cell := "cA", preState := .natural 0, postState := .natural 0, halfEdges := [("ETH", -100), ("USDC", 50)] }
  let dEth2 : CellDelta := { cell := "cB", preState := .natural 0, postState := .natural 0, halfEdges := [("ETH", 100), ("USDC", -50)] }
  assertChallenger "sumAssetDelta ETH is balanced (0)"
    (sumAssetDelta [dEth1, dEth2] "ETH" == 0)
  assertChallenger "sumAssetDelta USDC is balanced (0)"
    (sumAssetDelta [dEth1, dEth2] "USDC" == 0)
  assertChallenger "sumAssetDelta unmentioned BTC is balanced (0)"
    (sumAssetDelta [dEth1, dEth2] "BTC" == 0)

/-! =========================================================================
    Suite 4: DrEX Crossing Interval & ZoE Seat Adversarial Edge Cases
    ========================================================================= -/

def testClearingJudgeAndSeatEdgeCases : IO Unit := do
  IO.println "=== Suite 4: DrEX Crossing Interval & ZoE Seat Edge Cases ==="

  -- 4.1 Crossing orders: Bid at 100, Ask at 80. Crossing interval is [80, 100].
  let orderAsk : Order := {
    account := 1
    side := .ask
    qty := 10
    total := 800  -- limit price 80
  }
  let orderBid : Order := {
    account := 2
    side := .bid
    qty := 10
    total := 1000  -- limit price 100
  }
  let orders := [orderAsk, orderBid]

  assertChallenger "hasCrossingPair returns true for ask=80, bid=100"
    (hasCrossingPair orders == true)
  assertChallenger "priceInCrossingInterval accepts lowest ask (80)"
    (priceInCrossingInterval orders 80 == true)
  assertChallenger "priceInCrossingInterval accepts mid-market price (90)"
    (priceInCrossingInterval orders 90 == true)
  assertChallenger "priceInCrossingInterval accepts highest bid (100)"
    (priceInCrossingInterval orders 100 == true)
  assertChallenger "priceInCrossingInterval rejects below lowest ask (79)"
    (priceInCrossingInterval orders 79 == false)
  assertChallenger "priceInCrossingInterval rejects above highest bid (101)"
    (priceInCrossingInterval orders 101 == false)

  -- 4.2 Non-crossing book: Bid at 70, Ask at 80.
  let orderLowBid : Order := {
    account := 2
    side := .bid
    qty := 10
    total := 700  -- limit price 70
  }
  let nonCrossingOrders := [orderAsk, orderLowBid]
  assertChallenger "hasCrossingPair returns false for non-crossing book"
    (hasCrossingPair nonCrossingOrders == false)

  -- 4.3 ZoE Seat Account Protection
  -- protectedBase is 2^256
  let ordinaryAcc : AccountId := 1000
  let seatAcc : AccountId := (1 : Nat) <<< 256 + 42
  assertChallenger "ordinary account < 2^256 cannot equal seat coordinate"
    (ordinaryAcc ≠ seatAcc)
  assertChallenger "seat coordinate is in protected space >= 2^256"
    (seatAcc >= (1 : Nat) <<< 256)

def main : IO Unit := do
  IO.println "=========================================================="
  IO.println "=== [Milestone 2 Iteration 2 Empirical Challenger Suite] ==="
  IO.println "=========================================================="
  testDuplicateWriteCellsAndPins
  testBernsteinIndependenceAndHazards
  testStorePostInvariantsAndTransitions
  testClearingJudgeAndSeatEdgeCases
  IO.println "=========================================================="
  IO.println "=== [ALL EMPIRICAL CHALLENGER STRESS TESTS PASSED] ==="
  IO.println "=========================================================="

#eval main
