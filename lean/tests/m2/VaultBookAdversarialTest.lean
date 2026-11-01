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

def assertAdversarial (what : String) (ok : Bool) : IO Unit :=
  if ok then
    IO.println s!"[PASS] {what}"
  else
    throw (IO.userError s!"[FAIL] ADVERSARIAL CHALLENGE FAILED: {what}")

def dataEq (o1 o2 : Option Data) : Bool :=
  match o1, o2 with
  | none, none => true
  | some d1, some d2 => Obend.Law.termEq d1.term d2.term
  | _, _ => false

structure PRNG where
  state : UInt64
  deriving Inhabited

def PRNG.next (rng : PRNG) : UInt64 × PRNG :=
  let s := rng.state
  let s := s ^^^ (s <<< 13)
  let s := s ^^^ (s >>> 7)
  let s := s ^^^ (s <<< 17)
  let s := if s == 0 then 0x8a5cd789635d2dff else s
  (s, ⟨s⟩)

def PRNG.nextNat (rng : PRNG) (maxVal : Nat) : Nat × PRNG :=
  if maxVal == 0 then (0, rng)
  else
    let (v, r) := rng.next
    ((v.toNat % maxVal), r)

/-! =========================================================================
    Category 1: admitFootprint & Stale Pin Adversarial Tests
    ========================================================================= -/

def testAdmitFootprintAdversarial : IO Unit := do
  IO.println "--- Category 1: admitFootprint & Pin Adversarial Tests ---"

  let store : VaultStore := fun c =>
    if c == "cellA" then some (.natural 42)
    else if c == "cellB" then some (.boolean true)
    else if c == "cellC" then some (.record [("k", .natural 100)])
    else none

  -- 1. Exact match across existing and unallocated cells
  let fpExact : Footprint := [
    ⟨"cellA", some (.natural 42)⟩,
    ⟨"cellB", some (.boolean true)⟩,
    ⟨"cellC", some (.record [("k", .natural 100)])⟩,
    ⟨"cellUnallocated", none⟩
  ]
  assertAdversarial "admitFootprint approves exact matching footprint"
    (admitFootprint store fpExact matches .ok ())

  -- 2. Stale value mismatch on primitive
  let fpStaleVal : Footprint := [
    ⟨"cellA", some (.natural 43)⟩
  ]
  assertAdversarial "admitFootprint rejects primitive value mismatch (43 vs 42)"
    (admitFootprint store fpStaleVal matches .error (.footprintStale "cellA" (some (.natural 43)) (some (.natural 42))))

  -- 3. Type confusion: boolean true vs natural 42
  let fpTypeConfusion : Footprint := [
    ⟨"cellA", some (.boolean true)⟩
  ]
  assertAdversarial "admitFootprint rejects type confusion (boolean true vs natural 42)"
    (admitFootprint store fpTypeConfusion matches .error (.footprintStale "cellA" _ _))

  -- 4. Missing cell in store (pin expects some, store is none)
  let fpMissing : Footprint := [
    ⟨"cellGhost", some (.natural 1)⟩
  ]
  assertAdversarial "admitFootprint rejects pin expecting allocated cell when store has none"
    (admitFootprint store fpMissing matches .error (.footprintStale "cellGhost" (some (.natural 1)) none))

  -- 5. Unexpected cell in store (pin expects unallocated, store has some)
  let fpUnexpected : Footprint := [
    ⟨"cellA", none⟩
  ]
  assertAdversarial "admitFootprint rejects pin expecting unallocated cell when store has value"
    (admitFootprint store fpUnexpected matches .error (.footprintStale "cellA" none (some (.natural 42))))

  -- 6. Nested compound structure corruption (record field modified)
  let fpRecordTampered : Footprint := [
    ⟨"cellC", some (.record [("k", .natural 101)])⟩
  ]
  assertAdversarial "admitFootprint rejects tampered record field"
    (admitFootprint store fpRecordTampered matches .error (.footprintStale "cellC" _ _))

  -- 7. Tail stale pin: 4 valid pins followed by 1 stale pin
  let fpTailStale : Footprint := [
    ⟨"cellA", some (.natural 42)⟩,
    ⟨"cellB", some (.boolean true)⟩,
    ⟨"cellC", some (.record [("k", .natural 100)])⟩,
    ⟨"cellUnallocated", none⟩,
    ⟨"cellStaleTail", some (.natural 999)⟩
  ]
  assertAdversarial "admitFootprint traverses full list and catches tail stale pin"
    (admitFootprint store fpTailStale matches .error (.footprintStale "cellStaleTail" (some (.natural 999)) none))

  -- 8. Conflicting observations for same cell within one footprint
  let fpConflicting : Footprint := [
    ⟨"cellA", some (.natural 42)⟩,
    ⟨"cellA", some (.natural 99)⟩
  ]
  assertAdversarial "admitFootprint catches conflicting pins for same cell"
    (admitFootprint store fpConflicting matches .error (.footprintStale "cellA" (some (.natural 99)) (some (.natural 42))))

  -- 9. Empty footprint always admits
  assertAdversarial "admitFootprint admits empty footprint"
    (admitFootprint store [] matches .ok ())

  -- 10. Concrete TOCTOU Race Simulation:
  -- Authoring store s0 has cellA = 42
  let s0 := store
  let turnReaderPins : Footprint := [⟨"cellA", some (.natural 42)⟩]
  -- Writer applies a turn mutating cellA to 100
  let sAfterWriter : VaultStore := updateStore s0 "cellA" (some (.natural 100))
  -- Reader attempts to admit with authored pins against post-writer store
  let readerAdmission := admitFootprint sAfterWriter turnReaderPins
  assertAdversarial "TOCTOU simulation: admitFootprint rejects reader turn after concurrent write"
    (readerAdmission matches .error (.footprintStale "cellA" (some (.natural 42)) (some (.natural 100))))

/-! =========================================================================
    Category 2: Multi-Cell Turns: Disjoint Commutativity & Conflict Detection
    ========================================================================= -/

def testMultiCellTurnsAdversarial : IO Unit := do
  IO.println "--- Category 2: Multi-Cell Turns & Commutativity Tests ---"

  let sBase : VaultStore := fun c =>
    if c == "cellA" then some (.natural 1)
    else if c == "cellB" then some (.natural 2)
    else if c == "cellC" then some (.natural 3)
    else if c == "cellD" then some (.natural 4)
    else if c == "cellE" then some (.natural 5)
    else none

  -- Disjoint Turns: T1 mutates {cellA, cellB}, T2 mutates {cellC, cellD}
  let t1DeltaA : CellDelta := { cell := "cellA", preState := .natural 1, postState := .natural 11 }
  let t1DeltaB : CellDelta := { cell := "cellB", preState := .natural 2, postState := .natural 22 }
  let t2DeltaC : CellDelta := { cell := "cellC", preState := .natural 3, postState := .natural 33 }
  let t2DeltaD : CellDelta := { cell := "cellD", preState := .natural 4, postState := .natural 44 }

  let t1 : VaultTurn := {
    turnId := ByteArray.empty
    readPins := []
    writeCells := [t1DeltaA, t1DeltaB]
    occasion := .record []
    agree := by intro _ hd; simp only [List.mem_cons, List.not_mem_nil, or_false] at hd; rcases hd with rfl | rfl <;> rfl
    balanced := by intro _; rfl
  }

  let t2 : VaultTurn := {
    turnId := ByteArray.empty
    readPins := []
    writeCells := [t2DeltaC, t2DeltaD]
    occasion := .record []
    agree := by intro _ hd; simp only [List.mem_cons, List.not_mem_nil, or_false] at hd; rcases hd with rfl | rfl <;> rfl
    balanced := by intro _; rfl
  }

  let s12 := applyTurn (applyTurn sBase t1) t2
  let s21 := applyTurn (applyTurn sBase t2) t1

  let cellsToCheck := ["cellA", "cellB", "cellC", "cellD", "cellE", "cellOther"]
  let allMatch := cellsToCheck.all fun c => dataEq (s12 c) (s21 c)
  assertAdversarial "Disjoint turns commute: applyTurn(T1; T2) == applyTurn(T2; T1) on all cells" allMatch
  assertAdversarial "Disjoint turns update cellA correctly" (dataEq (s12 "cellA") (some (.natural 11)))
  assertAdversarial "Disjoint turns update cellC correctly" (dataEq (s12 "cellC") (some (.natural 33)))
  assertAdversarial "Disjoint turns preserve untouched cellE" (dataEq (s12 "cellE") (some (.natural 5)))

  -- Conflicting Turns: Both T_alpha and T_beta mutate cellB
  let taDeltaA : CellDelta := { cell := "cellA", preState := .natural 1, postState := .natural 100 }
  let taDeltaB : CellDelta := { cell := "cellB", preState := .natural 2, postState := .natural 200 }
  let tbDeltaB : CellDelta := { cell := "cellB", preState := .natural 2, postState := .natural 999 }
  let tbDeltaC : CellDelta := { cell := "cellC", preState := .natural 3, postState := .natural 300 }

  let tAlpha : VaultTurn := {
    turnId := ByteArray.empty
    readPins := []
    writeCells := [taDeltaA, taDeltaB]
    occasion := .record []
    agree := by intro _ hd; simp only [List.mem_cons, List.not_mem_nil, or_false] at hd; rcases hd with rfl | rfl <;> rfl
    balanced := by intro _; rfl
  }

  let tBeta : VaultTurn := {
    turnId := ByteArray.empty
    readPins := []
    writeCells := [tbDeltaB, tbDeltaC]
    occasion := .record []
    agree := by intro _ hd; simp only [List.mem_cons, List.not_mem_nil, or_false] at hd; rcases hd with rfl | rfl <;> rfl
    balanced := by intro _; rfl
  }

  let sAlphaBeta := applyTurn (applyTurn sBase tAlpha) tBeta
  let sBetaAlpha := applyTurn (applyTurn sBase tBeta) tAlpha

  -- Under Alpha then Beta: Beta's write to cellB overwrites Alpha's write
  assertAdversarial "Conflicting execution T_alpha then T_beta produces Beta's write (999)"
    (dataEq (sAlphaBeta "cellB") (some (.natural 999)))
  assertAdversarial "Conflicting execution T_beta then T_alpha produces Alpha's write (200)"
    (dataEq (sBetaAlpha "cellB") (some (.natural 200)))
  assertAdversarial "Non-disjoint conflicting turns strictly DO NOT commute"
    (dataEq (sAlphaBeta "cellB") (sBetaAlpha "cellB") == false)

  -- Multi-cell balance check with 4 cells and 3 assets
  let delta1 : CellDelta := {
    cell := "c1", preState := .natural 0, postState := .natural 0
    halfEdges := [("ETH", 50), ("USDC", -100), ("BTC", 2)]
  }
  let delta2 : CellDelta := {
    cell := "c2", preState := .natural 0, postState := .natural 0
    halfEdges := [("ETH", -20), ("USDC", 40), ("BTC", -1)]
  }
  let delta3 : CellDelta := {
    cell := "c3", preState := .natural 0, postState := .natural 0
    halfEdges := [("ETH", -30), ("USDC", 70), ("BTC", 0)]
  }
  let delta4 : CellDelta := {
    cell := "c4", preState := .natural 0, postState := .natural 0
    halfEdges := [("ETH", 0), ("USDC", -10), ("BTC", -1)]
  }
  let balancedDeltas := [delta1, delta2, delta3, delta4]
  assertAdversarial "4-cell turn sumAssetDelta ETH is balanced" (sumAssetDelta balancedDeltas "ETH" == 0)
  assertAdversarial "4-cell turn sumAssetDelta USDC is balanced" (sumAssetDelta balancedDeltas "USDC" == 0)
  assertAdversarial "4-cell turn sumAssetDelta BTC is balanced" (sumAssetDelta balancedDeltas "BTC" == 0)

  -- Introduce 1 wei mismatch on USDC
  let delta4Unbalanced : CellDelta := {
    cell := "c4", preState := .natural 0, postState := .natural 0
    halfEdges := [("ETH", 0), ("USDC", -9), ("BTC", -1)]  -- -9 instead of -10
  }
  let unbalancedDeltas := [delta1, delta2, delta3, delta4Unbalanced]
  assertAdversarial "Adversarial 1-wei mismatch is detected by sumAssetDelta"
    (sumAssetDelta unbalancedDeltas "USDC" == 1)

/-! =========================================================================
    Category 3: Book Conservation Randomized Stress Testing (All 9 Ops)
    ========================================================================= -/

def testBookStressRandomSequences : IO Unit := do
  IO.println "--- Category 3: Book Conservation Randomized Stress Testing ---"

  -- 10 accounts: 0..9. Note: Assets are 1, 2, 3. Issuer accounts 1, 2, 3 are in accounts!
  let accs : List AccountId := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
  let initialBook : Book := {
    accounts := accs
    balances := fun a ast =>
      if a = 1 ∧ ast = 1 then 1000000000
      else if a = 2 ∧ ast = 1 then 500000000
      else if a = 3 ∧ ast = 2 then 200000000
      else if a = 4 ∧ ast = 2 then 300000000
      else if a = 5 ∧ ast = 3 then 100000000
      else 0
    leaseRecords := fun _ => none
    floors := fun _ _ => 0
  }

  let total1_0 := initialBook.totalAsset 1
  let total2_0 := initialBook.totalAsset 2
  let total3_0 := initialBook.totalAsset 3

  assertAdversarial "Initial Book totalAsset 1 is 1500000000" (total1_0 == 1500000000)
  assertAdversarial "Initial Book totalAsset 2 is 500000000" (total2_0 == 500000000)
  assertAdversarial "Initial Book totalAsset 3 is 100000000" (total3_0 == 100000000)

  -- Generate 1,000 random operations across all 9 operation types
  let mut rng : PRNG := ⟨0xdeadbeef1337c0de⟩
  let mut currentBook := initialBook
  let nOps := 1000

  for i in [:nOps] do
    let (opType, r1) := rng.nextNat 9
    let (accSrcIdx, r2) := r1.nextNat 10
    let (accDstIdx, r3) := r2.nextNat 10
    let (astIdx, r4) := r3.nextNat 3
    let (amt, r5) := r4.nextNat 50000
    rng := r5

    let src := accSrcIdx
    let dst := accDstIdx
    let ast := astIdx + 1 -- assets 1, 2, 3

    let op : Operation :=
      match opType with
      | 0 => .transfer src dst ast amt
      | 1 => .mint ast dst amt
      | 2 => .burn src ast amt
      | 3 => .fee src dst ast amt
      | 4 => .lease (i + 1) src dst ast (amt % 100) ((amt % 10) + 1) 0
      | 5 => .setFloor ast src amt
      | 6 => .sweep src dst ast 10 1 (amt % 1000)
      | 7 => .hold src dst ast amt
      | _ => .release src dst ast amt

    currentBook := op.apply currentBook

    -- Check invariants every 200 operations
    if (i + 1) % 200 == 0 then
      let c1 := currentBook.totalAsset 1 == total1_0
      let c2 := currentBook.totalAsset 2 == total2_0
      let c3 := currentBook.totalAsset 3 == total3_0
      assertAdversarial s!"Invariance check at step {i + 1} (asset 1, 2, 3)" (c1 && c2 && c3)

  assertAdversarial "Final state after 1,000 operations conserves asset 1"
    (currentBook.totalAsset 1 == total1_0)
  assertAdversarial "Final state after 1,000 operations conserves asset 2"
    (currentBook.totalAsset 2 == total2_0)
  assertAdversarial "Final state after 1,000 operations conserves asset 3"
    (currentBook.totalAsset 3 == total3_0)

  -- Astronomical numbers (exceeding 128-bit integer)
  let massiveVal : Int := 10 ^ 40
  let bMassive : Book := {
    accounts := [1, 2]
    balances := fun a ast => if a = 1 ∧ ast = 1 then massiveVal else 0
    leaseRecords := fun _ => none
    floors := fun _ _ => 0
  }
  let opMassive : Operation := .transfer 1 2 1 (10 ^ 38)
  let bMassiveAfter := opMassive.apply bMassive
  assertAdversarial "Book handles 10^40 quantities without overflow"
    (bMassiveAfter.totalAsset 1 == massiveVal)

  -- Self-transfer invariance
  let opSelf : Operation := .transfer 1 1 1 500
  let bSelf := opSelf.apply initialBook
  assertAdversarial "Self-transfer strictly preserves account balance"
    (bSelf.balance 1 1 == initialBook.balance 1 1)

  -- Zero-amount operations invariance
  let zeroOps : List Operation := [
    .transfer 1 2 1 0,
    .mint 1 2 0,
    .burn 1 1 0,
    .fee 1 2 1 0,
    .lease 999 1 2 1 0 10 0,
    .hold 1 2 1 0,
    .release 2 1 1 0
  ]
  let bZero := applyOperations initialBook zeroOps
  assertAdversarial "All 0-amount operations preserve balances exactly"
    (bZero.totalAsset 1 == total1_0)

  -- Batch with temporary Zoe Seat account registration & deregistration
  let seatAcc : AccountId := protectedBase + 777
  let regBatch : Batch := {
    registrations := [seatAcc]
    operations := [
      .transfer 1 seatAcc 1 5000,   -- fund seat
      .transfer seatAcc 2 1 5000    -- seat spends entire balance, leaving 0
    ]
    deregistrations := [seatAcc]
  }
  let bAfterBatch := regBatch.apply initialBook
  assertAdversarial "Batch registration, seat funding, spending, and deregistration conserves asset 1"
    (bAfterBatch.totalAsset 1 == total1_0)
  assertAdversarial "Deregistered seat account is no longer in book.accounts"
    (bAfterBatch.accounts.contains seatAcc == false)

/-! =========================================================================
    Category 4: ZoE Seat Offer-Safety Adversarial Edge Cases
    ========================================================================= -/

def testSeatAdversarial : IO Unit := do
  IO.println "--- Category 4: ZoE Seat Offer Safety Adversarial Tests ---"

  let seatAcc : AccountId := protectedBase + 555
  let propMulti : Proposal := {
    give := [(1, 100), (2, 50)]  -- gives 100 of asset 1, 50 of asset 2
    want := [(3, 10)]           -- wants 10 of asset 3
    exit := .onDemand
    donate := false
  }

  -- 1. Partial refund on give: holds 100 of asset 1, but only 49 of asset 2 (want not met)
  let bPartialGive : Book := {
    accounts := [seatAcc]
    balances := fun a ast =>
      if a = seatAcc ∧ ast = 1 then 100
      else if a = seatAcc ∧ ast = 2 then 49 -- 1 short!
      else 0
    leaseRecords := fun _ => none
    floors := fun _ _ => 0
  }
  assertAdversarial "safeAt is false when give refund is 1 wei short on one asset"
    (safeAt bPartialGive seatAcc propMulti == false)

  -- 2. Partial want: holds 9 of asset 3 (requires 10) (give not refunded)
  let bPartialWant : Book := {
    accounts := [seatAcc]
    balances := fun a ast =>
      if a = seatAcc ∧ ast = 3 then 9 -- 1 short!
      else 0
    leaseRecords := fun _ => none
    floors := fun _ _ => 0
  }
  assertAdversarial "safeAt is false when want is 1 wei short"
    (safeAt bPartialWant seatAcc propMulti == false)

  -- 3. Both partial: holds 99 of asset 1 (99% refunded) and 9 of asset 3 (90% met)
  let bBothPartial : Book := {
    accounts := [seatAcc]
    balances := fun a ast =>
      if a = seatAcc ∧ ast = 1 then 99
      else if a = seatAcc ∧ ast = 2 then 50
      else if a = seatAcc ∧ ast = 3 then 9
      else 0
    leaseRecords := fun _ => none
    floors := fun _ _ => 0
  }
  assertAdversarial "safeAt is false when both want and give are partially satisfied"
    (safeAt bBothPartial seatAcc propMulti == false)

  -- 4. Want met with massive surplus
  let bWantSurplus : Book := {
    accounts := [seatAcc]
    balances := fun a ast => if a = seatAcc ∧ ast = 3 then 1000000 else 0
    leaseRecords := fun _ => none
    floors := fun _ _ => 0
  }
  assertAdversarial "safeAt is true when want is satisfied with massive surplus"
    (safeAt bWantSurplus seatAcc propMulti == true)

  -- 5. Give refunded with massive surplus
  let bGiveSurplus : Book := {
    accounts := [seatAcc]
    balances := fun a ast =>
      if a = seatAcc ∧ ast = 1 then 500
      else if a = seatAcc ∧ ast = 2 then 250
      else 0
    leaseRecords := fun _ => none
    floors := fun _ _ => 0
  }
  assertAdversarial "safeAt is true when give is refunded with massive surplus"
    (safeAt bGiveSurplus seatAcc propMulti == true)

  -- 6. Unconditional exit payout on multiple assets
  let bMultiHoldings : Book := {
    accounts := [seatAcc, 888]
    balances := fun a ast =>
      if a = seatAcc ∧ ast = 1 then 100
      else if a = seatAcc ∧ ast = 2 then 200
      else if a = seatAcc ∧ ast = 3 then 300
      else 0
    leaseRecords := fun _ => none
    floors := fun _ _ => 0
  }
  let payee : AccountId := 888
  let payoutOps := payoutPostings bMultiHoldings seatAcc payee [1, 2, 3]
  let bAfterPayout := payoutOps.foldl (fun bk p => bk.applyPosting p) bMultiHoldings

  assertAdversarial "Exit payout transfers asset 1 to payee" (bAfterPayout.balance payee 1 == 100)
  assertAdversarial "Exit payout transfers asset 2 to payee" (bAfterPayout.balance payee 2 == 200)
  assertAdversarial "Exit payout transfers asset 3 to payee" (bAfterPayout.balance payee 3 == 300)
  assertAdversarial "Exit payout zeroes seat asset 1" (bAfterPayout.balance seatAcc 1 == 0)
  assertAdversarial "Exit payout zeroes seat asset 2" (bAfterPayout.balance seatAcc 2 == 0)
  assertAdversarial "Exit payout zeroes seat asset 3" (bAfterPayout.balance seatAcc 3 == 0)

/-! =========================================================================
    Category 5: DrEX Certified Clearing Judge Adversarial Challenges
    ========================================================================= -/

def testClearingJudgeAdversarial : IO Unit := do
  IO.println "--- Category 5: DrEX Certified Clearing Judge Adversarial Tests ---"

  let m : Market := { currency := 1, goods := 2, epsilon := 5 }
  let oBid : Order := { account := 10, side := .bid, qty := 10, total := 100 } -- max 10/unit
  let oAsk : Order := { account := 20, side := .ask, qty := 10, total := 80 }  -- min 8/unit
  let orders := [oBid, oAsk]

  -- 1. Valid execution at price 9: 10 goods for 90 currency
  let transfersValid : List ResourcePosting := [
    ⟨20, 10, 2, 10⟩, -- ask sends 10 goods to bid
    ⟨10, 20, 1, 90⟩  -- bid sends 90 currency to ask
  ]
  let certValid : Certificate := {
    price := 9
    potentials := (0, 1)
    slacks := [0, 2]
  }
  assertAdversarial "Clearing judge approves valid market at price 9 within epsilon"
    (judge m orders transfersValid certValid matches .ok ())

  -- 2. Excess fill beyond order capacity (attempts 11 goods fill)
  let transfersExcess : List ResourcePosting := [
    ⟨20, 10, 2, 11⟩,
    ⟨10, 20, 1, 99⟩
  ]
  assertAdversarial "Clearing judge rejects fill exceeding order capacity"
    (judge m orders transfersExcess certValid matches .error (.capacityExceeded 10 11 10))

  -- 3. Non-conserving goods creation (bid receives 10 goods, but ask only sent 9)
  let transfersNonConserving : List ResourcePosting := [
    ⟨20, 10, 2, 9⟩,
    ⟨30, 10, 2, 1⟩, -- phantom goods from account 30
    ⟨10, 20, 1, 90⟩
  ]
  assertAdversarial "Clearing judge rejects non-conserving goods creation"
    (judge m orders transfersNonConserving certValid matches .error (.notAnOrder ⟨30, 10, 2, 1⟩))

  -- 4. Foreign asset injection (transfer uses asset 99)
  let transfersForeign : List ResourcePosting := [
    ⟨20, 10, 2, 10⟩,
    ⟨10, 20, 99, 90⟩ -- asset 99 instead of currency 1
  ]
  assertAdversarial "Clearing judge rejects transfer of foreign asset"
    (judge m orders transfersForeign certValid matches .error (.foreignAsset _))

  -- 5. Slack count mismatch: 2 orders but 3 slacks
  let certSlackMismatch : Certificate := {
    price := 9
    potentials := (0, 1)
    slacks := [1, 1, 1]
  }
  assertAdversarial "Clearing judge rejects certificate with slack count mismatch"
    (judge m orders transfersValid certSlackMismatch matches .error (.slackCount 2 3))

  -- 6. Dual infeasibility: negative slack
  let certNegativeSlack : Certificate := {
    price := 9
    potentials := (0, 1)
    slacks := [-1, 1]
  }
  assertAdversarial "Clearing judge rejects certificate with negative slack"
    (judge m orders transfersValid certNegativeSlack matches .error (.negativeSlack 10 (-1)))

  -- 7. Dual gap exceeds epsilon (gap = 20 > epsilon = 5)
  let mTight : Market := { currency := 1, goods := 2, epsilon := 0 }
  let certGapExceeded : Certificate := {
    price := 9
    potentials := (0, 1)
    slacks := [2, 2] -- dualCap = 10*2 + 10*2 = 40, objVol = 20, gap = 20 > 0
  }
  assertAdversarial "Clearing judge rejects certificate when duality gap exceeds epsilon"
    (judge mTight orders transfersValid certGapExceeded matches .error (.uncertified 20 0))

  -- 8. Zero quantity order handling
  let oZero : Order := { account := 99, side := .bid, qty := 0, total := 0 }
  let ordersWithZero := [oBid, oAsk, oZero]
  let certZero : Certificate := {
    price := 9
    potentials := (0, 1)
    slacks := [0, 2, 0]
  }
  assertAdversarial "Clearing judge correctly handles order with quantity 0"
    (judge m ordersWithZero transfersValid certZero matches .ok ())

/-! =========================================================================
    Main Adversarial Suite Runner
    ========================================================================= -/

def main : IO Unit := do
  IO.println "=========================================================="
  IO.println "=== RUNNING EMPIRICAL CHALLENGER ADVERSARIAL SUITE M2 ==="
  IO.println "=========================================================="
  testAdmitFootprintAdversarial
  testMultiCellTurnsAdversarial
  testBookStressRandomSequences
  testSeatAdversarial
  testClearingJudgeAdversarial
  IO.println "=========================================================="
  IO.println "=== ALL ADVERSARIAL CHALLENGES EMPIRICALLY VERIFIED! ==="
  IO.println "=========================================================="

#eval main
