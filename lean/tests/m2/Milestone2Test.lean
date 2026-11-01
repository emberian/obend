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

def assertOk (what : String) (ok : Bool) : IO Unit :=
  if ok then
    IO.println s!"[PASS] {what}"
  else
    throw (IO.userError s!"[FAIL] {what}")

def dataEq (o1 o2 : Option Data) : Bool :=
  match o1, o2 with
  | none, none => true
  | some d1, some d2 => Obend.Law.termEq d1.term d2.term
  | _, _ => false

/-! =========================================================================
    Feature 16, 17, 18: VaultTurn & Wide-Pullback Turn Tests
    ========================================================================= -/

-- 1. Check abstract categorical wide-pullback theorems
theorem test_hyperedge_legs_agree
    {ι Carrier Turn TurnId Bal : Type} [DecidableEq TurnId] [Zero Bal] [Add Bal]
    {step : Carrier → Turn → Carrier} {turnId : ι → Carrier → TurnId} {halfEdge : ι → Carrier → Turn → Bal}
    {incidences : List ι}
    (H : Hyperedge ι Carrier Turn TurnId Bal step turnId halfEdge incidences) (i j : ι) :
    turnId i (step (H.x i) H.t) = turnId j (step (H.x j) H.t) :=
  Hyperedge.legs_agree H i j

theorem test_hyperedge_binary_balanced
    {ι Carrier Turn TurnId Bal : Type} [DecidableEq TurnId] [Zero Bal] [Add Bal]
    {step : Carrier → Turn → Carrier} {turnId : ι → Carrier → TurnId} {halfEdge : ι → Carrier → Turn → Bal}
    {i₁ i₂ : ι}
    (H : Hyperedge ι Carrier Turn TurnId Bal step turnId halfEdge [i₁, i₂])
    (h_zero : ∀ (b : Bal), (0 : Bal) + b = b) :
    halfEdge i₁ (H.x i₁) H.t + halfEdge i₂ (H.x i₂) H.t = 0 :=
  Hyperedge.binary_balanced H h_zero

theorem test_hyperedge_binding_is_proper :
    ∃ (x : Unit → Int) (t : Int) (tid : Int)
      (step : Int → Int → Int) (turnId : Unit → Int → Int) (halfEdge : Unit → Int → Int → Int)
      (incidences : List Unit),
      (∀ (i : Unit), turnId i (step (x i) t) = tid) ∧
      (incidences.map (fun i => halfEdge i (x i) t)).foldl (· + ·) 0 ≠ 0 :=
  Hyperedge.binding_is_proper

-- 2. Check VaultTurn theorems
theorem test_vaultTurn_legs_agree (turn : VaultTurn) {d₁ d₂ : CellDelta}
    (h₁ : d₁ ∈ turn.writeCells) (h₂ : d₂ ∈ turn.writeCells) :
    legTurnId d₁ = legTurnId d₂ :=
  VaultTurn.legs_agree turn h₁ h₂

theorem test_vaultTurn_disjoint_commutes (s : VaultStore) (T₁ T₂ : VaultTurn)
    (h_disj : DisjointTurns T₁ T₂) :
    applyTurn (applyTurn s T₁) T₂ = applyTurn (applyTurn s T₂) T₁ :=
  vaultTurn_disjoint_commutes s T₁ T₂ h_disj

-- 3. Executable footprint admission and turn application tests
def testVaultTurnFootprint : IO Unit := do
  let s : VaultStore := fun c =>
    if c == "cellAlpha" then some (.natural 42)
    else if c == "cellBeta" then some (.natural 99)
    else none

  let fpGood : Footprint := [
    ⟨"cellAlpha", some (.natural 42), none⟩,
    ⟨"cellBeta", some (.natural 99), none⟩
  ]
  let admitGood := admitFootprint s fpGood
  assertOk "Footprint admission passes on matching store" (admitGood matches .ok ())

  let fpStale : Footprint := [
    ⟨"cellAlpha", some (.natural 42), none⟩,
    ⟨"cellBeta", some (.natural 100), none⟩
  ]
  let admitStale := admitFootprint s fpStale
  assertOk "Footprint admission catches stale pin" (admitStale matches .error (.footprintStale "cellBeta" _ _))

  -- Conservation of asset deltas
  let d1 : CellDelta := {
    cell := "cellAlpha"
    preState := .natural 42
    postState := .natural 52
    halfEdges := [("ETH", 10), ("USDC", -20)]
  }
  let d2 : CellDelta := {
    cell := "cellBeta"
    preState := .natural 99
    postState := .natural 89
    halfEdges := [("ETH", -10), ("USDC", 20)]
  }
  let cells := [d1, d2]
  assertOk "sumAssetDelta ETH is balanced" (sumAssetDelta cells "ETH" == 0)
  assertOk "sumAssetDelta USDC is balanced" (sumAssetDelta cells "USDC" == 0)
  assertOk "sumAssetDelta unmentioned asset is balanced" (sumAssetDelta cells "BTC" == 0)

  -- Turn application updates postState
  let turnDelta1 : CellDelta := {
    cell := "cellAlpha"
    preState := .natural 42
    postState := .natural 52
  }
  let turnDelta2 : CellDelta := {
    cell := "cellBeta"
    preState := .natural 99
    postState := .natural 89
  }
  let turnCells := [turnDelta1, turnDelta2]
  let dummyTurn : VaultTurn := {
    turnId := ByteArray.empty
    readPins := fpGood
    writeCells := turnCells
    occasion := .record []
    agree := by
      intro d hd
      simp only [turnCells, turnDelta1, turnDelta2, List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl <;> rfl
    balanced := by
      intro _
      rfl
  }
  let sAfter := applyTurn s dummyTurn
  assertOk "applyTurn writes postState for cellAlpha" (dataEq (sAfter "cellAlpha") (some (.natural 52)))
  assertOk "applyTurn writes postState for cellBeta" (dataEq (sAfter "cellBeta") (some (.natural 89)))
  assertOk "applyTurn preserves unwritten cells" (dataEq (sAfter "cellGamma") none)

/-! =========================================================================
    Feature 19: Book Multi-Asset Ledger & 9 Operations Conservation
    ========================================================================= -/

def testBookConservation : IO Unit := do
  -- Initial Book with 5 accounts and 2 assets (asset 1 = currency, asset 2 = goods)
  let b0 : Book := {
    accounts := [0, 1, 2, 3, 4]
    balances := fun a ast =>
      if a = 1 ∧ ast = 1 then 100
      else if a = 2 ∧ ast = 1 then 50
      else if a = 3 ∧ ast = 1 then 20
      else if a = 4 ∧ ast = 1 then 10
      else if a = 1 ∧ ast = 2 then 5
      else if a = 2 ∧ ast = 2 then 15
      else 0
    leaseRecords := fun _ => none
    floors := fun _ _ => 0
  }
  let initialTotal1 := b0.totalAsset 1
  let initialTotal2 := b0.totalAsset 2
  assertOk "Initial totalAsset 1 is 180" (initialTotal1 == 180)
  assertOk "Initial totalAsset 2 is 20" (initialTotal2 == 20)

  -- Op 1: transfer 30 of asset 1 from acc 1 to acc 2
  let opTransfer : Operation := .transfer 1 2 1 30
  let b1 := opTransfer.apply b0
  assertOk "transfer conserves asset 1" (b1.totalAsset 1 == initialTotal1)
  assertOk "transfer conserves asset 2" (b1.totalAsset 2 == initialTotal2)

  -- Op 2: mint 40 of asset 1 to acc 1 (mint asset dest amount)
  let opMint : Operation := .mint 1 1 40
  let b2 := opMint.apply b1
  assertOk "mint conserves asset 1" (b2.totalAsset 1 == initialTotal1)

  -- Op 3: burn 15 of asset 1 from acc 1 (burn src asset amount)
  let opBurn : Operation := .burn 1 1 15
  let b3 := opBurn.apply b2
  assertOk "burn conserves asset 1" (b3.totalAsset 1 == initialTotal1)

  -- Op 4: fee 5 of asset 1 from acc 2 to fee collector 3
  let opFee : Operation := .fee 2 3 1 5
  let b4 := opFee.apply b3
  assertOk "fee conserves asset 1" (b4.totalAsset 1 == initialTotal1)

  -- Op 5: lease 1 prepays rate 2 * 5 epochs = 10 from acc 2 to lessor 4
  let opLease : Operation := .lease 1 2 4 1 2 5 0
  let b5 := opLease.apply b4
  assertOk "lease conserves asset 1" (b5.totalAsset 1 == initialTotal1)
  assertOk "lease installs lease record" (b5.leases 1 matches some ⟨2, 4, 1, 10, 0, 5⟩)

  -- Op 6: setFloor installs credit floor 25 on acc 1 for asset 1 (setFloor asset acc floor)
  let opFloor : Operation := .setFloor 1 1 25
  let b6 := opFloor.apply b5
  assertOk "setFloor conserves asset 1" (b6.totalAsset 1 == initialTotal1)
  assertOk "setFloor installs credit floor" (b6.floor 1 1 == 25)

  -- Op 7: sweep 0 of asset 1 from acc 2 to issuer well 0
  let opSweep : Operation := .sweep 2 0 1 100 1 0
  let b7 := opSweep.apply b6
  assertOk "sweep conserves asset 1" (b7.totalAsset 1 == initialTotal1)

  -- Op 8: hold 10 of asset 1 from acc 1 in escrow 3
  let opHold : Operation := .hold 1 3 1 10
  let b8 := opHold.apply b7
  assertOk "hold conserves asset 1" (b8.totalAsset 1 == initialTotal1)

  -- Op 9: release 10 of asset 1 from escrow 3 to acc 4
  let opRelease : Operation := .release 3 4 1 10
  let b9 := opRelease.apply b8
  assertOk "release conserves asset 1" (b9.totalAsset 1 == initialTotal1)

  -- Batch execution of all 9 operations
  let allOps := [opTransfer, opMint, opBurn, opFee, opLease, opFloor, opSweep, opHold, opRelease]
  let bBatch := applyOperations b0 allOps
  assertOk "Batch execution of all 9 operations conserves asset 1" (bBatch.totalAsset 1 == initialTotal1)
  assertOk "Batch execution of all 9 operations conserves asset 2" (bBatch.totalAsset 2 == initialTotal2)

/-! =========================================================================
    Feature 20: ZoE Seat Offer-Safety & Protected Coordinates
    ========================================================================= -/

def testSeatOfferSafety : IO Unit := do
  let seatAcc : AccountId := protectedBase + 100
  assertOk "Seat account is in protected space >= 2^256" (protectedBase ≤ seatAcc)

  let prop : Proposal := {
    give := [(1, 10)]  -- gives 10 of asset 1
    want := [(2, 2)]   -- wants 2 of asset 2
    exit := .onDemand
    donate := false
  }

  -- State 1: Want met (holds 0 asset 1, 2 asset 2)
  let bMet : Book := {
    accounts := [seatAcc]
    balances := fun a ast => if a = seatAcc ∧ ast = 2 then 2 else 0
    leaseRecords := fun _ => none
    floors := fun _ _ => 0
  }
  assertOk "safeAt is true when want is met" (safeAt bMet seatAcc prop == true)

  -- State 2: Give refunded (holds 10 asset 1, 0 asset 2)
  let bRefunded : Book := {
    accounts := [seatAcc]
    balances := fun a ast => if a = seatAcc ∧ ast = 1 then 10 else 0
    leaseRecords := fun _ => none
    floors := fun _ _ => 0
  }
  assertOk "safeAt is true when give is refunded" (safeAt bRefunded seatAcc prop == true)

  -- State 3: Unmet state (holds 5 asset 1, 1 asset 2 - neither met nor refunded)
  let bUnmet : Book := {
    accounts := [seatAcc]
    balances := fun a ast =>
      if a = seatAcc ∧ ast = 1 then 5
      else if a = seatAcc ∧ ast = 2 then 1
      else 0
    leaseRecords := fun _ => none
    floors := fun _ _ => 0
  }
  assertOk "safeAt is false when neither want nor give is satisfied" (safeAt bUnmet seatAcc prop == false)

  -- State 4: Monotonicity safeAt_mono
  let bMetHigher : Book := {
    accounts := [seatAcc]
    balances := fun a ast => if a = seatAcc ∧ ast = 2 then 5 else 0
    leaseRecords := fun _ => none
    floors := fun _ _ => 0
  }
  assertOk "Credited balance preserves offer safety" (safeAt bMetHigher seatAcc prop == true)

  -- State 5: Exit pays allocation
  let payeeAcc : AccountId := 999
  let bExit := bRefunded.applyPosting ⟨seatAcc, payeeAcc, 1, 10⟩
  assertOk "Exit payout moves seat balance to payee" (bExit.balance payeeAcc 1 == 10)
  assertOk "Exit payout zeroes seat balance" (bExit.balance seatAcc 1 == 0)

/-! =========================================================================
    Feature 21: DrEX Certified Primal-Dual LP Clearing Judge
    ========================================================================= -/

def testClearingJudge : IO Unit := do
  let market : Market := { currency := 1, goods := 2, epsilon := 0 }

  -- 4-order market clearing at uniform price 4
  -- Alice (acc 1) bids 2 goods for max 10 currency (5/unit) -> crosses
  let o1 : Order := { account := 1, side := .bid, qty := 2, total := 10 }
  -- Bob (acc 2) bids 3 goods for max 12 currency (4/unit) -> crosses
  let o2 : Order := { account := 2, side := .bid, qty := 3, total := 12 }
  -- Carol (acc 3) asks 2 goods for min 6 currency (3/unit) -> crosses
  let o3 : Order := { account := 3, side := .ask, qty := 2, total := 6 }
  -- Dave (acc 4) asks 3 goods for min 12 currency (4/unit) -> crosses
  let o4 : Order := { account := 4, side := .ask, qty := 3, total := 12 }
  let orders := [o1, o2, o3, o4]

  -- Transfers executing 5 goods for 20 currency at price 4:
  -- Carol -> Alice: 2 goods; Alice -> Carol: 8 currency
  -- Dave -> Bob: 3 goods; Bob -> Dave: 12 currency
  let transfers : List ResourcePosting := [
    ⟨3, 1, 2, 2⟩,   -- Carol sends 2 goods to Alice
    ⟨1, 3, 1, 8⟩,   -- Alice sends 8 currency to Carol
    ⟨4, 2, 2, 3⟩,   -- Dave sends 3 goods to Bob
    ⟨2, 4, 1, 12⟩   -- Bob sends 12 currency to Dave
  ]

  -- Certificate at price 4: potentials (0, 1), slacks [0, 0, 2, 2]
  let certValid : Certificate := {
    price := 4
    potentials := (0, 1)
    slacks := [0, 0, 2, 2]
  }

  let verdictValid := judge market orders transfers certValid
  assertOk "Clearing judge approves optimal certificate at ε=0" (verdictValid matches .ok ())

  -- Test Judge instance
  let query : ClearingQuery := { market := market, orders := orders, transfers := transfers }
  let judgeCheck := drexClearingJudge.check 0 query certValid
  assertOk "drexClearingJudge instance check returns .ok" (judgeCheck matches .ok)

  -- Negative test: Suboptimal / zero fill with price 4 yields uncertified duality gap 10 > 0
  let certSuboptimal : Certificate := {
    price := 4
    potentials := (0, 1)
    slacks := [0, 0, 2, 2]
  }
  let verdictSuboptimal := judge market orders [] certSuboptimal
  assertOk "Clearing judge rejects suboptimal fill with uncertified gap"
    (verdictSuboptimal matches .error (.uncertified 10 0))

  -- Negative test: Malformed market (currency == goods)
  let badMarket : Market := { currency := 1, goods := 1, epsilon := 0 }
  let verdictMalformed := judge badMarket orders transfers certValid
  assertOk "Clearing judge rejects malformed market with same currency/goods"
    (verdictMalformed matches .error .marketMalformed)

  -- Negative test: Non-uniform price
  let badTransfers : List ResourcePosting := [
    ⟨3, 1, 2, 2⟩,
    ⟨1, 3, 1, 7⟩,   -- Alice pays 7 instead of 8
    ⟨4, 2, 2, 3⟩,
    ⟨2, 4, 1, 12⟩
  ]
  let verdictNonUniform := judge market orders badTransfers certValid
  assertOk "Clearing judge catches non-uniform execution price"
    (verdictNonUniform matches .error (.notUniform 1))

/-! =========================================================================
    Main Runner
    ========================================================================= -/

def main : IO Unit := do
  IO.println "=== Running Milestone 2 Verification Suite ==="
  testVaultTurnFootprint
  testBookConservation
  testSeatOfferSafety
  testClearingJudge
  IO.println "=== All Milestone 2 Verification Tests Passed! ==="

#eval main

#print axioms test_hyperedge_legs_agree
#print axioms test_hyperedge_binary_balanced
#print axioms test_hyperedge_binding_is_proper
#print axioms test_vaultTurn_legs_agree
#print axioms test_vaultTurn_disjoint_commutes
