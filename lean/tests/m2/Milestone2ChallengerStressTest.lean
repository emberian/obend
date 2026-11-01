import Obend.Ledger.Book
import Obend.Ledger.Seat
import Obend.Judge.Clearing
import Obend.Judge.Class
import Obend.Vault.Hyperedge
import Obend.Law.Contract
import Obend.Core.Data
import Obend.Core.Term

open Obend.Vault
open Obend.Ledger
open Obend.Judge
open Obend.Law
open Obend.Core.Data

set_option linter.unusedVariables false

def assertPass (what : String) (ok : Bool) : IO Unit :=
  if ok then
    IO.println s!"[PASS] {what}"
  else
    throw (IO.userError s!"[FAIL] ADVERSARIAL STRESS TEST FAILED: {what}")

/-! =========================================================================
    Challenger Suite 1: DrEX Crossing Interval & Zero-Volume Bypasses
    ========================================================================= -/

def testCrossingIntervalAndZeroVolumeAttacks : IO Unit := do
  IO.println "=== Challenger Suite 1: DrEX Crossing Interval & Zero-Volume Attacks ==="

  let market : Market := { currency := 1, goods := 2, epsilon := 0 }

  -- Setup an order book with spread [6, 10]:
  -- Highest bid: buyer bids 10 goods for total 100 currency (limit price 10)
  let oBidHigh : Order := { account := 101, side := .bid, qty := 10, total := 100 }
  -- Lowest ask: seller asks 10 goods for total 60 currency (limit price 6)
  let oAskLow : Order := { account := 102, side := .ask, qty := 10, total := 60 }
  let stdOrders := [oBidHigh, oAskLow]

  -- 1. Verify crossing detection
  assertPass "hasCrossingPair correctly detects crossing pair [6, 10]"
    (hasCrossingPair stdOrders == true)

  -- 2. Attack: Propose price below crossing interval (price = 5 < lowest ask 6)
  assertPass "priceInCrossingInterval rejects price 5 below lowest ask 6"
    (priceInCrossingInterval stdOrders 5 == false)
  let certLow : Certificate := { price := 5, potentials := (0, 1), slacks := [0, 2] }
  assertPass "Judge rejects clearing price 5 with invalidPrice 5"
    (judge market stdOrders [] certLow matches .error (.invalidPrice 5))

  -- 3. Attack: Propose price above crossing interval (price = 11 > highest bid 10)
  assertPass "priceInCrossingInterval rejects price 11 above highest bid 10"
    (priceInCrossingInterval stdOrders 11 == false)
  let certHigh : Certificate := { price := 11, potentials := (0, 1), slacks := [0, 2] }
  assertPass "Judge rejects clearing price 11 with invalidPrice 11"
    (judge market stdOrders [] certHigh matches .error (.invalidPrice 11))

  -- 4. Attack: Propose zero price when asks are non-free
  assertPass "priceInCrossingInterval rejects price 0 for positive-price ask"
    (priceInCrossingInterval stdOrders 0 == false)
  let certZero : Certificate := { price := 0, potentials := (0, 1), slacks := [0, 2] }
  assertPass "Judge rejects zero price with invalidPrice 0"
    (judge market stdOrders [] certZero matches .error (.invalidPrice 0))

  -- 5. Exact boundaries: price 6 and price 10 must be valid crossing prices
  assertPass "priceInCrossingInterval accepts lower boundary price 6"
    (priceInCrossingInterval stdOrders 6 == true)
  assertPass "priceInCrossingInterval accepts upper boundary price 10"
    (priceInCrossingInterval stdOrders 10 == true)
  assertPass "priceInCrossingInterval accepts interior price 8"
    (priceInCrossingInterval stdOrders 8 == true)

  -- 6. Attack: Force zero-volume trade when bids cross asks under epsilon=0
  -- Duality gap is 20 > 0, so judge rejects with uncertified 20 0
  let certValidPrice8 : Certificate := { price := 8, potentials := (0, 1), slacks := [0, 2] }
  let resZeroEps0 := judge market stdOrders [] certValidPrice8
  IO.println s!"resZeroEps0: {repr resZeroEps0}"
  assertPass "Judge rejects 0-volume trade under ε=0 with uncertified gap"
    (resZeroEps0 matches .error (.uncertified 20 0))

  -- 7. Attack: Force zero-volume trade with large epsilon (1,000,000)
  -- Here gap <= epsilon, BUT objVol == 0 and hasCrossingPair triggers unservedCrossing!
  let looseMarket : Market := { currency := 1, goods := 2, epsilon := 1000000 }
  let resZeroLoose := judge looseMarket stdOrders [] certValidPrice8
  IO.println s!"resZeroLoose: {repr resZeroLoose}"
  assertPass "Judge rejects zero-volume trade even under gigantic epsilon 10^6 with unservedCrossing"
    (resZeroLoose matches .error .unservedCrossing)

  -- 8. Mixed book: non-crossing orders mixed with crossing orders
  -- Out-of-the-money bid: qty 5, total 20 (limit price 4)
  let oBidOTM : Order := { account := 103, side := .bid, qty := 5, total := 20 }
  -- Out-of-the-money ask: qty 5, total 75 (limit price 15)
  let oAskOTM : Order := { account := 104, side := .ask, qty := 5, total := 75 }
  let mixedOrders := [oBidOTM, oBidHigh, oAskLow, oAskOTM]

  assertPass "highestBid? correctly selects in-the-money bid 101 over OTM bid 103"
    (highestBid? mixedOrders == some oBidHigh)
  assertPass "lowestAsk? correctly selects in-the-money ask 102 over OTM ask 104"
    (lowestAsk? mixedOrders == some oAskLow)
  assertPass "priceInCrossingInterval on mixed book rejects price 5"
    (priceInCrossingInterval mixedOrders 5 == false)
  assertPass "priceInCrossingInterval on mixed book rejects price 12"
    (priceInCrossingInterval mixedOrders 12 == false)
  assertPass "priceInCrossingInterval on mixed book accepts price 7"
    (priceInCrossingInterval mixedOrders 7 == true)

  -- 9. Truly non-crossing market: bids do NOT cross asks
  -- Bid: qty 10, total 50 (limit 5). Ask: qty 10, total 80 (limit 8).
  let oBidUncrossed : Order := { account := 201, side := .bid, qty := 10, total := 50 }
  let oAskUncrossed : Order := { account := 202, side := .ask, qty := 10, total := 80 }
  let uncrossedOrders := [oBidUncrossed, oAskUncrossed]

  assertPass "hasCrossingPair correctly detects uncrossed market"
    (hasCrossingPair uncrossedOrders == false)
  assertPass "priceInCrossingInterval trivially true for uncrossed market"
    (priceInCrossingInterval uncrossedOrders 6 == true)

  -- For uncrossed market, zero-trade is optimal:
  -- Potentials: (0, 0) -> Δ = 0.
  -- Orders do not cross price 6:
  -- oBid: 6 * 10 = 60 > 50 (does not cross -> cap = 0)
  -- oAsk: 80 > 6 * 10 = 60 (does not cross -> cap = 0)
  -- dualCap = 0 * 1 + 0 * 1 = 0, objVol = 0, gap = 0.
  let certUncrossedZero : Certificate := { price := 6, potentials := (0, 0), slacks := [1, 1] }
  assertPass "Judge approves genuine 0-volume trade when market has no crossing pair"
    (judge market uncrossedOrders [] certUncrossedZero matches .ok ())

/-! =========================================================================
    Challenger Suite 2: Order Account Stress & Authorization Attacks
    ========================================================================= -/

def testOrderAccountAuthorizationAttacks : IO Unit := do
  IO.println "=== Challenger Suite 2: Order Account Stress & Authorization Attacks ==="

  let market : Market := { currency := 1, goods := 2, epsilon := 0 }
  let oBid : Order := { account := 1, side := .bid, qty := 2, total := 10 }
  let oAsk : Order := { account := 2, side := .ask, qty := 2, total := 10 }
  let stdOrders := [oBid, oAsk]
  let certValid : Certificate := { price := 5, potentials := (0, 1), slacks := [0, 2] }

  -- 1. Attack: Transfer from unauthorized source account (phantom account 9999)
  let badSourceTransfer : List ResourcePosting := [
    ⟨9999, 1, 2, 2⟩,  -- Phantom source 9999 sends goods to Buyer 1
    ⟨1, 2, 1, 10⟩
  ]
  assertPass "Judge rejects unauthorized transfer source with notAnOrder"
    (judge market stdOrders badSourceTransfer certValid matches .error (.notAnOrder ⟨9999, 1, 2, 2⟩))

  -- 2. Attack: Transfer to unauthorized destination account (siphon account 8888)
  let badDestTransfer : List ResourcePosting := [
    ⟨2, 8888, 2, 2⟩,  -- Seller sends goods to third-party siphon 8888 instead of Buyer
    ⟨1, 2, 1, 10⟩
  ]
  assertPass "Judge rejects unauthorized transfer destination with notAnOrder"
    (judge market stdOrders badDestTransfer certValid matches .error (.notAnOrder ⟨2, 8888, 2, 2⟩))

  -- 3. Attack: Transfer between two completely unauthorized accounts
  let badBothTransfer : List ResourcePosting := [
    ⟨8888, 9999, 2, 2⟩,
    ⟨2, 1, 2, 2⟩,
    ⟨1, 2, 1, 10⟩
  ]
  assertPass "Judge rejects wholly unauthorized transfer with notAnOrder"
    (judge market stdOrders badBothTransfer certValid matches .error (.notAnOrder ⟨8888, 9999, 2, 2⟩))

  -- 4. Attack: Reversed payment (seller pays currency to buyer)
  let reversedCurrencyTransfers : List ResourcePosting := [
    ⟨2, 1, 2, 2⟩,   -- Goods from 2 to 1
    ⟨2, 1, 1, 10⟩   -- Currency also from 2 to 1!
  ]
  assertPass "Judge rejects reverse payment direction with notUniform"
    (judge market stdOrders reversedCurrencyTransfers certValid matches .error (.notUniform _))

  -- 5. Attack: Circular currency transfer among orders (1 -> 2 -> 1)
  -- 1 pays 10 to 2, 2 pays 5 back to 1. Net payment of 1 is 5 instead of 10.
  let circularCurrencyTransfers : List ResourcePosting := [
    ⟨2, 1, 2, 2⟩,
    ⟨1, 2, 1, 10⟩,
    ⟨2, 1, 1, 5⟩
  ]
  assertPass "Judge rejects circular payment deficit with notUniform"
    (judge market stdOrders circularCurrencyTransfers certValid matches .error (.notUniform 1))

  -- 6. Circular transfers with zero net flow: 1 -> 2 (10), 2 -> 1 (10)
  -- Alice receives 2 goods, Dave receives 2 goods
  -- In net flow: cancels out.
  let netZeroCircularCurrencyTransfers : List ResourcePosting := [
    ⟨2, 1, 2, 2⟩,
    ⟨1, 2, 1, 10⟩,
    ⟨2, 1, 1, 10⟩,
    ⟨1, 2, 1, 10⟩  -- net 10 currency from 1 to 2
  ]
  assertPass "Judge accepts net-conserving multi-hop circular transfers when net flow matches price exactly"
    (judge market stdOrders netZeroCircularCurrencyTransfers certValid matches .ok ())

  -- 7. Self-transfer within order account: ⟨1, 1, goods, 10⟩
  let selfTransferGoods : List ResourcePosting := [
    ⟨2, 1, 2, 2⟩,
    ⟨1, 2, 1, 10⟩,
    ⟨1, 1, 2, 10⟩  -- buyer transfers goods to self
  ]
  assertPass "Self-transfer does not alter netFlow and is accepted if orders are satisfied"
    (judge market stdOrders selfTransferGoods certValid matches .ok ())

/-! =========================================================================
    Challenger Suite 3: Seat Coordinate Boundaries & Self-Payout Rejection
    ========================================================================= -/

def testSeatCoordinateBoundariesAndSelfPayout : IO Unit := do
  IO.println "=== Challenger Suite 3: Seat Coordinate Boundaries & Self-Payout Rejection ==="

  -- 1. Test coordinate floor boundary
  let floorAcc : AccountId := protectedBase
  let belowFloorAcc : AccountId := protectedBase - 1
  let aboveFloorAcc : AccountId := protectedBase + 1000000

  assertPass "Floor coordinate protectedBase satisfies boundary" (protectedBase ≤ floorAcc)
  assertPass "Below floor coordinate protectedBase - 1 strictly violates boundary"
    (decide (protectedBase ≤ belowFloorAcc) == false)
  assertPass "Above floor coordinate satisfies boundary" (protectedBase ≤ aboveFloorAcc)

  -- 2. Verify ordinary accounts can NEVER collide with seat accounts
  let sValid : Seat := {
    account := protectedBase + 77
    payee := 42
    proposal := { give := [], want := [], exit := .onDemand, donate := false }
  }
  have h_ord0 : (0 : AccountId) < protectedBase := by decide
  have _h_ne0 : (0 : AccountId) ≠ sValid.account := ordinary_ne_seat_account sValid h_ord0
  assertPass "ordinary_ne_seat_account holds for ordinary account 0"
    (0 != sValid.account)

  have h_ordMax : (protectedBase - 1 : AccountId) < protectedBase := by decide
  have _h_neMax : (protectedBase - 1 : AccountId) ≠ sValid.account := ordinary_ne_seat_account sValid h_ordMax
  assertPass "ordinary_ne_seat_account holds for ordinary account 2^256 - 1"
    (protectedBase - 1 != sValid.account)

  -- 3. Self-payout rejection: payee must differ from account
  -- Test what happens to balance if payee == account:
  let bSelf : Book := {
    accounts := [protectedBase + 10]
    balances := fun a ast => if a = protectedBase + 10 ∧ ast = 1 then 100 else 0
    leaseRecords := fun _ => none
    floors := fun _ _ => 0
  }
  let pSelf : ResourcePosting := ⟨protectedBase + 10, protectedBase + 10, 1, 100⟩
  let bSelfAfter := bSelf.applyPosting pSelf
  -- If payee == account, balance is UNCHANGED (100 - 100 + 100 = 100)!
  assertPass "Self-transfer leaves seat balance unchanged at 100 (proving why payee ≠ account is mandatory)"
    (bSelfAfter.balance (protectedBase + 10) 1 == 100)

  -- 4. World unique seat coordinates: nodup_seats
  let s1 : Seat := { account := protectedBase + 1, payee := 1, proposal := { give := [], want := [], exit := .onDemand, donate := false } }
  let s2 : Seat := { account := protectedBase + 2, payee := 2, proposal := { give := [], want := [], exit := .onDemand, donate := false } }
  let w : World := {
    book := { accounts := [], balances := fun _ _ => 0, leaseRecords := fun _ => none, floors := fun _ _ => 0 }
    seats := [s1, s2]
    nodup_seats := by decide
  }
  assertPass "World.seat? finds registered seat s1"
    (w.seat? (protectedBase + 1) == some s1)
  assertPass "World.seat? finds registered seat s2"
    (w.seat? (protectedBase + 2) == some s2)
  assertPass "World.seat? returns none for unregistered seat"
    (w.seat? (protectedBase + 3) == none)

/-! =========================================================================
    Challenger Suite 4: Multi-Asset Exit Precondition & Large Collection Stress
    ========================================================================= -/

def testMultiAssetExitStress : IO Unit := do
  IO.println "=== Challenger Suite 4: Multi-Asset Exit Precondition & Large Collection Stress ==="

  let seatAcc : AccountId := protectedBase + 999
  let payeeAcc : AccountId := 12345

  -- Test across 50 distinct assets:
  let assetCount := 50
  let assets50 : List AssetId := List.range assetCount

  -- Initial balance: asset i has balance (i + 1) * 10
  let initialSeatBalance (ast : AssetId) : Int :=
    if ast < assetCount then ((ast + 1) * 10 : Nat) else 0

  let initialPayeeBalance (ast : AssetId) : Int := 1000

  let b50 : Book := {
    accounts := [seatAcc, payeeAcc]
    balances := fun a ast =>
      if a = seatAcc then initialSeatBalance ast
      else if a = payeeAcc then initialPayeeBalance ast
      else 0
    leaseRecords := fun _ => none
    floors := fun _ _ => 0
  }

  -- Compute payoutPostings for all 50 assets
  let ps50 := payoutPostings b50 seatAcc payeeAcc assets50
  assertPass "payoutPostings generated exactly 50 postings" (ps50.length == 50)

  -- Apply all postings
  let b50After := applyPostings b50 ps50

  -- Empirically verify all 50 assets on the seat are EXACTLY ZERO:
  let mut allSeatZero := true
  for i in [0:assetCount] do
    if b50After.balance seatAcc i ≠ 0 then
      allSeatZero := false
  assertPass "All 50 assets on seat are zeroed post-exit payout" allSeatZero

  -- Empirically verify all 50 assets on payee are EXACTLY initialPayee + initialSeat:
  let mut allPayeeCredited := true
  for i in [0:assetCount] do
    let expected := initialPayeeBalance i + initialSeatBalance i
    if b50After.balance payeeAcc i ≠ expected then
      allPayeeCredited := false
  assertPass "All 50 assets on payee are credited exact amounts post-exit payout" allPayeeCredited

  -- Empirically verify totalAsset conservation across all 50 assets:
  let mut allConserved := true
  for i in [0:assetCount] do
    if b50After.totalAsset i ≠ b50.totalAsset i then
      allConserved := false
  assertPass "Total assets strictly conserved across all 50 assets in book" allConserved

  -- Attack: Duplicate assets in payout list [1, 1]
  -- Demonstrates why h_nodup is required in ExitPrecondition:
  let dupAssets : List AssetId := [1, 1]
  let psDup := payoutPostings b50 seatAcc payeeAcc dupAssets
  let bDupAfter := applyPostings b50 psDup
  -- Seat balance for asset 1 should become negative because it was subtracted twice!
  assertPass "Duplicate assets in payout list cause negative seat balance (-20), proving necessity of Nodup"
    (bDupAfter.balance seatAcc 1 < 0)

  -- Attack: Seat holds unlisted asset 999
  -- Demonstrates why h_zero_outside is required in ExitPrecondition:
  let bUnlisted : Book := {
    accounts := [seatAcc, payeeAcc]
    balances := fun a ast =>
      if a = seatAcc ∧ ast = 1 then 100
      else if a = seatAcc ∧ ast = 999 then 50  -- asset 999 is outside active list [1]
      else 0
    leaseRecords := fun _ => none
    floors := fun _ _ => 0
  }
  let psUnlisted := payoutPostings bUnlisted seatAcc payeeAcc [1]
  let bUnlistedAfter := applyPostings bUnlisted psUnlisted
  assertPass "Unlisted asset 999 remains stranded on seat (50 ≠ 0), proving necessity of h_zero_outside"
    (bUnlistedAfter.balance seatAcc 999 == 50)

/-! =========================================================================
    Main Runner
    ========================================================================= -/

def main : IO Unit := do
  IO.println "============================================================"
  IO.println "=== M2 ITERATION 2 EMPIRICAL CHALLENGER STRESS HARNESS ==="
  IO.println "============================================================"
  testCrossingIntervalAndZeroVolumeAttacks
  testOrderAccountAuthorizationAttacks
  testSeatCoordinateBoundariesAndSelfPayout
  testMultiAssetExitStress
  IO.println "============================================================"
  IO.println "=== ALL EMPIRICAL CHALLENGER STRESS TESTS PASSED! ==="
  IO.println "============================================================"

#eval main
