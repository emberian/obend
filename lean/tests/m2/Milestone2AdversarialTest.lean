import Obend.Ledger.Book
import Obend.Ledger.Seat
import Obend.Judge.Clearing
import Obend.Judge.Class
import Obend.Vault.Hyperedge

open Obend.Vault
open Obend.Ledger
open Obend.Judge

def assertOk (what : String) (ok : Bool) : IO Unit :=
  if ok then
    IO.println s!"[PASS] {what}"
  else
    throw (IO.userError s!"[FAIL] {what}")

/-! =========================================================================
    Part 1: ZoE Seat Offer-Safety Adversarial Tests
    ========================================================================= -/

def testZoeSeatOfferSafetyAdversarial : IO Unit := do
  IO.println "--- Testing ZoE Seat Offer Safety Adversarial Harness ---"

  let seatAcc : AccountId := protectedBase + 500
  let payeeAcc : AccountId := 42

  let propSingle : Proposal := {
    give := [(1, 100)]   -- gives 100 of asset 1
    want := [(2, 50)]    -- wants 50 of asset 2
    exit := .onDemand
    donate := false
  }

  -- 1. Partial Fill (Unrefunded): receives 25 asset 2, but 100 asset 1 was taken
  let bPartialUnrefunded : Book := {
    accounts := [seatAcc]
    balances := fun a ast =>
      if a = seatAcc ∧ ast = 1 then 0
      else if a = seatAcc ∧ ast = 2 then 25
      else 0
    leaseRecords := fun _ => none
    floors := fun _ _ => 0
  }
  assertOk "Partial fill without refund violates ZoE offer safety"
    (safeAt bPartialUnrefunded seatAcc propSingle == false)

  -- 2. Partial Fill (Proportional give held): receives 25 asset 2, retains 50 asset 1
  -- Zoe offer safety is all-or-nothing: neither all want (25 < 50) nor all give (50 < 100)
  let bPartialProportional : Book := {
    accounts := [seatAcc]
    balances := fun a ast =>
      if a = seatAcc ∧ ast = 1 then 50
      else if a = seatAcc ∧ ast = 2 then 25
      else 0
    leaseRecords := fun _ => none
    floors := fun _ _ => 0
  }
  assertOk "Partial fill with partial refund violates strict ZoE offer safety"
    (safeAt bPartialProportional seatAcc propSingle == false)

  -- 3. Partial fill completed to full fill: receives remaining 25 asset 2 (total 50)
  let bFullFill : Book := {
    accounts := [seatAcc]
    balances := fun a ast =>
      if a = seatAcc ∧ ast = 1 then 0
      else if a = seatAcc ∧ ast = 2 then 50
      else 0
    leaseRecords := fun _ => none
    floors := fun _ _ => 0
  }
  assertOk "Completed fill satisfies ZoE offer safety (want met)"
    (safeAt bFullFill seatAcc propSingle == true)

  -- 4. Partial fill reverted to full refund: returns 100 asset 1, 0 asset 2
  let bFullRefund : Book := {
    accounts := [seatAcc]
    balances := fun a ast =>
      if a = seatAcc ∧ ast = 1 then 100
      else if a = seatAcc ∧ ast = 2 then 0
      else 0
    leaseRecords := fun _ => none
    floors := fun _ _ => 0
  }
  assertOk "Full refund satisfies ZoE offer safety (give refunded)"
    (safeAt bFullRefund seatAcc propSingle == true)

  -- 5. Refund short by 1 unit: 99 asset 1
  let bRefundShort : Book := {
    accounts := [seatAcc]
    balances := fun a ast =>
      if a = seatAcc ∧ ast = 1 then 99
      else 0
    leaseRecords := fun _ => none
    floors := fun _ _ => 0
  }
  assertOk "Refund short by 1 unit strictly violates offer safety"
    (safeAt bRefundShort seatAcc propSingle == false)

  -- 6. Refund surplus: 101 asset 1
  let bRefundSurplus : Book := {
    accounts := [seatAcc]
    balances := fun a ast =>
      if a = seatAcc ∧ ast = 1 then 101
      else 0
    leaseRecords := fun _ => none
    floors := fun _ _ => 0
  }
  assertOk "Refund with surplus satisfies offer safety (monotonicity)"
    (safeAt bRefundSurplus seatAcc propSingle == true)

  -- 7. Wrong asset refund: holds 100 of asset 3 instead of asset 1
  let bWrongAsset : Book := {
    accounts := [seatAcc]
    balances := fun a ast =>
      if a = seatAcc ∧ ast = 3 then 100
      else 0
    leaseRecords := fun _ => none
    floors := fun _ _ => 0
  }
  assertOk "Wrong asset refund violates offer safety"
    (safeAt bWrongAsset seatAcc propSingle == false)

  -- 8. Multi-Asset Proposal: give [(1, 10), (2, 20)], want [(3, 5), (4, 15)]
  let propMulti : Proposal := {
    give := [(1, 10), (2, 20)]
    want := [(3, 5), (4, 15)]
    exit := .onDemand
    donate := false
  }

  -- Multi-asset: 3 want satisfied, 4 short by 1 -> false
  let bMultiWantShort : Book := {
    accounts := [seatAcc]
    balances := fun a ast =>
      if a = seatAcc ∧ ast = 3 then 5
      else if a = seatAcc ∧ ast = 4 then 14
      else 0
    leaseRecords := fun _ => none
    floors := fun _ _ => 0
  }
  assertOk "Multi-asset want short by 1 unit fails offer safety"
    (safeAt bMultiWantShort seatAcc propMulti == false)

  -- Multi-asset: 1 give refunded, 2 short by 1 -> false
  let bMultiGiveShort : Book := {
    accounts := [seatAcc]
    balances := fun a ast =>
      if a = seatAcc ∧ ast = 1 then 10
      else if a = seatAcc ∧ ast = 2 then 19
      else 0
    leaseRecords := fun _ => none
    floors := fun _ _ => 0
  }
  assertOk "Multi-asset give short by 1 unit fails offer safety"
    (safeAt bMultiGiveShort seatAcc propMulti == false)

  -- Multi-asset: both want satisfied -> true
  let bMultiWantFull : Book := {
    accounts := [seatAcc]
    balances := fun a ast =>
      if a = seatAcc ∧ ast = 3 then 5
      else if a = seatAcc ∧ ast = 4 then 15
      else 0
    leaseRecords := fun _ => none
    floors := fun _ _ => 0
  }
  assertOk "Multi-asset want fully satisfied passes offer safety"
    (safeAt bMultiWantFull seatAcc propMulti == true)

  -- Multi-asset: both give refunded -> true
  let bMultiGiveFull : Book := {
    accounts := [seatAcc]
    balances := fun a ast =>
      if a = seatAcc ∧ ast = 1 then 10
      else if a = seatAcc ∧ ast = 2 then 20
      else 0
    leaseRecords := fun _ => none
    floors := fun _ _ => 0
  }
  assertOk "Multi-asset give fully refunded passes offer safety"
    (safeAt bMultiGiveFull seatAcc propMulti == true)

  -- 9. Zero Transfers & Degenerate Proposals
  -- Zero balance payout: seat has 0 balance, executes payout posting
  let bZeroBal : Book := Book.empty
  let pZero : ResourcePosting := ⟨seatAcc, payeeAcc, 1, (bZeroBal.balance seatAcc 1).toNat⟩
  assertOk "Zero balance produces amount 0 posting" (pZero.amount == 0)
  let bZeroAfter := bZeroBal.applyPosting pZero
  assertOk "Zero amount transfer leaves seat balance at 0" (bZeroAfter.balance seatAcc 1 == 0)
  assertOk "Zero amount transfer leaves payee balance at 0" (bZeroAfter.balance payeeAcc 1 == 0)

  -- Zero-quantity proposal: give [(1, 0)], want [(2, 0)]
  let propZeroAmt : Proposal := {
    give := [(1, 0)]
    want := [(2, 0)]
    exit := .onDemand
    donate := false
  }
  assertOk "Zero-quantity proposal is safe with zero balances"
    (safeAt bZeroBal seatAcc propZeroAmt == true)

  -- Empty proposal: give [], want []
  let propEmpty : Proposal := {
    give := []
    want := []
    exit := .onDemand
    donate := false
  }
  assertOk "Empty proposal is unconditionally safe"
    (safeAt bZeroBal seatAcc propEmpty == true)

  -- Empty give proposal: give [], want [(2, 10)]
  let propEmptyGive : Proposal := {
    give := []
    want := [(2, 10)]
    exit := .onDemand
    donate := false
  }
  assertOk "Empty give proposal is safe by vacuously true refund"
    (safeAt bZeroBal seatAcc propEmptyGive == true)

  -- Empty want proposal: give [(1, 10)], want []
  let propEmptyWant : Proposal := {
    give := [(1, 10)]
    want := []
    exit := .onDemand
    donate := false
  }
  assertOk "Empty want proposal is safe by vacuously true want met"
    (safeAt bZeroBal seatAcc propEmptyWant == true)

  -- Self-payout no-op: payee == seatAcc
  let bSelfPayee : Book := {
    accounts := [seatAcc]
    balances := fun a ast => if a = seatAcc ∧ ast = 1 then 50 else 0
    leaseRecords := fun _ => none
    floors := fun _ _ => 0
  }
  let pSelf : ResourcePosting := ⟨seatAcc, seatAcc, 1, 50⟩
  let bSelfAfter := bSelfPayee.applyPosting pSelf
  assertOk "Self-payout leaves balance identical (no leak or loss)"
    (bSelfAfter.balance seatAcc 1 == 50)

  -- 10. Boundary Accounts Around 2^256
  let boundBelow : AccountId := protectedBase - 1
  let boundExact : AccountId := protectedBase
  let boundAbove : AccountId := protectedBase + 1
  let boundExtreme : AccountId := 2 * protectedBase

  assertOk "Boundary account 2^256 - 1 is strictly outside protected space"
    ((protectedBase ≤ boundBelow) == false)
  assertOk "Boundary account 2^256 is exactly the floor of protected space"
    (protectedBase ≤ boundExact)
  assertOk "Boundary account 2^256 + 1 is within protected space"
    (protectedBase ≤ boundAbove)
  assertOk "Boundary account 2^512 is within protected space"
    (protectedBase ≤ boundExtreme)

  -- Test full payout lifecycle at exact boundary 2^256
  let bExactInit : Book := {
    accounts := [boundExact, payeeAcc]
    balances := fun a ast =>
      if a = boundExact ∧ ast = 1 then 1000000
      else 0
    leaseRecords := fun _ => none
    floors := fun _ _ => 0
  }
  let pExact : ResourcePosting := ⟨boundExact, payeeAcc, 1, (bExactInit.balance boundExact 1).toNat⟩
  let bExactPost := bExactInit.applyPosting pExact
  assertOk "Exact boundary 2^256 payout zeroes seat balance"
    (bExactPost.balance boundExact 1 == 0)
  assertOk "Exact boundary 2^256 payout credits payee"
    (bExactPost.balance payeeAcc 1 == 1000000)
  assertOk "Exact boundary 2^256 payout conserves total asset"
    (bExactPost.totalAsset 1 == bExactInit.totalAsset 1)

  -- Test cross-protected transfer from 2^256 + 1 to 2^256
  let bCrossInit : Book := {
    accounts := [boundAbove, boundExact]
    balances := fun a ast =>
      if a = boundAbove ∧ ast = 1 then 777
      else 0
    leaseRecords := fun _ => none
    floors := fun _ _ => 0
  }
  let pCross : ResourcePosting := ⟨boundAbove, boundExact, 1, 777⟩
  let bCrossPost := bCrossInit.applyPosting pCross
  assertOk "Cross-protected transfer moves balance accurately"
    (bCrossPost.balance boundAbove 1 == 0 ∧ bCrossPost.balance boundExact 1 == 777)

  -- Test payoutPostings multi-asset generator
  let bMultiPayout : Book := {
    accounts := [seatAcc, payeeAcc]
    balances := fun a ast =>
      if a = seatAcc ∧ ast = 1 then 100
      else if a = seatAcc ∧ ast = 2 then 200
      else 0
    leaseRecords := fun _ => none
    floors := fun _ _ => 0
  }
  let postings := payoutPostings bMultiPayout seatAcc payeeAcc [1, 2]
  assertOk "payoutPostings generates correct posting count" (postings.length == 2)
  let bMultiAfter := postings.foldl Book.applyPosting bMultiPayout
  assertOk "Multi-asset payout zeroes seat asset 1" (bMultiAfter.balance seatAcc 1 == 0)
  assertOk "Multi-asset payout zeroes seat asset 2" (bMultiAfter.balance seatAcc 2 == 0)
  assertOk "Multi-asset payout credits payee asset 1" (bMultiAfter.balance payeeAcc 1 == 100)
  assertOk "Multi-asset payout credits payee asset 2" (bMultiAfter.balance payeeAcc 2 == 200)

/-! =========================================================================
    Part 2: drex-clearing@1 LP Judge Adversarial Tests
    ========================================================================= -/

def testClearingJudgeAdversarial : IO Unit := do
  IO.println "--- Testing drex-clearing@1 LP Judge Adversarial Harness ---"

  let mktStd : Market := { currency := 1, goods := 2, epsilon := 0 }

  -- Standard 2-order balanced crossing at price 5:
  -- Buyer (acc 1): bid 2 goods for max 10 currency (price 5) -> crosses
  let oBid : Order := { account := 1, side := .bid, qty := 2, total := 10 }
  -- Seller (acc 2): ask 2 goods for min 10 currency (price 5) -> crosses
  let oAsk : Order := { account := 2, side := .ask, qty := 2, total := 10 }
  let stdOrders := [oBid, oAsk]

  let stdTransfers : List ResourcePosting := [
    ⟨2, 1, 2, 2⟩,  -- Seller sends 2 goods to Buyer
    ⟨1, 2, 1, 10⟩  -- Buyer sends 10 currency to Seller
  ]

  -- Optimal certificate for std market at price 5:
  -- Potentials (0, 1) -> Δ = 1.
  -- Bid: Δ + s = 1 + 0 = 1 >= 1. s1 = 0.
  -- Ask: -Δ + s = -1 + 2 = 1 >= 1. s2 = 2.
  -- dualCap = 2 * 0 + 2 * 2 = 4.
  -- objVol = 2 + 2 = 4.
  -- gap = 4 - 4 = 0.
  let certOptimal : Certificate := {
    price := 5
    potentials := (0, 1)
    slacks := [0, 2]
  }

  assertOk "Judge accepts baseline optimal certificate at ε=0"
    (judge mktStd stdOrders stdTransfers certOptimal matches .ok ())

  /- -----------------------------------------------------------------------
     Adversarial Test 1: Degenerate Duals
     ----------------------------------------------------------------------- -/

  -- D1: Equal potentials (p1 = 0, p2 = 0 -> Δ = 0) with valid slacks [1, 1]
  -- Bid: Δ + s = 0 + 1 = 1 >= 1.
  -- Ask: -Δ + s = -0 + 1 = 1 >= 1.
  -- dualCap = 2 * 1 + 2 * 1 = 4. objVol = 4. gap = 0.
  let certDegenerateValid : Certificate := {
    price := 5
    potentials := (0, 0)
    slacks := [1, 1]
  }
  assertOk "Judge accepts valid degenerate dual with equal potentials Δ=0 and s=[1, 1]"
    (judge mktStd stdOrders stdTransfers certDegenerateValid matches .ok ())

  -- D2: Equal potentials (Δ = 0) with inadequate bid slack s1 = 0
  -- Bid: 0 + 0 = 0 < 1 -> dualInfeasible!
  let certDegenerateInfeasibleBid : Certificate := {
    price := 5
    potentials := (0, 0)
    slacks := [0, 1]
  }
  assertOk "Judge strictly rejects degenerate dual with s1=0 < 1 for bid"
    (judge mktStd stdOrders stdTransfers certDegenerateInfeasibleBid matches
      .error (.dualInfeasible 1 .bid 0 1))

  -- D3: Inverted potentials (p1 = 1, p2 = 0 -> Δ = -1)
  -- Bid: -1 + s >= 1 -> requires s1 >= 2.
  -- Ask: -(-1) + s = 1 + s >= 1 -> s2 >= 0.
  let certInvertedPotentialsValid : Certificate := {
    price := 5
    potentials := (1, 0)
    slacks := [2, 0]
  }
  assertOk "Judge accepts inverted potentials Δ=-1 when slacks satisfy dual feasibility [2, 0]"
    (judge mktStd stdOrders stdTransfers certInvertedPotentialsValid matches .ok ())

  -- D4: Inverted potentials (Δ = -1) with insufficient slack s1 = 1
  -- Bid: -1 + 1 = 0 < 1 -> dualInfeasible!
  let certInvertedPotentialsInvalid : Certificate := {
    price := 5
    potentials := (1, 0)
    slacks := [1, 0]
  }
  assertOk "Judge rejects inverted potentials Δ=-1 when bid slack is insufficient (s1=1)"
    (judge mktStd stdOrders stdTransfers certInvertedPotentialsInvalid matches
      .error (.dualInfeasible 1 .bid 1 1))

  -- D5: Extreme arbitrary-precision potentials around 2^256
  let potHuge1 : Int := (2^256 : Nat)
  let potHuge2 : Int := (2^256 : Nat) + 1
  let certHugePotentials : Certificate := {
    price := 5
    potentials := (potHuge1, potHuge2)
    slacks := [0, 2]
  }
  assertOk "Judge handles extreme potentials at 2^256 without overflow"
    (judge mktStd stdOrders stdTransfers certHugePotentials matches .ok ())

  /- -----------------------------------------------------------------------
     Adversarial Test 2: Zero Prices
     ----------------------------------------------------------------------- -/

  -- Z1: Valid zero-price clearing (Donation ask with total = 0, price = 0)
  -- Ask donates 5 goods for 0 currency
  let oDonationAsk : Order := { account := 20, side := .ask, qty := 5, total := 0 }
  -- Bid wants 5 goods, willing to pay up to 10 currency
  let oZeroPriceBid : Order := { account := 10, side := .bid, qty := 5, total := 10 }
  let zeroPriceOrders := [oZeroPriceBid, oDonationAsk]

  -- Transfers move goods, 0 currency moved
  let zeroPriceTransfers : List ResourcePosting := [
    ⟨20, 10, 2, 5⟩  -- 5 goods moved from seller to buyer
  ]
  let certZeroPrice : Certificate := {
    price := 0
    potentials := (0, 1)
    slacks := [0, 2]
  }
  assertOk "Judge accepts valid zero-price clearing with free goods (total=0)"
    (judge mktStd zeroPriceOrders zeroPriceTransfers certZeroPrice matches .ok ())

  -- Z2: Illicit currency payment under zero clearing price
  -- Market cleared at price 0, but buyer paid 1 currency to seller
  let badZeroPriceTransfers : List ResourcePosting := [
    ⟨20, 10, 2, 5⟩,
    ⟨10, 20, 1, 1⟩  -- illicit 1 currency transfer
  ]
  assertOk "Judge strictly rejects non-zero payment under zero clearing price"
    (judge mktStd zeroPriceOrders badZeroPriceTransfers certZeroPrice matches
      .error (.notUniform 10))

  -- Z3: Zero price attempting to fill non-zero ask (seller wants > 0)
  let oPaidAsk : Order := { account := 20, side := .ask, qty := 5, total := 1 }
  let badZeroPriceOrders := [oZeroPriceBid, oPaidAsk]
  assertOk "Judge strictly rejects filling ask whose reserve price exceeds zero"
    (judge mktStd badZeroPriceOrders zeroPriceTransfers certZeroPrice matches
      .error (.invalidPrice 0))

  /- -----------------------------------------------------------------------
     Adversarial Test 3: Inverted Bids / Asks (Out-of-the-Money Fills)
     ----------------------------------------------------------------------- -/

  -- I1: Out-of-the-money bid attempted to fill
  -- Clearing price 10. Buyer only willing to pay 8 (qty 2, total 16 -> 8/unit < 10)
  let oUncrossedBid : Order := { account := 1, side := .bid, qty := 2, total := 16 }
  let oCrossedAsk : Order := { account := 2, side := .ask, qty := 2, total := 20 }
  let otmOrders := [oUncrossedBid, oCrossedAsk]
  let otmTransfers : List ResourcePosting := [
    ⟨2, 1, 2, 2⟩,
    ⟨1, 2, 1, 20⟩
  ]
  let certPrice10 : Certificate := {
    price := 10
    potentials := (0, 1)
    slacks := [0, 2]
  }
  assertOk "Judge strictly rejects filling out-of-the-money bid"
    (judge mktStd otmOrders otmTransfers certPrice10 matches
      .error (.capacityExceeded 1 2 0))

  -- I2: Out-of-the-money ask attempted to fill
  -- Clearing price 10. Seller wants at least 12 (qty 2, total 24 -> 12/unit > 10)
  let oCrossedBid : Order := { account := 1, side := .bid, qty := 2, total := 20 }
  let oUncrossedAsk : Order := { account := 2, side := .ask, qty := 2, total := 24 }
  let otmAskOrders := [oCrossedBid, oUncrossedAsk]
  assertOk "Judge strictly rejects filling out-of-the-money ask"
    (judge mktStd otmAskOrders otmTransfers certPrice10 matches
      .error (.capacityExceeded 2 2 0))

  -- I3: Non-crossing market (bid price 4 < ask price 6) certified with zero trade
  let oBidLow : Order := { account := 1, side := .bid, qty := 2, total := 8 }
  let oAskHigh : Order := { account := 2, side := .ask, qty := 2, total := 12 }
  let nonCrossingOrders := [oBidLow, oAskHigh]
  let certZeroTrade : Certificate := {
    price := 5
    potentials := (0, 1)
    slacks := [0, 2]
  }
  assertOk "Judge certifies optimal zero clearing for non-crossing orderbook"
    (judge mktStd nonCrossingOrders [] certZeroTrade matches .ok ())

  -- I4: Crossed market falsely claimed optimal with zero trade
  let oBidHigh : Order := { account := 1, side := .bid, qty := 2, total := 20 }
  let oAskLow : Order := { account := 2, side := .ask, qty := 2, total := 8 }
  let crossedOrders := [oBidHigh, oAskLow]
  assertOk "Judge rejects zero trade on crossed market due to uncertified duality gap"
    (judge mktStd crossedOrders [] certZeroTrade matches
      .error (.uncertified 4 0))

  /- -----------------------------------------------------------------------
     Adversarial Test 4: Negative Quantities, Illegal Slacks & Manipulations
     ----------------------------------------------------------------------- -/

  -- N1: Negative fill on bid (buyer is forced to send goods instead of receiving)
  let revBidTransfers : List ResourcePosting := [
    ⟨1, 2, 2, 2⟩,  -- buyer sends goods!
    ⟨2, 1, 1, 10⟩  -- seller pays currency!
  ]
  assertOk "Judge strictly catches negative fill on buyer side"
    (judge mktStd stdOrders revBidTransfers certOptimal matches
      .error (.negativeFill 1 (-2)))

  -- N2: Negative fill on ask (seller receives goods instead of sending)
  -- Seller 1 (acc 2, ask) sends goods, Seller 2 (acc 3, ask) receives goods
  let oSeller1 : Order := { account := 2, side := .ask, qty := 2, total := 10 }
  let oSeller2 : Order := { account := 3, side := .ask, qty := 2, total := 10 }
  let twoSellerOrders := [oSeller1, oSeller2]
  let twoSellerTransfers : List ResourcePosting := [
    ⟨2, 3, 2, 2⟩,  -- Seller 1 sends goods to Seller 2
    ⟨3, 2, 1, 10⟩  -- Seller 2 sends currency to Seller 1
  ]
  let certTwoSellers : Certificate := {
    price := 5
    potentials := (0, 1)
    slacks := [2, 2]
  }
  assertOk "Judge strictly catches negative fill on seller side"
    (judge mktStd twoSellerOrders twoSellerTransfers certTwoSellers matches
      .error (.negativeFill 3 (-2)))

  -- N3: Negative slack in certificate to artificially deflate dual objective
  let certNegativeSlack : Certificate := {
    price := 5
    potentials := (0, 1)
    slacks := [-1, 2]
  }
  assertOk "Judge strictly catches negative slack in certificate"
    (judge mktStd stdOrders stdTransfers certNegativeSlack matches
      .error (.negativeSlack 1 (-1)))

  -- N4: External non-order account rejected (Finding 7 remediation)
  -- External account 99 injects goods to Buyer, caught by isOrderAccount
  let nonConservingTransfers : List ResourcePosting := [
    ⟨2, 1, 2, 2⟩,  -- Seller sends 2 goods to Buyer
    ⟨99, 1, 2, 1⟩, -- External account 99 injects 1 good to Buyer
    ⟨1, 2, 1, 10⟩, -- Buyer pays 10 currency to Seller
    ⟨1, 99, 1, 5⟩  -- Buyer pays 5 currency to external account 99
  ]
  assertOk "Judge strictly rejects external non-order account transfer"
    (judge mktStd stdOrders nonConservingTransfers certOptimal matches
      .error (.notAnOrder ⟨99, 1, 2, 1⟩))

  -- N5: Foreign asset in transfers (sneaking asset 99 into clearing)
  let foreignTransfers : List ResourcePosting := [
    ⟨2, 1, 2, 2⟩,
    ⟨1, 2, 1, 10⟩,
    ⟨1, 2, 99, 5⟩  -- foreign asset 99
  ]
  assertOk "Judge strictly catches foreign asset posting"
    (judge mktStd stdOrders foreignTransfers certOptimal matches
      .error (.foreignAsset ⟨1, 2, 99, 5⟩))

  -- N6: Slack count mismatch
  let certSlackMismatch : Certificate := {
    price := 5
    potentials := (0, 1)
    slacks := [0, 2, 0]  -- 3 slacks for 2 orders
  }
  assertOk "Judge strictly rejects certificate with mismatched slack count"
    (judge mktStd stdOrders stdTransfers certSlackMismatch matches
      .error (.slackCount 2 3))

  -- N7: Malformed market (currency == goods)
  let badMkt : Market := { currency := 1, goods := 1, epsilon := 0 }
  assertOk "Judge rejects market where currency equals goods"
    (judge badMkt stdOrders stdTransfers certOptimal matches
      .error .marketMalformed)

  -- N8: Order with qty = 0
  let oZeroQtyBid : Order := { account := 1, side := .bid, qty := 0, total := 10 }
  let zeroQtyOrders := [oZeroQtyBid, oAsk]
  assertOk "Judge rejects positive fill on zero-quantity order"
    (judge mktStd zeroQtyOrders stdTransfers certOptimal matches
      .error (.capacityExceeded 1 2 0))

  /- -----------------------------------------------------------------------
     Adversarial Test 5: Boundary Epsilon Tolerances
     ----------------------------------------------------------------------- -/

  -- Set up an execution with a known non-zero duality gap = 4
  -- With std orders (cap = [2, 2]), fills = [2, 2] (objVol = 4).
  -- Suppose dual potentials (0, 0) -> Δ = 0.
  -- Valid dual slacks: s1 = 1, s2 = 3.
  -- Bid: 0 + 1 = 1 >= 1.
  -- Ask: -0 + 3 = 3 >= 1.
  -- dualCap = 2 * 1 + 2 * 3 = 8.
  -- objVol = 4.
  -- gap = 8 - 4 = 4.
  let certGap4 : Certificate := {
    price := 5
    potentials := (0, 0)
    slacks := [1, 3]
  }

  -- E1: Exact boundary (epsilon = 4, gap = 4) -> ACCEPT
  let mktEps4 : Market := { currency := 1, goods := 2, epsilon := 4 }
  assertOk "Judge accepts certificate at exact epsilon boundary (gap == eps == 4)"
    (judge mktEps4 stdOrders stdTransfers certGap4 matches .ok ())

  -- E2: Boundary exceeded by 1 (epsilon = 3, gap = 4) -> REJECT
  let mktEps3 : Market := { currency := 1, goods := 2, epsilon := 3 }
  assertOk "Judge strictly rejects certificate exceeding epsilon tolerance by 1 unit"
    (judge mktEps3 stdOrders stdTransfers certGap4 matches
      .error (.uncertified 4 3))

  -- E3: Sub-boundary tolerance (epsilon = 5, gap = 4) -> ACCEPT
  let mktEps5 : Market := { currency := 1, goods := 2, epsilon := 5 }
  assertOk "Judge accepts certificate within loose epsilon tolerance (gap < eps)"
    (judge mktEps5 stdOrders stdTransfers certGap4 matches .ok ())

  -- E4: Zero tolerance boundary (epsilon = 0, gap = 4) -> REJECT
  let mktEps0 : Market := { currency := 1, goods := 2, epsilon := 0 }
  assertOk "Judge strictly rejects gap=4 under epsilon=0"
    (judge mktEps0 stdOrders stdTransfers certGap4 matches
      .error (.uncertified 4 0))

  -- E5: Arbitrary large epsilon (epsilon = 10^18, gap = 4) -> ACCEPT
  let mktEpsHuge : Market := { currency := 1, goods := 2, epsilon := 1000000000000000000 }
  assertOk "Judge accepts gap under 64-bit large epsilon tolerance"
    (judge mktEpsHuge stdOrders stdTransfers certGap4 matches .ok ())

/-! =========================================================================
    Part 3: Formal Adversarial Metatheory Theorems (0 sorryAx, 0 axioms)
    ========================================================================= -/

/-- An empty-give proposal is unconditionally safe for any account and book state. -/
theorem empty_give_safeAt (b : Book) (acc : AccountId) (p : Proposal) (hgive : p.give = []) :
    safeAt b acc p = true := by
  unfold safeAt
  rw [hgive]
  simp

/-- An empty-want proposal is unconditionally safe for any account and book state. -/
theorem empty_want_safeAt (b : Book) (acc : AccountId) (p : Proposal) (hwant : p.want = []) :
    safeAt b acc p = true := by
  unfold safeAt
  rw [hwant]
  simp

/-- Unconditional exit payout strictly conserves asset balance between seat and payee. -/
theorem payout_single_conserves (b : Book) (acc payee : AccountId) (ast : AssetId)
    (hdiff : payee ≠ acc) (hnonneg : 0 ≤ b.balance acc ast) :
    let p : ResourcePosting := ⟨acc, payee, ast, (b.balance acc ast).toNat⟩
    (b.applyPosting p).balance acc ast + (b.applyPosting p).balance payee ast =
    b.balance acc ast + b.balance payee ast := by
  intro p
  have h := payout_single_balance b acc payee ast hdiff hnonneg
  rcases h with ⟨hseat, hpayee⟩
  rw [hseat, hpayee]
  omega

/-- Adversarial weak duality holds under degenerate potentials (Δ = 0). -/
theorem weak_duality_degenerate_potentials (n : Nat) (A : Fin n → Int) (c : Fin n → Int)
    (f' : Fin n → Int)
    (hprim_cons : finSum n (fun i => A i * f' i) = 0)
    (hprim_nonneg : ∀ i, 0 ≤ f' i)
    (hprim_cap : ∀ i, f' i ≤ c i) :
    finSum n f' ≤ finSum n (fun i => c i * 1) := by
  have hdual_nonneg : ∀ (i : Fin n), 0 ≤ (1 : Int) := by intro _; decide
  have hdual_feas : ∀ (i : Fin n), 1 ≤ 0 * A i + 1 := by intro _; simp
  exact weak_duality n A c (fun _ => 1) f' 0 hprim_cons hprim_nonneg hprim_cap hdual_nonneg hdual_feas

/-- Boundary ε-gap guarantees that suboptimal allocations cannot beat certified value + ε. -/
theorem epsilon_gap_bounds_adversary (n : Nat) (A : Fin n → Int) (c : Fin n → Int) (s : Fin n → Int)
    (f f_adv : Fin n → Int) (diff : Int) (eps : Nat)
    (hgap : finSum n (fun i => c i * s i) - finSum n f ≤ (eps : Int))
    (hprim_cons : finSum n (fun i => A i * f_adv i) = 0)
    (hprim_nonneg : ∀ i, 0 ≤ f_adv i)
    (hprim_cap : ∀ i, f_adv i ≤ c i)
    (hdual_nonneg : ∀ i, 0 ≤ s i)
    (hdual_feas : ∀ i, 1 ≤ diff * A i + s i) :
    finSum n f_adv ≤ finSum n f + (eps : Int) :=
  certifies_epsilon_optimal n A c s f f_adv diff eps hgap hprim_cons hprim_nonneg hprim_cap hdual_nonneg hdual_feas

/-! =========================================================================
    Main Runner
    ========================================================================= -/

def main : IO Unit := do
  IO.println "========================================================="
  IO.println "=== Running Milestone 2 Adversarial Challenge Suite ==="
  IO.println "========================================================="
  testZoeSeatOfferSafetyAdversarial
  IO.println ""
  testClearingJudgeAdversarial
  IO.println "========================================================="
  IO.println "=== All Adversarial Challenge Tests Passed! ==="
  IO.println "========================================================="

#eval main

#print axioms empty_give_safeAt
#print axioms empty_want_safeAt
#print axioms payout_single_conserves
#print axioms weak_duality_degenerate_potentials
#print axioms epsilon_gap_bounds_adversary

