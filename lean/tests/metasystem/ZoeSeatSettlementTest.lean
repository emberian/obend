module
/-
# ZoeSeatSettlementTest — escrowed offers, a three-party match, exits, refusals and teeth

Exercises `Obend.Polis.ZoeSeatSettlement` on the ledger spine (`Obend.Ledger.Seat` over a seat
`Book`, mirrored leg for leg on a `FloorBook`):

1. **Bundles.** `AssetBundle` against the ledger's `assetAmountSum`, and the checked merge.
2. **Offers.** Three funded offers are escrowed out of their offerors' `FloorBook` accounts. An
   offer whose `give` is not in a `FloorBook` account, an offer above the offeror's balance, an
   unmarked donation, a spent invitation and an occupied seat are each refused by name.
3. **Match and exit.** A guest's three-way swap, then exits that pay each seat to its payee; a
   theft, a mint and an early exit are refused; per-asset totals are those of the genesis.
4. **Holders.** A seat is exited by the preimage of its 256-bit cSHAKE256 commitment only.
5. **Teeth.** Each `#tooth` replaces one check and reports that a stored proof no longer checks.

The kernel runs cSHAKE256 once per holder capability (through the proved fast path, about 3 s
each): `tableHash` is `zoeHash` read from that table, so no run below pays for a hash.
-/
public import Obend.Polis.ZoeSeatSettlement
import all Obend.Consensus.Simplex
import all Obend.Consensus.SimplexProtocol
import all Obend.Polis.ZoeSeatSettlement
import all Init.Data.List.Sort.Basic
import Obend.Tactic.Tooth
import Obend.AssertAxioms
import all Obend.Apps.ZkNtt.Goldilocks
import all Obend.AssertAxioms
import all Obend.Core.Data
import all Obend.Core.Digest
import all Obend.Core.Machine
import all Obend.Core.MachineFast
import all Obend.Core.Term
import all Obend.Core.Ty
import all Obend.Crypto.Multilinear
import all Obend.Crypto.Transcript
import all Obend.Digest.Cshake256
import all Obend.Digest.Cshake256.Fast
import all Obend.Digest.Cshake256.Seam
import all Obend.Digest.Cshake256.Spec
import all Obend.Digest.HashBytes
import all Obend.Fold
import all Obend.Judge.Class
import all Obend.Judge.Computational
import all Obend.Law.Syntax
import all Obend.Ledger.Book
import all Obend.Ledger.Floors
import all Obend.Ledger.Register
import all Obend.Ledger.Seat
import all Obend.Logic.SeparationFrame
import all Obend.Polis.CapTP
import all Obend.Receipt
import all Obend.Receipt.Merkle
import all Obend.Run.Control
import all Obend.Run.Fold
import all Obend.Run.Fork
import all Obend.Run.Proofs.Control
import all Obend.Run.Proofs.Invariant
import all Obend.Run.Proofs.Shared
import all Obend.Run.Runner
import all Obend.Run.Shared
import all Obend.Run.Spec
import all Obend.Slot
import all Obend.Slot.Integrity
import all Obend.Slot.Proofs.Protocol
import all Obend.Slot.Proofs.ProtocolTyping
import all Obend.Slot.Protocol
import all Obend.Slot.Selection
import all Obend.Slot.World
import all Obend.Tactic.Cases
import all Obend.Tactic.Tooth
import all Obend.Vault.Mandate

public section
namespace Obend.Polis.ZoeSeatSettlement.Test

open Obend.Ledger
open Obend.Digest.HashBytes (Collision)
open Obend.Digest.Cshake256 Obend.Digest.Cshake256.Fast

set_option maxRecDepth 8192

deriving instance DecidableEq for Except

/-! ## 1. Bundles against the ledger's lists -/

def a100 : AssetBundle := .singleton 0 100 (by decide)
def a95 : AssetBundle := .singleton 0 95 (by decide)
def b200 : AssetBundle := .singleton 1 200 (by decide)
def c50 : AssetBundle := .singleton 2 50 (by decide)
def improved : AssetBundle := ⟨#[(0, 5), (1, 200)], by simp [Canonical]⟩

example : improved.toPairs = [(0, 5), (1, 200)] := by decide +kernel
example : improved.amountOf 0 = 5 ∧ improved.amountOf 1 = 200 ∧ improved.amountOf 2 = 0 := by
  decide +kernel
-- The binary search and the ledger's list sum agree, here and for every bundle and asset.
example : assetAmountSum improved.toPairs 1 = 200 := by decide +kernel
example (k : AssetId) : assetAmountSum improved.toPairs k = improved.amountOf k :=
  improved.toPairs_amount k
example (a b : AssetBundle) :
    a.bundleLeq b = true ↔ ∀ k, assetAmountSum a.toPairs k ≤ assetAmountSum b.toPairs k :=
  a.bundleLeq_iff_ledger b
example : (bundleProposal a100 b200 .onDemand).assetsNodupB = true :=
  bundleProposal_assetsNodup _ _ _ _
-- A bundle proposal wants nothing exactly when its `want` bundle is empty.
example : (bundleProposal a100 .empty .onDemand).wantsNothing = true ∧
    (bundleProposal a100 b200 .onDemand).wantsNothing = false := by decide +kernel

def maxA : AssetBundle := .singleton 0 18446744073709551615 (by decide)
def oneA : AssetBundle := .singleton 0 1 (by decide)
-- The merge checks the sum before it converts: 2^64 - 1 plus 1 is refused, not wrapped.
theorem checked_overflow : maxA.addChecked oneA = none := by
  have hm : mergeAmounts maxA.entries.toList oneA.entries.toList = none := by
    change mergeAmounts [(0, 18446744073709551615)] [(0, 1)] = none
    rw [mergeAmounts]
    decide
  unfold AssetBundle.addChecked
  split
  · rfl
  · rename_i zs hz
    rw [hm] at hz
    contradiction
example (c : AssetBundle) (h : a95.addChecked a100 = some c) (k : AssetId) :
    assetAmountSum c.toPairs k = assetAmountSum a95.toPairs k + assetAmountSum a100.toPairs k :=
  AssetBundle.addChecked_ledger h k

/-! ## 2. Holder capabilities and the hash table -/

def capA : List UInt8 := [1, 1]
def capB : List UInt8 := [2, 2]
def capC : List UInt8 := [3, 3]
def capWrong : List UInt8 := [9, 9]

def outA : List UInt8 :=
  [12, 118, 226, 35, 143, 122, 120, 164, 75, 36, 201, 179, 203, 254, 199, 219, 216, 109, 160, 16,
    127, 229, 22, 142, 46, 59, 246, 254, 209, 132, 29, 103]
def outB : List UInt8 :=
  [151, 251, 229, 230, 24, 45, 249, 84, 47, 34, 16, 43, 41, 123, 144, 48, 32, 203, 236, 205, 160,
    136, 6, 244, 252, 233, 29, 66, 249, 26, 229, 140]
def outC : List UInt8 :=
  [11, 109, 136, 136, 14, 193, 200, 213, 57, 172, 219, 190, 152, 12, 204, 101, 124, 227, 161, 2,
    13, 115, 227, 52, 6, 189, 178, 33, 77, 211, 175, 250]
def outWrong : List UInt8 :=
  [55, 173, 126, 169, 191, 110, 167, 138, 116, 215, 167, 85, 215, 199, 86, 159, 58, 127, 177, 26,
    101, 180, 115, 157, 4, 168, 140, 234, 150, 72, 233, 17]

theorem outA_eq : zoeHash (holderPreimage 0 capA) = outA := by
  unfold zoeHash; rw [← cshake256Fast_eq]; decide +kernel
theorem outB_eq : zoeHash (holderPreimage 1 capB) = outB := by
  unfold zoeHash; rw [← cshake256Fast_eq]; decide +kernel
theorem outC_eq : zoeHash (holderPreimage 2 capC) = outC := by
  unfold zoeHash; rw [← cshake256Fast_eq]; decide +kernel
theorem outWrong_eq : zoeHash (holderPreimage 0 capWrong) = outWrong := by
  unfold zoeHash; rw [← cshake256Fast_eq]; decide +kernel

/-- `zoeHash`, with its value on the four fixture openings looked up instead of recomputed. -/
def tableHash : Obend.Digest.HashBytes.Hash := fun pre =>
  if pre = holderPreimage 0 capA then outA
  else if pre = holderPreimage 1 capB then outB
  else if pre = holderPreimage 2 capC then outC
  else if pre = holderPreimage 0 capWrong then outWrong
  else cshake256Fast zoeHolderDomain pre

/-- It is `zoeHash`: what holds of one below holds of the other. -/
theorem tableHash_eq : tableHash = zoeHash := by
  funext pre
  unfold tableHash
  split
  · next h => rw [h, outA_eq]
  · split
    · next h => rw [h, outB_eq]
    · split
      · next h => rw [h, outC_eq]
      · split
        · next h => rw [h, outWrong_eq]
        · exact cshake256Fast_eq _ _

/-- The three commitments, written out. -/
def cA : BitVec 256 :=
  5637802890025593490513560489684692929328010108804128597593016849018319543655#256
def cB : BitVec 256 :=
  68744305452580155177172332752842321848848932788793398437443897664431279760780#256
def cC : BitVec 256 :=
  5168969970086774817489511108422456277209475605066988833803166268412166123514#256

theorem cA_eq : holderCommit zoeHash 0 capA = cA := by rw [← tableHash_eq]; decide +kernel
theorem cB_eq : holderCommit zoeHash 1 capB = cB := by rw [← tableHash_eq]; decide +kernel
theorem cC_eq : holderCommit zoeHash 2 capC = cC := by rw [← tableHash_eq]; decide +kernel
example : holderCommit zoeHash 0 capWrong ≠ cA := by rw [← tableHash_eq]; decide +kernel

/-! ## 3. A funded genesis and three escrowed offers -/

def alice : AccountId := 1
def bob : AccountId := 2
def carol : AccountId := 3
def seatOf (k : Nat) : AccountId := protectedBase + k

/-- Alice holds 100 of asset 0, Bob 200 of asset 1, Carol 50 of asset 2. -/
def genesis : ZoeHost :=
  { fundedHost [(alice, 0, 100), (bob, 1, 200), (carol, 2, 50)] with
    epochKeys := (List.range 5).map (fun i => epochCommit tableHash (i + 1) [UInt8.ofNat (i + 42)]) }

def aliceP : Proposal := bundleProposal a100 b200 .onDemand
def bobP : Proposal := bundleProposal b200 c50 (.afterDeadline 5)
def carolP : Proposal := bundleProposal c50 a95 .onDemand

/-- Alice's seat pays Carol 95 of asset 0, Bob's pays Alice 200 of asset 1, Carol's pays Bob 50
of asset 2. Alice keeps 5 more than she asked for. -/
def otcRealloc : BatchRealloc :=
  ⟨[⟨seatOf 1, seatOf 0, 1, 200⟩, ⟨seatOf 2, seatOf 1, 2, 50⟩, ⟨seatOf 0, seatOf 2, 0, 95⟩]⟩
def otcGuest : GuestContract := fun _ => some otcRealloc

def mints : List ZoeTurn :=
  [.mintInvitation 7 "otc", .mintInvitation 7 "otc", .mintInvitation 7 "otc",
    .mintInvitation 7 "otc"]
def offers : List ZoeTurn :=
  [.enterOffer 0 alice alice 0 aliceP cA, .enterOffer 1 bob bob 1 bobP cB,
    .enterOffer 2 carol carol 2 carolP cC]
def allSeats : List AccountId := [seatOf 0, seatOf 1, seatOf 2]

def minted : ZoeHost := runZoe tableHash otcGuest genesis mints
def threeHost : ZoeHost := runZoe tableHash otcGuest minted offers
def matchedHost : ZoeHost := runZoe tableHash otcGuest threeHost [.invokeGuestContract allSeats]

theorem genesis_inv : ZoeInv genesis := fundedHost_invariant _
theorem minted_inv : ZoeInv minted :=
  (trace_invariant tableHash otcGuest mints genesis minted genesis_inv
    ((validZoeTrace_iff_run _ _ _ _ _).mpr rfl)).1
theorem threeHost_inv : ZoeInv threeHost :=
  (trace_invariant _ _ offers _ _ minted_inv ((validZoeTrace_iff_run _ _ _ _ _).mpr rfl)).1

-- The genesis: both books hold the grants, and the issuer wells carry the supply.
example : genesis.floorBook.balance (.user alice) 0 = 100 ∧
    genesis.floorBook.balance (.issuerWell 0) 0 = -100 ∧ genesis.seatBook.balance alice 0 = 100 ∧
    genesis.floorBook.assetSum 0 = 0 := by decide +kernel

-- Every offer is accepted, and each `give` left its offeror's `FloorBook` account for the seat's.
example : (stepZoeHost tableHash otcGuest minted (.enterOffer 0 alice alice 0 aliceP cA)).isOk =
    true := by decide +kernel
example : threeHost.seats.length = 3 ∧
    threeHost.floorBook.balance (.user alice) 0 = 0 ∧
    threeHost.floorBook.balance (.seat 0) 0 = 100 ∧
    threeHost.floorBook.balance (.user bob) 1 = 0 ∧
    threeHost.floorBook.balance (.seat 1) 1 = 200 ∧
    threeHost.floorBook.balance (.user carol) 2 = 0 ∧
    threeHost.floorBook.balance (.seat 2) 2 = 50 := by decide +kernel

-- The universal theorem on Alice's offer: debited, credited, covered, guard passed, spent.
def aliceIn : ZoeHost := runZoe tableHash otcGuest minted [.enterOffer 0 alice alice 0 aliceP cA]
theorem alice_entered : enterOffer minted 0 alice alice 0 aliceP cA = .ok aliceIn := by
  decide +kernel
example (ast : AssetId) :
    aliceIn.floorBook.balance (addrOf alice) ast =
      minted.floorBook.balance (addrOf alice) ast - (assetAmountSum aliceP.give ast : Int) ∧
    (assetAmountSum aliceP.give ast : Int) ≤ minted.floorBook.balance (addrOf alice) ast :=
  ⟨(enterOffer_escrows minted_inv alice_entered ast).1,
    (enterOffer_escrows minted_inv alice_entered ast).2.2.1⟩

/-- A host whose seat `Book` credits Alice but whose `FloorBook` holds nothing: the `give` was
never put in an account. -/
def unescrowedHost : ZoeHost := { minted with floorBook := FloorBook.empty }
/-- A seat `Book` that claims 150 where the `FloorBook` holds 100. -/
def inflatedHost : ZoeHost :=
  { minted with seatBook := minted.seatBook.setBalance alice 0 150 }

-- **Unescrowed offer refused**: the seat `Book` alone cannot fund a seat.
example : enterOffer unescrowedHost 0 alice alice 0 aliceP cA = .error .unescrowed := by
  decide +kernel
-- **Insufficient `FloorBook` balance refused**: 120 offered against 100 held, though the seat
-- `Book` claims 150; and 101 against 100 where the books agree.
example : enterOffer inflatedHost 0 alice alice 0
    (bundleProposal (.singleton 0 120 (by decide)) b200 .onDemand) cA = .error .unescrowed := by
  decide +kernel
example : enterOffer minted 0 alice alice 0
    (bundleProposal (.singleton 0 101 (by decide)) b200 .onDemand) cA =
    .error (.offer (.insufficientOffererBalance 0)) := by decide +kernel
-- A refused offer mints nothing: the host is as it was.
example : applyZoeTurn tableHash otcGuest unescrowedHost (.enterOffer 0 alice alice 0 aliceP cA) =
    unescrowedHost := by decide +kernel
-- **Unmarked donation refused**: a `give` with no `want` and no `donate` mark.
example : enterOffer minted 0 alice alice 0 (bundleProposal a100 .empty .onDemand) cA =
    .error (.offer .donationUnmarked) := by decide +kernel
example (h : ZoeHost) (c : BitVec 256)
    (hfresh : h.seats.all (fun s => s.account != protectedBase + 0) = true) :
    enterOffer h 0 alice alice 0 (bundleProposal a100 .empty .onDemand) c =
      .error (.offer .donationUnmarked) :=
  enterOffer_donationUnmarked_refused h 0 alice alice 0 _ c (by decide) ⟨by decide, hfresh⟩
    (by decide +kernel) rfl
-- Marked, the same gift is accepted; marked with a `want`, refused.
example : (enterOffer minted 0 alice alice 0 (bundleProposal a100 .empty .onDemand true) cA).isOk =
    true := by decide +kernel
example : enterOffer minted 0 alice alice 0 (bundleProposal a100 b200 .onDemand true) cA =
    .error (.offer .donationMarkedWithWant) := by decide +kernel
-- A spent invitation, an occupied seat and a protected offeror are refused.
example : enterOffer threeHost 0 alice alice 5 aliceP cA =
    .error (.offer (.invitationInvalid 0)) := by decide +kernel
example : enterOffer threeHost 3 alice alice 0 aliceP cA = .error .seatOccupied := by
  decide +kernel
example : enterOffer minted 0 (seatOf 9) alice 0 aliceP cA = .error .notOrdinary := by
  decide +kernel

/-! ## 4. The match, exits, and what is refused -/

example : checkBatchReallocSafe threeHost.seatBook threeHost.seats otcRealloc = true := by
  decide +kernel
-- After the match each seat holds what its offer wanted, and Alice's 5 units over.
example : matchedHost.floorBook.balance (.seat 0) 0 = 5 ∧
    matchedHost.floorBook.balance (.seat 0) 1 = 200 ∧
    matchedHost.floorBook.balance (.seat 1) 2 = 50 ∧
    matchedHost.floorBook.balance (.seat 2) 0 = 95 ∧
    matchedHost.floorBook.balance (.seat 1) 1 = 0 := by decide +kernel
-- **Totals are conserved on the match**: per asset, over the seats and over the whole book.
example : (allSeats.map fun s => matchedHost.seatBook.balance s 0) = [5, 0, 95] ∧
    (allSeats.map fun s => threeHost.seatBook.balance s 0) = [100, 0, 0] ∧
    matchedHost.floorBook.assetSum 0 = threeHost.floorBook.assetSum 0 ∧
    matchedHost.floorBook.assetSum 1 = threeHost.floorBook.assetSum 1 ∧
    matchedHost.floorBook.assetSum 2 = threeHost.floorBook.assetSum 2 := by decide +kernel
-- The match as a conserved value: 95 units of asset 0 leave Alice's seat for Carol's.
example : (reallocConservedValue otcRealloc 0).entries = [(seatOf 0, -95), (seatOf 2, 95)] := by
  decide +kernel

/-- A seat that gives and wants nothing, entered as a marked donation of nothing. -/
def attackHost : ZoeHost := runZoe tableHash otcGuest threeHost
  [.enterOffer 3 4 4 3 ⟨[], [], .onDemand, true, {}⟩ 0#256]
def theftGuest : GuestContract := fun _ => some ⟨[⟨seatOf 0, seatOf 3, 0, 100⟩]⟩
def mintGuest : GuestContract := fun _ => some ⟨[⟨issuerWellAccount 0, seatOf 3, 0, 100⟩]⟩
def userGuest : GuestContract := fun _ => some ⟨[⟨bob, seatOf 3, 1, 0⟩]⟩

example : attackHost.seats.length = 4 := by decide +kernel
-- A theft balances but leaves Alice's seat unsafe; a mint and a leg from a user are not legs
-- between the invoked seats. Each is refused, and the host is as it was.
example : reallocStep theftGuest attackHost (seatOf 3 :: allSeats) = .error .reallocUnsafe := by
  decide +kernel
example : reallocStep mintGuest attackHost (seatOf 3 :: allSeats) = .error .reallocUnsafe := by
  decide +kernel
example : reallocStep userGuest attackHost (seatOf 3 :: allSeats) = .error .reallocUnsafe := by
  decide +kernel
example : applyZoeTurn tableHash theftGuest attackHost
    (.invokeGuestContract (seatOf 3 :: allSeats)) = attackHost := by decide +kernel
example : reallocStep (fun _ => none) threeHost allSeats = .error .guestDeclined := by
  decide +kernel

-- Exit: Alice presents her capability and is paid her whole seat; the seat is gone.
def aliceOut : ZoeHost := runZoe tableHash otcGuest matchedHost [.exitSeat 0 capA]
example : (exitSeatStep tableHash matchedHost 0 capA).isOk = true := by decide +kernel
example : aliceOut.seats.length = 2 ∧
    aliceOut.floorBook.balance (.user alice) 0 = 5 ∧
    aliceOut.floorBook.balance (.user alice) 1 = 200 ∧
    aliceOut.floorBook.balance (.seat 0) 0 = 0 ∧ aliceOut.floorBook.balance (.seat 0) 1 = 0 ∧
    aliceOut.floorBook.assetSum 0 = matchedHost.floorBook.assetSum 0 ∧
    aliceOut.floorBook.assetSum 1 = matchedHost.floorBook.assetSum 1 := by decide +kernel
-- Before the match she exits with her refund.
example : ((runZoe tableHash otcGuest threeHost [.exitSeat 0 capA]).floorBook.balance
    (.user alice) 0) = 100 := by decide +kernel
-- A wrong capability, a missing seat, a second exit and an exit before its deadline are refused.
example : exitSeatStep tableHash matchedHost 0 capWrong = .error .wrongHolder := by decide +kernel
example : exitSeatStep tableHash matchedHost 1 capA = .error .wrongHolder := by decide +kernel
example : exitSeatStep tableHash matchedHost 7 capA = .error .noSuchSeat := by decide +kernel
example : exitSeatStep tableHash aliceOut 0 capA = .error .noSuchSeat := by decide +kernel
example : exitSeatStep tableHash matchedHost 1 capB = .error .exitNotAllowed := by decide +kernel
example : ExitViolation tableHash matchedHost 1 capB :=
  (exitSeatStep_refused_iff _ _ _ _).mp ⟨_, (by decide +kernel :
    exitSeatStep tableHash matchedHost 1 capB = .error .exitNotAllowed)⟩

/-- Clock tokens are epoch specific and consumed; neither an outsider nor a replay advances time. -/
example : stepZoeHost tableHash otcGuest genesis (.advanceEpoch [99]) =
    .error .epochUnauthorized := by decide +kernel
example : (runZoe tableHash otcGuest genesis [.advanceEpoch [42], .advanceEpoch [42]]).epoch = 1 := by
  decide +kernel
example : stepZoeHost tableHash otcGuest initHost (.advanceEpoch [42]) =
    .error .epochUnauthorized := by rfl
/-- A stalled guest cannot suppress a holder's deadline refund once the clock authority ticks. -/
def refunded : ZoeHost := runZoe tableHash (fun _ => none) threeHost
  [.invokeGuestContract allSeats, .advanceEpoch [42], .advanceEpoch [43], .advanceEpoch [44],
   .advanceEpoch [45], .advanceEpoch [46], .exitSeat 1 capB]
example : refunded.floorBook.balance (.user bob) 1 = 200 ∧
    refunded.floorBook.balance (.user (seatOf 1)) 1 = 0 := by decide +kernel

#tooth Obend.Polis.ZoeSeatSettlement.advanceEpoch_authorized by mutation
  Obend.Polis.ZoeSeatSettlement.stepZoeHost := fun _ _ h _ => .ok { h with epoch := h.epoch + 1 }

/-- Offers, the match, an early exit that is refused, five epochs, then every seat exits. -/
def longTurns : List ZoeTurn :=
  mints ++ offers ++ [.invokeGuestContract allSeats, .exitSeat 1 capB, .advanceEpoch [42],
    .advanceEpoch [43], .advanceEpoch [44], .advanceEpoch [45], .advanceEpoch [46], .exitSeat 1 capB,
    .exitSeat 0 capA, .exitSeat 2 capC]
def settled : ZoeHost := runZoe tableHash otcGuest genesis longTurns

-- **Totals are conserved on exit**: every seat is empty, every party holds what it wanted, and
-- each asset's units are those of the genesis, account by account and over the whole book.
example : settled.seats = [] ∧ settled.holders = [] ∧ settled.epoch = 5 ∧
    settled.floorBook.balance (.user alice) 0 = 5 ∧
    settled.floorBook.balance (.user alice) 1 = 200 ∧
    settled.floorBook.balance (.user bob) 2 = 50 ∧
    settled.floorBook.balance (.user carol) 0 = 95 ∧
    (allSeats.map fun s => settled.seatBook.balance s 0) = [0, 0, 0] ∧
    settled.floorBook.assetSum 0 = genesis.floorBook.assetSum 0 ∧
    settled.floorBook.assetSum 1 = genesis.floorBook.assetSum 1 ∧
    settled.floorBook.assetSum 2 = genesis.floorBook.assetSum 2 := by decide +kernel

-- The same trace under the deployed hash, and the universal theorem on it: floors, totals,
-- offer safety and non-negative escrow, for this guest and for any other.
theorem settled_deployed : runZoe zoeHash otcGuest genesis longTurns = settled :=
  tableHash_eq ▸ rfl
example (guest : GuestContract) (turns : List ZoeTurn) (ast : AssetId) :
    FloorsHold (runZoe zoeHash guest genesis turns).floorBook ∧
      (runZoe zoeHash guest genesis turns).floorBook.assetSum ast =
        genesis.floorBook.assetSum ast :=
  have h := trace_invariant zoeHash guest turns genesis _
    (fundedHost_invariant _) ((validZoeTrace_iff_run _ _ _ _ _).mpr rfl)
  ⟨h.1.1, h.2.1 ast⟩

-- **Only the holder exits**, under the deployed hash: whatever capability exits Alice's seat is
-- hers, or cSHAKE256 collides.
example (cap : List UInt8) (f : ZoeHost) (he : exitSeatStep zoeHash matchedHost 0 cap = .ok f) :
    cap = capA ∨ Obend.Digest.HashBytes.CollisionAmong zoeHash
      (fun x => x = holderPreimage 0 cap ∨ x = holderPreimage 0 capA) :=
  exit_requires_holder_preimage zoeHash_length (by decide)
    (by rw [cA_eq]; decide +kernel) he
-- Exit pays the payee, by the universal theorem.
theorem matched_inv : ZoeInv matchedHost :=
  (trace_invariant _ _ _ _ _ threeHost_inv ((validZoeTrace_iff_run _ _ _ _ _).mpr rfl)).1
example (f : ZoeHost) (he : exitSeatStep tableHash matchedHost 0 capA = .ok f) :
    ∃ s ∈ matchedHost.seats, s.account = protectedBase + 0 ∧
      (∀ ast, f.floorBook.balance (addrOf s.account) ast = 0) ∧
      (∀ ast, f.floorBook.balance (addrOf s.payee) ast =
        matchedHost.floorBook.balance (addrOf s.payee) ast +
          matchedHost.floorBook.balance (addrOf s.account) ast) ∧
      (∀ t ∈ f.seats, t.account ≠ s.account) :=
  exit_pays_payee matched_inv he
-- A guest leaves every ordinary account alone.
example (f : ZoeHost) (he : reallocStep otcGuest threeHost allSeats = .ok f) (ast : AssetId) :
    f.floorBook.balance (addrOf bob) ast = threeHost.floorBook.balance (addrOf bob) ast :=
  (realloc_leaves_ordinary_untouched threeHost_inv he bob (by decide) ast).1

/-! ## 5. Teeth -/

-- Move the seat `Book` without asking the `FloorBook`: offers funded from thin air.
#tooth Obend.Polis.ZoeSeatSettlement.enterOffer_escrows by mutation
  Obend.Polis.ZoeSeatSettlement.postBoth := fun fb b ps => some (fb, applyPostings b ps)

-- Post the legs to the `FloorBook` with no amount.
#tooth Obend.Polis.ZoeSeatSettlement.postBoth_sound by mutation
  Obend.Polis.ZoeSeatSettlement.typedPosting := fun p =>
    ⟨addrOf p.source, addrOf p.destination, p.asset, 0⟩

-- Drop the ledger's donation guard.
#tooth Obend.Polis.ZoeSeatSettlement.enterOffer_donationUnmarked_refused by mutation
  Obend.Ledger.checkDonationGuard := fun _ => .ok ()

-- Let a guest move anything: no `checkBatchReallocSafe`, no restriction to the invoked seats.
#tooth Obend.Polis.ZoeSeatSettlement.realloc_leaves_ordinary_untouched by mutation
  Obend.Polis.ZoeSeatSettlement.reallocStep := fun guest h accts =>
    match guest (guestInput h accts) with
    | none => .error .guestDeclined
    | some r =>
      match postBoth h.floorBook h.seatBook r.postings with
      | none => .error .reallocFloorRefused
      | some (fb', b') => .ok { h with floorBook := fb', seatBook := b' }

-- Commit to the capability alone, without the seat it is for.
#tooth Obend.Polis.ZoeSeatSettlement.holderCommit_binding by mutation
  Obend.Polis.ZoeSeatSettlement.holderPreimage := fun _ cap => cap

-- Let every exit rule allow exit at once.
#tooth Obend.Polis.ZoeSeatSettlement.premature_exit_refused by mutation
  Obend.Polis.ZoeSeatSettlement.exitAllowed := fun _ _ => true

-- On a refused turn, reset the host instead of keeping it.
#tooth Obend.Polis.ZoeSeatSettlement.trace_invariant by mutation
  Obend.Polis.ZoeSeatSettlement.applyZoeTurn := fun H guest h t =>
    match stepZoeHost H guest h t with
    | .ok f => f
    | .error _ => initHost

-- Read a bundle's amount from its first entry only.
#tooth Obend.Polis.ZoeSeatSettlement.mergeAmounts_sum by mutation
  Obend.Polis.ZoeSeatSettlement.amountList := fun xs b =>
    match xs with
    | [] => 0
    | (k, v) :: _ => if k = b then v.toNat else 0

run_cmd do
  for name in [``reallocConservedValue, ``AssetBundle.addChecked, ``holderCommit_binding] do
    let dependencies ← Lean.Elab.Command.liftCoreM (Lean.collectAxioms name)
    if dependencies.contains ``Classical.choice then
      throwError "{name} depends on classical choice"

#print axioms zoe_offer_safety_unconditional
#print axioms enterOffer_escrows
#print axioms exit_requires_holder_preimage
#print axioms zoeStep_skip_implies_violation
#assert_axioms_tree

end Obend.Polis.ZoeSeatSettlement.Test
