module
public import Obend.Polis.ZoeSeatSettlement
import all Obend.Polis.ZoeSeatSettlement
import all Init.Data.List.Sort.Basic
import all Obend.Polis.CapTP
import all Obend.Logic.SeparationFrame
import Obend.Tactic.Tooth
import Obend.AssertAxioms

import all Obend.Apps.ZkNtt.Goldilocks
import all Obend.AssertAxioms
import all Obend.Core.Digest
import all Obend.Core.Term
import all Obend.Crypto.Multilinear
import all Obend.Crypto.Transcript
import all Obend.Digest.Cshake256
import all Obend.Digest.Cshake256.Fast
import all Obend.Digest.Cshake256.Seam
import all Obend.Digest.Cshake256.Spec
import all Obend.Digest.HashBytes
import all Obend.Judge.Class
import all Obend.Judge.Computational
import all Obend.Tactic.Tooth
import all Obend.Vault.Mandate
public section
namespace Obend.Polis.ZoeSeatSettlement.Test

set_option maxRecDepth 4096
set_option maxHeartbeats 800000
attribute [local simp] Canonical admitReallocation validStaging checkAssetConservation
  checkOfferSafety checkTotals support bundleTotal allocations stagedSeats updateStaging
  List.lookup offerSafeB AssetBundle.bundleLeq AssetBundle.amountOf CapTP.search
  ZoeSeat.currentAllocation activeId AssetBundle.singleton AssetBundle.empty AssetBundle.amountSpec
  amountList stepZoeHost applyZoeTurn guestInput exitSeats exitAllowed closeSeat
  totalAssets AssetBundle.addChecked mergeAmounts initHost enteredSeat
  stagingToConservedValue stagingDeltas normalizedDeltas DeltaNormalization.insert
  sortedDifference bundleEntries negateEntries zeroGroups List.mergeSort List.merge
  zeroGroups.eq_1 zeroGroups.eq_2 zeroGroups.eq_3
  mergeAmounts.eq_1 mergeAmounts.eq_2 mergeAmounts.eq_3


@[simp] def a100 : AssetBundle := .singleton 0 100 (by simp <;> first | rfl | decide)
@[simp] def a95 : AssetBundle := .singleton 0 95 (by simp <;> first | rfl | decide)
@[simp] def b200 : AssetBundle := .singleton 1 200 (by simp <;> first | rfl | decide)
@[simp] def c50 : AssetBundle := .singleton 2 50 (by simp <;> first | rfl | decide)
@[simp] def improved : AssetBundle := ⟨#[(0,5),(1,200)], by simp <;> first | rfl | decide⟩

@[simp] def aliceProposal : Proposal := ⟨a100,b200,.onDemand⟩
@[simp] def bobProposal : Proposal := ⟨b200,c50,.afterEpoch 5⟩
@[simp] def carolProposal : Proposal := ⟨c50,a95,.onDemand⟩
@[simp] def alice : ZoeSeat := ⟨0,101,aliceProposal,a100,.active,.empty⟩
@[simp] def bob : ZoeSeat := ⟨1,102,bobProposal,b200,.active,.empty⟩
@[simp] def carol : ZoeSeat := ⟨2,103,carolProposal,c50,.active,.empty⟩
@[simp] def threeHost : ZoeHost := ⟨[alice,bob,carol],[a100,b200,c50],0⟩
@[simp] def otcStaging : List (SeatId × AssetBundle) := [(0,improved),(1,c50),(2,a95)]
@[simp] def otcGuest : GuestContract := fun _ => some otcStaging

theorem three_offer_trace (guest : GuestContract) :
    ValidZoeTrace guest initHost
      [.enterOffer aliceProposal 101,.enterOffer bobProposal 102,.enterOffer carolProposal 103] threeHost :=
  .cons rfl (.cons rfl (.cons rfl (.nil threeHost)))

example : admitReallocation threeHost [0,1,2] otcStaging = true := by simp <;> first | rfl | decide
example : checkAssetConservation threeHost otcStaging = true := by simp <;> first | rfl | decide
example : checkOfferSafety threeHost otcStaging = true := by simp <;> first | rfl | decide

example : satisfiesWant aliceProposal improved :=
  (AssetBundle.bundleLeq_iff_forall_brand _ _).mp (by simp <;> first | rfl | decide)
example : satisfiesWant bobProposal c50 :=
  (AssetBundle.bundleLeq_iff_forall_brand _ _).mp (by simp <;> first | rfl | decide)
example : satisfiesWant carolProposal a95 :=
  (AssetBundle.bundleLeq_iff_forall_brand _ _).mp (by simp <;> first | rfl | decide)
example : improved.amountOf 0 = 5 := by simp <;> first | rfl | decide
example : improved.amountOf 1 = 200 := by simp <;> first | rfl | decide
example : totalAssets threeHost 0 = 100 ∧ totalAssets threeHost 1 = 200 ∧ totalAssets threeHost 2 = 50 := by simp <;> first | rfl | decide

example (brand : AssetBrand) :
    ∃ v : Obend.Logic.ConservedValue, ∀ q, Obend.Logic.deltaAt v.entries q =
      ((stagingDeltas threeHost.seats otcStaging brand).map (fun p => if q == p.1 then p.2 else 0)).sum :=
  conservation_bridges_separationFrame threeHost [0,1,2] otcStaging (by simp <;> first | rfl | decide) brand

/-- The witness records a real transfer of 95 units from seat 0 to seat 2. -/
example : (stagingToConservedValue threeHost [0,1,2] otcStaging (by simp <;> first | rfl | decide) 0).entries =
    [(0,-95),(2,95)] := by simp <;> first | rfl | decide

example : stepZoeHost otcGuest threeHost (.invokeGuestContract [0,1,2]) =
    some { threeHost with seats := stagedSeats threeHost otcStaging } := by simp <;> first | rfl | decide

@[simp] def matchedHost : ZoeHost := { threeHost with seats := stagedSeats threeHost otcStaging }

theorem matched_trace : ValidZoeTrace otcGuest initHost
    [.enterOffer aliceProposal 101,.enterOffer bobProposal 102,.enterOffer carolProposal 103,
     .invokeGuestContract [0,1,2]] matchedHost :=
  .cons rfl (.cons rfl (.cons rfl (.cons (by simp <;> first | rfl | decide) (.nil matchedHost))))

example : (stepZoeHost otcGuest matchedHost (.exitSeat 0 101)).isSome = true := by simp <;> first | rfl | decide
example : (stepZoeHost otcGuest matchedHost (.settleSeat 1 102)).isSome = true := by simp <;> first | rfl | decide
example : stepZoeHost otcGuest threeHost (.exitSeat 0 999) = none := by simp <;> first | rfl | decide

/-- An empty attacker offer makes the theft conserve assets while failing only offer safety. -/
@[simp] def attacker : ZoeSeat := ⟨1,201,⟨.empty,.empty,.onDemand⟩,.empty,.active,.empty⟩
@[simp] def attackHost : ZoeHost := ⟨[alice,attacker],[a100,.empty],0⟩
@[simp] def theft : List (SeatId × AssetBundle) := [(0,.empty),(1,a100)]
@[simp] def mint : List (SeatId × AssetBundle) := [(0,b200),(1,a100)]
@[simp] def evilGuest : GuestContract := fun _ => some theft
@[simp] def mintingGuest : GuestContract := fun _ => some mint

example : checkAssetConservation attackHost theft = true ∧ checkOfferSafety attackHost theft = false := by simp <;> first | rfl | decide
example : checkAssetConservation attackHost mint = false ∧ checkOfferSafety attackHost mint = true := by simp <;> first | rfl | decide
example : stepZoeHost evilGuest attackHost (.invokeGuestContract [0,1]) = none := by simp <;> first | rfl | decide
example : stepZoeHost mintingGuest attackHost (.invokeGuestContract [0,1]) = none := by simp <;> first | rfl | decide
example : applyZoeTurn evilGuest attackHost (.invokeGuestContract [0,1]) = attackHost := by simp <;> first | rfl | decide
example : applyZoeTurn mintingGuest attackHost (.invokeGuestContract [0,1]) = attackHost := by simp <;> first | rfl | decide
example : (applyZoeTurn evilGuest attackHost (.invokeGuestContract [0,1])).seats.head?.map
    (fun s => (s.status,s.escrowed.amountOf 0)) = some (.active,100) := by simp <;> first | rfl | decide
example : (stepZoeHost evilGuest attackHost (.exitSeat 0 101)).isSome = true := by simp <;> first | rfl | decide
example : (stepZoeHost mintingGuest attackHost (.exitSeat 0 101)).isSome = true := by simp <;> first | rfl | decide

@[simp] def maxA : AssetBundle := .singleton 0 18446744073709551615 (by simp <;> first | rfl | decide)
@[simp] def oneA : AssetBundle := .singleton 0 1 (by simp <;> first | rfl | decide)
@[simp] theorem checked_overflow : maxA.addChecked oneA = none := by
  have hm : mergeAmounts maxA.entries.toList oneA.entries.toList = none := by
    change mergeAmounts [(0,18446744073709551615)] [(0,1)] = none
    rw [mergeAmounts]
    decide
  unfold AssetBundle.addChecked
  split
  · rfl
  · rename_i zs hz
    rw [hm] at hz
    contradiction

@[simp] def overflowGuest : GuestContract := fun _ =>
  (maxA.addChecked oneA).map (fun a => [(0,a),(1,.empty)])

example : maxA.addChecked oneA = none := checked_overflow
theorem overflow_rejected : stepZoeHost overflowGuest attackHost (.invokeGuestContract [0,1]) = none := by
  simp only [stepZoeHost, overflowGuest, checked_overflow, Option.map_none, bind, Option.bind]
example : applyZoeTurn overflowGuest attackHost (.invokeGuestContract [0,1]) = attackHost :=
  rejected_staging_atomic _ _ _ overflow_rejected
example : (stepZoeHost overflowGuest attackHost (.exitSeat 0 101)).isSome = true := by simp <;> first | rfl | decide

/-- Exact totals also reject a guest that exploits a wrapping aggregate, even though
both input bundles are individually representable and both seats allow refunds or wants. -/
@[simp] def wideHost : ZoeHost :=
  ⟨[⟨0,301,⟨maxA,.empty,.onDemand⟩,maxA,.active,.empty⟩,
    ⟨1,302,⟨oneA,.empty,.onDemand⟩,oneA,.active,.empty⟩],[maxA,oneA],0⟩
@[simp] def burnWrapped : List (SeatId × AssetBundle) := [(0,.empty),(1,.empty)]
example : totalAssets wideHost 0 = 18446744073709551616 := by simp <;> first | rfl | decide
example : checkOfferSafety wideHost burnWrapped = true ∧
    checkAssetConservation wideHost burnWrapped = false := by simp <;> first | rfl | decide
example : admitReallocation wideHost [0,1] burnWrapped = false := by simp <;> first | rfl | decide

example : admitReallocation attackHost [0,1] [(0,a100),(0,.empty),(1,.empty)] = false := by simp <;> first | rfl | decide
example : admitReallocation attackHost [0,0,1] [(0,a100),(1,.empty)] = false := by simp <;> first | rfl | decide
example : admitReallocation attackHost [0,2] [(0,a100),(2,.empty)] = false := by simp <;> first | rfl | decide

@[simp] def exitedAliceHost : ZoeHost :=
  { attackHost with seats := [closeSeat false alice,attacker] }
example : stepZoeHost evilGuest attackHost (.exitSeat 0 101) = some exitedAliceHost := by simp <;> first | rfl | decide
example : stepZoeHost evilGuest exitedAliceHost (.exitSeat 0 101) = none := by simp <;> first | rfl | decide
example : admitReallocation exitedAliceHost [0,1] [(0,a100),(1,.empty)] = false := by simp <;> first | rfl | decide
example : totalAssets exitedAliceHost 0 = 100 := by simp <;> first | rfl | decide

@[simp] def waivedHost : ZoeHost :=
  { attackHost with seats := [{ alice with proposal := { aliceProposal with exitRule := .waived } },attacker] }
example : stepZoeHost evilGuest waivedHost (.exitSeat 0 101) = none := by simp <;> first | rfl | decide
example : stepZoeHost otcGuest { threeHost with epoch := 3 } (.exitSeat 1 102) = none := by simp <;> first | rfl | decide
example : (stepZoeHost otcGuest { threeHost with epoch := 5 } (.exitSeat 1 102)).isSome = true := by simp <;> first | rfl | decide
example : (stepZoeHost otcGuest threeHost (.exitSeat 0 101)).isSome = true := by simp <;> first | rfl | decide

/-- Rejection, advancing epochs, an early refused exit, then an allowed payout all
occur in one trace; deposits and terminal payouts remain in the accounting. -/
@[simp] def longTurns : List ZoeTurn :=
  [.enterOffer aliceProposal 101,.enterOffer bobProposal 102,.enterOffer carolProposal 103,
   .invokeGuestContract [0,1,2],.exitSeat 1 102,.advanceEpoch,.advanceEpoch,.advanceEpoch,
   .advanceEpoch,.advanceEpoch,.exitSeat 1 102,.exitSeat 0 101,.settleSeat 2 103]

@[simp] def runTurns (guest : GuestContract) : ZoeHost → List ZoeTurn → ZoeHost
  | h, [] => h
  | h, t :: ts => runTurns guest (applyZoeTurn guest h t) ts

theorem runTurns_valid (guest : GuestContract) (h : ZoeHost) (ts : List ZoeTurn) :
    ValidZoeTrace guest h ts (runTurns guest h ts) := by
  induction ts generalizing h with
  | nil => exact .nil h
  | cons t ts ih => exact .cons rfl (ih _)

example : (runTurns otcGuest initHost longTurns).seats.map ZoeSeat.status = [.exited,.exited,.settled] := by simp <;> first | rfl | decide
example : totalAssets (runTurns otcGuest initHost longTurns) 0 = 100 ∧
    totalAssets (runTurns otcGuest initHost longTurns) 1 = 200 ∧
    totalAssets (runTurns otcGuest initHost longTurns) 2 = 50 := by simp <;> first | rfl | decide

example (guest : GuestContract) (ts : List ZoeTurn) (b : AssetBrand) :
    totalAssets (runTurns guest initHost ts) b = bundleTotal (runTurns guest initHost ts).deposits b :=
  (zoe_offer_safety_unconditional guest ts _ (runTurns_valid guest initHost ts)).1 b

#tooth admitReallocation_sound by mutation admitReallocation :=
  fun h ids ps => validStaging h ids ps && (checkAssetConservation h ps || checkOfferSafety h ps)

#tooth offerSafeB_iff by mutation offerSafeB :=
  fun s => s.proposal.want.bundleLeq s.currentAllocation && s.proposal.give.bundleLeq s.currentAllocation

#tooth checkTotals_iff by mutation checkTotals :=
  fun xs ys => (support xs ++ support ys).all (fun b =>
    decide (UInt64.ofNat (bundleTotal xs b) = UInt64.ofNat (bundleTotal ys b)))

#tooth waived_exit_refused by mutation exitAllowed :=
  fun rule epoch => match rule with
    | .onDemand => true
    | .waived => true
    | .afterEpoch deadline => decide (deadline ≤ epoch)

#tooth admitReallocation_sound by mutation validStaging :=
  fun h ids ps => decide ids.Nodup && ids.all (activeId h) &&
    ids.all (fun id => (ps.map Prod.fst).contains id) && ps.all (fun p => ids.contains p.1)

run_cmd do
  for name in [``stagingToConservedValue, ``AssetBundle.addChecked] do
    let dependencies ← Lean.Elab.Command.liftCoreM (Lean.collectAxioms name)
    if dependencies.contains ``Classical.choice then
      throwError "Computational witness {name} depends on classical choice"

#print axioms stagingToConservedValue
#print axioms AssetBundle.addChecked
#print axioms zoe_offer_safety_unconditional
#print axioms onDemand_exit_guaranteed_before_commit
#print axioms zoeStep_skip_implies_violation
#assert_axioms_tree

end Obend.Polis.ZoeSeatSettlement.Test
