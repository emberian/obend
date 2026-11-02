import Obend.Ledger.Seat
import Obend.Ledger.Vault
import Obend.Run.Durable
import Obend.Run.DurableExample
import Obend.Run.Shared
import Obend.Run.Fork
import Obend.Slot.Selection
import Obend.Tactic.Tooth

/-!
# `tests/metasystem/DurableHostAndZoeSeatTest.lean` — Metasystem Regression & Verification Suite (`WS-O`)

Exercises all concrete Lean deliverables for `WS-O`:
1. Multi-Seat Atomic Batch Swap with Proved ZoE Offer Safety & Conservation
   (`BatchRealloc`, `checkBatchReallocSafe`, `applyBatchRealloc`,
   `batchRealloc_preserves_all_seats_offer_safe`, `batchRealloc_zero_sum_conservation`,
   `batchRealloc_disjoint_from_ordinary_accounts`, `settleVaultSeats`, `settleVaultSeats_sound`).
2. Idempotent Multi-Crash Recovery & Outbox Linearizability
   (`runDurableTrace`, `crash_recover_idempotent`, `pending_decreases_on_expose`).
3. Cost-Ordered / Priority-Monotone Selection Policy
   (`prioritySelect`, `priorityAdvance`, `priorityAdvance_sound`, `priorityAdvance_monotone`).
-/

namespace Obend.Tests.DurableHostAndZoeSeatTest

open Obend.Ledger
open Obend.Slot
open Obend.Slot.World
open Obend.Slot.Protocol
open Obend.Slot.Protocol.Negotiation
open Obend.Run.Control
open Obend.Run.Shared
open Obend.Run.Durable
open Obend.Run.SharedExample
open Obend.Run.DurableExample
open Obend.Run.Negotiation (Wv host O₀ ctl au stored₀ NCand commitOp)

-- ============================================================================
-- 1. Multi-Seat Atomic Batch Swap (`BatchRealloc`, `checkBatchReallocSafe`)
-- ============================================================================

def assetUsdc : AssetId := 1
def assetEth  : AssetId := 2
def assetBtc  : AssetId := 3

def ordinaryAlice : AccountId := 100
def ordinaryBob   : AccountId := 200

def seat1Acc : AccountId := protectedBase + 1
def seat2Acc : AccountId := protectedBase + 2
def seat3Acc : AccountId := protectedBase + 3

-- Seat 1 gives 100 USDC, wants 10 ETH
def seat1 : Seat :=
  { account := seat1Acc
  , payee := ordinaryAlice
  , proposal :=
      { give := [(assetUsdc, 100)]
      , want := [(assetEth, 10)]
      , exit := .onDemand
      , donate := false } }

-- Seat 2 gives 10 ETH, wants 2 BTC
def seat2 : Seat :=
  { account := seat2Acc
  , payee := ordinaryBob
  , proposal :=
      { give := [(assetEth, 10)]
      , want := [(assetBtc, 2)]
      , exit := .onDemand
      , donate := false } }

-- Seat 3 gives 2 BTC, wants 100 USDC
def seat3 : Seat :=
  { account := seat3Acc
  , payee := 300
  , proposal :=
      { give := [(assetBtc, 2)]
      , want := [(assetUsdc, 100)]
      , exit := .onDemand
      , donate := false } }

def activeSeats : List Seat := [seat1, seat2, seat3]

def initialEscrowBook : Book where
  accounts := [ordinaryAlice, ordinaryBob, 300, seat1Acc, seat2Acc, seat3Acc]
  balances := fun acc ast =>
    if acc == ordinaryAlice && ast == assetUsdc then 500
    else if acc == ordinaryBob && ast == assetEth then 50
    else if acc == seat1Acc && ast == assetUsdc then 100
    else if acc == seat2Acc && ast == assetEth then 10
    else if acc == seat3Acc && ast == assetBtc then 2
    else 0
  leaseRecords := fun _ => none
  floors := fun _ _ => 0

-- Valid 3-way circular ZoE swap satisfying every seat's `want` with zero-sum conservation
def valid3WaySwap : BatchRealloc :=
  { postings :=
      [ ⟨seat1Acc, seat3Acc, assetUsdc, 100⟩
      , ⟨seat2Acc, seat1Acc, assetEth, 10⟩
      , ⟨seat3Acc, seat2Acc, assetBtc, 2⟩ ] }

-- Invalid swap that violates Seat 1's offer safety (takes 100 USDC from Seat 1 but gives only 5 ETH < 10 ETH want)
def unsafeSwap : BatchRealloc :=
  { postings :=
      [ ⟨seat1Acc, seat3Acc, assetUsdc, 100⟩
      , ⟨seat2Acc, seat1Acc, assetEth, 5⟩
      , ⟨seat3Acc, seat2Acc, assetBtc, 2⟩ ] }

-- Invalid swap that touches an ordinary account (`ordinaryAlice < protectedBase`)
def unauthorizedOrdinaryTouchSwap : BatchRealloc :=
  { postings :=
      [ ⟨ordinaryAlice, seat1Acc, assetUsdc, 100⟩ ] }

-- Positive pole: `valid3WaySwap` passes `checkBatchReallocSafe` and `settleVaultSeats`
#guard checkBatchReallocSafe initialEscrowBook activeSeats valid3WaySwap == true
#guard (settleVaultSeats initialEscrowBook activeSeats valid3WaySwap).isSome == true

-- Negative poles: `unsafeSwap`, `unauthorizedOrdinaryTouchSwap`, and duplicate seat accounts are strictly refused
def duplicateSeats : List Seat := [seat1, seat1, seat2, seat3]

#guard checkBatchReallocSafe initialEscrowBook activeSeats unsafeSwap == false
#guard checkBatchReallocSafe initialEscrowBook activeSeats unauthorizedOrdinaryTouchSwap == false
#guard checkBatchReallocSafe initialEscrowBook duplicateSeats valid3WaySwap == false
#guard (settleVaultSeats initialEscrowBook activeSeats unsafeSwap).isNone == true
#guard (settleVaultSeats initialEscrowBook duplicateSeats valid3WaySwap).isNone == true

theorem test_unsafe_swap_rejected :
    checkBatchReallocSafe initialEscrowBook activeSeats unsafeSwap = false := rfl

#tooth test_unsafe_swap_rejected by mutation
  checkBatchReallocSafe := fun _ _ _ => true

-- Instantiate `batchRealloc_nodup_seats`, `batchRealloc_preserves_all_seats_offer_safe`, and `batchRealloc_zero_sum_all_assets`:
example : (activeSeats.map Seat.account).Nodup :=
  batchRealloc_nodup_seats initialEscrowBook activeSeats valid3WaySwap rfl

example :
    ∀ s ∈ activeSeats,
      safeAt (applyBatchRealloc initialEscrowBook valid3WaySwap) s.account s.proposal = true :=
  batchRealloc_preserves_all_seats_offer_safe initialEscrowBook activeSeats valid3WaySwap rfl

example (ast : AssetId) :
    batchTotalCredits activeSeats valid3WaySwap ast = batchTotalDebits activeSeats valid3WaySwap ast :=
  batchRealloc_zero_sum_all_assets initialEscrowBook activeSeats valid3WaySwap rfl ast

-- Instantiate `batchRealloc_disjoint_from_ordinary_accounts` on `ordinaryAlice`:
example (ast : AssetId) :
    (applyBatchRealloc initialEscrowBook valid3WaySwap).balance ordinaryAlice ast =
      initialEscrowBook.balance ordinaryAlice ast :=
  batchRealloc_disjoint_from_ordinary_accounts
    initialEscrowBook activeSeats valid3WaySwap rfl ordinaryAlice (by decide) ast

-- Verify ordinary account balances are untouched executable check:
#guard (applyBatchRealloc initialEscrowBook valid3WaySwap).balance ordinaryAlice assetUsdc == 500
#guard (applyBatchRealloc initialEscrowBook valid3WaySwap).balance ordinaryBob assetEth == 50

-- Instantiate `settleVaultSeats_sound` and `settleVaultSeats_conserves`:
example (b' : Book) (h : settleVaultSeats initialEscrowBook activeSeats valid3WaySwap = some b') :
    b' = applyBatchRealloc initialEscrowBook valid3WaySwap ∧
    checkBatchReallocSafe initialEscrowBook activeSeats valid3WaySwap = true ∧
    (∀ s ∈ activeSeats, safeAt b' s.account s.proposal = true) ∧
    (∀ ast ∈ batchAssets activeSeats valid3WaySwap,
      batchTotalCredits activeSeats valid3WaySwap ast = batchTotalDebits activeSeats valid3WaySwap ast) ∧
    (∀ ordinary, ordinary < protectedBase → ∀ ast, b'.balance ordinary ast = initialEscrowBook.balance ordinary ast) :=
  settleVaultSeats_sound initialEscrowBook b' activeSeats valid3WaySwap h

example (b' : Book) (h : settleVaultSeats initialEscrowBook activeSeats valid3WaySwap = some b') :
    (activeSeats.map Seat.account).Nodup ∧
    (∀ ast : AssetId, batchTotalCredits activeSeats valid3WaySwap ast = batchTotalDebits activeSeats valid3WaySwap ast) ∧
    (∀ (_h_reg : ∀ s ∈ activeSeats, s.account ∈ initialEscrowBook.accounts) (_hnodup : initialEscrowBook.accounts.Nodup) (ast : AssetId),
      b'.totalAsset ast = initialEscrowBook.totalAsset ast) :=
  settleVaultSeats_conserves initialEscrowBook b' activeSeats valid3WaySwap h

-- ============================================================================
-- 2. Idempotent Multi-Crash Recovery & Outbox Linearizability (`Run/Durable`)
-- ============================================================================

abbrev HostSt := DState nledger sig HoleN Res Unit Unit NCand Negotiation.Fact Ob .idle

def initHostState : HostSt := DState.init nledger J₀

def preCrashEvents : List HEv :=
  submitAll (reserve .alice ++ reserve .bob) ++
    [.submit (.dispatch .alice (commitOp .p1))]

def stateBeforeExpose : HostSt :=
  runDurableTrace nledger base (fun _ => spec) (fun _ => au) (fun _ => ctl) J₀ initHostState preCrashEvents

-- Before exposing position 4, pending effects are `[0, 2, 4]` and outbox is `[]`.
#guard pending nledger stateBeforeExpose == [0, 2, 4]
#guard stateBeforeExpose.outbox == []

-- Expose position 4 and verify `pending_decreases_on_expose`:
def stateAfterExpose : HostSt :=
  runDurableTrace nledger base (fun _ => spec) (fun _ => au) (fun _ => ctl) J₀ stateBeforeExpose [.expose 4]

#guard pending nledger stateAfterExpose == [0, 2]
#guard stateAfterExpose.outbox == [4]
#guard (pending nledger stateAfterExpose).length < (pending nledger stateBeforeExpose).length

example (s' : HostSt)
    (h : hstep nledger base (fun _ => spec) (fun _ => au) (fun _ => ctl) J₀ stateBeforeExpose (.expose 4) = .ok s') :
    s'.journal = stateBeforeExpose.journal ∧
    s'.mem = stateBeforeExpose.mem ∧
    s'.outbox = stateBeforeExpose.outbox ++ [4] ∧
    4 ∈ pending nledger stateBeforeExpose ∧
    4 ∉ pending nledger s' ∧
    pending nledger s' = (pending nledger stateBeforeExpose).filter (fun m => m != 4) ∧
    (pending nledger s').length < (pending nledger stateBeforeExpose).length :=
  pending_decreases_on_expose nledger base (fun _ => spec) (fun _ => au) (fun _ => ctl) J₀ stateBeforeExpose s' 4 h

-- Instantiate `crash_recover_idempotent` for any `crashes ≥ 1`:
example (s : HostSt) (crashes : Nat) (hc : 1 ≤ crashes) :
    let trace : List HEv := List.replicate crashes .crash ++ [.recover]
    let single : List HEv := [.crash, .recover]
    runDurableTrace nledger base (fun _ => spec) (fun _ => au) (fun _ => ctl) J₀ s trace =
      runDurableTrace nledger base (fun _ => spec) (fun _ => au) (fun _ => ctl) J₀ s single ∧
    (runDurableTrace nledger base (fun _ => spec) (fun _ => au) (fun _ => ctl) J₀ s trace).journal = s.journal ∧
    (runDurableTrace nledger base (fun _ => spec) (fun _ => au) (fun _ => ctl) J₀ s trace).outbox = s.outbox :=
  crash_recover_idempotent nledger base (fun _ => spec) (fun _ => au) (fun _ => ctl) J₀ s crashes hc

-- Executable check that 5 consecutive crashes + recover equals 1 crash + recover:
def stateAfter1CrashRecover : HostSt :=
  runDurableTrace nledger base (fun _ => spec) (fun _ => au) (fun _ => ctl) J₀ stateAfterExpose [.crash, .recover]

def stateAfter5CrashesRecover : HostSt :=
  runDurableTrace nledger base (fun _ => spec) (fun _ => au) (fun _ => ctl) J₀ stateAfterExpose
    (List.replicate 5 .crash ++ [.recover])

#guard stateAfter5CrashesRecover.outbox == stateAfter1CrashRecover.outbox
#guard pending nledger stateAfter5CrashesRecover == pending nledger stateAfter1CrashRecover
#guard stateAfter5CrashesRecover.mem.isSome == true

-- ============================================================================
-- 3. Cost-Ordered / Priority-Monotone Selection Policy (`Slot/Selection`)
-- ============================================================================

def memberCost : Member → Nat
  | .alice => 50
  | .bob   => 10

def testOrder : List Member := [.alice, .bob]

-- At height 0, both `.alice` and `.bob` are usable in `toySlot`, and `.bob` has lower cost (10 < 50):
example : prioritySelect toySlot (holdsAt (V := Nat) 0) testOrder memberCost = .ok .bob := rfl
#guard match prioritySelect toySlot (holdsAt (V := Nat) 0) testOrder memberCost with | .ok .bob => true | _ => false

-- If `.alice` (cost 50) is currently stored at height 0, `priorityAdvance memberCost` upgrades to `.bob` (cost 10):
example : (priorityAdvance memberCost).advance toySlot 0 testOrder (some .alice) = .ok .bob := rfl
#guard match (priorityAdvance memberCost).advance toySlot 0 testOrder (some .alice) with | .ok .bob => true | _ => false

-- If `.bob` (cost 10) is currently stored at height 0, `priorityAdvance memberCost` keeps `.bob`:
example : (priorityAdvance memberCost).advance toySlot 0 testOrder (some .bob) = .ok .bob := rfl
#guard match (priorityAdvance memberCost).advance toySlot 0 testOrder (some .bob) with | .ok .bob => true | _ => false

-- At height 1, `.alice` is retired, so `priorityAdvance` selects `.bob`:
example : (priorityAdvance memberCost).advance toySlot 1 testOrder (some .alice) = .ok .bob := rfl
#guard match (priorityAdvance memberCost).advance toySlot 1 testOrder (some .alice) with | .ok .bob => true | _ => false

-- Instantiate `priorityAdvance_sound` both with default cost and explicit `memberCost`:
example : SelectionSound (priorityAdvance : Advance Nat Member Member) :=
  priorityAdvance_sound

example : SelectionSound (priorityAdvance memberCost : Advance Nat Member Member) :=
  priorityAdvance_sound

-- Instantiate `priorityAdvance_monotone`:
example (c : Member)
    (h : (priorityAdvance memberCost).advance toySlot 0 testOrder (some .alice) = .ok c) :
    memberCost c ≤ memberCost .alice :=
  priorityAdvance_monotone toySlot 0 testOrder .alice c rfl h

-- ============================================================================
-- 4. Axiom Audit (`0 sorryAx`)
-- ============================================================================

#print axioms batchRealloc_nodup_seats
#print axioms batchRealloc_preserves_all_seats_offer_safe
#print axioms batchRealloc_zero_sum_conservation
#print axioms batchRealloc_zero_sum_all_assets
#print axioms batchRealloc_disjoint_from_ordinary_accounts
#print axioms batchRealloc_conserves
#print axioms settleVaultSeats_sound
#print axioms settleVaultSeats_conserves
#print axioms crash_recover_idempotent
#print axioms pending_decreases_on_expose
#print axioms prioritySelect_ok
#print axioms priorityAdvance_sound
#print axioms priorityAdvance_monotone

end Obend.Tests.DurableHostAndZoeSeatTest
