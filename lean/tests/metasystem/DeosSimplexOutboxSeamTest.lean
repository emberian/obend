module
/-
# DeosSimplexOutboxSeamTest — the settlement, consensus and outbox seam, end to end

One file across the modules that used to disagree at their edges:

1. `Polis.JointCoReceipt` on the `FloorBook`: a duplicated vat, an unbound `pre` and an overdraft
   are each refused.
2. `Polis.ZoeSeatSettlement` on `Ledger.Seat` + `FloorBook`: an unescrowed offer, an under-funded
   offer and an unmarked donation are each refused; match and exit conserve the book.
3. A real 256-bit `IrreversibleOutbox` commitment (cSHAKE256, above `2 ^ 64`) is proposed in a
   four-validator committee with one Byzantine member, signed by the three honest validators under
   their slot keys, finalized on an adversarial timed trace, dispatched once by a
   `DurableSimplexHost`, and refused on replay after crashes; a forged Byzantine signature is
   refused, and any accepted forgery would be a cSHAKE256 collision.

Every `decide` below is `decide +kernel`: the kernel runs cSHAKE256 itself.
-/

public import Obend.Vault.UnifiedDeos
public import Obend.Consensus.SimplexLiveness
public import Obend.Tactic.Tooth
public import Obend.Polis.JointCoReceipt
import all Obend.Polis.JointCoReceipt
meta import all Obend.Polis.JointCoReceipt
meta import all Obend.Ledger.Floors
public import Obend.Ledger.Seat
import all Obend.Ledger.Seat
import all Obend.Ledger.Book
import all Obend.Ledger.Seat
import all Obend.Ledger.Register
import all Obend.Consensus.Simplex
import all Obend.Consensus.SimplexProtocol
import all Obend.Consensus.SimplexTrace
import all Obend.Consensus.SimplexLiveness
import all Obend.Consensus.Finality
import all Obend.Vault.IrreversibleOutbox
import all Obend.Vault.UnifiedDeos
import all Obend.Trailblaze.Polis
import all Obend.Trailblaze.PolisBlum
import all Obend.Trailblaze.Obligations
import all Obend.Judge.Computational
import all Obend.Digest.HashBytes
import all Obend.Digest.Cshake256.Spec
import all Obend.Digest.Cshake256.Fast
import all Obend.Digest.Cshake256.Seam

public section
namespace Obend.Tests.DeosSimplexOutboxSeam

set_option autoImplicit false
set_option maxRecDepth 100000

-- SEAM-SECTION-1-COREICEPT-BEGIN
/-! ## 1. Joint co-receipts on the floor book -/

namespace CoReceipt

open Obend.Polis
open Obend.Polis.JointCoReceipt
open Obend.Ledger (FloorBook FloorsHold floorsHold_empty)

/-- Receipts over one forest: every leg names the forest's digest. -/
def sealTurn (raw : List LocalTurn) : ByteArray × List LocalTurn :=
  (turnDigest raw, raw.map fun t => { t with turnId := turnDigest raw })

/-- Vats 0 and 1 each hold ten units of asset 0, issued from its well. -/
def book0 : FloorBook :=
  (FloorBook.empty.applyRaw ⟨.issuerWell 0, .user 0, 0, 10⟩).applyRaw ⟨.issuerWell 0, .user 1, 0, 10⟩

def ledger0 : LedgerState := ⟨book0, 0, RevokedSet.empty, 0⟩

theorem floorsHold_book0 : FloorsHold book0 :=
  (FloorBook.admitBatch_preserves_floors (fb := .empty) (fb' := book0)
    [⟨.issuerWell 0, .user 0, 0, 10⟩, ⟨.issuerWell 0, .user 1, 0, 10⟩] floorsHold_empty
    (by decide)).1

/-- Vat 0 pays vat 1 one unit. -/
def turn1Raw : List LocalTurn :=
  [⟨0, .empty, .empty, 10, -1, 9, 0, 0, 0⟩, ⟨1, .empty, .empty, 10, 1, 11, 0, 0, 0⟩]
/-- On the ledger the first turn leaves, vat 1 pays four back. -/
def turn2Raw : List LocalTurn :=
  [⟨0, .empty, .empty, 9, 4, 13, 0, 0, 0⟩, ⟨1, .empty, .empty, 11, -4, 7, 0, 0, 0⟩]
/-- Vat 0 named twice. Each leg is valid, each `pre` is the ledger's, the half-edges sum to zero. -/
def dupVatRaw : List LocalTurn :=
  [⟨0, .empty, .empty, 10, -1, 9, 0, 0, 0⟩, ⟨0, .empty, .empty, 10, -1, 9, 0, 0, 0⟩, ⟨1, .empty, .empty, 10, 2, 12, 0, 0, 0⟩]
/-- Vat 0 says it held a thousand. A joint turn on its own; only the ledger knows better. -/
def unboundPreRaw : List LocalTurn :=
  [⟨0, .empty, .empty, 1000, -900, 100, 0, 0, 0⟩, ⟨1, .empty, .empty, 10, 900, 910, 0, 0, 0⟩]
/-- Vat 0 pays eleven of its ten. -/
def overdraftRaw : List LocalTurn :=
  [⟨0, .empty, .empty, 10, -11, -1, 0, 0, 0⟩, ⟨1, .empty, .empty, 10, 11, 21, 0, 0, 0⟩]

def stepSealed (raw : List LocalTurn) : Option LedgerState :=
  stepJoint 2 ledger0 (sealTurn raw).1 (sealTurn raw).2

-- Executed (compiled cSHAKE256): two turns move the book, and each exploit is refused by the
-- check it breaks while its honest neighbour is applied.
#guard ((runTrace 2 ledger0 [sealTurn turn1Raw, sealTurn turn2Raw]).map fun s =>
  (s.balances 0, s.balances 1, total (List.range 2) s.balances, s.book.assetSum 0)) ==
    some (13, 7, 20, 0)
#guard (runTrace 2 ledger0 [sealTurn turn1Raw, sealTurn turn1Raw]).isNone
#guard (runTrace 2 ledger0 [sealTurn turn2Raw]).isNone
#guard ((stepSealed [⟨0, .empty, .empty, 10, -2, 8, 0, 0, 0⟩, ⟨1, .empty, .empty, 10, 2, 12, 0, 0, 0⟩]).map fun s =>
  (s.balances 0, s.balances 1)) == some (8, 12)
#guard (stepSealed dupVatRaw).isNone
#guard !vatsDistinct (sealTurn dupVatRaw).2
#guard (stepSealed unboundPreRaw).isNone
#guard checkJoint (sealTurn unboundPreRaw).1 (sealTurn unboundPreRaw).2
#guard !stepOk 2 ledger0 (sealTurn unboundPreRaw).1 (sealTurn unboundPreRaw).2
#guard (stepSealed overdraftRaw).isNone
#guard !(sealTurn overdraftRaw).2.all (·.valid)

theorem map_seal {β : Type} (d : ByteArray) (f : LocalTurn → β)
    (hf : ∀ t : LocalTurn, f { t with turnId := d } = f t) (raw : List LocalTurn) :
    (raw.map fun t => { t with turnId := d }).map f = raw.map f := by
  rw [List.map_map]
  exact List.map_congr_left fun t _ => hf t

/-- Receipts stamped with the turn id `d`. -/
def sealWith (d : ByteArray) (raw : List LocalTurn) : List LocalTurn :=
  raw.map fun t => { t with turnId := d }

theorem map_sealWith {β : Type} (d : ByteArray) (f : LocalTurn → β)
    (hf : ∀ t : LocalTurn, f { t with turnId := d } = f t) (raw : List LocalTurn) :
    (sealWith d raw).map f = raw.map f := map_seal d f hf raw

/-- Stamped receipts are a joint turn under the digest of their legs whenever the legs are valid,
distinct and balanced. The digest stays a variable: no hash is evaluated. -/
theorem checkJoint_sealWith (d : ByteArray) (raw : List LocalTurn) (hd' : d = turnDigest raw)
    (hv : ∀ t, t ∈ raw → t.valid = true) (hd : (raw.map (·.vat)).Nodup)
    (hb : (raw.map (·.half)).sum = 0) : checkJoint d (sealWith d raw) = true := by
  have h1 : ∀ t ∈ sealWith d raw, t.valid = true := by
    intro t ht
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 ht
    have := hv u hu
    unfold LocalTurn.valid at this ⊢
    exact this
  have h2 : vatsDistinct (sealWith d raw) = true := by
    rw [vatsDistinct_iff, map_sealWith d (·.vat) (fun _ => rfl)]
    exact hd
  have h3 : ∀ t ∈ sealWith d raw, t.turnId = d := by
    intro t ht
    obtain ⟨u, _, rfl⟩ := List.mem_map.1 ht
    rfl
  have h4 : d = turnDigest (sealWith d raw) := by
    unfold turnDigest
    rw [map_sealWith d LocalTurn.legBytes (fun t => by unfold LocalTurn.legBytes; rfl)]
    exact hd'
  have h5 : ((sealWith d raw).map (·.half)).sum = 0 := by
    rw [map_sealWith d (·.half) (fun _ => rfl)]
    exact hb
  unfold checkJoint
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩

/-- Sealed receipts are a joint turn whenever the legs are: no hash is evaluated. -/
theorem sealTurn_checks (raw : List LocalTurn) (hv : ∀ t, t ∈ raw → t.valid = true)
    (hd : (raw.map (·.vat)).Nodup) (hb : (raw.map (·.half)).sum = 0) :
    checkJoint (sealTurn raw).1 (sealTurn raw).2 = true :=
  checkJoint_sealWith (turnDigest raw) raw rfl hv hd hb

/-- **The honest turn is applied, in the kernel**: the guard holds on `ledger0`, the step is
complete, the vats hold their receipts' `post`, and the book's floors still hold. -/
theorem turn1_applies : ∃ s', stepSealed turn1Raw = some s' ∧ s'.balances 0 = 9 ∧
    s'.balances 1 = 11 ∧ FloorsHold s'.book := by
  have hj := sealTurn_checks turn1Raw (by decide) (by decide) (by decide)
  have hnew : ledger0.seen.contains (turnKey (sealTurn turn1Raw).1) = false :=
    Bool.eq_false_iff.2 fun h => by
      simpa [ledger0, RevokedSet.empty] using (RevokedSet.contains_iff _ _).1 h
  have hpre : (sealTurn turn1Raw).2.all
      (fun t => decide (t.vat < 2) && decide (t.pre = ledger0.balances t.vat)) = true := by decide
  have hdomain : (sealTurn turn1Raw).2.all
      (fun t => decide (t.asset = ledger0.asset ∧ t.epoch = ledger0.epoch)) = true := by decide
  obtain ⟨s', hs⟩ := stepJoint_complete (s := ledger0) floorsHold_book0
    (shared := (sealTurn turn1Raw).1) (legs := (sealTurn turn1Raw).2) (n := 2)
    (by simp only [stepOk, hj, hnew, hpre, hdomain, Bool.not_false, Bool.and_self]) (by
      intro t ht f hf
      simp only [sealTurn, turn1Raw, List.map_cons, List.map_nil, List.mem_cons,
        List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl
      · have hf' : some (0 : Int) = some f := hf
        cases hf'
        decide
      · have hf' : some (0 : Int) = some f := hf
        cases hf'
        decide)
  exact ⟨s', hs, (stepJoint_post_balance hs).1 _ List.mem_cons_self,
    (stepJoint_post_balance hs).1 _ (List.mem_cons_of_mem _ List.mem_cons_self),
    (stepJoint_refines_floorBook floorsHold_book0 hs).2.1⟩

/-- **Duplicate vat**: refused on every ledger. -/
theorem dupVat_refused (n : Nat) (s : LedgerState) :
    stepJoint n s (sealTurn dupVatRaw).1 (sealTurn dupVatRaw).2 = none :=
  duplicate_vat_refused n s _ _ (by decide)

/-- **Unbound `pre`**: refused by the ledger that holds ten, not a thousand. -/
theorem unboundPre_refused : stepSealed unboundPreRaw = none :=
  unbound_pre_refused 2 ledger0 _ _ _ List.mem_cons_self (by decide)

/-- **Overdraft**: refused on every ledger. -/
theorem overdraft_refused_everywhere (n : Nat) (s : LedgerState) :
    stepJoint n s (sealTurn overdraftRaw).1 (sealTurn overdraftRaw).2 = none :=
  overdraft_refused n s _ _ _ List.mem_cons_self (by decide)

/-- **Every trace from `ledger0`**, of any length: the total stays twenty, no vat is negative, the
book's floors hold and asset 0 still sums to zero over all accounts. -/
theorem every_trace_from_ledger0 (trace : List (ByteArray × List LocalTurn)) (s : LedgerState)
    (h : runTrace 2 ledger0 trace = some s) :
    total (List.range 2) s.balances = 20 ∧ (∀ v, 0 ≤ s.balances v) ∧ FloorsHold s.book ∧
      s.book.assetSum 0 = 0 := by
  have hv := (runTrace_eq_some_iff 2 trace ledger0 s).1 h
  obtain ⟨hf, hsum, hnn⟩ := jointTrace_preserves_floors 2 trace ledger0 s floorsHold_book0 hv
  refine ⟨?_, hnn, hf, ?_⟩
  · rw [(jointTrace_conserves_total_balance 2 trace ledger0 s hv).1]
    decide
  · rw [hsum]
    decide

-- A joint checker that lets one vat sign twice.
#tooth Obend.Polis.JointCoReceipt.duplicate_vat_refused by mutation
  Obend.Polis.JointCoReceipt.vatsDistinct := fun _ => true

-- A step that takes a receipt's word for the balance before.
#tooth Obend.Polis.JointCoReceipt.unbound_pre_refused by mutation
  Obend.Polis.JointCoReceipt.stepOk := fun n s shared legs =>
    checkJoint shared legs && !s.seen.contains (turnKey shared) &&
      legs.all (fun t => decide (t.vat < n))

-- A receipt allowed to end below zero.
#tooth Obend.Polis.JointCoReceipt.overdraft_refused by mutation
  Obend.Polis.JointCoReceipt.LocalTurn.valid := fun t =>
    decide (t.post = t.pre + t.half) && decide (0 ≤ t.pre)

-- Across a trace: with one vat signing twice the total is not conserved.
#tooth Obend.Polis.JointCoReceipt.jointTrace_conserves_total_balance by mutation
  Obend.Polis.JointCoReceipt.vatsDistinct := fun _ => true

-- Across a trace: a receipt allowed to end below zero overdraws its vat.
#tooth Obend.Polis.JointCoReceipt.jointTrace_no_overdraft by mutation
  Obend.Polis.JointCoReceipt.LocalTurn.valid := fun t =>
    decide (t.post = t.pre + t.half) && decide (0 ≤ t.pre)

#print axioms Obend.Polis.JointCoReceipt.stepJoint_refines_floorBook
#print axioms Obend.Polis.JointCoReceipt.stepJoint_complete
#print axioms Obend.Polis.JointCoReceipt.jointTrace_preserves_floors
#print axioms Obend.Polis.JointCoReceipt.coReceiptDigest_binds
#print axioms turn1_applies
#print axioms every_trace_from_ledger0

end CoReceipt
-- SEAM-SECTION-1-COREICEPT-END

-- SEAM-SECTION-2-ZOE-BEGIN
/-! ## 2. Zoe seats on `Ledger.Seat` and the floor book -/

namespace Zoe

open Obend.Ledger
open Obend.Polis.ZoeSeatSettlement
open Obend.Vault.UnifiedDeos

deriving instance DecidableEq for Except

def a100 : AssetBundle := .singleton 0 100 (by decide)
def b200 : AssetBundle := .singleton 1 200 (by decide)
def alice : AccountId := 1

/-- No turn below opens a seat, so no hash is ever asked for. -/
def noHash : Obend.Digest.HashBytes.Hash := fun _ => []
def noGuest : GuestContract := fun _ => none

/-- Alice holds 100 of asset 0 in the floor book; two invitations are minted. -/
def genesis : ZoeHost := fundedHost [(alice, 0, 100), (2, 1, 200)]
def mints : List ZoeTurn := [.mintInvitation 7 "otc", .mintInvitation 7 "otc"]
def minted : ZoeHost := runZoe noHash noGuest genesis mints

theorem minted_inv : ZoeInv minted :=
  (trace_invariant _ _ mints _ _ (fundedHost_invariant _)
    ((validZoeTrace_iff_run _ _ _ _ _).mpr rfl)).1

def aliceP : Proposal := bundleProposal a100 b200 .onDemand
def entered : ZoeHost := runZoe noHash noGuest minted [.enterOffer 0 alice alice 0 aliceP 7#256]

/-- **An escrowed offer is admitted**, and the give leaves Alice's floor-book account. -/
theorem alice_entered : enterOffer minted 0 alice alice 0 aliceP 7#256 = .ok entered := by
  decide +kernel

theorem alice_escrowed (ast : AssetId) :
    entered.floorBook.balance (addrOf alice) ast =
      minted.floorBook.balance (addrOf alice) ast - (assetAmountSum aliceP.give ast : Int) ∧
    (assetAmountSum aliceP.give ast : Int) ≤ minted.floorBook.balance (addrOf alice) ast :=
  ⟨(enterOffer_escrows minted_inv alice_entered ast).1,
    (enterOffer_escrows minted_inv alice_entered ast).2.2.1⟩

/-- A host whose seat `Book` credits Alice while its `FloorBook` holds nothing. -/
def unescrowedHost : ZoeHost := { minted with floorBook := FloorBook.empty }
/-- A seat `Book` that claims 150 where the `FloorBook` holds 100. -/
def inflatedHost : ZoeHost := { minted with seatBook := minted.seatBook.setBalance alice 0 150 }

/-- **Unescrowed, under-funded and unmarked-donation offers are refused**, each by name, and a
    refused offer leaves the host as it was. -/
theorem offers_refused :
    enterOffer unescrowedHost 0 alice alice 0 aliceP 7#256 = .error .unescrowed ∧
    enterOffer inflatedHost 0 alice alice 0
      (bundleProposal (.singleton 0 120 (by decide)) b200 .onDemand) 7#256 = .error .unescrowed ∧
    enterOffer minted 0 alice alice 0
      (bundleProposal (.singleton 0 101 (by decide)) b200 .onDemand) 7#256 =
        .error (.offer (.insufficientOffererBalance 0)) ∧
    enterOffer minted 0 alice alice 0 (bundleProposal a100 .empty .onDemand) 7#256 =
      .error (.offer .donationUnmarked) ∧
    applyZoeTurn noHash noGuest unescrowedHost (.enterOffer 0 alice alice 0 aliceP 7#256) =
      unescrowedHost := by
  decide +kernel

/-- The donation guard on every host, not only this one. -/
theorem donation_refused_everywhere (h : ZoeHost) (c : BitVec 256)
    (hfresh : h.seats.all (fun s => s.account != protectedBase + 0) = true) :
    enterOffer h 0 alice alice 0 (bundleProposal a100 .empty .onDemand) c =
      .error (.offer .donationUnmarked) :=
  enterOffer_donationUnmarked_refused h 0 alice alice 0 _ c (by decide) ⟨by decide, hfresh⟩
    (by decide +kernel) rfl

/-- **On the spine.** Put this ledger in a `UnifiedDeosSpine` over any world: every Zoe trace
    (offers, guest matches, exits, under any hash and guest) keeps the floors, conserves every
    asset of the floor book, and hands back seats that pass the unified turn's seat clause. -/
theorem zoe_trace_on_spine (w : Obend.Vault.Replay.World) (H : Obend.Digest.HashBytes.Hash)
    (guest : GuestContract) (turns : List ZoeTurn) (f : ZoeHost)
    (ht : ValidZoeTrace H guest minted turns f) :
    FloorsHold f.floorBook ∧
    (∀ ast : AssetId, f.floorBook.assetSum ast = minted.floorBook.assetSum ast) ∧
    f.seats.all (fun s => safeAt f.seatBook s.account s.proposal) = true :=
  have r := unifiedDeos_zoe_trace_on_spine H guest
    ⟨w, Obend.Vault.emptyStore, minted.floorBook, minted.seatBook, minted.invReg, minted.seats,
      minted.holders, minted.epoch, minted.epochKeys⟩ turns f minted_inv ht
  ⟨r.1, r.2.1, r.2.2.1⟩

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

#print axioms zoe_trace_on_spine

end Zoe
-- SEAM-SECTION-2-ZOE-END

/-! ## 3. A 256-bit outbox digest through four validators and a durable host -/

namespace Outbox

open Obend.Consensus.Simplex (NodeId)
open Obend.Consensus.SimplexProtocol
open Obend.Consensus.SimplexLiveness
open Obend.Vault.IrreversibleOutbox
open Obend.Vault.UnifiedDeos
open Obend.Trailblaze.Polis (sampleValidPartition checkMicrokitIsolation)
open Obend.Digest
open Obend.Digest.Cshake256.Native (bytesOfList bytesOfList_toList)
open Obend.Judge.Computational (HashCollisionWitness)

/-- `n = 4`, `f = 1`: validators `0, 1, 2` honest, validator `3` Byzantine. -/
def proto4 : Protocol := ⟨[0, 1, 2, 3], 1, (· == 3), by decide, by decide, by decide⟩

def payloadA : ByteArray := bytesOfList [0xDE, 0xAD, 0xBE, 0xEF]
def payloadB : ByteArray := bytesOfList [0xCA, 0xFE, 0x01, 0x02]

/-- The two outbox commitments, written out: 256-bit numbers. -/
def commitA : Nat := 79817041280646677348372407200226764119291410642631118685939725383524999737416
def commitB : Nat := 103324176270572647848140286090186155230911491861731471782663868340299450874569

theorem commitA_eq : effectCommitNat 10 .irreversibleActuation payloadA = commitA := by
  decide +kernel
theorem commitB_eq : effectCommitNat 30 .irreversibleActuation payloadB = commitB := by
  decide +kernel

/-- Neither fits 64 bits; both fit 256. -/
example : 2 ^ 64 ≤ commitA ∧ commitA < 2 ^ 256 ∧ 2 ^ 64 ≤ commitB ∧ commitB < 2 ^ 256 := by
  decide +kernel

def chainA : Chain := [.block 1 commitA]
def chainAB : Chain := [.block 1 commitA, .block 2 commitB]

/-- The wire takes the full digest: the vote for the outbox block is canonical. -/
theorem wire_accepts_256 : msgCanonical ⟨0, 1, .vote, .block chainA⟩ = true := by decide +kernel

/-! ### The adversarial timed network -/

def cfg4 : NetConfig := ⟨0, 1, 5⟩

def netEmpty : NetState where
  time := 0
  log := []
  delivered := fun _ _ => false
  viewEntry := fun _ _ => none

def honest3 : List NodeId := [0, 1, 2]
def prop (v : Nat) (c : Chain) : Msg := ⟨proto4.leader v, v, .propose, .block c⟩
def votesOf (v : Nat) (c : Chain) : List Msg := honest3.map fun n => ⟨n, v, .vote, .block c⟩
def finsOf (v : Nat) (c : Chain) : List Msg := honest3.map fun n => ⟨n, v, .finalize, .block c⟩
def deliverTo (ms : List Msg) : List NetEvent :=
  ms.flatMap fun m => honest3.map fun n => NetEvent.deliver n m

/-- One view under an honest leader: every delivery at its deadline, and `byz` injected by the
    Byzantine validator in the middle of the vote. -/
def viewEvents (v : Nat) (parent c : Chain) (byz : List Msg) : List NetEvent :=
  honest3.map (fun n => NetEvent.enter n v parent) ++ [.send (prop v c)] ++
  deliverTo [prop v c] ++ (votesOf v c).map NetEvent.send ++ byz.map NetEvent.inject ++ [.tick] ++
  deliverTo (votesOf v c ++ byz) ++ (finsOf v c).map NetEvent.send ++ [.tick] ++
  deliverTo (finsOf v c) ++ [.tick]

/-- The Byzantine validator votes for a different block in view 1. -/
def byzVote : Msg := ⟨3, 1, .vote, .block [.block 1 666]⟩

def run1 : List NetEvent := viewEvents 1 [] chainA [byzVote]
def run2 : List NetEvent := viewEvents 2 chainA chainAB []

/-- The message lists the two runs leave, newest first. -/
def sent1 : Sent :=
  (finsOf 1 chainA).reverse ++ [byzVote] ++ (votesOf 1 chainA).reverse ++ [prop 1 chainA]
def sent2 : Sent :=
  (finsOf 2 chainAB).reverse ++ (votesOf 2 chainAB).reverse ++ [prop 2 chainAB] ++ sent1

theorem run1_sent :
    (runNet proto4 cfg4 netEmpty run1).map (fun s => (s.sent, s.time)) = some (sent1, 3) := by
  decide +kernel

theorem run12_sent :
    (runNet proto4 cfg4 netEmpty (run1 ++ run2)).map (fun s => (s.sent, s.time)) =
      some (sent2, 6) := by
  decide +kernel

/-- The network refuses what the model forbids: a tick while a due message is undelivered, an
    honest dummy vote before the timer, a second honest vote, an injection under an honest name. -/
example :
    (runNet proto4 cfg4 netEmpty
      (honest3.map (fun n => NetEvent.enter n 1 []) ++ [.send (prop 1 chainA), .tick, .tick])).isNone
      = true ∧
    (runNet proto4 cfg4 netEmpty
      [.enter 0 1 [], .send ⟨0, 1, .vote, .dummy 1⟩]).isNone = true ∧
    (runNet proto4 cfg4 netEmpty
      [.enter 0 1 [], .send (prop 1 chainA), .deliver 0 (prop 1 chainA),
       .send ⟨0, 1, .vote, .block chainA⟩, .send ⟨0, 1, .vote, .block chainA⟩]).isNone = true ∧
    (runNet proto4 cfg4 netEmpty [.inject ⟨0, 1, .vote, .block [.block 1 666]⟩]).isNone = true := by
  decide +kernel

theorem runNet_sentSteps {P : Protocol} {cfg : NetConfig} :
    ∀ (evs : List NetEvent) {s s' : NetState},
      runNet P cfg s evs = some s' → SentSteps P s.sent s'.sent
  | [], s, s', h => by
    have h' : some s = some s' := h
    injection h' with h'
    subst h'
    exact SentSteps.refl _
  | e :: es, s, s', h => by
    obtain ⟨s₁, h1, h2⟩ := runNet_cons.1 h
    have ih := runNet_sentSteps es h2
    rcases netStep_sent h1 with hs | hs
    · rw [hs] at ih
      exact ih
    · exact sentSteps_trans (SentSteps.step (SentSteps.refl _) hs) ih

/-- Both message lists are `SimplexProtocol` runs, the second an extension of the first. -/
theorem sent_facts :
    Reach proto4 sent1 ∧ SentSteps proto4 [] sent1 ∧ SentSteps proto4 sent1 sent2 := by
  cases h : runNet proto4 cfg4 netEmpty (run1 ++ run2) with
  | none =>
    have e := run12_sent
    rw [h] at e
    cases e
  | some s₂ =>
    obtain ⟨s₁, h1, h2⟩ := (runNet_append run1 run2).1 h
    have e1 := run1_sent
    rw [h1] at e1
    have e2 := run12_sent
    rw [h] at e2
    simp only [Option.map_some] at e1 e2
    injection e1 with e1
    injection e2 with e2
    have hs1 : s₁.sent = sent1 := congrArg Prod.fst e1
    have hs2 : s₂.sent = sent2 := congrArg Prod.fst e2
    have st1 : SentSteps proto4 [] s₁.sent := runNet_sentSteps run1 h1
    have st2 := runNet_sentSteps run2 h2
    rw [hs1] at st1 st2
    rw [hs2] at st2
    exact ⟨sentSteps_reach Reach.nil st1, st1, st2⟩

/-- View 1 launched: the honest leader has proposed the outbox block, the honest validators have
    entered. -/
def launchedA : NetState where
  time := 0
  log := [(prop 1 chainA, 0)]
  delivered := fun _ _ => false
  viewEntry := fun _ v => if v = 1 then some 0 else none

theorem launchedA_ok : ViewLaunched proto4 cfg4 launchedA 1 [] commitA where
  reach := Reach.step Reach.nil
    (Step.propose [] (proto4.leader 1) 1 chainA ⟨by decide, by decide⟩ rfl)
  postGst := Nat.le_refl _
  deltaPos := by decide
  stamped := by decide
  viewPos := Nat.le_refl _
  parentLen := rfl
  leaderHonest := ⟨by decide, by decide⟩
  proposed := List.Mem.head _
  oneProposal := by
    intro m hm _ _ _
    have hm' : m ∈ [prop 1 chainA] := hm
    rw [List.mem_singleton] at hm'
    rw [hm']
    rfl
  entered := fun _ _ => ⟨0, rfl, by decide⟩
  parentKnown := fun _ _ k hk => absurd hk (Nat.not_lt_zero k)
  fresh := fun n _ => by simp [votedAny, launchedA, NetState.sent, prop]

/-- **The adversary cannot stop the outbox block.** Whatever event list the network accepts from
    the launch (any delivery order, any Byzantine injections), once the clock has passed
    `2 * deltaNet` the block carrying the 256-bit commitment is finalized. -/
theorem outbox_block_finalizes_on_every_trace (evs : List NetEvent) (s : NetState)
    (h : runNet proto4 cfg4 launchedA evs = some s) (ht : 2 < s.time) :
    Reach proto4 s.sent ∧ Finalized proto4 s.sent 1 chainA :=
  have r := gst_honest_leader_finalizes launchedA_ok h (show 0 + 2 * 1 < s.time by omega)
  ⟨r.1, r.2.2.1⟩

/-! ### Slot-key signatures over cSHAKE256 -/

def sigDomain : List UInt8 := [0x53, 0x4C, 0x4F, 0x54]

def sigHash : HashBytes.Hash := Cshake256.Fast.cshake256Fast sigDomain

theorem sigHash_length (bs : List UInt8) : (sigHash bs).length = 32 := by
  unfold sigHash
  rw [Cshake256.Fast.cshake256Fast_eq]
  exact Cshake256.cshake256Bytes_length _ _

def saltOf : NodeId → Nat → Kind → ByteArray :=
  fun n v _ => bytesOfList (List.replicate 32 (UInt8.ofNat (16 * n + v)))

/-- What was signed in view 1, oldest first: the proposal, the three honest votes for the outbox
    block, and the Byzantine validator's own vote. -/
def signLog : List Msg := prop 1 chainA :: (votesOf 1 chainA ++ [byzVote])

def keys : KeyDirectory := KeyDirectory.derive sigHash signLog saltOf
def scheme : SignatureScheme := commitSlotSigScheme sigHash 4096
def sign (m : Msg) : SignedSimplexMsg := ⟨m, saltOf m.sender m.view m.kind⟩

/-- The proposal and the three distinct honest votes for the 256-bit block verify, with the
    Byzantine validator's vote under its own key. -/
theorem signed_trace_accepted :
    verifySignedSent scheme keys proto4.committee (signLog.map sign) = true := by
  decide +kernel

/-- The Byzantine validator puts validator 0's name on its own vote. -/
def forgedVote : SignedSimplexMsg := ⟨⟨0, 1, .vote, .block [.block 1 666]⟩, saltOf 3 1 .vote⟩

/-- Validator 0's real signature, moved onto another block. -/
def replayedSig : SignedSimplexMsg := ⟨⟨0, 1, .vote, .block [.block 1 666]⟩, saltOf 0 1 .vote⟩

theorem forged_byzantine_signature_refused :
    verifySignedMsg scheme keys proto4.committee forgedVote = false ∧
    verifySignedMsg scheme keys proto4.committee replayedSig = false := by
  decide +kernel

theorem honest_keys : HonestSlotKeys sigHash 4096 keys proto4 signLog saltOf :=
  KeyDirectory.derive_honestSlotKeys sigHash 4096 200 proto4 signLog saltOf sigHash_length
    (by decide +kernel) (fun n v k => by simp [saltOf, bytesOfList_toList]) (by decide +kernel)
    (by decide)

/-- **Any accepted forgery against the three honest validators is a cSHAKE256 collision.** -/
theorem any_forgery_is_a_collision (w : EufCmaForgeryWitness scheme keys proto4 signLog) :
    HashBytes.CollisionAmong sigHash (fun x => x = forgedSlotPreimage w.forgedMsg ∨
      x = registeredSlotPreimage signLog saltOf w.forgedMsg.msg) :=
  (forgedSignature_reduces_to_hashCollision sigHash 4096 keys proto4 signLog saltOf honest_keys w).toCollisionAmong

#tooth Obend.Consensus.Finality.chainDigest_binds by mutation
  Obend.Consensus.SimplexProtocol.Entry.encode := fun _ => []
#tooth Obend.Vault.UnifiedDeos.UnifiedDeosSpine.zoeHost_writeback by mutation
  Obend.Vault.UnifiedDeos.UnifiedDeosSpine.withZoeHost := fun S _ => S

/-! ### The durable host dispatches once -/

def initOutbox : OutboxState where
  gatekeeperPd         := 3
  highWaterNullifier   := 0
  escrowVaultBalance   := 500
  readAuditCount       := 0
  activeEscrows        := []
  settledEscrowTotal   := 0
  dispatchedActuations := []

def host₀ : DurableSimplexHost where
  self := 0
  deadline := 10
  journaledVotes := []
  volatileState := some { self := 0, deadline := 10 }
  outbox := initOutbox

def reqA : OutboxEffectReq where
  nullifierId   := 10
  effectClass   := .irreversibleActuation
  targetView    := 1
  proposedChain := chainA
  finCert?      := some ⟨1, chainA, [0, 1, 2]⟩
  escrowBond?   := none
  spsc          := ⟨0, payloadA⟩

def reqB : OutboxEffectReq where
  nullifierId   := 30
  effectClass   := .irreversibleActuation
  targetView    := 2
  proposedChain := chainAB
  finCert?      := some ⟨2, chainAB, [0, 1, 2]⟩
  escrowBond?   := none
  spsc          := ⟨0, payloadB⟩

def hostV : DurableSimplexHost := (durableCastVote host₀ 1 chainA).getD host₀
def hostA : DurableSimplexHost :=
  (durableDispatch proto4 sampleValidPartition sent1 hostV reqA).getD hostV
def hostB : DurableSimplexHost :=
  (durableDispatch proto4 sampleValidPartition sent2
    (recoverSimplexHost (crashSimplexHost (crashSimplexHost hostA))) reqB).getD hostA

theorem hostV_eq : durableCastVote host₀ 1 chainA = some hostV := by decide +kernel
theorem hostA_eq : durableDispatch proto4 sampleValidPartition sent1 hostV reqA = some hostA := by
  decide +kernel
theorem hostB_eq : durableDispatch proto4 sampleValidPartition sent2
    (recoverSimplexHost (crashSimplexHost (crashSimplexHost hostA))) reqB = some hostB := by
  decide +kernel

-- The elaborator need not run cSHAKE to compare hosts; the kernel did, just above.
attribute [irreducible] hostV hostA hostB

/-- Vote, dispatch the first digest, crash twice, recover, dispatch the second. -/
def hostEvents : List HostEvent :=
  [.vote 1 chainA, .dispatch ⟨sent1, reqA, none⟩, .crash, .crash, .recover,
   .dispatch ⟨sent2, reqB, none⟩]

theorem hostRun_valid :
    ValidHostRun proto4 sampleValidPartition [] host₀ hostEvents sent2 hostB := by
  obtain ⟨hR1, hS1, hS2⟩ := sent_facts
  have hIso : checkMicrokitIsolation sampleValidPartition = true := by decide +kernel
  exact ⟨hostV, hostV_eq, Reach.nil, hS1, hostA, hostA.outbox, hostA_eq, rfl, hR1, hS2, hostB,
    hostB.outbox, hostB_eq, rfl, rfl, rfl, sentSteps_reach hR1 hS2, hIso⟩

/-- Both digests went out, each once, with the bytes that were committed. -/
theorem dispatched_exactly :
    hostB.outbox.dispatchedActuations.map
        (fun a => (a.nullifierId, a.dispatchedPayload.data.toList)) =
      [(30, [0xCA, 0xFE, 0x01, 0x02]), (10, [0xDE, 0xAD, 0xBE, 0xEF])] := by
  decide +kernel

/-- The library theorem on this run: no nullifier twice; each actuation finalized on the full
    256-bit commitment and never rolled back; refused under its nullifier after any crashes. -/
theorem seam_dispatch_once :
    (hostB.outbox.dispatchedActuations.map DispatchedActuation.nullifierId).Nodup ∧
    ∀ a ∈ hostB.outbox.dispatchedActuations,
      Finalized proto4 sent2 a.view a.chain ∧
      a.chain.getLast? = some (.block a.view
        (effectCommitNat a.nullifierId .irreversibleActuation a.dispatchedPayload)) ∧
      effectCommitNat a.nullifierId .irreversibleActuation a.dispatchedPayload < 256 ^ 32 ∧
      (∀ (vCanon : Nat) (cCanon : Chain),
        Finalized proto4 sent2 vCanon cCanon → a.view ≤ vCanon → a.chain <+: cCanon) ∧
      ∀ (extraCrashes : Nat) (P' : Protocol) (sent : Sent) (req : OutboxEffectReq),
        req.effectClass ≠ .idempotentRead → req.nullifierId = a.nullifierId →
        (recoverSimplexHost (Nat.repeat crashSimplexHost (extraCrashes + 1) hostB)).volatileState.isSome
          = true ∧
        durableDispatch P' sampleValidPartition sent
          (recoverSimplexHost (Nat.repeat crashSimplexHost (extraCrashes + 1) hostB)) req = none :=
  durable_outbox_dispatch_once_across_crashes rfl hostRun_valid

/-- Concretely: after a crash and recovery the same request is refused; a crashed host dispatches
    nothing; other bytes under the finalized commitment are refused; a block that is voted but not
    finalized is refused. -/
theorem replay_and_tamper_refused :
    durableDispatch proto4 sampleValidPartition sent2
      (recoverSimplexHost (crashSimplexHost hostB)) reqA = none ∧
    durableDispatch proto4 sampleValidPartition sent2 (crashSimplexHost hostB)
      { reqB with nullifierId := 40 } = none ∧
    durableDispatch proto4 sampleValidPartition sent1 hostV { reqA with spsc := ⟨0, payloadB⟩ }
      = none ∧
    durableDispatch proto4 sampleValidPartition (sent1.drop 3) hostV reqA = none := by
  decide +kernel

/-! ### Teeth -/

-- The 64-bit wire of before: a block carrying an outbox commitment is no longer canonical.
#tooth Obend.Vault.IrreversibleOutbox.outboxBlock_canonical by mutation
  Obend.Consensus.SimplexProtocol.Entry.canonical := fun e =>
    match e with
    | .block v payload => decide (v < 256 ^ 8) && decide (payload < 256 ^ 8)
    | .dummy v => decide (v < 256 ^ 8)

-- An encoding that keeps 8 bytes of the payload is not injective.
#tooth Obend.Consensus.SimplexProtocol.Entry.encode_injective by mutation
  Obend.Consensus.SimplexProtocol.Entry.encode := fun e =>
    match e with
    | .block v payload =>
      (0x01 : UInt8) :: (Obend.Digest.HashBytes.be 8 v ++ Obend.Digest.HashBytes.be 8 payload)
    | .dummy v => (0x00 : UInt8) :: (Obend.Digest.HashBytes.be 8 v ++ Obend.Digest.HashBytes.be 8 0)

-- A verifier that accepts everything lets a forged signature into the projected run.
#tooth Obend.Consensus.SimplexLiveness.verifySignedSent_projects_to_reach by mutation
  Obend.Consensus.SimplexLiveness.verifySignedMsg := fun _ _ _ _ => true

-- A network that may tick whenever it likes delivers nothing on time.
#tooth Obend.Consensus.SimplexLiveness.gst_honest_leader_finalizes by mutation
  Obend.Consensus.SimplexLiveness.settledB := fun _ _ _ => true

-- A crash that loses the outbox journal reopens every spent nullifier.
#tooth Obend.Vault.UnifiedDeos.durable_outbox_dispatch_once_across_crashes by mutation
  Obend.Vault.UnifiedDeos.crashSimplexHost := fun h =>
    { h with volatileState := none, outbox := { h.outbox with highWaterNullifier := 0 } }

-- A tip check that accepts any commitment lets other bytes stand in for the finalized ones.
#tooth Obend.Vault.IrreversibleOutbox.dispatched_payload_bound_to_finalized_commit by mutation
  Obend.Vault.IrreversibleOutbox.checkChainTipCommit := fun _ _ _ => true

#print axioms seam_dispatch_once
#print axioms outbox_block_finalizes_on_every_trace
#print axioms any_forgery_is_a_collision

end Outbox

end Obend.Tests.DeosSimplexOutboxSeam
end
