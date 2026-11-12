module
/-
# SimplexLivenessAndOutboxTest — the signed wire, the timed network and the outbox, unit by unit

1. `Obend.Consensus.SimplexLiveness`, timed network: runs of `N = 4, f = 1` and `N = 7, f = 2`
   committees under two delivery schedules with a Byzantine equivocation, finalizing a block whose
   payload needs 256 bits; a timed-out view that notarizes its dummy; the events the network
   refuses; `gst_honest_leader_finalizes` instantiated on a launched `N = 7` view.
2. Slot-key signatures: a derived directory for four validators (three honest) accepts their
   signed trace and refuses a forged and a replayed signature; under a constant hash the forgery
   is accepted, `extractForgedVoteSignature` returns it, and
   `forgedSignature_reduces_to_hashCollision` turns it into a collision of that hash.
3. `Obend.Vault.IrreversibleOutbox`: a real cSHAKE256 commitment at the tip of a finalized chain;
   each named refusal; escrow rollback on an orphaned branch; a multi-turn `ValidOutboxTrace` with
   the apex theorem, the finalized-commitment binding and the replay refusal applied to it.
4. `#tooth` witnesses and `#assert_axioms_tree`.
-/

public import Obend.Consensus.SimplexLiveness
public import Obend.Vault.IrreversibleOutbox
public import Obend.Tactic.Tooth
public import Obend.AssertAxioms

import all Obend.Consensus.SimplexLiveness
import all Obend.Vault.IrreversibleOutbox
import all Obend.Trailblaze.Polis
import all Obend.Consensus.SimplexProtocol
import all Obend.Consensus.SimplexTrace
import all Obend.Consensus.Finality
import all Obend.Judge.Computational
meta import all Obend.Consensus.SimplexLiveness
meta import all Obend.Vault.IrreversibleOutbox
meta import all Obend.Trailblaze.Polis
meta import all Obend.Consensus.SimplexProtocol
meta import all Obend.Consensus.SimplexTrace
meta import all Obend.Consensus.Finality
meta import all Obend.Judge.Computational

-- Transitive package bodies for `#assert_axioms_tree`
import all Obend.AssertAxioms
import all Obend.Consensus.Simplex
import all Obend.Core.AliasExposure
import all Obend.Core.Assumptions
import all Obend.Core.Bidirectional
import all Obend.Core.Brand
import all Obend.Core.CanonicalExtension
import all Obend.Core.Capacity
import all Obend.Core.Check
import all Obend.Core.Code
import all Obend.Core.Data
import all Obend.Core.Digest
import all Obend.Core.EquiRecursiveAgreement
import all Obend.Core.EquiRecursiveLookup
import all Obend.Core.FieldCongruence
import all Obend.Core.FiniteBisimulation
import all Obend.Core.FinitePresentation
import all Obend.Core.FiniteRowLaws
import all Obend.Core.Invariant
import all Obend.Core.LegacyAgreement
import all Obend.Core.Machine
import all Obend.Core.MachineFast
import all Obend.Core.MachineTyping
import all Obend.Core.Nominal
import all Obend.Core.Proofs.Adequacy.Birth
import all Obend.Core.Proofs.Adequacy.CasesControl
import all Obend.Core.Proofs.Adequacy.CasesEval
import all Obend.Core.Proofs.Adequacy.CasesReturn
import all Obend.Core.Proofs.Adequacy.Defs
import all Obend.Core.Proofs.Adequacy.Graph
import all Obend.Core.Proofs.Adequacy.Meaning
import all Obend.Core.Proofs.Adequacy.Origins
import all Obend.Core.Proofs.Adequacy.Progress
import all Obend.Core.Proofs.Adequacy.Reach
import all Obend.Core.Proofs.Adequacy.Run
import all Obend.Core.Proofs.Adequacy.Safety
import all Obend.Core.Proofs.Adequacy.SafetyRaw
import all Obend.Core.Proofs.Adequacy.Scoped
import all Obend.Core.Proofs.Adequacy.Sound
import all Obend.Core.Proofs.Adequacy.Source
import all Obend.Core.Proofs.Adequacy.StepRaw
import all Obend.Core.Proofs.BidirectionalCompleteness
import all Obend.Core.Proofs.Completeness
import all Obend.Core.Proofs.DataSoundness
import all Obend.Core.Proofs.GroundExecution
import all Obend.Core.Proofs.Preservation.Base.Heads
import all Obend.Core.Proofs.Preservation.Base.Insert
import all Obend.Core.Proofs.Preservation.Base.Reusable
import all Obend.Core.Proofs.Preservation.Base.Values
import all Obend.Core.Proofs.Preservation.Base.Weaken
import all Obend.Core.Proofs.StepCases
import all Obend.Core.Proofs.Substitution.Defs
import all Obend.Core.Proofs.Substitution.Uses
import all Obend.Core.Proofs.TypedSubstitution
import all Obend.Core.RecursiveAgreement
import all Obend.Core.RecursiveRows
import all Obend.Core.ResourceSemantics
import all Obend.Core.RowCongruence
import all Obend.Core.RowExposureInvariance
import all Obend.Core.RowHit
import all Obend.Core.RuntimeOrigins
import all Obend.Core.Term
import all Obend.Core.TermTraverse
import all Obend.Core.Traverse
import all Obend.Core.Ty
import all Obend.Core.TypeGraph
import all Obend.Core.TypeGraphAlias
import all Obend.Core.TypeGraphHead
import all Obend.Core.TypeGraphResource
import all Obend.Digest.Cshake256
import all Obend.Digest.Cshake256.Fast
import all Obend.Digest.Cshake256.Seam
import all Obend.Digest.Cshake256.Spec
import all Obend.Digest.HashBytes
import all Obend.Elab.Work
import all Obend.Equiv.Ahead
import all Obend.Equiv.Behaviour
import all Obend.Equiv.Fields
import all Obend.Equiv.Quote
import all Obend.Equiv.Reduction
import all Obend.Equiv.Simulation
import all Obend.Fold
import all Obend.Intention
import all Obend.Judge.Class
import all Obend.Judge.Clearing
import all Obend.Judge.Lrat
import all Obend.Kind
import all Obend.Law.Claim
import all Obend.Law.Contract
import all Obend.Law.Inherit
import all Obend.Law.Machine
import all Obend.Law.Proofs.Claim
import all Obend.Law.Proofs.Eval
import all Obend.Law.Proofs.Inherit
import all Obend.Law.Proofs.Machine
import all Obend.Law.Proofs.Run
import all Obend.Law.Proofs.Std
import all Obend.Law.Run
import all Obend.Law.Std
import all Obend.Law.Syntax
import all Obend.Ledger.Book
import all Obend.Ledger.Floors
import all Obend.Ledger.Register
import all Obend.Ledger.Seat
import all Obend.Logic.Claim
import all Obend.Logic.Frame
import all Obend.Logic.Ground
import all Obend.Logic.LateBinding
import all Obend.Logic.Obligation
import all Obend.Logic.Program
import all Obend.Logic.Receipt
import all Obend.Logic.Rewrite
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
import all Obend.Slot.Core4
import all Obend.Slot.Integrity
import all Obend.Slot.Proofs.Protocol
import all Obend.Slot.Proofs.ProtocolTyping
import all Obend.Slot.Protocol
import all Obend.Slot.Selection
import all Obend.Slot.World
import all Obend.Spec.C4
import all Obend.Spec.DataWire
import all Obend.Spec.Proofs.C4
import all Obend.Tactic.Cases
import all Obend.Tactic.MonadicReduction
import all Obend.Tactic.Tooth
import all Obend.Trailblaze.Obligations
import all Obend.Trailblaze.PolisBlum
import all Obend.Vault.Hyperedge

public section
namespace Obend.Tests.SimplexLivenessAndOutbox

open Obend.Consensus.Simplex (NodeId)
open Obend.Consensus.SimplexProtocol
open Obend.Consensus.SimplexLiveness
open Obend.Vault.IrreversibleOutbox
open Obend.Trailblaze.Polis (sampleValidPartition checkMicrokitIsolation)
open Obend.Digest
open Obend.Digest.Cshake256.Native (bytesOfList bytesOfList_toList)
open Obend.Judge.Computational (HashCollisionWitness ComputationalJudge)

set_option autoImplicit false
set_option maxRecDepth 100000

/-! ## 1. The adversarial timed network -/

/-- `N = 4, f = 1`: validator `3` is Byzantine. -/
def proto4 : Protocol := ⟨[0, 1, 2, 3], 1, (· == 3), by decide, by decide, by decide⟩

/-- `N = 7, f = 2`: validators `5` and `6` are Byzantine. -/
def proto7 : Protocol :=
  ⟨[0, 1, 2, 3, 4, 5, 6], 2, (fun n => n == 5 || n == 6), by decide, by decide, by decide⟩

def cfg : NetConfig := ⟨0, 1, 5⟩

def netEmpty : NetState where
  time := 0
  log := []
  delivered := fun _ _ => false
  viewEntry := fun _ _ => none

/-- A block whose payload does not fit 64 bits. -/
def wide (v x : Nat) : Entry := .block v (2 ^ 200 + x)

def prop (P : Protocol) (v : Nat) (c : Chain) : Msg := ⟨P.leader v, v, .propose, .block c⟩
def votesOf (hs : List NodeId) (v : Nat) (c : Chain) : List Msg :=
  hs.map fun n => ⟨n, v, .vote, .block c⟩
def finsOf (hs : List NodeId) (v : Nat) (c : Chain) : List Msg :=
  hs.map fun n => ⟨n, v, .finalize, .block c⟩
def deliverTo (hs : List NodeId) (ms : List Msg) : List NetEvent :=
  ms.flatMap fun m => hs.map fun n => NetEvent.deliver n m

/-- One view under an honest leader, every delivery at its deadline, `byz` injected mid-vote. -/
def viewLate (P : Protocol) (hs : List NodeId) (v : Nat) (parent c : Chain) (byz : List Msg) :
    List NetEvent :=
  hs.map (fun n => NetEvent.enter n v parent) ++ [.send (prop P v c)] ++
  deliverTo hs [prop P v c] ++ (votesOf hs v c).map NetEvent.send ++ byz.map NetEvent.inject ++
  [.tick] ++ deliverTo hs (votesOf hs v c ++ byz) ++ (finsOf hs v c).map NetEvent.send ++ [.tick] ++
  deliverTo hs (finsOf hs v c) ++ [.tick]

/-- The same view with every delivery at once: all of it happens before the first tick. -/
def viewEager (P : Protocol) (hs : List NodeId) (v : Nat) (parent c : Chain) (byz : List Msg) :
    List NetEvent :=
  hs.map (fun n => NetEvent.enter n v parent) ++ byz.map NetEvent.inject ++ [.send (prop P v c)] ++
  deliverTo hs (prop P v c :: byz) ++ (votesOf hs v c).map NetEvent.send ++
  deliverTo hs (votesOf hs v c) ++ (finsOf hs v c).map NetEvent.send ++
  deliverTo hs (finsOf hs v c) ++ [.tick, .tick, .tick]

/-- What a run leaves: its clock, and whether the block has a checking finalization certificate. -/
def outcome (P : Protocol) (evs : List NetEvent) (v : Nat) (c : Chain) : Option (Nat × Bool) :=
  (runNet P cfg netEmpty evs).map fun s =>
    (s.time, match extractFinCert? P s.sent v c with
             | some cert => cert.checks P s.sent
             | none => false)

def byz4 : List Msg := [⟨3, 1, .vote, .block [wide 1 666]⟩, ⟨3, 1, .vote, .dummy 1⟩]

example : outcome proto4 (viewLate proto4 [0, 1, 2] 1 [] [wide 1 401] byz4) 1 [wide 1 401] =
    some (3, true) := by decide +kernel
example : outcome proto4 (viewEager proto4 [0, 1, 2] 1 [] [wide 1 401] byz4) 1 [wide 1 401] =
    some (3, true) := by decide +kernel

/-- Two views in a row: view 2 (leader `1`) extends the block view 1 finalized. -/
example :
    outcome proto4
      (viewLate proto4 [0, 1, 2] 1 [] [wide 1 401] byz4 ++
       viewEager proto4 [0, 1, 2] 2 [wide 1 401] [wide 1 401, wide 2 402] [])
      2 [wide 1 401, wide 2 402] = some (6, true) := by decide +kernel

def byz7 : List Msg := [⟨5, 1, .vote, .block [wide 1 9]⟩, ⟨6, 1, .vote, .block [wide 1 9]⟩]

example : outcome proto7 (viewLate proto7 [0, 1, 2, 3, 4] 1 [] [wide 1 1001] byz7) 1 [wide 1 1001] =
    some (3, true) := by decide +kernel

/-- A view whose leader stays silent: once the timers expire the honest validators vote for the
    dummy and it is notarized; before the timer such a vote is refused. -/
def silentView : List NetEvent :=
  [0, 1, 2].map (fun n => NetEvent.enter n 1 []) ++ List.replicate 5 NetEvent.tick ++
  [0, 1, 2].map (fun n => NetEvent.send ⟨n, 1, .vote, .dummy 1⟩)

example :
    (runNet proto4 cfg netEmpty silentView).map
      (fun s => decide (NotarizedDummy proto4 s.sent 1)) = some true ∧
    (runNet proto4 cfg netEmpty
      [.enter 0 1 [], .tick, .send ⟨0, 1, .vote, .dummy 1⟩]).isNone = true := by
  decide +kernel

/-- Refused events: a tick while a due message is undelivered; a tick while an honest node sits
    on a vote its deliveries enable; a second honest vote; a second proposal by the honest leader;
    an injection under an honest name; a finalize before the node's deliveries notarize. -/
example :
    (runNet proto4 cfg netEmpty
      [.enter 0 1 [], .send (prop proto4 1 [wide 1 1]), .tick, .tick]).isNone = true ∧
    (runNet proto4 cfg netEmpty
      [.enter 0 1 [], .send (prop proto4 1 [wide 1 1]), .deliver 0 (prop proto4 1 [wide 1 1]),
       .tick]).isNone = true ∧
    (runNet proto4 cfg netEmpty
      [.enter 0 1 [], .send (prop proto4 1 [wide 1 1]), .deliver 0 (prop proto4 1 [wide 1 1]),
       .send ⟨0, 1, .vote, .block [wide 1 1]⟩, .send ⟨0, 1, .vote, .block [wide 1 1]⟩]).isNone
      = true ∧
    (runNet proto4 cfg netEmpty
      [.enter 0 1 [], .send (prop proto4 1 [wide 1 1]), .send (prop proto4 1 [wide 1 2])]).isNone
      = true ∧
    (runNet proto4 cfg netEmpty [.inject ⟨0, 1, .vote, .block [wide 1 666]⟩]).isNone = true ∧
    (runNet proto4 cfg netEmpty
      [.enter 0 1 [], .send (prop proto4 1 [wide 1 1]), .deliver 0 (prop proto4 1 [wide 1 1]),
       .send ⟨0, 1, .vote, .block [wide 1 1]⟩, .send ⟨0, 1, .finalize, .block [wide 1 1]⟩]).isNone
      = true := by
  decide +kernel

/-- A launched view of the seven-validator committee. -/
def launched7 : NetState where
  time := 0
  log := [(prop proto7 1 [wide 1 1001], 0)]
  delivered := fun _ _ => false
  viewEntry := fun _ v => if v = 1 then some 0 else none

theorem launched7_ok : ViewLaunched proto7 cfg launched7 1 [] (2 ^ 200 + 1001) where
  reach := Reach.step Reach.nil
    (Step.propose [] (proto7.leader 1) 1 [wide 1 1001] ⟨by decide, by decide⟩ rfl)
  postGst := Nat.le_refl _
  deltaPos := by decide
  stamped := by decide
  viewPos := Nat.le_refl _
  parentLen := rfl
  leaderHonest := ⟨by decide, by decide⟩
  proposed := List.Mem.head _
  oneProposal := by
    intro m hm _ _ _
    have hm' : m ∈ [prop proto7 1 [wide 1 1001]] := hm
    rw [List.mem_singleton] at hm'
    rw [hm']
    rfl
  entered := fun _ _ => ⟨0, rfl, by decide⟩
  parentKnown := fun _ _ k hk => absurd hk (Nat.not_lt_zero k)
  fresh := fun n _ => by simp [votedAny, launched7, NetState.sent, prop]

/-- Every trace of the seven-validator view finalizes: no delivery order and no injection by
    validators `5` and `6` prevents it. -/
theorem launched7_finalizes (evs : List NetEvent) (s : NetState)
    (h : runNet proto7 cfg launched7 evs = some s) (ht : 2 < s.time) :
    Finalized proto7 s.sent 1 [wide 1 1001] ∧
    ∀ n, proto7.honest n → voted s.sent n 1 (.dummy 1) = false :=
  have r := gst_honest_leader_finalizes launched7_ok h (show 0 + 2 * 1 < s.time by omega)
  ⟨r.2.2.1, fun n hn => (r.2.1 n hn).2⟩

/-- Pre-GST equivocation exposes the missing faulty-view recovery rule: two block votes
and one dummy vote survive GST without a quorum, and vote-once forbids the rescuing dummy votes. -/
def byzantineLeader : Protocol := ⟨[3, 0, 1, 2], 1, (· == 3), by decide, by decide, by decide⟩
def splitCfg : NetConfig := ⟨100, 1, 5⟩
def splitA : Msg := prop byzantineLeader 1 [wide 1 10]
def splitB : Msg := prop byzantineLeader 1 [wide 1 20]
def splitVotes : List Msg :=
  [⟨0, 1, .vote, .block [wide 1 10]⟩, ⟨1, 1, .vote, .block [wide 1 20]⟩, ⟨2, 1, .vote, .dummy 1⟩]
def splitRun : List NetEvent :=
  [0, 1, 2].map (fun n => .enter n 1 []) ++
  [.inject splitA, .inject splitB, .deliver 0 splitA, .send ⟨0, 1, .vote, .block [wide 1 10]⟩,
   .deliver 1 splitB, .send ⟨1, 1, .vote, .block [wide 1 20]⟩] ++ List.replicate 5 .tick ++
  [.send ⟨2, 1, .vote, .dummy 1⟩] ++ deliverTo [0, 1, 2] (splitA :: splitB :: splitVotes) ++
  List.replicate 100 .tick
example : (runNet byzantineLeader splitCfg netEmpty splitRun).map (fun s =>
    (s.time, decide (NotarizedDummy byzantineLeader s.sent 1),
      decide (NotarizedBlock byzantineLeader s.sent 1 [wide 1 10]),
      decide (NotarizedBlock byzantineLeader s.sent 1 [wide 1 20]),
      (netStep byzantineLeader splitCfg s (.send ⟨0, 1, .vote, .dummy 1⟩)).isNone,
      (netStep byzantineLeader splitCfg s (.enter 0 2 [.dummy 1])).isNone)) =
    some (105, false, false, false, true, true) := by decide +kernel

/-! ## 2. Slot-key signatures -/

def realHash : HashBytes.Hash :=
  Cshake256.Fast.cshake256Fast simplexAuthDomainBytes

/-- A hash with one output: every opening of every slot key is accepted under it. -/
def constHash : HashBytes.Hash := fun _ => HashBytes.be 32 7

def saltOf : NodeId → Nat → Kind → ByteArray :=
  fun n v _ => bytesOfList (List.replicate 32 (UInt8.ofNat (16 * n + v)))

def blockA : Chain := [wide 1 401]

/-- Signed in view 1, oldest first: the proposal, three honest votes, the Byzantine vote. -/
def signLog : List Msg :=
  prop proto4 1 blockA :: (votesOf [0, 1, 2] 1 blockA ++ [⟨3, 1, .vote, .block [wide 1 666]⟩])

def sign (m : Msg) : SignedSimplexMsg := ⟨m, saltOf m.sender m.view m.kind⟩

def forgedVote : SignedSimplexMsg := ⟨⟨0, 1, .vote, .block [wide 1 666]⟩, saltOf 3 1 .vote⟩
def replayedSig : SignedSimplexMsg := ⟨⟨0, 1, .vote, .block [wide 1 666]⟩, saltOf 0 1 .vote⟩

theorem honestKeys (H : HashBytes.Hash) (hH : ∀ bs, (H bs).length = 32) :
    HonestSlotKeys H 4096 (KeyDirectory.derive H signLog saltOf) proto4 signLog saltOf :=
  KeyDirectory.derive_honestSlotKeys H 4096 200 proto4 signLog saltOf hH (by decide +kernel)
    (fun n v k => by simp [saltOf, bytesOfList_toList]) (by decide +kernel) (by decide)

/-- Under real cSHAKE the honest trace verifies; forgery and signature replay are refused. -/
theorem real_signatures :
    verifySignedSent (commitSlotSigScheme realHash 4096) (KeyDirectory.derive realHash signLog saltOf)
      proto4.committee (signLog.map sign) = true ∧
    verifySignedMsg (commitSlotSigScheme realHash 4096) (KeyDirectory.derive realHash signLog saltOf)
      proto4.committee forgedVote = false ∧
    verifySignedMsg (commitSlotSigScheme realHash 4096) (KeyDirectory.derive realHash signLog saltOf)
      proto4.committee replayedSig = false := by
  decide +kernel

def isForgery {α : Sort _} {β : Sort _} : PSum α β → Bool
  | .inl _ => false
  | .inr _ => true

theorem forged_ver :
    verifySignedSent (commitSlotSigScheme constHash 4096)
      (KeyDirectory.derive constHash signLog saltOf) proto4.committee [forgedVote] = true := by
  decide +kernel

theorem forged_oracle : HonestSigningOracle proto4 [] signLog [forgedVote] := by
  intro pre sm suf hEq _ hIn
  have hmem : sm ∈ [forgedVote] := by rw [hEq]; simp
  rw [List.mem_singleton] at hmem
  subst hmem
  exact absurd hIn (by decide +kernel)

/-- Under the constant hash the forged vote is accepted and the extractor returns it. -/
theorem forged_extracted :
    isForgery (extractForgedVoteSignature (commitSlotSigScheme constHash 4096)
      (KeyDirectory.derive constHash signLog saltOf) proto4 signLog [forgedVote]
      forged_ver forged_oracle) = true := by
  decide +kernel

/-- **The reduction, run.** The accepted forgery becomes a collision of the hash that let it in. -/
theorem constHash_collides : HashBytes.Collision constHash := by
  cases h : extractForgedVoteSignature (commitSlotSigScheme constHash 4096)
      (KeyDirectory.derive constHash signLog saltOf) proto4 signLog [forgedVote]
      forged_ver forged_oracle with
  | inl _ =>
    have hf := forged_extracted
    rw [h] at hf
    cases hf
  | inr w =>
    exact (forgedSignature_reduces_to_hashCollision constHash 4096 _ proto4 signLog saltOf
        (honestKeys constHash (fun _ => by simp [constHash, HashBytes.length_be])) w).toCollisionAmong.global

theorem signed_oracle : HonestSigningOracle proto4 [] signLog (signLog.map sign) := by
  intro pre sm suf he hon _
  change [sign (prop proto4 1 blockA), sign ⟨0, 1, .vote, .block blockA⟩,
    sign ⟨1, 1, .vote, .block blockA⟩, sign ⟨2, 1, .vote, .block blockA⟩,
    sign ⟨3, 1, .vote, .block [wide 1 666]⟩] = pre ++ sm :: suf at he
  cases pre with
  | nil =>
    simp only [List.nil_append, List.cons.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    decide +kernel
  | cons x pre =>
    simp only [List.cons_append, List.cons.injEq] at he
    obtain ⟨rfl, he⟩ := he
    cases pre with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      decide +kernel
    | cons x pre =>
      simp only [List.cons_append, List.cons.injEq] at he
      obtain ⟨rfl, he⟩ := he
      cases pre with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        decide +kernel
      | cons x pre =>
        simp only [List.cons_append, List.cons.injEq] at he
        obtain ⟨rfl, he⟩ := he
        cases pre with
        | nil =>
          simp only [List.nil_append, List.cons.injEq] at he
          obtain ⟨rfl, rfl⟩ := he
          decide +kernel
        | cons x pre =>
          simp only [List.cons_append, List.cons.injEq] at he
          obtain ⟨rfl, he⟩ := he
          cases pre with
          | nil =>
            simp only [List.nil_append, List.cons.injEq] at he
            obtain ⟨rfl, rfl⟩ := he
            cases hon.2
          | cons x pre =>
            simp only [List.cons_append, List.cons.injEq] at he
            obtain ⟨rfl, he⟩ := he
            cases pre <;> cases he

def honestObj : SignedSlotTraceObj :=
  ⟨proto4, KeyDirectory.derive realHash signLog saltOf, signLog, saltOf, signLog.map sign⟩
def honestJudgment := signedSimplexCompJudge realHash 4096 honestObj real_signatures.1 signed_oracle
  (honestKeys realHash (fun bs => by
    rw [realHash, Cshake256.Fast.cshake256Fast_eq]
    exact Cshake256.cshake256Bytes_length _ _))
example : isForgery honestJudgment = false := by decide +kernel

/-- The finite judge actually returns a pair drawn from the rejected trace's slot scope. -/
def forgedObj : SignedSlotTraceObj :=
  ⟨proto4, KeyDirectory.derive constHash signLog saltOf, signLog, saltOf, [forgedVote]⟩
def finiteJudgment := signedSimplexCompJudge constHash 4096 forgedObj forged_ver forged_oracle
  (honestKeys constHash (fun _ => by simp [constHash, HashBytes.length_be]))
def collisionBranch {A B : Sort _} : PSum A B → Bool
  | .inl _ => false
  | .inr _ => true
example : collisionBranch finiteJudgment = true := by decide +kernel
example : HashBytes.CollisionAmong constHash (fun x => x ∈ slotTracePreimages forgedObj) := by
  cases h : finiteJudgment with
  | inl w =>
    have hc : collisionBranch finiteJudgment = true := by decide +kernel
    rw [h] at hc; cases hc
  | inr c => exact c.toCollisionAmong

/-! ## 3. The irreversible outbox -/

def checkOutboxErr (res : Except OutboxRefusal OutboxState) (expected : OutboxRefusal) : Bool :=
  match res with
  | .error r => r == expected
  | .ok _ => false

def payloadA : ByteArray := bytesOfList [0xDE, 0xAD, 0xBE, 0xEF]
def tampered : ByteArray := bytesOfList [0xFF, 0x00, 0xFF, 0x00]

/-- `effectCommitNat 10 .irreversibleActuation payloadA`, written out. -/
def commitA : Nat := 79817041280646677348372407200226764119291410642631118685939725383524999737416

theorem commitA_eq : effectCommitNat 10 .irreversibleActuation payloadA = commitA := by
  decide +kernel

def chainA : Chain := [.block 1 commitA]

/-- View 1 finalized on `chainA`, newest message first. -/
def sentA : Sent :=
  (finsOf [0, 1, 2] 1 chainA).reverse ++ (votesOf [0, 1, 2] 1 chainA).reverse ++
    [prop proto4 1 chainA]

/-- The same view with the votes but no finalize vote. -/
def sentVotesOnly : Sent := (votesOf [0, 1, 2] 1 chainA).reverse ++ [prop proto4 1 chainA]

theorem sentA_reach : Reach proto4 sentA ∧ SentSteps proto4 [] sentA := by
  have hrun : (runNet proto4 cfg netEmpty (viewLate proto4 [0, 1, 2] 1 [] chainA [])).map
      (fun s => s.sent) = some sentA := by decide +kernel
  cases h : runNet proto4 cfg netEmpty (viewLate proto4 [0, 1, 2] 1 [] chainA []) with
  | none => rw [h] at hrun; cases hrun
  | some s =>
    rw [h] at hrun
    simp only [Option.map_some] at hrun
    injection hrun with hs
    have hr := runNet_reach _ h Reach.nil
    have hsteps : ∀ (evs : List NetEvent) {a b : NetState},
        runNet proto4 cfg a evs = some b → SentSteps proto4 a.sent b.sent := by
      intro evs
      induction evs with
      | nil =>
        intro a b hab
        have hab' : some a = some b := hab
        injection hab' with hab'
        subst hab'
        exact SentSteps.refl _
      | cons e es ih =>
        intro a b hab
        obtain ⟨m, h1, h2⟩ := runNet_cons.1 hab
        rcases netStep_sent h1 with hs' | hs'
        · have := ih h2
          rw [hs'] at this
          exact this
        · exact sentSteps_trans (SentSteps.step (SentSteps.refl _) hs') (ih h2)
    have hst : SentSteps proto4 [] s.sent := hsteps _ h
    rw [hs] at hr hst
    exact ⟨hr, hst⟩

def certA : FinCert := ⟨1, chainA, [0, 1, 2]⟩

def initOutbox : OutboxState where
  gatekeeperPd         := 3
  highWaterNullifier   := 0
  escrowVaultBalance   := 500
  readAuditCount       := 0
  activeEscrows        := []
  settledEscrowTotal   := 0
  dispatchedActuations := []

def reqRead : OutboxEffectReq where
  nullifierId   := 1
  effectClass   := .idempotentRead
  targetView    := 1
  proposedChain := []
  finCert?      := none
  escrowBond?   := none
  spsc          := ⟨0, bytesOfList [0x01]⟩

def reqAct : OutboxEffectReq where
  nullifierId   := 10
  effectClass   := .irreversibleActuation
  targetView    := 1
  proposedChain := chainA
  finCert?      := some certA
  escrowBond?   := none
  spsc          := ⟨0, payloadA⟩

/-- An optimistic escrow on a branch `[.block 1 999999]` that view 1 does not finalize. -/
def reqEscrow : OutboxEffectReq where
  nullifierId   := 5
  effectClass   := .compensatableEscrow
  targetView    := 1
  proposedChain := [.block 1 999999]
  finCert?      := none
  escrowBond?   := some ⟨100, 25⟩
  spsc          := ⟨0, bytesOfList [0x77, 0x88]⟩

def audit (sent : Sent) (st : OutboxState) (req : OutboxEffectReq) :=
  auditOutboxStep proto4 sampleValidPartition sent st req

/-- Each refusal by its name: the snapshot is not the committed bytes; no certificate; a
    certificate that does not check (votes without finalize votes); a channel that is not the
    gatekeeper's; an underfunded bond. -/
example :
    checkOutboxErr (audit sentA initOutbox { reqAct with spsc := ⟨0, tampered⟩ })
      (.unfinalizedOrMismatchedBlockCommit 10 1) = true ∧
    checkOutboxErr (audit sentA initOutbox { reqAct with finCert? := none })
      (.missingFinalityCert 10) = true ∧
    checkOutboxErr (audit sentVotesOnly initOutbox reqAct) (.invalidFinalityCert 10 1) = true ∧
    checkOutboxErr (audit sentA initOutbox { reqAct with spsc := ⟨7, payloadA⟩ })
      (.invalidSpscChannel 7) = true ∧
    checkOutboxErr (audit [] initOutbox { reqEscrow with escrowBond? := some ⟨900, 25⟩ })
      (.underfundedEscrowBond 900 25 500) = true := by
  decide +kernel

def st1 : OutboxState := (stepOutbox proto4 sampleValidPartition [] initOutbox reqRead).getD initOutbox
def st2 : OutboxState := (stepOutbox proto4 sampleValidPartition [] st1 reqEscrow).getD initOutbox
def st3Mid : OutboxState := (stepOutbox proto4 sampleValidPartition sentA st2 reqAct).getD initOutbox
def st3 : OutboxState := (reconcileEscrowsWithCert proto4 sentA certA st3Mid).getD initOutbox

theorem step1 : stepOutbox proto4 sampleValidPartition [] initOutbox reqRead = some st1 := by
  decide +kernel
theorem step2 : stepOutbox proto4 sampleValidPartition [] st1 reqEscrow = some st2 := by
  decide +kernel
theorem step3 : stepOutbox proto4 sampleValidPartition sentA st2 reqAct = some st3Mid := by
  decide +kernel
theorem rec3 : reconcileEscrowsWithCert proto4 sentA certA st3Mid = some st3 := by
  decide +kernel

/-- The orphaned escrow is rolled back (75 refunded, 25 compensation kept, total 500 conserved),
    the actuation went out once with the committed bytes, and its nullifier is spent. -/
example :
    st3.escrowVaultBalance = 475 ∧ st3.settledEscrowTotal = 25 ∧ st3.activeEscrows = [] ∧
    st3.dispatchedActuations.map
      (fun a => (a.nullifierId, a.dispatchedPayload.data.toList)) = [(10, [0xDE, 0xAD, 0xBE, 0xEF])] ∧
    checkOutboxErr (audit sentA st3 reqAct) (.staleOrDuplicateNullifier 10 10) = true := by
  decide +kernel

-- Compare states by the kernel's evaluation above, not the elaborator's.
attribute [irreducible] st1 st2 st3Mid st3

def turns : List OutboxTurn :=
  [⟨[], reqRead, none⟩, ⟨[], reqEscrow, none⟩, ⟨sentA, reqAct, some certA⟩]

theorem turns_valid :
    ValidOutboxTrace proto4 sampleValidPartition [] initOutbox turns sentA st3 := by
  have hIso : checkMicrokitIsolation sampleValidPartition = true := by decide +kernel
  exact ⟨Reach.nil, SentSteps.refl [], st1, st1, step1, rfl,
    ⟨Reach.nil, SentSteps.refl [], st2, st2, step2, rfl,
      ⟨Reach.nil, sentA_reach.2, st3Mid, st3, step3, rec3,
        ⟨rfl, rfl, sentA_reach.1, hIso⟩⟩⟩⟩

/-- The library theorems on this trace: capDL non-interference, at-most-once, conservation; no
    other bytes fit the finalized commitment; the spent nullifier is refused whatever comes. -/
theorem turns_safe :
    (st3.dispatchedActuations.map DispatchedActuation.nullifierId).Nodup ∧
    st3.escrowVaultBalance + lockedEscrowDeposits st3.activeEscrows + st3.settledEscrowTotal =
      initOutbox.escrowVaultBalance + lockedEscrowDeposits initOutbox.activeEscrows +
        initOutbox.settledEscrowTotal ∧
    (∀ a ∈ st3.dispatchedActuations, ∀ other : ByteArray,
      other.data.toList.length < OutboxBound64 →
      a.chain.getLast? = some (.block a.view
        (effectCommitNat a.nullifierId .irreversibleActuation other)) →
      other = a.dispatchedPayload ∨
        HashBytes.CollisionAmong (Cshake256.cshake256Bytes outboxEffectDomain.data.toList)
          (fun x => x = encodeEffectPreimage a.nullifierId .irreversibleActuation a.dispatchedPayload ∨
            x = encodeEffectPreimage a.nullifierId .irreversibleActuation other)) ∧
    (∀ a ∈ st3.dispatchedActuations, ∀ (P' : Protocol) (sent : Sent) (req : OutboxEffectReq),
      req.effectClass ≠ .idempotentRead → req.nullifierId = a.nullifierId →
      stepOutbox P' sampleValidPartition sent st3 req = none) := by
  have hApex := firmament_sel4_copy_before_verify_and_irreversible_outbox_safe rfl turns_valid
  exact ⟨hApex.2.2.1, hApex.2.2.2.1,
    dispatched_payload_bound_to_finalized_commit rfl turns_valid,
    dispatched_nullifier_never_replays rfl turns_valid⟩

/-! ## 4. Teeth and the axiom audit -/

-- An honest rule that lets a node send anything (a dummy vote before its timer, say).
#tooth Obend.Consensus.SimplexLiveness.gst_honest_leader_finalizes by mutation
  Obend.Consensus.SimplexLiveness.honestSendOk := fun _ _ _ _ => true

-- Without the width check two messages share signed bytes.
#tooth Obend.Consensus.SimplexLiveness.signableByteArray_injective by mutation
  Obend.Consensus.SimplexLiveness.msgCanonical := fun _ => true

-- A channel check without the length bound: the commitment no longer binds the payload.
#tooth Obend.Vault.IrreversibleOutbox.dispatched_payload_bound_to_finalized_commit by mutation
  Obend.Vault.IrreversibleOutbox.checkSpscChannelToGatekeeper := fun _ _ _ _ => .ok ()

-- Minting refunds on rollback breaks vault conservation.
#tooth Obend.Vault.IrreversibleOutbox.reconcileEscrowsWithCert_conserves by mutation
  Obend.Vault.IrreversibleOutbox.reconcileEscrowList := fun _ _ _ => ([], 999, 0)

#assert_axioms_tree

end Obend.Tests.SimplexLivenessAndOutbox
end
