module
import all Init.Data.Array.Basic
public import Obend.Vault.WorldTree
import all Obend.Analysis.Coverage
import all Obend.Apps.ZkNtt.Goldilocks
import all Obend.AssertAxioms
import all Obend.Core.AliasExposure
import all Obend.Core.Assumptions
import all Obend.Core.Bidirectional
import all Obend.Core.Brand
import all Obend.Core.Capacity
import all Obend.Core.Check
import all Obend.Core.Code
import all Obend.Core.Data
import all Obend.Core.Digest
import all Obend.Core.EquiRecursiveAgreement
import all Obend.Core.EquiRecursiveLookup
import all Obend.Core.FieldCongruence
import all Obend.Core.Fill
import all Obend.Core.FiniteBisimulation
import all Obend.Core.FinitePresentation
import all Obend.Core.FiniteRowLaws
import all Obend.Core.Invariant
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
import all Obend.Core.Proofs.Conservation
import all Obend.Core.Proofs.DataSoundness
import all Obend.Core.Proofs.FillTyping
import all Obend.Core.Proofs.GroundExecution
import all Obend.Core.Proofs.Preservation.Base.Focus
import all Obend.Core.Proofs.Preservation.Base.Heads
import all Obend.Core.Proofs.Preservation.Base.Insert
import all Obend.Core.Proofs.Preservation.Base.Reusable
import all Obend.Core.Proofs.Preservation.Base.Values
import all Obend.Core.Proofs.Preservation.Base.Weaken
import all Obend.Core.Proofs.Preservation.Cases.Functions
import all Obend.Core.Proofs.Preservation.Cases.Records
import all Obend.Core.Proofs.Preservation.Cases.Sums
import all Obend.Core.Proofs.StepCases
import all Obend.Core.Proofs.SubjectReduction
import all Obend.Core.Proofs.SubjectReduction.Substitution
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
import all Obend.Crypto.BinaryTower256
import all Obend.Crypto.FastRing
import all Obend.Crypto.DualSpine
import all Obend.Crypto.Multilinear
import all Obend.Crypto.PCS
import all Obend.Crypto.Sumcheck
import all Obend.Crypto.Transcript
import all Obend.Digest.Cshake256
import all Obend.Digest.Cshake256.Fast
import all Obend.Digest.Cshake256.Seam
import all Obend.Digest.Cshake256.Spec
import all Obend.Digest.HashBytes
import all Obend.Doc
import all Obend.Doc.Backlinks
import all Obend.Doc.Graph
import all Obend.Doc.Merge
import all Obend.Doc.Patch
import all Obend.Doc.Render
import all Obend.Doc.Section
import all Obend.Doc.Structured
import all Obend.Elab.Coerce
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
import all Obend.Judge.Computational
import all Obend.Judge.Instances
import all Obend.Judge.Lrat
import all Obend.Kind
import all Obend.Kind.Proofs
import all Obend.Law.Claim
import all Obend.Law.Contract
import all Obend.Law.Inherit
import all Obend.Law.Machine
import all Obend.Law.Proofs.Claim
import all Obend.Law.Proofs.Eval
import all Obend.Law.Proofs.Fill
import all Obend.Law.Proofs.Inherit
import all Obend.Law.Proofs.Machine
import all Obend.Law.Proofs.Run
import all Obend.Law.Proofs.Std
import all Obend.Law.Proofs.Typing
import all Obend.Law.Run
import all Obend.Law.Std
import all Obend.Law.Syntax
import all Obend.Ledger.Book
import all Obend.Ledger.Commit
import all Obend.Ledger.Floors
import all Obend.Ledger.Json
import all Obend.Ledger.Register
import all Obend.Ledger.Report
import all Obend.Ledger.Seat
import all Obend.Ledger.Vault
import all Obend.Logic.Claim
import all Obend.Logic.Frame
import all Obend.Logic.Ground
import all Obend.Logic.LateBinding
import all Obend.Logic.Obligation
import all Obend.Logic.Program
import all Obend.Logic.Receipt
import all Obend.Logic.Rewrite
import all Obend.Polis.BlumRam
import all Obend.Reasons
import all Obend.Receipt
import all Obend.Receipt.Merkle
import all Obend.Receipt.Negotiation
import all Obend.Run.Control
import all Obend.Run.Core4
import all Obend.Run.Fold
import all Obend.Run.Fork
import all Obend.Run.Negotiation
import all Obend.Run.Proofs.Control
import all Obend.Run.Proofs.Interpret
import all Obend.Run.Proofs.Invariant
import all Obend.Run.Proofs.Shared
import all Obend.Run.Runner
import all Obend.Run.Shared
import all Obend.Run.Spec
import all Obend.Slot
import all Obend.Slot.Core4
import all Obend.Slot.Integrity
import all Obend.Slot.Proofs.Negotiation
import all Obend.Slot.Proofs.Protocol
import all Obend.Slot.Proofs.ProtocolTyping
import all Obend.Slot.Protocol
import all Obend.Slot.Selection
import all Obend.Slot.World
import all Obend.Spec.C4
import all Obend.Spec.DataWire
import all Obend.Spec.Law
import all Obend.Spec.LawCompile
import all Obend.Spec.LawDial
import all Obend.Spec.Proofs.C4
import all Obend.Spec.Proofs.LawCompile
import all Obend.Tactic.Cases
import all Obend.Tactic.MonadicReduction
import all Obend.Tactic.Tooth
import all Obend.Vault.Affordance
import all Obend.Vault.Branch
import all Obend.Vault.Cost
import all Obend.Vault.DecodeCache
import all Obend.Vault.Form
import all Obend.Vault.FormCheck
import all Obend.Vault.FormCheckCache
import all Obend.Vault.Hyperedge
import all Obend.Vault.Index
import all Obend.Vault.Json
import all Obend.Vault.Law
import all Obend.Vault.Log
import all Obend.Vault.Merge
import all Obend.Vault.Page
import all Obend.Vault.Rehydration
import all Obend.Vault.Replay
import all Obend.Vault.Retention
import all Obend.Vault.Store
import all Obend.Vault.Transport
import all Obend.Vault.WorldTree
import all Obend.Category.Refines
import all Obend.Core.Collect
import all Obend.Core.Proofs.Collect.Compact
import all Obend.Core.Proofs.Collect.Extract
import all Obend.Core.Proofs.Collect.Lockstep
import all Obend.Core.Proofs.Collect.Mark
import all Obend.Core.Proofs.Collect.Rename
import all Obend.Core.Proofs.Collect.Runs
import all Obend.Core.Proofs.Collect.Segment
import all Obend.Core.Proofs.Collect.Statements
import all Obend.Core.Proofs.Collect.Typing
import all Obend.Core.Proofs.Force
import all Obend.Core.Proofs.Preservation
import all Obend.Core.Proofs.Preservation.Cases.Activities
import all Obend.Core.Proofs.Preservation.Cases.Arithmetic
import all Obend.Core.Proofs.Preservation.Cases.Pairs
import all Obend.Core.Proofs.Preservation.Cases.Split
import all Obend.Core.Proofs.Settle
import all Obend.Core.RangeSafe
import all Obend.Crypto.GameSoundness
import all Obend.Hardware.Compiler
import all Obend.Hardware.HDL
import all Obend.Hardware.Types
import all Obend.Leaf.BytecodeRegisterJit
import all Obend.Leaf.Emit
import all Obend.Leaf.Flatten
import all Obend.Leaf.Served
import all Obend.Leaf.Specialize
import all Obend.Leaf.Static
import all Obend.Leaf.UpTo
import all Obend.Lower.Fragment
import all Obend.Lower.Proofs.Book
import all Obend.Consensus.Simplex
import all Obend.Consensus.SimplexProtocol
import all Obend.Logic.SeparationFrame
import all Obend.Polis.CapTP
import all Obend.Run.Durable
import all Obend.Run.Proofs.Durable
import all Obend.Vault.Mandate

public section
namespace Obend.Tests.Metasystem.ExpVerkleAndOpenHashTest
open Obend.Vault.ExpVerkleAndOpenHash
set_option autoImplicit false
set_option Elab.async false

/-- Deliberately inexpensive fixture hash; production uses domain-separated cSHAKE256. -/
def fixtureHash : Hash256 := fun bs =>
  ⟨⟨(Array.range 32).map fun j => bs.foldl
    (fun acc b => acc * UInt8.ofNat (2 * j + 3) + b) (UInt8.ofNat j)⟩,
    by change ((Array.range 32).map _).size = 32; simp⟩

def forest : ExpVerkleForestExec := ⟨#[17,29,41]⟩
def opening := openExpVerkle fixtureHash forest 1
def root := commitExpVerkle fixtureHash forest
#guard verifyExpVerkleOpening fixtureHash root 1 29 opening
#guard !verifyExpVerkleOpening fixtureHash root 1 30 opening
#guard !verifyExpVerkleOpening fixtureHash root 0 29 opening
#guard !verifyExpVerkleOpening fixtureHash root 3 29 opening
#guard !verifyExpVerkleOpening fixtureHash root 1 29 { opening with count := 4 }
#guard !verifyExpVerkleOpening fixtureHash root 1 29 { opening with height := 3 }
#guard !verifyExpVerkleOpening fixtureHash root 1 29
  { opening with vectors := opening.vectors.map (fun a => a.setIfInBounds 0 (fixtureHash [99])) }
-- Reject even a self-consistent noncanonical height/root pair.
#guard !verifyExpVerkleOpening fixtureHash (expVerkleRoot fixtureHash forest 3) 1 29
  (proveExpVerkle fixtureHash forest 3 1)
#guard ([1,2,3,4,5,16,17].all fun n =>
  let f : ExpVerkleForestExec := ⟨(Array.range n).map (BitVec.ofNat 256)⟩
  verifyExpVerkleOpening fixtureHash (commitExpVerkle fixtureHash f) (n-1)
    (BitVec.ofNat 256 (n-1)) (openExpVerkle fixtureHash f (n-1)))
#guard !verifyExpVerkleOpening fixtureHash (commitExpVerkle fixtureHash ⟨#[]⟩) 0 0
  (openExpVerkle fixtureHash ⟨#[]⟩ 0)
example (H : Hash256) (f : ExpVerkleForestExec) (i : Nat) (hi : i < f.entries.size) :
    verifyExpVerkleOpening H (commitExpVerkle H f) i f.entries[i] (openExpVerkle H f i) = true :=
  every_index_opens H f i hi
example (H : Hash256) : verifyExpVerkleOpening H (commitExpVerkle H forest) 1 29
    (openExpVerkle H forest 1) = true := every_index_opens H forest 1 (by decide +kernel)
example : expVerkleDepth (2^32) = 6 := by decide +kernel

def table0 := emptyTable 16 3 (BitVec.ofNat 256 (2^255 + 19))
def table1 := (insert table0 1 17).1
def table := insertSeq table1 [(17,29),(33,41),(49,53),(65,67),(1,999)]
#guard lookup table 1 == some 17
#guard lookup table 65 == some 67
#guard (insert table 1 999).2 == .conflict 17
#guard (probeCoords table 1).length == 12
#guard (searchCount table 1 (probeCoords table 1)).2 ≤ probeBudget table
#guard (searchCount table 999 (probeCoords table 999)).2 == probeBudget table
#guard probeDigest fixtureHash 0 1 0 != probeDigest fixtureHash (BitVec.ofNat 256 (2^255)) 1 0
#guard tableDigest fixtureHash table != tableDigest fixtureHash { table with seed := 0 }

example : TableWF table := by
  unfold table table1
  apply insertSeq_wf
  apply insert_wf
  exact emptyTable_wf _ _ _
example : KeyUnique table := by
  unfold table table1
  apply insertSeq_unique
  · exact insert_wf _ _ _ (emptyTable_wf _ _ _)
  · exact insert_unique _ _ _ (emptyTable_wf _ _ _) (emptyTable_unique _ _ _)
example (t : ElasticOpenTable) (xs : List (Key × Val)) (k : Key) (v : Val) (h : lookup t k = some v) :
    lookup (insertSeq t xs) k = some v := lookup_stable t xs k v h
example (t : ElasticOpenTable) (xs : List (Key × Val)) (p : PhysSlot) (e : Key × Val)
    (h : getSlot t p = some e) : getSlot (insertSeq t xs) p = some e :=
  insertSeq_preserves_all_prior_slots t xs p e h

/-- All six slots lie in every key's windows: worst-case saturation is explicit,
and a refused seventh insertion preserves every previously accepted binding. -/
def clustered := insertSeq (emptyTable 4 2 7) [(1,11),(17,22),(33,33),(49,44),(65,55),(81,66)]
#guard (insert clustered 97 77).2 == .tableFull
#guard lookup clustered 1 == some 11
#guard lookup clustered 81 == some 66
#guard lookup (insert clustered 97 77).1 81 == some 66
#guard (searchCount clustered 97 (probeCoords clustered 97)).2 == 6

def absence := proveAbsence fixtureHash table 999
#guard verifyExpVerkleAbsence fixtureHash (tableDigest fixtureHash table) 999 absence
#guard !verifyExpVerkleAbsence fixtureHash (tableDigest fixtureHash table) 1 (proveAbsence fixtureHash table 1)
#guard !verifyExpVerkleAbsence fixtureHash (tableDigest fixtureHash table) 999 { absence with windows := [] }
#guard !verifyExpVerkleAbsence fixtureHash (tableDigest fixtureHash table) 999
  { absence with windows := absence.windows.drop 1 }
#guard !verifyExpVerkleAbsence fixtureHash (tableDigest fixtureHash table) 999
  { absence with header := { absence.header with seed := 0 } }
#guard !verifyExpVerkleAbsence fixtureHash (fixtureHash [99]) 999 absence
#guard !verifyExpVerkleAbsence fixtureHash (tableDigest fixtureHash table) 999
  { absence with windows := absence.windows.map fun o => { o with state := some (999, 0) } }
#guard verifyExpVerkleAbsence fixtureHash (tableDigest fixtureHash clustered) 97
  (proveAbsence fixtureHash clustered 97)
#guard verifyExpVerkleAbsence fixtureHash (tableDigest fixtureHash (emptyTable 0 0)) 5
  (proveAbsence fixtureHash (emptyTable 0 0) 5)

example (H : Hash256) (t : ElasticOpenTable) (k : Key) (hn : lookup t k = none) :
    verifyExpVerkleAbsence H (tableDigest H t) k (proveAbsence H t k) = true :=
  verifyAbsence_complete H t k hn
example (H : Hash256) (t : ElasticOpenTable) (k : Key) (c : AbsenceCertificate)
    (hc : verifyExpVerkleAbsence H (tableDigest H t) k c = true) :
    lookup t k = none ∨ Nonempty (ScopedCollision H (absencePreimages H t c)) :=
  verifyAbsence_sound_or_collision H t k c hc
example : Obend.Vault.ExpVerkleAndOpenHash.importFromChunkedWorld
    (exportToChunkedWorld {} table forest) = some (table, forest) :=
  exportToChunkedWorld_roundtrip _ _ _

#guard checkSnapshotTable table ⟨#[17,29,41,53,67]⟩
#guard !checkSnapshotTable table forest

def misplaced : ElasticOpenTable :=
  let outside := ((List.range 16).find? fun j => !(probeSlots 1 0 16).contains j).getD 0
  ⟨#[(Array.replicate 16 none).setIfInBounds outside (some (1,17))], 0⟩
#guard !checkSnapshotTable misplaced forest
example (H : Hash256) : verifySnapshot H
    (buildSnapshot H {} (emptyTable 0 0) ⟨#[]⟩ 0) = true :=
  buildSnapshot_complete H {} (emptyTable 0 0) ⟨#[]⟩ 0 (by decide +kernel)
    ((checkSnapshotTable_iff _ _).mp (by decide +kernel))
#tooth checkSnapshotTable_iff by mutation checkSnapshotTable := fun _ _ => true
#tooth verifySnapshot_iff by mutation verifySnapshot := fun _ _ => true
#tooth insert_succeeds_of_vacancy by mutation Obend.Vault.ExpVerkleAndOpenHash.insert :=
  fun t _ _ => (t, .tableFull)

#tooth leafBytes_injective by mutation leafBytes := fun idx _ => frameBytes [[0], natBytes idx]
#tooth nodeBytes_injective by mutation nodeBytes := fun level _ => frameBytes [[1], natBytes level]
#tooth slotBytes_injective by mutation slotBytes := fun _ => []
#tooth headerBytes_injective by mutation headerBytes := fun _ => []
#tooth probe_seed_binding by mutation probePreimage := fun _ k level =>
  frameBytes [[20], Obend.Digest.HashBytes.be 32 k.toNat, natBytes level]
#tooth verifyExpVerkleOpening_binds_or_collision by mutation verifyExpVerkleOpening := fun _ _ _ _ _ => true
#tooth verifyAbsence_sound_or_collision by mutation verifyExpVerkleAbsence := fun _ _ _ _ => true
#tooth verifyAbsence_complete by mutation verifyExpVerkleAbsence := fun _ _ _ _ => false
#tooth lookup_stable by mutation Obend.Vault.ExpVerkleAndOpenHash.insert := fun t k v =>
  (⟨t.levels.modify 0 (fun row => row.setIfInBounds 0 (some (k,v))), t.seed⟩, .inserted (0,0))
#tooth insertSeq_unique by mutation Obend.Vault.ExpVerkleAndOpenHash.insert := fun t k v =>
  (⟨t.levels.modify 0 (fun row => row.setIfInBounds 0 (some (k,v))), t.seed⟩, .inserted (0,0))
#tooth lookup_worst_case by mutation searchCount := fun _ _ ps => (none, ps.length + 1)
-- A separate constructive-extraction gate: the package census permits choice.
open Lean Elab Command in
run_cmd do
  for name in [``comparePreimages, ``extractNodeCollision, ``extractOpeningCollision, ``extractSlotCollision, ``verifyAbsence_sound_or_collision] do
    let axioms ← liftCoreM (collectAxioms name)
    if axioms.contains ``Classical.choice then
      throwError "Constructive audit failed: {name} uses choice"
  logInfo "B1 constructive security audit passed"
#assert_axioms_tree

end Obend.Tests.Metasystem.ExpVerkleAndOpenHashTest
