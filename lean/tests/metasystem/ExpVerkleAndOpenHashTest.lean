module
import all Init.Data.Array.Basic
public import Obend.Vault.ExpVerkleAndOpenHash
import all Obend.Analysis.Coverage
import all Obend.Apps.ZkNtt.Goldilocks
import all Obend.AssertAxioms
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
import all Obend.Core.Fill
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
import all Obend.Polis.VerkleUmem
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
import all Obend.Vault.ChunkedWorld
import all Obend.Vault.Cost
import all Obend.Vault.DecodeCache
import all Obend.Vault.ExpVerkleAndOpenHash
import all Obend.Vault.Form
import all Obend.Vault.FormCheck
import all Obend.Vault.FormCheckCache
import all Obend.Vault.Hyperedge
import all Obend.Vault.Index
import all Obend.Vault.Json
import all Obend.Vault.Law
import all Obend.Vault.Log
import all Obend.Vault.LogBytes
import all Obend.Vault.Merge
import all Obend.Vault.Page
import all Obend.Vault.Rehydration
import all Obend.Vault.Replay
import all Obend.Vault.Retention
import all Obend.Vault.SegmentLog
import all Obend.Vault.Store
import all Obend.Vault.Transport
import all Obend.Vault.VerkleSnapshotBridge

public section
namespace Obend.Tests.Metasystem.ExpVerkleAndOpenHashTest
open Obend.Vault.ExpVerkleAndOpenHash
set_option autoImplicit false
set_option Elab.async false

#assert_axioms_tree

open Lean Elab Command in
run_cmd do
  for n in [``comparePreimages, ``extractNodeCollision, ``extractOpeningCollision,
      ``verifyExpVerkleOpening_binds_or_collision] do
    let axioms ← liftCoreM (collectAxioms n)
    for a in axioms do
      unless a == ``propext || a == ``Quot.sound do
        throwError "constructive extractor {n} uses {a}"
  logInfo "Opening collision extractors: no choice, compiler trust, or custom axioms."

/-- Fixture hash only: 32 independent byte accumulators. Security theorems quantify over H;
production uses cSHAKE256, never this deliberately inexpensive test function. -/
def fixtureHash : Hash256 := fun bs =>
  ⟨⟨(Array.range 32).map fun j => bs.foldl
    (fun acc b => acc * UInt8.ofNat (2 * j + 3) + b) (UInt8.ofNat j)⟩, by change ((Array.range 32).map _).size = 32; simp⟩

def forest0 : ExpVerkleForestExec := ⟨#[]⟩
def forest1 := appendExpVerkle forest0 17
def forest2 := appendExpVerkle forest1 29
def forest3 := appendExpVerkle forest2 41

def opening := proveExpVerkle fixtureHash forest3 2 1
def root := expVerkleRoot fixtureHash forest3 2

#guard forest3.entries == #[17, 29, 41]
#guard verifyExpVerkleOpening fixtureHash root 1 29 opening
#guard !verifyExpVerkleOpening fixtureHash root 1 30 opening
#guard !verifyExpVerkleOpening fixtureHash root 0 29 opening
#guard !verifyExpVerkleOpening fixtureHash root 3 29 opening
#guard !verifyExpVerkleOpening fixtureHash root 1 29
  { opening with vectors := opening.vectors.map (fun a => a.setIfInBounds 0 (fixtureHash [99])) }

example : Simulates ⟨[17, 29, 41]⟩ forest3 := by
  unfold Simulates specEntries forest3 forest2 forest1 forest0 appendExpVerkle
  rfl
example : expVerkleDepth (2 ^ 32) = 6 := by decide +kernel
example : capacity 6 = 2 ^ 32 := by decide +kernel
example : expVerkleDepth (2 ^ 32) ≤ 6 := expVerkle_depth_le_logLog _ 5 (by decide +kernel)
example : (appendExpVerkle forest3 53).entries[1]? = forest3.entries[1]? :=
  appendExpVerkle_preserves _ _ _ (by decide +kernel)

def table0 := emptyTable 16 3
def table1 := (insert table0 1 17).1
def table2 := (insert table1 17 29).1
def table3 := insertSeq table2 [(33, 41), (49, 53), (65, 67), (1, 99)]
def pointer : SlotPointer := ⟨(0, 1), 1, 17⟩

#guard (probeSlots 1 0 16).length == 4
#guard (probeCoords table0 1).length == 12
#guard lookup table3 1 == some 17
#guard lookup table3 65 == some 67
#guard getSlot table3 (0, 1) == some (1, 17)
#guard verifySlotPointer table3 pointer
#guard !verifySlotPointer table3 { pointer with coordinate := (0, 2) }

example : TableWF table3 := by
  unfold table3 table2 table1
  apply insertSeq_wf
  apply insert_wf
  apply insert_wf
  exact emptyTable_wf _ _

example (xs : List (Key × Val)) : getSlot (insertSeq table1 xs) (0, 1) = some (1, 17) :=
  insertSeq_preserves_all_prior_slots _ _ _ _ (by decide +kernel)

def authenticated := authenticateTable fixtureHash table3
def absence := proveAbsence fixtureHash authenticated 99
#guard verifyAbsenceCert authenticated 99 absence
#guard !verifyAbsenceCert authenticated 1 (proveAbsence fixtureHash authenticated 1)
#guard !verifyAbsenceCert authenticated 99 { absence with coordinates := [] }
#guard !verifyAbsenceCert authenticated 99 { absence with states := [] }
#guard !verifyAbsenceCert authenticated 99 { absence with root := fixtureHash [99] }

example : lookup table3 99 = none ∧
    ∀ p ∈ probeCoords table3 99, ∀ v, getSlot table3 p ≠ some (99, v) :=
  (verifyAbsenceCert_sound fixtureHash authenticated 99 absence
    (verifyAbsenceCert_complete fixtureHash authenticated 99 (by decide +kernel))).2

example : Obend.Vault.ExpVerkleAndOpenHash.importFromChunkedWorld
    (exportToChunkedWorld {} table3 forest3) = some (table3, forest3) :=
  exportToChunkedWorld_roundtrip _ _ _

example : verifySnapshot fixtureHash (buildSnapshot fixtureHash {} table3 forest3 2) = true :=
  buildSnapshot_complete _ _ _ _ _ (by decide +kernel)

example : (expVerkleVaultJudge fixtureHash).Fragment (buildSnapshot fixtureHash {} table3 forest3 2) :=
  True.intro

/-- A full-width root distinct from the expected one, computed constructively. -/
def differentDigest (d : Digest) : Digest :=
  if d = fixtureHash [1] then fixtureHash [2] else fixtureHash [1]

theorem differentDigest_ne (d : Digest) : differentDigest d ≠ d := by
  unfold differentDigest
  split
  next h => rw [h]; decide +kernel
  next h => exact Ne.symm h

theorem badSnapshot_refused (s : ExpVerkleVaultSnapshot) (bad : Digest)
    (h : bad ≠ bindVerkleUmemRoot (exportToChunkedWorld s.world s.table s.forest)) :
    (expVerkleVaultJudge fixtureHash).check 0 { s with umemRoot := bad } () =
      .refused SnapshotRefusal.inconsistentCommitment [] :=
  snapshot_refusal fixtureHash { s with umemRoot := bad } h 0

example (s : ExpVerkleVaultSnapshot) : ∃ bad : Digest,
    (expVerkleVaultJudge fixtureHash).check 0 { s with umemRoot := bad } () =
      .refused SnapshotRefusal.inconsistentCommitment [] := by
  let d := bindVerkleUmemRoot (exportToChunkedWorld s.world s.table s.forest)
  exact ⟨differentDigest d, badSnapshot_refused s (differentDigest d) (differentDigest_ne d)⟩

def vault0 : VaultState := (emptyTable 16 3, ⟨#[]⟩)
def vault1 := (appendVault vault0 1 17).1
def vaultTrace := appendVaultSeq vault1 [(17, 29), (33, 41), (1, 999), (49, 53)]
def linkedSlot : VaultSlotLink := ⟨⟨(0, 1), 1, 17⟩, 0⟩

#guard vaultTrace.2.entries == #[17, 29, 41, 53]
#guard getSlot vaultTrace.1 (0, 1) == some (1, 17)
#guard verifyExpVerkleOpening cshakeHash (commitExpVerkle cshakeHash vaultTrace.2) 0 17
  (openExpVerkle cshakeHash vaultTrace.2 0)
#guard !verifyExpVerkleOpening cshakeHash (commitExpVerkle cshakeHash vaultTrace.2) 0 18
  (openExpVerkle cshakeHash vaultTrace.2 0)

example : VaultLinkValid vaultTrace linkedSlot := by
  apply appendVaultSeq_preserves_links
  exact appendVault_inserted vault0 1 17 (0, 1) (by decide +kernel)

example (xs : List (Key × Val)) : VaultLinkValid (appendVaultSeq vault1 xs) linkedSlot :=
  appendVaultSeq_preserves_links _ _ _
    (appendVault_inserted vault0 1 17 (0, 1) (by decide +kernel))

-- Each mutation replays a universal stored proof, not just a closed fixture.
#tooth leafBytes_injective by mutation leafBytes := fun idx _ => frameBytes [[0], natBytes idx]
#tooth verifyExpVerkleOpening_complete by mutation verifyExpVerkleOpening := fun H r _ v p =>
  decide (0 < p.count ∧ p.count ≤ capacity p.height ∧ H (forestBytes p.count p.height p.treeRoot) = r) &&
    verifyNode H p.height 0 0 v p.treeRoot p.vectors
#tooth nodeBytes_injective by mutation nodeBytes := fun level _ => frameBytes [[1], natBytes level]
#tooth verifyAbsenceCert_sound by mutation verifyAbsenceCert := fun {_} _ _ _ => true
#tooth verifyAbsenceCert_sound by mutation verifyAbsenceCert := fun {_} t k c =>
  decide (c.root = t.root ∧ c.states = c.coordinates.map (getSlot t.table)) &&
    c.states.all (fun s => match s with | none => true | some (key, _) => decide (key ≠ k))
#tooth verifySnapshot_iff by mutation verifySnapshot := fun H s =>
  decide (s.forest.entries.size ≤ capacity s.height) &&
    decide (s.forestRoot = expVerkleRoot H s.forest s.height) &&
    decide (s.tableRoot = tableDigest H s.table) &&
    decide (s.root = H (weldBytes s.forestRoot s.tableRoot s.umemRoot))
#tooth insert_preserves_all_prior_slots by mutation Obend.Vault.ExpVerkleAndOpenHash.insert := fun t k v =>
  (⟨t.levels.modify 0 (fun row => row.setIfInBounds 0 (some (k, v)))⟩, .inserted (0, 0))

end Obend.Tests.Metasystem.ExpVerkleAndOpenHashTest
