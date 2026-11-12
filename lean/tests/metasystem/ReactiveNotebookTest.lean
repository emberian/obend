module
public import Obend.Doc.ReactiveNotebook
meta import Obend.Doc.ReactiveNotebook
import Obend.Tactic.Tooth
import Obend.AssertAxioms
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
import all Obend.Crypto.Multilinear
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
import all Obend.Doc.ReactiveNotebook
import all Obend.Doc.Render
import all Obend.Doc.Section
import all Obend.Doc.Structured
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
import all Obend.Judge.Lrat
import all Obend.Kind
import all Obend.Kind.Proofs
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
import all Obend.Law.Proofs.Typing
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
import all Obend.Logic.SuperRefines
import all Obend.Polis.VerkleUmem
import all Obend.Receipt
import all Obend.Receipt.Merkle
import all Obend.Run.Control
import all Obend.Run.Core4
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
import all Obend.Slot.SupportSheaf
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
import all Obend.Vault.Form
import all Obend.Vault.FrustumMembrane
import all Obend.Vault.Hyperedge
import all Obend.Vault.Index
import all Obend.Vault.Law
import all Obend.Vault.Page
import all Obend.Vault.Rehydration
import all Obend.Vault.Store

public section
namespace Obend.Doc.Reactive.Tests
open Lean (Json)
set_option autoImplicit false

private def lit (n : Int) : Instruction := ⟨.literal, n⟩
private def input (n : Nat) : Instruction := ⟨.input, n⟩
private def add : Instruction := ⟨.add, 0⟩
private def sub : Instruction := ⟨.sub, 0⟩
private def mul : Instruction := ⟨.mul, 0⟩
private def div : Instruction := ⟨.div, 0⟩

/-- Units are MHz, mV, ps and mW. Supply-dependent delay and dynamic power use integer units. -/
def scientificNotebook : List ReactiveCell := [
  ⟨1, .prose, [], [], [], "Supply/clock sweep: MHz, mV, ps and mW; RC coefficient 200000."⟩,
  ⟨2, .obendCode, [], ["freq_mhz", "vdd_mv"], [[lit 100], [lit 1000]], "clock and supply"⟩,
  ⟨3, .casSymbolic, ["freq_mhz", "vdd_mv"], ["delay_ps", "power_mw"],
    [[lit 200000, input 1, div],
     [input 0, input 1, mul, input 1, mul, lit 1000000, div]], "RC delay and dynamic power"⟩,
  ⟨4, .hardwareSchematic, ["freq_mhz", "delay_ps"], ["margin_ps"],
    [[lit 1000000, input 0, div, input 1, sub]], "clock period minus RC delay"⟩,
  ⟨5, .lawContract, [], ["policy_ok"], [[lit 1]], "independent governance authorization"⟩,
  ⟨6, .ledgerSeat, ["policy_ok"], ["escrow_authorized"], [[input 0, lit 42, mul]], "escrow units released by policy"⟩]

def clockEdit : NotebookAction := ⟨2, [[lit 200], [lit 1000]]⟩
def supplyEdit : NotebookAction := ⟨2, [[lit 200], [lit 800]]⟩
def policyEdit : NotebookAction := ⟨5, [[lit 0]]⟩

example : checkNotebookDag scientificNotebook = true := by decide
example : dirtyCone scientificNotebook 2 = [2, 3, 4] := by decide
example : dirtyCone scientificNotebook 5 = [5, 6] := by decide
example : dirtyCone scientificNotebook 99 = [] := by decide
example : checkNotebookDag (applyEdit clockEdit scientificNotebook) = true := by decide

/-- This checks the concrete diamond values while allowing every full-width receipt function. -/
theorem diamond_values (hash : List UInt8 → BitVec 256) :
    ((editCellAndRecompute ⟨arithmeticRun, hash⟩
      (evalFromScratch ⟨arithmeticRun, hash⟩ scientificNotebook) clockEdit).cells.map
        (fun c => c.result.values)) = [[], [200, 1000], [200, 200], [4800], [1], [42]] := by
  rfl

theorem original_values (hash : List UInt8 → BitVec 256) :
    ((evalFromScratch ⟨arithmeticRun, hash⟩ scientificNotebook).cells.map
      (fun c => c.result.values)) = [[], [100, 1000], [200, 100], [9800], [1], [42]] := by rfl

theorem scientific_edit_equivalence (k : CellKernel) :
    editCellAndRecompute k (evalFromScratch k scientificNotebook) clockEdit =
      evalFromScratch k (applyEdit clockEdit scientificNotebook) :=
  incrementalRecompute_eq_fromScratch k scientificNotebook clockEdit

/-- The three disjoint caches are copied exactly, with arbitrary kernel and receipt outputs. -/
theorem disjoint_cache_identity (k : CellKernel) :
    let old := evalFromScratch k scientificNotebook
    let new := editCellAndRecompute k old clockEdit
    new.cells[0]? = old.cells[0]? ∧ new.cells[4]? = old.cells[4]? ∧
      new.cells[5]? = old.cells[5]? := by
  exact ⟨rfl, rfl, rfl⟩

theorem scientific_json (k : CellKernel) :
    decodeNotebookObnbJson (encodeNotebookObnbJson (evalFromScratch k scientificNotebook)) =
      .ok (evalFromScratch k scientificNotebook) := notebook_roundtrip_obnb_json _

example : ProjectionKind.all.map (fun kind => kindOfJson (kindJson kind)) =
    ProjectionKind.all.map Except.ok := by rfl
example : receiptOfJson (natJson (2^255 + 173)) = .ok (BitVec.ofNat 256 (2^255 + 173)) := by rfl
example : receiptOfJson (natJson (2^256)) = .error "receipt exceeds 256 bits" := by rfl
example : kindOfJson (.str "unknown") = .error "unknown projection kind" := by rfl

private def node (id : Nat) (reads defs : List String) : ReactiveCell :=
  ⟨id, .obendCode, reads, defs, [[lit 1]], ""⟩
example : checkNotebookDag [node 1 ["b"] ["a"], node 2 ["a"] ["b"]] = false := by decide
example : checkNotebookDag
    [node 1 ["c"] ["a"], node 2 ["a"] ["b"], node 3 ["b"] ["c"]] = false := by decide
example : checkNotebookDag [node 1 [] ["a"], node 2 [] ["a"]] = false := by decide
example : checkNotebookDag [node 1 [] ["a", "a"]] = false := by decide
example : checkNotebookDag [node 1 ["a"] ["a"]] = false := by decide
example : checkNotebookDag [node 1 [] ["a"], node 1 [] ["b"]] = false := by decide
example : checkNotebookDag [] = true := by decide

/-- The session premise is inhabited by real stateful edits in both disconnected components. -/
example (k : CellKernel) : ValidNotebookSession k scientificNotebook
    [clockEdit, supplyEdit, policyEdit]
    (editCellAndRecompute k (editCellAndRecompute k
      (editCellAndRecompute k (evalFromScratch k scientificNotebook) clockEdit) supplyEdit)
      policyEdit) := by
  exact .step policyEdit (.step supplyEdit (.step clockEdit (.start _ (by decide))))

example (k : CellKernel) (actions : List NotebookAction) :
    runNotebookSession k (evalFromScratch k scientificNotebook) actions =
      evalFromScratch k (editTrace scientificNotebook actions) :=
  runNotebookSession_eq_fromScratch k scientificNotebook actions

/-- Nonempty, reachable environment changes: supply edits propagate through the full diamond. -/
theorem trace_values (hash : List UInt8 → BitVec 256) :
    ((runNotebookSession ⟨arithmeticRun, hash⟩
      (evalFromScratch ⟨arithmeticRun, hash⟩ scientificNotebook)
      [clockEdit, supplyEdit, policyEdit]).cells.map (fun c => c.result.values)) =
      [[], [200, 800], [250, 128], [4750], [0], [0]] := by rfl

def allProjectionNotebook : List ReactiveCell :=
  ProjectionKind.all.zipIdx.map fun (kind, i) =>
    ⟨i + 1, kind, [], [], [], kind.toLabel⟩

example : checkNotebookDag allProjectionNotebook = true := by decide
example (k : CellKernel) :
    decodeNotebookObnbJson (encodeNotebookObnbJson (evalFromScratch k allProjectionNotebook)) =
      .ok (evalFromScratch k allProjectionNotebook) := notebook_roundtrip_obnb_json _

example (k : CellKernel) : RecomputeExecution k clockEdit
    (evalFromScratch k scientificNotebook).cells (fun _ => 0) []
    (editCellAndRecompute k (evalFromScratch k scientificNotebook) clockEdit).cells [2, 3, 4] := by
  exact recompute_execution k clockEdit (evalFromScratch k scientificNotebook).cells _ []

#tooth checkNotebookDag_acyclic_sound by mutation
  uniqueExports := fun _ => true
#tooth checkNotebookDag_acyclic_sound by mutation
  scheduleCheck := fun _ => true
#tooth incrementalRecompute_eq_fromScratch by mutation
  reuseOrEval := fun _ _ old _ _ => old
#tooth untouchedCells_preserve_receipts by mutation
  reuseOrEval := fun k _ _ c env => evalCell k c env
#tooth dirtyCone_exact by mutation
  nextChanged := fun _ changed _ => changed
#tooth notebook_roundtrip_obnb_json by mutation
  kindJson := fun _ => .str "prose"

#tooth edgesTree_refines by mutation
  edgesTree := fun _ => true
#tooth recomputeTable_refines by mutation
  dirtyTree := fun _ _ _ => false

#print axioms checkNotebookDag_acyclic_sound
#print axioms incrementalRecompute_eq_fromScratch
#print axioms untouchedCells_preserve_receipts
#print axioms notebook_roundtrip_obnb_json
#assert_axioms_tree

/- Run the real cSHAKE256 receipt and JSON parser, beyond the symbolic codec proof. -/
#eval do
  if checkNotebookDag scientificNotebook ≠ true then throw (IO.userError "admission failed")
  let old := evalFromScratch scientificKernel scientificNotebook
  let new := editCellAndRecompute scientificKernel old clockEdit
  let full := evalFromScratch scientificKernel (applyEdit clockEdit scientificNotebook)
  if new ≠ full then throw (IO.userError "incremental/full mismatch")
  let bytes := (encodeNotebookObnbJson new).compress
  let parsed ← match Json.parse bytes with
    | .ok j => pure j
    | .error e => throw (IO.userError e)
  match decodeNotebookObnbJson parsed with
  | .error e => throw (IO.userError e)
  | .ok decoded => if decoded ≠ new then throw (IO.userError "wire roundtrip mismatch")
  if (new.cells[4]?.map (fun (c : CachedCell) => c.result.receipt)) ≠
      (old.cells[4]?.map (fun (c : CachedCell) => c.result.receipt)) then
    throw (IO.userError "law receipt changed")
  IO.println "reactive notebook: diamond, cSHAKE256 receipts and JSON text roundtrip passed"

end Obend.Doc.Reactive.Tests
