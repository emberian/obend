/-
# The axiom census: every constant of the library, one check

Imports every file under `Obend/` and ends in `#assert_axioms_tree` (`Obend/AssertAxioms.lean`):
the build fails if any constant declared in the library, public or private, rests on `sorryAx` or
a declared axiom. The compiled trust (`native_decide`'s `…._native…` axioms) is counted and
reported in the verdict line, not refused; each such theorem carries its own `#assert_compiled`.

This file is deliberately not a `module`. A `module` may import only modules, so it could not
see the legacy leaves (`Core/Teeth/*`, `Core/Proofs/DataBudget`, …), and it sees an imported
theorem whose body is not exposed only as an axiom, which the census would refuse; `import all`
fixes the second and not the first. A plain file imports every module with its private part.
`Obend.lean` does not import this file; `lake build` builds it with the rest of the `Obend` glob.

The first command refuses a file under `Obend/` that this list does not import. It runs when this
file is rebuilt, that is, when anything it imports changes; a new leaf added alone is caught at the
next such rebuild, not at its own.
-/
import Obend
import Obend.AssertAxioms
import Obend.AssertCompiled
import Obend.Core.AliasExposure
import Obend.Core.Assumptions
import Obend.Core.Backend
import Obend.Core.Bidirectional
import Obend.Core.CanonicalExtension
import Obend.Core.Capacity
import Obend.Core.Check
import Obend.Core.Checkpoint
import Obend.Core.Collect
import Obend.Core.Data
import Obend.Core.DecisionReduction
import Obend.Core.Digest
import Obend.Core.EquiRecursiveAgreement
import Obend.Core.EquiRecursiveLookup
import Obend.Core.EquiRecursiveSubstitutionTransport
import Obend.Core.Extensions
import Obend.Core.FieldCongruence
import Obend.Core.FilteredStream
import Obend.Core.FilteredStreamCompleteness
import Obend.Core.FilteredStreamSoundness
import Obend.Core.FilteredStreamSteps
import Obend.Core.FiniteBisimulation
import Obend.Core.FinitePresentation
import Obend.Core.FiniteRowLaws
import Obend.Core.Graded
import Obend.Core.Interaction
import Obend.Core.Invariant
import Obend.Core.LegacyAgreement
import Obend.Core.Machine
import Obend.Core.MachineFast
import Obend.Core.MachineTyping
import Obend.Core.Packet
import Obend.Core.Proofs.Adequacy
import Obend.Core.Proofs.BidirectionalCompleteness
import Obend.Core.Proofs.CheckCompletenessObstruction
import Obend.Core.Proofs.CheckTeeth
import Obend.Core.Proofs.CheckpointRoundTrip
import Obend.Core.Proofs.Collect
import Obend.Core.Proofs.Completeness
import Obend.Core.Proofs.DataBudget
import Obend.Core.Proofs.DataSoundness
import Obend.Core.Proofs.DigestChecks
import Obend.Core.Proofs.EquiRecursiveBoundary
import Obend.Core.Proofs.EquiRecursiveSubstitution
import Obend.Core.Proofs.EquiRecursiveTeeth
import Obend.Core.Proofs.Force
import Obend.Core.Proofs.Forcing.Agree
import Obend.Core.Proofs.Forcing.Back
import Obend.Core.Proofs.Forcing.BackFail
import Obend.Core.Proofs.Forcing.Chain
import Obend.Core.Proofs.Forcing.Converse
import Obend.Core.Proofs.Forcing.Demand
import Obend.Core.Proofs.Forcing.Extract
import Obend.Core.Proofs.Forcing.Nest
import Obend.Core.Proofs.Forcing.Pend
import Obend.Core.Proofs.Forcing.Run
import Obend.Core.Proofs.Forcing.Segment
import Obend.Core.Proofs.Forcing.Switch
import Obend.Core.Proofs.GroundExecution
import Obend.Core.Proofs.Hole
import Obend.Core.Proofs.LedgerPoles
import Obend.Core.Proofs.Preservation
import Obend.Core.Proofs.Preservation.Base
import Obend.Core.Proofs.Preservation.Cases.Activities
import Obend.Core.Proofs.Preservation.Cases.Arithmetic
import Obend.Core.Proofs.Preservation.Cases.Functions
import Obend.Core.Proofs.Preservation.Cases.Pairs
import Obend.Core.Proofs.Preservation.Cases.Records
import Obend.Core.Proofs.Preservation.Cases.Sums
import Obend.Core.Proofs.Settle
import Obend.Core.Proofs.StepCases
import Obend.Core.Proofs.Substitution
import Obend.Core.Proofs.Templates
import Obend.Core.Proofs.TypedSubstitution
import Obend.Core.RecursiveAgreement
import Obend.Core.RecursiveRows
import Obend.Core.RelationalRowSearch
import Obend.Core.ResidualNominalPath
import Obend.Core.ResourcePredicate
import Obend.Core.ResourceSemantics
import Obend.Core.ResourceSubstitution
import Obend.Core.ResourceValidity
import Obend.Core.RowAlphabet
import Obend.Core.RowCongruence
import Obend.Core.RowExposureInvariance
import Obend.Core.RowHit
import Obend.Core.RowResourceSafety
import Obend.Core.RuntimeOrigins
import Obend.Core.SubstitutionBisimulation
import Obend.Core.SubstitutionExposure
import Obend.Core.SubstitutionResidual
import Obend.Core.SubstitutionResidualTransport
import Obend.Core.SubstitutionResourceCongruence
import Obend.Core.SubstitutionRows
import Obend.Core.SubstitutionStreamSteps
import Obend.Core.Teeth.BackFail
import Obend.Core.Teeth.Collect
import Obend.Core.Teeth.CollectTyping
import Obend.Core.Teeth.CollectYield
import Obend.Core.Teeth.DataSoundness
import Obend.Core.Teeth.Force
import Obend.Core.TemplateDischarge
import Obend.Core.Term
import Obend.Core.TermTraverse
import Obend.Core.Traverse
import Obend.Core.Ty
import Obend.Core.TypeGraph
import Obend.Core.TypeGraphAlias
import Obend.Core.TypeGraphHead
import Obend.Core.TypeGraphResource
import Obend.Core.WeightedResource
import Obend.Core.WeightedRowSafety
import Obend.Digest.Class
import Obend.Digest.Cshake256
import Obend.Digest.Cshake256.Fast
import Obend.Digest.Cshake256.Seam
import Obend.Digest.Cshake256.Spec
import Obend.Digest.HashBytes
import Obend.Doc
import Obend.Doc.Backlinks
import Obend.Doc.Graph
import Obend.Doc.Merge
import Obend.Doc.Patch
import Obend.Doc.Render
import Obend.Doc.Section
import Obend.Elab
import Obend.Elab.Coerce
import Obend.Elab.Gate
import Obend.Elab.Prepare
import Obend.Elab.Proofs.AliasFree
import Obend.Elab.Proofs.CoerceProbes
import Obend.Elab.Proofs.PrepareChecks
import Obend.Elab.Proofs.PrepareProbes
import Obend.Elab.Proofs.Refines
import Obend.Elab.Work
import Obend.Equiv.Ahead
import Obend.Equiv.Behaviour
import Obend.Equiv.FareTests
import Obend.Equiv.Fields
import Obend.Equiv.Reduction
import Obend.Equiv.Simulation
import Obend.Just
import Obend.Law
import Obend.Law.Claim
import Obend.Law.Inherit
import Obend.Law.Proofs.Claim
import Obend.Law.Proofs.Eval
import Obend.Law.Machine
import Obend.Law.Proofs.Inherit
import Obend.Law.Proofs.LawJudgeTeeth
import Obend.Law.Proofs.Machine
import Obend.Law.Proofs.MachineTeeth
import Obend.Law.Proofs.Run
import Obend.Law.Proofs.Std
import Obend.Law.Proofs.Typing
import Obend.Law.Proofs.TypingTeeth
import Obend.Law.Run
import Obend.Law.Std
import Obend.Law.Syntax
import Obend.Main
import Obend.Run
import Obend.Run.Control
import Obend.Run.ControlExample
import Obend.Run.Core4
import Obend.Run.Core4Example
import Obend.Run.LawJudge
import Obend.Run.Negotiation
import Obend.Run.Proofs.Control
import Obend.Run.Proofs.Core4
import Obend.Run.Proofs.Interpret
import Obend.Run.Proofs.Invariant
import Obend.Run.Runner
import Obend.Run.Spec
import Obend.Slot
import Obend.Slot.Budget
import Obend.Slot.Calculus
import Obend.Slot.Core4
import Obend.Slot.Integrity
import Obend.Slot.PolySlot
import Obend.Slot.Proofs.Negotiation
import Obend.Slot.Proofs.Protocol
import Obend.Slot.Proofs.ProtocolTyping
import Obend.Slot.Protocol
import Obend.Slot.Repair
import Obend.Slot.Selection
import Obend.Slot.World
import Obend.Spec
import Obend.Spec.Annotated
import Obend.Spec.C4
import Obend.Spec.Capture
import Obend.Spec.Contract
import Obend.Spec.DataWire
import Obend.Spec.Ecosystem
import Obend.Spec.Elaborate
import Obend.Spec.FrontEnd
import Obend.Spec.Identity
import Obend.Spec.Law
import Obend.Spec.LawCompile
import Obend.Spec.PackageLaw
import Obend.Spec.Parse
import Obend.Spec.Preview
import Obend.Spec.Proofs.C4Vectors
import Obend.Spec.Proofs.Contract
import Obend.Spec.Proofs.Ecosystem
import Obend.Spec.Proofs.FrontEndAdequacy
import Obend.Spec.Proofs.Law
import Obend.Spec.Proofs.LawCompile
import Obend.Spec.Proofs.LawCompileTeeth
import Obend.Spec.Proofs.PackageLaw
import Obend.Spec.Proofs.SpecificationClosure
import Obend.Spec.Proofs.TermWire
import Obend.Spec.Sha256
import Obend.Spec.Syntax
import Obend.Spec.Types
import Obend.Spec.Workspace
import Obend.Tactic.Cases
import Obend.Tactic.Fuel
import Obend.Tactic.MonadicReduction
import Obend.Tactic.Tooth
import Obend.Tactic.ToothChecks
import Obend.Vault
import Obend.Vault.Cli
import Obend.Vault.Json
import Obend.Vault.Law
import Obend.Vault.Page
import Obend.Vault.Store
import Obend.Vault.Teeth

open Lean Elab Command in
run_cmd do
  let imported := (← getEnv).header.moduleNames
  let files ← System.FilePath.walkDir "Obend"
  let sources := files.filter (·.extension == some "lean")
  if sources.isEmpty then
    throwError "census: no sources under Obend/ from {← IO.currentDir}; cannot check coverage"
  let mut missing : Array Name := #[]
  for file in sources do
    let module := (file.withExtension "").components.foldl Name.str .anonymous
    unless module == `Obend.Census || imported.contains module do
      missing := missing.push module
  unless missing.isEmpty do
    throwError "census: {missing.size} library modules are not imported here: {missing.toList}"

#assert_axioms_tree
