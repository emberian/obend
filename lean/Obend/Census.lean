/-
# The axiom census: every constant of the library, one check

Imports every file under `Obend/` and ends in `#assert_axioms_tree` (`Obend/AssertAxioms.lean`):
the build fails if any constant declared in the library, public or private, rests on `sorryAx` or
a declared axiom. The compiled trust (`native_decide`'s `…._native…` axioms) is counted and
reported in the verdict line, not refused; each such theorem carries its own `#assert_compiled`.

This file is deliberately not a `module`. A `module` may import only modules, so it could not
see the legacy leaves (`Teeth/Core/*`, `Teeth/Law/*`, …), and it sees an imported
theorem whose body is not exposed only as an axiom, which the census would refuse; `import all`
fixes the second and not the first. A plain file imports every module with its private part.
`Obend.lean` does not import this file. It is tier 2 with the teeth: `lake build Obend.Census Teeth`
(`lakefile.toml`), run before a push; `lake build` does not build it.

The first command refuses a file under `Obend/` that this list does not import, and a module outside
`Obend/Teeth/` that the `Obend` library's globs in `lakefile.toml` do not name (`lake build` would
skip it unless something imports it). It runs when this file is rebuilt, that is, when anything it
imports changes; a new leaf added alone is caught at the next such rebuild, not at its own.
-/
import Obend
import Obend.AssertAxioms
import Obend.AssertCompiled
import Obend.Core.AliasExposure
import Obend.Core.Assumptions
import Obend.Core.Bidirectional
import Obend.Core.CanonicalExtension
import Obend.Core.Capacity
import Obend.Core.Check
import Obend.Core.Checkpoint
import Obend.Core.Code
import Obend.Core.Collect
import Obend.Core.Data
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
import Obend.Core.Interaction
import Obend.Core.Invariant
import Obend.Core.LegacyAgreement
import Obend.Core.Machine
import Obend.Core.MachineFast
import Obend.Core.MachineTyping
import Obend.Core.Packet
import Obend.Core.Proofs.Adequacy
import Obend.Core.Proofs.Adequacy.Birth
import Obend.Core.Proofs.Adequacy.CasesControl
import Obend.Core.Proofs.Adequacy.CasesEval
import Obend.Core.Proofs.Adequacy.CasesReturn
import Obend.Core.Proofs.Adequacy.Defs
import Obend.Core.Proofs.Adequacy.Examples
import Obend.Core.Proofs.Adequacy.Graph
import Obend.Core.Proofs.Adequacy.Meaning
import Obend.Core.Proofs.Adequacy.Origins
import Obend.Core.Proofs.Adequacy.Progress
import Obend.Core.Proofs.Adequacy.Reach
import Obend.Core.Proofs.Adequacy.Run
import Obend.Core.Proofs.Adequacy.Safety
import Obend.Core.Proofs.Adequacy.SafetyRaw
import Obend.Core.Proofs.Adequacy.Scoped
import Obend.Core.Proofs.Adequacy.Sound
import Obend.Core.Proofs.Adequacy.Source
import Obend.Core.Proofs.Adequacy.StepRaw
import Obend.Core.Proofs.BidirectionalCompleteness
import Obend.Core.Proofs.CheckCompletenessObstruction
import Obend.Core.Proofs.CheckpointRoundTrip
import Obend.Core.Proofs.Collect
import Obend.Core.Proofs.Collect.Compact
import Obend.Core.Proofs.Collect.Extract
import Obend.Core.Proofs.Collect.Lockstep
import Obend.Core.Proofs.Collect.Mark
import Obend.Core.Proofs.Collect.Rename
import Obend.Core.Proofs.Collect.Runs
import Obend.Core.Proofs.Collect.Segment
import Obend.Core.Proofs.Collect.Statements
import Obend.Core.Proofs.Collect.Typing
import Obend.Core.Proofs.Completeness
import Obend.Core.Proofs.Conservation
import Obend.Core.Proofs.DataSoundness
import Obend.Core.Proofs.DigestChecks
import Obend.Core.Proofs.EquiRecursiveBoundary
import Obend.Core.Proofs.EquiRecursiveSubstitution
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
import Obend.Core.Proofs.Preservation.Base.Focus
import Obend.Core.Proofs.Preservation.Base.Heads
import Obend.Core.Proofs.Preservation.Base.Insert
import Obend.Core.Proofs.Preservation.Base.Reusable
import Obend.Core.Proofs.Preservation.Base.Values
import Obend.Core.Proofs.Preservation.Base.Weaken
import Obend.Core.Proofs.Preservation.Cases.Activities
import Obend.Core.Proofs.Preservation.Cases.Arithmetic
import Obend.Core.Proofs.Preservation.Cases.Functions
import Obend.Core.Proofs.Preservation.Cases.Pairs
import Obend.Core.Proofs.Preservation.Cases.Records
import Obend.Core.Proofs.Preservation.Cases.Sums
import Obend.Core.Proofs.Settle
import Obend.Core.Proofs.StepCases
import Obend.Core.Proofs.SubjectReduction
import Obend.Core.Proofs.SubjectReduction.Substitution
import Obend.Core.Proofs.Substitution
import Obend.Core.Proofs.Substitution.Defs
import Obend.Core.Proofs.Substitution.Mono
import Obend.Core.Proofs.Substitution.Msubst
import Obend.Core.Proofs.Substitution.Transport
import Obend.Core.Proofs.Substitution.Uses
import Obend.Core.Proofs.Templates
import Obend.Core.Proofs.TickCost
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
import Obend.Equiv.Clairvoyant
import Obend.Equiv.Cost
import Obend.Equiv.CostTests
import Obend.Equiv.FareTests
import Obend.Equiv.Fields
import Obend.Equiv.Quote
import Obend.Equiv.Improvement
import Obend.Equiv.Reduction
import Obend.Equiv.Simulation
import Obend.Fold
import Obend.Intention
import Obend.Kind
import Obend.Kind.Proofs
import Obend.Equiv.Yields
import Obend.Judge
import Obend.Judge.Certified
import Obend.Judge.Cost
import Obend.Judge.Class
import Obend.Judge.Identity
import Obend.Judge.Instances
import Obend.Judge.Lrat
import Obend.Law
import Obend.Law.Claim
import Obend.Law.Fold
import Obend.Law.Inherit
import Obend.Law.Machine
import Obend.Law.Proofs.Claim
import Obend.Law.Proofs.Eval
import Obend.Law.Proofs.Inherit
import Obend.Law.Proofs.Machine
import Obend.Law.Proofs.Run
import Obend.Law.Proofs.Std
import Obend.Law.Proofs.Typing
import Obend.Law.Run
import Obend.Law.Std
import Obend.Law.Syntax
import Obend.Logic.Claim
import Obend.Logic.Frame
import Obend.Logic.Ground
import Obend.Logic.LateBinding
import Obend.Logic.Rewrite
import Obend.Main
import Obend.Receipt
import Obend.Receipt.Cli
import Obend.Receipt.Export
import Obend.Receipt.Merkle
import Obend.Receipt.Negotiation
import Obend.Run
import Obend.Run.Adapter
import Obend.Run.Control
import Obend.Run.ControlExample
import Obend.Run.Core4
import Obend.Run.Core4Example
import Obend.Run.Durable
import Obend.Run.DurableExample
import Obend.Run.Fold
import Obend.Run.Fork
import Obend.Run.ForkExample
import Obend.Run.LawJudge
import Obend.Run.Negotiation
import Obend.Run.Proofs.Adapter
import Obend.Run.Proofs.Control
import Obend.Run.Proofs.Core4
import Obend.Run.Proofs.Durable
import Obend.Run.Proofs.Interpret
import Obend.Run.Proofs.Invariant
import Obend.Run.Proofs.Shared
import Obend.Run.Runner
import Obend.Run.Shared
import Obend.Run.SharedExample
import Obend.Run.Spec
import Obend.Slot
import Obend.Slot.Budget
import Obend.Slot.Core4
import Obend.Slot.Integrity
import Obend.Slot.Proofs.Negotiation
import Obend.Slot.Proofs.Protocol
import Obend.Slot.Proofs.ProtocolTyping
import Obend.Slot.Protocol
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
import Obend.Spec.Proofs.C4
import Obend.Spec.Proofs.C4Vectors
import Obend.Spec.Proofs.Contract
import Obend.Spec.Proofs.Ecosystem
import Obend.Spec.Proofs.FrontEndAdequacy
import Obend.Spec.Proofs.Law
import Obend.Spec.Proofs.LawCompile
import Obend.Spec.Proofs.PackageLaw
import Obend.Spec.Proofs.SpecificationClosure
import Obend.Spec.Sha256
import Obend.Spec.Syntax
import Obend.Spec.Types
import Obend.Spec.Workspace
import Obend.Tactic.Cases
import Obend.Tactic.MonadicReduction
import Obend.Tactic.Tooth
import Obend.Teeth.Core.BackFail
import Obend.Teeth.Core.CheckTeeth
import Obend.Teeth.Core.Collect
import Obend.Teeth.Core.CollectTyping
import Obend.Teeth.Core.CollectYield
import Obend.Teeth.Core.DataBudget
import Obend.Teeth.Core.DataSoundness
import Obend.Teeth.Core.EquiRecursiveTeeth
import Obend.Teeth.Core.Force
import Obend.Teeth.Core.LinearTeeth
import Obend.Teeth.Core.SubstitutionTeeth
import Obend.Teeth.Equiv.CostTeeth
import Obend.Teeth.Law.LawJudgeTeeth
import Obend.Teeth.Law.MachineTeeth
import Obend.Teeth.Law.TypingTeeth
import Obend.Teeth.Logic.FrameTeeth
import Obend.Teeth.Logic.GroundTeeth
import Obend.Teeth.Logic.LateBindingTeeth
import Obend.Teeth.Spec.C4Teeth
import Obend.Teeth.Spec.LawCompileTeeth
import Obend.Teeth.Spec.TermWire
import Obend.Teeth.Tactic.ToothChecks
import Obend.Teeth.Vault
import Obend.Vault
import Obend.Vault.Cli
import Obend.Vault.Json
import Obend.Vault.Law
import Obend.Vault.Page
import Obend.Vault.Store

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
  -- Tier 1 is the `Obend` library's `globs` array in `lakefile.toml`: `"M"` names one module, `"M.+"`
  -- its submodules, `"M.*"` both. Read the array between `name = "Obend"` and the next table.
  let lakefile ← IO.FS.readFile "lakefile.toml"
  let some library := (lakefile.splitOn "name = \"Obend\"")[1]?
    | throwError "census: no `Obend` library in lakefile.toml"
  let library := (library.splitOn "[[")[0]!
  let globs := ((library.splitOn "globs = [")[1]?.getD "").splitOn "]" |>.head!
    |>.splitOn "," |>.map (·.trimAscii.toString) |>.filter (· != "")
    |>.map (fun g => (g.drop 1).dropRight 1 |>.toString)
  let base (g : String) : Name := (String.ofList (g.toList.take (g.length - 2))).toName
  let tier1 (module : Name) : Bool := globs.any fun g =>
    if g.endsWith ".+" then (base g).isPrefixOf module && base g != module
    else if g.endsWith ".*" then (base g).isPrefixOf module
    else g.toName == module
  let mut unbuilt : Array Name := #[]
  for file in sources do
    let module := (file.withExtension "").components.foldl Name.str .anonymous
    unless module == `Obend.Census || (`Obend.Teeth).isPrefixOf module || tier1 module do
      unbuilt := unbuilt.push module
  unless unbuilt.isEmpty do
    throwError "census: {unbuilt.size} modules are in neither tier (add a glob to the `Obend` library in lakefile.toml): {unbuilt.toList}"

#assert_axioms_tree
