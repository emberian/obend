/-
# The census: every constant of the library, one check; every theorem, one classification

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

## The classification (2026-11-04)

Before the axiom check the census prints, per directory, what replaced the headline counts: how
many theorems quantify over something (`universal`), how many are closed statements (`closed`: a
fixture, decided on concrete data), how many `example`s and how many `#tooth` commands the
directory's files hold (`Obend.AssertAxioms.theoremCensus`). No totals, and none belong in a
document; the number that matters is `closed`, and after the triage below it should only fall.
The closed theorems still carrying the keyword are listed by name: each is either consumed by a
proof, a `#tooth` or an `#assert_compiled` (and says so in a `-- fixture kept` line) or is the next
conversion. The documents census (`#check_docs_census` for paths and `Obend.*` names,
`#docs_census` for every backticked identifier against the environment, `Obend/Tactic/DocsCensus.lean`)
runs last: a governed root document that cites a name the tree does not have stops the merge.
Before it, `#census_environment` writes the names the tree has to `.lake/build/census/environment.txt`
(the package's constants and the allowlisted tactics, one per line): the file a vault's kind page
names as its `environment:`, against which `obend open` resolves the backticked names a page cites
(`review/ledger/_kind.md` for the decisions ledger; `Obend/Vault/Page.lean`, "Names cited in
backticks"). `tests/decisions/Environment.lean` writes the same file from the tier-1 library alone.

## The time budget (review/DECISIONS-20261031.md, 2026-11-04)

No build step takes an hour. A module of tier 1 may elaborate for 60 s, a module of tier 2 for
600 s; `tools/build.sh tier1|tier2` reads Lake's own `Built M (12s)` lines back and fails the build
when a module is over, even when Lake succeeded. The pre-push hook runs tier 1 through it. The other
way a module gets slow is `set_option maxHeartbeats`: the command below refuses, in tier 1, any such
site that is not in the baseline it carries (the sites that existed on 2026-11-04, with their
values), any value raised above its baseline, and any new file. Shrinking the baseline is the only
edit it accepts; a proof that needs more heartbeats than the default is restructured or moved to
tier 2, and the budget itself moves only by a ledger decision.

## The fixture triage (review/DECISIONS-20261031.md, 2026-11-04)

Every declaration under `Obend/` proved with `decide +kernel`, `native_decide` or `bv_decide` was
classified once (485 of them). A *proof step* is a decide inside a universal proof: not a fixture,
untouched. A fixture is *kept* when it guards something a theorem does not state (a refusal the
checker must produce, a known-answer vector re-run by `#assert_compiled`, a property of a defined
constant), and then carries a `-- fixture kept` line saying why; it stays a named `theorem` only
when a proof, a `#tooth` or an `#assert_compiled` consumes the name, otherwise it is an `example`.
It goes *to Teeth* (`Obend/Teeth/<Dir>/Fixtures.lean`, tier 2) when it is an end-to-end run on a
golden object worth doing before a push and not on every library build, and its data is `public`
(a fixture over module-private data stays where it is, as an `example`, and says so). It is *deleted* when it is
an instance nobody would miss: a preset passing its own signoff, arithmetic on preset numbers, a
substring check on emitted text, a cycle-count replay. Counts per directory, nothing finer here;
the per-site reasons are in the files. The Apps and Stdlib rows are classified here and applied by
the lanes that own those files (one Apps deletion, the 21-cycle CPU run the ledger names).

| directory | proof steps | kept | kept, named (cited) | to Teeth | deleted |
|---|---|---|---|---|---|
| Analysis | 19 | 4 | 25 | 4 | 2 |
| Apps | 24 | 10 | 27 | 0 | 1 |
| Core | 0 | 6 | 11 | 0 | 0 |
| Elab | 1 | 0 | 5 | 0 | 0 |
| Equiv | 0 | 0 | 6 | 0 | 0 |
| Hardware | 64 | 9 | 30 | 12 | 23 |
| Judge | 0 | 3 | 2 | 0 | 1 |
| Kind | 0 | 0 | 1 | 0 | 1 |
| Law | 1 | 6 | 0 | 8 | 0 |
| Ledger | 0 | 0 | 1 | 0 | 0 |
| Logic | 0 | 1 | 2 | 0 | 0 |
| Lower | 9 | 0 | 13 | 10 | 4 |
| Slot | 1 | 0 | 2 | 0 | 0 |
| Spec | 0 | 4 | 23 | 0 | 1 |
| Stdlib | 1 | 0 | 5 | 0 | 0 |
| Tactic | 1 | 0 | 5 | 0 | 0 |
| Teeth | 2 | 62 | 23 | 0 | 1 |
| Vault | 1 | 1 | 3 | 0 | 1 |

Over budget at this date and recorded here: `Obend/Hardware/QuantumMatter.lean` took 102–112 s in
tier 1; its three kernel-evaluated Clifford theorems (29 s, 13 s, 10 s) are in
`Obend/Teeth/Hardware/CliffordKernel.lean`, names unchanged, until the physics lane has a
structural proof.

The first command refuses a file under `Obend/` that this list does not import, and a module outside
`Obend/Teeth/` that the `Obend` library's globs in `lakefile.toml` do not name (`lake build` would
skip it unless something imports it). It runs when this file is rebuilt, that is, when anything it
imports changes; a new leaf added alone is caught at the next such rebuild, not at its own.

The first command refuses a file under `Obend/` that this list does not import, and a module outside
`Obend/Teeth/` that the `Obend` library's globs in `lakefile.toml` do not name (`lake build` would
skip it unless something imports it). It runs when this file is rebuilt, that is, when anything it
imports changes; a new leaf added alone is caught at the next such rebuild, not at its own.
-/
import Journal.Journal
import Obend
import Obend.Analysis.Cli
import Obend.Analysis.Coverage
import Obend.Analysis.Diff
import Obend.Analysis.EqSatHypergraph
import Obend.Analysis.Equitable
import Obend.Analysis.Flowpipe
import Obend.Analysis.Format
import Obend.Analysis.Groebner
import Obend.Analysis.Hybrid
import Obend.Analysis.HyperbolicPdeCert
import Obend.Analysis.Impact
import Obend.Analysis.PdeSexprAndApprox
import Obend.Analysis.QuantumWalk
import Obend.Analysis.RealAnalysis
import Obend.Analysis.Replay
import Obend.Analysis.Setup
import Obend.Analysis.SimplicialFeecFem
import Obend.Analysis.SosLyapunov
import Obend.Analysis.TaylorModel
import Obend.Analysis.Worlds
import Obend.Apps.FidgetCam
import Obend.Apps.FidgetCamCert
import Obend.Apps.FocHil
import Obend.Apps.ObendRisc
import Obend.Apps.QuantumPhotonicMatter
import Obend.Apps.SdrFt8
import Obend.Apps.SdrFt8Rx
import Obend.Apps.SiliconKernelVerilator
import Obend.Apps.SovereignDrex
import Obend.Apps.ZkNtt
import Obend.AssertAxioms
import Obend.AssertCompiled
import Obend.Category
import Obend.Category.GradedLogic
import Obend.Category.OpenSystem
import Obend.Category.Refines
import Obend.ClusterGov.PhysicalEnvelope
import Obend.Codec.DetCbor
import Obend.Consensus
import Obend.Consensus.Epistemic
import Obend.Consensus.Finality
import Obend.Consensus.Simplex
import Obend.Consensus.SimplexLiveness
import Obend.Consensus.SimplexProtocol
import Obend.Consensus.SimplexTrace
import Obend.Crypto
import Obend.Crypto.BinarySpartanAndShout
import Obend.Crypto.BinaryTower256
import Obend.Crypto.CanopyReduce
import Obend.Crypto.DarkBazaar
import Obend.Crypto.DualSpine
import Obend.Crypto.FastRing
import Obend.Crypto.Multilinear
import Obend.Crypto.PCS
import Obend.Crypto.PikkuFoldLayered
import Obend.Crypto.Poseidon2Goldilocks
import Obend.Crypto.SameOpening
import Obend.Crypto.Sumcheck
import Obend.Crypto.ThresholdFheAndLatticeVrf
import Obend.Crypto.Transcript
import Obend.Core.AliasExposure
import Obend.Core.Assumptions
import Obend.Core.Bidirectional
import Obend.Core.Brand
import Obend.Core.CanonicalExtension
import Obend.Core.Capacity
import Obend.Core.Check
import Obend.Core.Checkpoint
import Obend.Core.Code
import Obend.Core.Collect
import Obend.Core.Cubical2LTT
import Obend.Core.Data
import Obend.Core.Digest
import Obend.Core.EquiRecursiveAgreement
import Obend.Core.EquiRecursiveLookup
import Obend.Core.EquiRecursiveSubstitutionTransport
import Obend.Core.Extensions
import Obend.Core.FieldCongruence
import Obend.Core.Fill
import Obend.Core.Proofs.FillTyping
import Obend.Core.FilteredStream
import Obend.Core.FilteredStreamCompleteness
import Obend.Core.FilteredStreamSoundness
import Obend.Core.FilteredStreamSteps
import Obend.Core.FiniteBisimulation
import Obend.Core.FinitePresentation
import Obend.Core.FiniteRowLaws
import Obend.Core.GradedSessionMetatheory
import Obend.Core.Interaction
import Obend.Core.Invariant
import Obend.Core.LegacyAgreement
import Obend.Core.Machine
import Obend.Core.MachineFast
import Obend.Core.MachineTyping
import Obend.Core.Nominal
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
import Obend.Core.Proofs.Aggregate
import Obend.Core.Proofs.BidirectionalCompleteness
import Obend.Core.Proofs.CheckCompletenessObstruction
import Obend.Core.Proofs.CheckerTransport
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
import Obend.Core.Proofs.GradedRecord
import Obend.Core.Proofs.GroundExecution
import Obend.Core.Proofs.Hole
import Obend.Core.Proofs.JoinReading
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
import Obend.Core.Proofs.Preservation.Cases.Split
import Obend.Core.Proofs.Preservation.Cases.Sums
import Obend.Core.Proofs.Settle
import Obend.Core.Proofs.Splice
import Obend.Core.Proofs.StepCases
import Obend.Core.Proofs.SubjectReduction
import Obend.Core.Proofs.SubjectReduction.Substitution
import Obend.Core.Proofs.Substitution
import Obend.Core.Proofs.Substitution.Defs
import Obend.Core.Proofs.Substitution.Uses
import Obend.Core.Proofs.Templates
import Obend.Core.Proofs.TickCost
import Obend.Core.Proofs.TickTrace
import Obend.Core.Proofs.TypedSubstitution
import Obend.Core.PrototypeProvenance
import Obend.Core.RangeSafe
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
import Obend.Doc.ReactiveNotebook
import Obend.Doc.Render
import Obend.Doc.Section
import Obend.Doc.Structured
import Obend.Elab
import Obend.Elab.AutoCertTaylorSound
import Obend.Elab.Coerce
import Obend.Elab.Gate
import Obend.Elab.Prepare
import Obend.Elab.Proofs.AliasFree
import Obend.Elab.Proofs.CoerceProbes
import Obend.Elab.Proofs.PrepareChecks
import Obend.Elab.Proofs.PrepareProbes
import Obend.Elab.Proofs.Refines
import Obend.Elab.Work
import Obend.Elab.Workbook
import Obend.Equiv.Ahead
import Obend.Equiv.Behaviour
import Obend.Equiv.Clairvoyant
import Obend.Equiv.ClairvoyantBook
import Obend.Equiv.Cost
import Obend.Equiv.CostTests
import Obend.Equiv.Demand
import Obend.Equiv.FareTests
import Obend.Equiv.Fields
import Obend.Equiv.Improvement
import Obend.Equiv.Quote
import Obend.Equiv.Reduction
import Obend.Equiv.Simulation
import Obend.Equiv.Yields
import Obend.FFI
import Obend.FFI.Bridge
import Obend.Fold
import Obend.Fold.Collapse
import Obend.Format.Reader
import Obend.Geometry.CochainAndGauge
import Obend.Geometry.DiracDoubleCat
import Obend.Hardware
import Obend.Hardware.Accelerators
import Obend.Hardware.AgenticEDA
import Obend.Hardware.Analog
import Obend.Hardware.AwsF2Shell
import Obend.Hardware.Cic
import Obend.Hardware.CircuitDae
import Obend.Hardware.Circuits
import Obend.Hardware.Cli
import Obend.Hardware.Codec
import Obend.Hardware.Compiler
import Obend.Hardware.CurrentLoop
import Obend.Hardware.Fabulous.Mac8Bin
import Obend.Hardware.Fabulous.Mac8Cert
import Obend.Hardware.Fabulous.Mac8CertCheck
import Obend.Hardware.Fabulous.Mac8Tiles
import Obend.Hardware.DRC
import Obend.Hardware.DSP
import Obend.Hardware.Datasheet
import Obend.Hardware.DprStutter
import Obend.Hardware.Device.Constants
import Obend.Hardware.Device.DriftDiffusion
import Obend.Hardware.Device.Enclosure
import Obend.Hardware.Device.Sky130Diode
import Obend.Hardware.Device.Wafer
import Obend.Hardware.FSM
import Obend.Hardware.Fabric
import Obend.Hardware.GeometryCAM
import Obend.Hardware.GlitchAndTempestSafe
import Obend.Hardware.Gpu.CollectiveImport
import Obend.Hardware.Gpu.CollectiveWorkBuild
import Obend.Hardware.Gpu.NttCorrect
import Obend.Hardware.Gpu.Rdna2.AsyncRefinement
import Obend.Hardware.Gpu.Rdna2.DppShuffle
import Obend.Hardware.Gpu.SoacOptimize
import Obend.Hardware.Gpu.StencilTile
import Obend.Hardware.HDL
import Obend.Hardware.Hvm
import Obend.Hardware.Hvm.Model
import Obend.Hardware.Hvm.Net
import Obend.Hardware.Hvm.Lower
import Obend.Hardware.Hvm.Inet
import Obend.Hardware.HvmConfluence
import Obend.Hardware.Judge
import Obend.Hardware.Kinematics
import Obend.Hardware.Magnetics
import Obend.Hardware.OpenHypergraph
import Obend.Hardware.OpenUSD
import Obend.Hardware.PCB
import Obend.Hardware.Photonics
import Obend.Hardware.PipelinedRisc
import Obend.Hardware.PipelinedRiscCore
import Obend.Hardware.PipelinedZkCrypto
import Obend.Hardware.PlaceRoute
import Obend.Hardware.Process
import Obend.Hardware.QuantumMatter
import Obend.Hardware.ReductionMachine
import Obend.Hardware.ReductionMachine.Arena
import Obend.Hardware.Retiming
import Obend.Hardware.Rules
import Obend.Hardware.SafePhysicalShield
import Obend.Hardware.Silicon
import Obend.Hardware.SiliconOuroboros
import Obend.Hardware.SwitchedCapRf
import Obend.Hardware.SymplecticVehicle6Dof
import Obend.Hardware.Synth
import Obend.Hardware.TapeoutPipeline
import Obend.Hardware.ThermalPassivity
import Obend.Hardware.Tpu.CryptoSystolic
import Obend.Hardware.Tpu.Machine
import Obend.Hardware.Types
import Obend.Hardware.UserspacePhysical
import Obend.Intention
import Obend.Judge
import Obend.Judge.AutomataConfinement
import Obend.Judge.Certified
import Obend.Judge.CertifierRatchet
import Obend.Judge.Class
import Obend.Judge.Clearing
import Obend.Judge.Computational
import Obend.Judge.Genealogy
import Obend.Judge.GenealogyCli
import Obend.Judge.Cost
import Obend.Judge.DecoAndCallTree
import Obend.Judge.Identity
import Obend.Judge.Instances
import Obend.Judge.LayeredCost
import Obend.Judge.Lrat
import Obend.Judge.Netting
import Obend.Judge.RealAnalysis
import Obend.Judge.ReflectiveGate
import Obend.Judge.SvenvsCorrigibility
import Obend.Judge.SymbolicRegexBisim
import Obend.Judge.TranscriptPolicy
import Obend.Judge.VpaComplementAndJson
import Obend.Kind
import Obend.Kind.Proofs
import Obend.Kind.Registry
import Obend.Law
import Obend.Law.AmendCli
import Obend.Law.Claim
import Obend.Law.Contract
import Obend.Law.Fold
import Obend.Law.Inherit
import Obend.Law.Machine
import Obend.Law.PointwiseRevise
import Obend.Law.Proofs.Claim
import Obend.Law.Proofs.Eval
import Obend.Law.Proofs.Fill
import Obend.Law.Proofs.Inherit
import Obend.Law.Proofs.Machine
import Obend.Law.Proofs.Run
import Obend.Law.Proofs.Std
import Obend.Law.Proofs.Typing
import Obend.Law.Run
import Obend.Law.Std
import Obend.Law.Syntax
import Obend.Leaf.Emit
import Obend.Leaf.Flatten
import Obend.Leaf.Futamura
import Obend.Leaf.LinkSpecialize
import Obend.Leaf.Residual
import Obend.Leaf.Specialize
import Obend.Leaf.Static
import Obend.Leaf.UpTo
import Obend.Ledger
import Obend.Ledger.Book
import Obend.Ledger.Cli
import Obend.Ledger.Commit
import Obend.Ledger.Floors
import Obend.Ledger.Json
import Obend.Ledger.Register
import Obend.Ledger.Report
import Obend.Ledger.Seat
import Obend.Ledger.Vault
import Obend.Logic.Claim
import Obend.Logic.Frame
import Obend.Logic.Ground
import Obend.Logic.GuardedLob
import Obend.Logic.LateBinding
import Obend.Logic.MultiTurnHoare
import Obend.Logic.Obligation
import Obend.Logic.Program
import Obend.Logic.Receipt
import Obend.Logic.Rewrite
import Obend.Logic.SeparationFrame
import Obend.Logic.SuperRefines
import Obend.Logic.Turn
import Obend.Lower.Cli
import Obend.Lower.DiscrTreeLUT
import Obend.Lower.ExprCAM
import Obend.Lower.Fragment
import Obend.Lower.Inductive
import Obend.Lower.Judge
import Obend.Lower.LCNF
import Obend.Lower.LeanKernel
import Obend.Lower.Lower
import Obend.Lower.MetaUnify
import Obend.Lower.PolicyToGrain
import Obend.Lower.Proofs.Book
import Obend.Lower.Proofs.Checks
import Obend.Lower.Proofs.Complete
import Obend.Lower.Proofs.Hardware
import Obend.Lower.Proofs.SiliconKernel
import Obend.Lower.Proofs.Sound
import Obend.Lower.Proofs.Subst
import Obend.Lower.Reflect
import Obend.Lower.Semantics
import Obend.Lower.SiliconElabFabric
import Obend.Lower.Syntax
import Obend.Lower.Transport
import Obend.Lower.Typing
import Obend.Main
import Obend.OS.Sel4MicrokitKernel
import Obend.OS.Sel4MicrokitKernelCore
import Obend.Paco.GPaco
import Obend.Polis.CapTP
import Obend.Polis.EpistemicVouchMarket
import Obend.Polis.EvidencedOcap
import Obend.Polis.GrainCustodyHost
import Obend.Polis.GrainPowerbox
import Obend.Polis.HouyhnhnmMonitor
import Obend.Polis.HouyhnhnmTurn
import Obend.Polis.JointCoReceipt
import Obend.Polis.PrepaidLeaseAndFork
import Obend.Polis.PrivatePredicate
import Obend.Polis.VerifiableCredentials
import Obend.Polis.VerkleUmem
import Obend.Polis.ZkBiscuit
import Obend.Polis.ZoeSeatSettlement
import Obend.Reasons
import Obend.Reasons.UnifiedEquilibrium
import Obend.Receipt
import Obend.Receipt.Cli
import Obend.Receipt.Export
import Obend.Receipt.Merkle
import Obend.Receipt.Negotiation
import Obend.Repair
import Obend.Repair.AlgConfig
import Obend.Repair.CoalgConfig
import Obend.Repair.DeltaLensRenew
import Obend.Repair.DeriveConfig
import Obend.Repair.QuotAssembly
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
import Obend.Run.HyperLaw
import Obend.Run.LawJudge
import Obend.Run.Negotiation
import Obend.Run.Proofs.Adapter
import Obend.Run.Proofs.Control
import Obend.Run.Proofs.Core4
import Obend.Run.Proofs.Durable
import Obend.Run.Proofs.Interpret
import Obend.Run.Proofs.Invariant
import Obend.Run.Proofs.Shared
import Obend.Run.Reflect
import Obend.Run.Runner
import Obend.Run.Shared
import Obend.Run.SharedExample
import Obend.Run.Spec
import Obend.Run.Ticks
import Obend.Run.VaultDurableBridge
import Obend.Slot
import Obend.Slot.Budget
import Obend.Slot.Core4
import Obend.Slot.Integrity
import Obend.Slot.Proofs.Negotiation
import Obend.Slot.Proofs.Protocol
import Obend.Slot.Proofs.ProtocolTyping
import Obend.Slot.Protocol
import Obend.Slot.Selection
import Obend.Slot.SupportSheaf
import Obend.Slot.World
import Obend.Spec
import Obend.Spec.Annotated
import Obend.Spec.BidirectionalSurfaceElab
import Obend.Spec.C4
import Obend.Spec.Capture
import Obend.Spec.Contract
import Obend.Spec.CrossPackage
import Obend.Spec.DataWire
import Obend.Spec.Ecosystem
import Obend.Spec.Elaborate
import Obend.Spec.FrontEnd
import Obend.Spec.Identity
import Obend.Spec.Law
import Obend.Spec.LawCompile
import Obend.Spec.LawDial
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
import Obend.Stdlib
import Obend.SymbolicZk.CamUnifyArith
import Obend.SymbolicZk.CompileToPiop
import Obend.SymbolicZk.CompileToPiopCore
import Obend.SymbolicZk.LinMem
import Obend.SymbolicZk.RankedFixpointArith
import Obend.SymbolicZk.SemiringDatalog
import Obend.SymbolicZk.SkolemChaseCore
import Obend.SymbolicZk.StencilRolloutStark
import Obend.Tactic.Cases
import Obend.Tactic.ClaimAudit
import Obend.Tactic.Compositional
import Obend.Tactic.DataRefinement
import Obend.Tactic.DocsCensus
import Obend.Tactic.MonadicReduction
import Obend.Tactic.ProgramLogic
import Obend.Tactic.SiliconElab
import Obend.Tactic.SymbolicCert
import Obend.Tactic.Tooth
import Obend.Tactic.Weave
import Obend.Trailblaze.CathedralApex
import Obend.Trailblaze.ClusterGov
import Obend.Trailblaze.LeanFpga
import Obend.Trailblaze.Obligations
import Obend.Trailblaze.Polis
import Obend.Trailblaze.PolisBlum
import Obend.Trailblaze.StageBInstances
import Obend.Trailblaze.ZkStripe
import Obend.Teeth.Analysis.Fixtures
import Obend.Teeth.Core.AggregateTeeth
import Obend.Teeth.Core.BackFail
import Obend.Teeth.Core.CheckTeeth
import Obend.Teeth.Core.CodeTeeth
import Obend.Teeth.Core.Collect
import Obend.Teeth.Core.CollectTyping
import Obend.Teeth.Core.CollectYield
import Obend.Teeth.Core.DataBudget
import Obend.Teeth.Core.DataSoundness
import Obend.Teeth.Core.EquiRecursiveTeeth
import Obend.Teeth.Core.Force
import Obend.Teeth.Core.JoinReadingTeeth
import Obend.Teeth.Core.LinearTeeth
import Obend.Teeth.Core.NominalTeeth
import Obend.Teeth.Core.SpliceTeeth
import Obend.Teeth.Core.SubstitutionTeeth
import Obend.Teeth.Equiv.CostTeeth
import Obend.Teeth.Hardware.CliffordKernel
import Obend.Teeth.Hardware.DeviceCertificates
import Obend.Teeth.Hardware.DeviceFixtures
import Obend.Teeth.Hardware.Fixtures
import Obend.Hardware.Gpu.CatgradImport
import Obend.Teeth.Hardware.Rdna2Runs
import Obend.Teeth.Hardware.ArrayTyping
import Obend.Teeth.Hardware.GpuArrayEncoding
import Obend.Teeth.Hardware.GpuArrayMember
import Obend.Teeth.Hardware.GpuLayout
import Obend.Teeth.Hardware.GpuSourcePrograms
import Obend.Teeth.Hardware.Workgroup
import Obend.Teeth.Hardware.SiliconTeeth
import Obend.Teeth.Law.Fixtures
import Obend.Teeth.Law.LawJudgeTeeth
import Obend.Teeth.Law.MachineTeeth
import Obend.Teeth.Law.TypingTeeth
import Obend.Teeth.Leaf.MachineSeven
import Obend.Teeth.Leaf.ReviewTeeth
import Obend.Teeth.Leaf.StaticTeeth
import Obend.Teeth.Logic.FrameTeeth
import Obend.Teeth.Logic.GroundTeeth
import Obend.Teeth.Logic.LateBindingTeeth
import Obend.Teeth.Lower.Fixtures
import Obend.Teeth.Lower.LowerTeeth
import Obend.Teeth.Spec.C4Teeth
import Obend.Teeth.Spec.LawCompileTeeth
import Obend.Teeth.Spec.TermWire
import Obend.Teeth.Tactic.ToothChecks
import Obend.Teeth.Vault
import Obend.Vault
import Obend.Vault.Affordance
import Obend.Vault.Branch
import Obend.Vault.BranchCli
import Obend.Vault.CheckedCarry
import Obend.Vault.ChunkedWorld
import Obend.Vault.Cli
import Obend.Vault.Cost
import Obend.Vault.DecodeCache
import Obend.Vault.Escrow
import Obend.Vault.ExpVerkleAndOpenHash
import Obend.Vault.Form
import Obend.Vault.FormCheck
import Obend.Vault.FormCheckCache
import Obend.Vault.FrustumMembrane
import Obend.Vault.HardwareProjection
import Obend.Vault.Hyperedge
import Obend.Vault.Index
import Obend.Vault.IrreversibleOutbox
import Obend.Vault.Json
import Obend.Vault.Law
import Obend.Vault.Log
import Obend.Vault.LogBytes
import Obend.Vault.Lsafe
import Obend.Vault.Mandate
import Obend.Vault.Merge
import Obend.Vault.Page
import Obend.Vault.PhysicalProjection
import Obend.Vault.PortableContinuation
import Obend.Vault.Projection
import Obend.Vault.Rehydration
import Obend.Vault.Replay
import Obend.Vault.Retention
import Obend.Vault.SegmentLog
import Obend.Vault.Store
import Obend.Vault.SurviveFirePor
import Obend.Vault.SwarmLedgerSeams
import Obend.Vault.TransclusionAndMirror
import Obend.Vault.Transport
import Obend.Vault.UnifiedDeos
import Obend.Vault.VerkleSnapshotBridge

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
  -- Tier 2 is the `Teeth` library's `globs` (the teeth, the apps, Obend.Stdlib, this file), read the
  -- same way.
  let parseGlobs (libName : String) : CommandElabM (List String) := do
    let some library := (lakefile.splitOn s!"name = \"{libName}\"")[1]?
      | throwError "census: no `{libName}` library in lakefile.toml"
    let library := (library.splitOn "[[")[0]!
    return ((library.splitOn "globs = [")[1]?.getD "").splitOn "]" |>.head!
      |>.splitOn "," |>.map (·.trimAscii.toString) |>.filter (· != "")
      |>.map (fun g => (g.drop 1).dropRight 1 |>.toString)
  let tier1Globs ← parseGlobs "Obend"
  let tier2Globs ← parseGlobs "Teeth"
  let base (g : String) : Name := (String.ofList (g.toList.take (g.length - 2))).toName
  let inTier (globs : List String) (module : Name) : Bool := globs.any fun g =>
    if g.endsWith ".+" then (base g).isPrefixOf module && base g != module
    else if g.endsWith ".*" then (base g).isPrefixOf module
    else g.toName == module
  let tier1 (module : Name) : Bool := inTier tier1Globs module
  let tier2 (module : Name) : Bool := inTier tier2Globs module
  let mut unbuilt : Array Name := #[]
  for file in sources do
    let module := (file.withExtension "").components.foldl Name.str .anonymous
    unless tier1 module || tier2 module do
      unbuilt := unbuilt.push module
  unless unbuilt.isEmpty do
    throwError "census: {unbuilt.size} modules are in neither tier (add a glob to the `Obend` or the `Teeth` library in lakefile.toml): {unbuilt.toList}"
  -- Per-directory file facts: `example`s and `#tooth` commands, by the directory the module reports under.
  let mut examples : NameMap Nat := {}
  let mut teeth : NameMap Nat := {}
  for file in sources do
    let module := (file.withExtension "").components.foldl Name.str .anonymous
    let dir := Obend.AssertAxioms.directoryOf module
    let text ← IO.FS.readFile file
    for line in text.splitOn "\n" do
      let l := line.trimAscii.toString
      if l.startsWith "example " || l.startsWith "example:" || l == "example" then
        examples := examples.insert dir (examples.getD dir 0 + 1)
      if l.startsWith "#tooth " then
        teeth := teeth.insert dir (teeth.getD dir 0 + 1)
  -- The classification: no totals, one line per directory, the closed theorems by name.
  let rows ← liftTermElabM Obend.AssertAxioms.theoremCensus
  let mut lines : Array MessageData := #[]
  let mut closedNames : Array Name := #[]
  for (dir, universal, closed) in rows do
    lines := lines.push m!"{dir}: {universal} universal theorems, {closed.size} closed theorems, {examples.getD dir 0} examples, {teeth.getD dir 0} teeth"
    closedNames := closedNames ++ closed
  logInfo m!"census: every module under Obend/ is imported here and belongs to a tier.\n{MessageData.joinSep lines.toList "\n"}"
  unless closedNames.isEmpty do
    logInfo m!"census: closed theorems still declared with `theorem` (each consumed by a proof, a #tooth or an #assert_compiled, or the next conversion): {closedNames.toList}"
  -- The Löb cost, counted (`Obend.Judge.Genealogy`): every package theorem whose statement carries
  -- `LobCost`, the hypothesis that the principles a stronger succession was labelled with hold.
  let mut lobCarriers : Array Name := #[]
  for (constant, info) in (← getEnv).constants.map₁.toList do
    let .thmInfo _ := info | continue
    if constant.isInternal then continue
    if (Obend.AssertAxioms.packageModule? (← getEnv) constant).isNone then continue
    if info.type.getUsedConstants.contains `Obend.Judge.Genealogy.LobCost then
      lobCarriers := lobCarriers.push constant
  logInfo m!"census: theorems carrying the Löb cost (`LobCost` in the statement): {(lobCarriers.qsort (·.toString < ·.toString)).toList}"
  -- The heartbeat baseline of tier 1 (see the header). Paths as `walkDir "Obend"` reports them; the
  -- values of every `set_option maxHeartbeats N` (file-level or `… in`) in that file on 2026-11-04.
  let heartbeatBaseline : List (String × List Nat) :=
    [ ("Obend/Analysis/EqSatHypergraph.lean", [800000, 800000])
    , ("Obend/Analysis/Equitable.lean", [800000])
    , ("Obend/Core/Proofs/Adequacy/Origins.lean", [800000])
    , ("Obend/Core/Proofs/Adequacy/Source.lean", [600000, 600000])
    , ("Obend/Core/Proofs/Adequacy/StepRaw.lean", [800000])
    , ("Obend/Core/Proofs/EquiRecursiveSubstitution.lean", [4000000])
    , ("Obend/Digest/Cshake256/Fast.lean", [4000000, 4000000, 4000000, 4000000])
    , ("Obend/Equiv/Reduction.lean", [600000])
    , ("Obend/Hardware/Judge.lean", [800000, 800000, 1600000])
    , ("Obend/Hardware/OpenHypergraph.lean", [1600000, 1600000])
    , ("Obend/Hardware/QuantumMatter.lean", [1600000]) ]
  let mut heartbeatOffenders : Array String := #[]
  for file in sources do
    let module := (file.withExtension "").components.foldl Name.str .anonymous
    unless tier1 module do continue
    let text ← IO.FS.readFile file
    let mut allowed : List Nat := (heartbeatBaseline.lookup file.toString).getD []
    for line in text.splitOn "\n" do
      let l := line.trimAscii.toString
      unless l.startsWith "set_option maxHeartbeats " do continue
      let digits := String.ofList ((l.toList.drop "set_option maxHeartbeats ".length).takeWhile Char.isDigit)
      let n := digits.toNat?.getD 0
      -- a value at or under the default costs nothing; above it, the site must be in the baseline
      if n ≤ 200000 then continue
      if allowed.contains n then allowed := allowed.erase n
      else heartbeatOffenders := heartbeatOffenders.push s!"{file}: maxHeartbeats {n}"
  unless heartbeatOffenders.isEmpty do
    throwError "census: tier 1 has `set_option maxHeartbeats` sites outside the 2026-11-04 baseline (a new site, a raised value, or a file not in the list): {heartbeatOffenders.toList}. Restructure the proof or move it to tier 2; the baseline only shrinks."

#assert_axioms_tree
#census_environment ".lake/build/census/environment.txt"
#check_docs_census
#docs_census
