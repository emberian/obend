module
import all Obend.Analysis.Diff
import all Obend.Analysis.Equitable
import all Obend.Analysis.Flowpipe
import all Obend.Analysis.Groebner
import all Obend.Analysis.HyperbolicPdeCert
import all Obend.Analysis.NonlinearMultiDPde
import all Obend.Analysis.PdeSexprAndApprox
import all Obend.Analysis.RealAnalysis
import all Obend.Analysis.SimplicialFeecFem
import all Obend.Analysis.SosLyapunov
import all Obend.Analysis.TaylorModel
import all Obend.Apps.ZkNtt.Goldilocks
import all Obend.AssertAxioms
import all Obend.Codec.DetCbor
import all Obend.Consensus.Simplex
import all Obend.Consensus.SimplexProtocol
import all Obend.Core.AliasExposure
import all Obend.Core.Assumptions
import all Obend.Core.Bidirectional
import all Obend.Core.Brand
import all Obend.Core.Capacity
import all Obend.Core.Check
import all Obend.Core.Code
import all Obend.Core.Collect
import all Obend.Core.Data
import all Obend.Core.Digest
import all Obend.Core.EquiRecursiveAgreement
import all Obend.Core.EquiRecursiveLookup
import all Obend.Core.FieldCongruence
import all Obend.Core.FiniteBisimulation
import all Obend.Core.FinitePresentation
import all Obend.Core.FiniteRowLaws
import all Obend.Core.Invariant
import all Obend.Core.Machine
import all Obend.Core.MachineFast
import all Obend.Core.MachineTyping
import all Obend.Core.Nominal
import all Obend.Core.Packet
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
import all Obend.Core.Proofs.Collect.Compact
import all Obend.Core.Proofs.Collect.Extract
import all Obend.Core.Proofs.Collect.Lockstep
import all Obend.Core.Proofs.Collect.Mark
import all Obend.Core.Proofs.Collect.Rename
import all Obend.Core.Proofs.Collect.Runs
import all Obend.Core.Proofs.Collect.Segment
import all Obend.Core.Proofs.Collect.Statements
import all Obend.Core.Proofs.Collect.Typing
import all Obend.Core.Proofs.Completeness
import all Obend.Core.Proofs.DataSoundness
import all Obend.Core.Proofs.Force
import all Obend.Core.Proofs.GroundExecution
import all Obend.Core.Proofs.Preservation
import all Obend.Core.Proofs.Preservation.Base.Focus
import all Obend.Core.Proofs.Preservation.Base.Heads
import all Obend.Core.Proofs.Preservation.Base.Insert
import all Obend.Core.Proofs.Preservation.Base.Reusable
import all Obend.Core.Proofs.Preservation.Base.Values
import all Obend.Core.Proofs.Preservation.Base.Weaken
import all Obend.Core.Proofs.Preservation.Cases.Activities
import all Obend.Core.Proofs.Preservation.Cases.Arithmetic
import all Obend.Core.Proofs.Preservation.Cases.Functions
import all Obend.Core.Proofs.Preservation.Cases.Pairs
import all Obend.Core.Proofs.Preservation.Cases.Records
import all Obend.Core.Proofs.Preservation.Cases.Split
import all Obend.Core.Proofs.Preservation.Cases.Sums
import all Obend.Core.Proofs.StepCases
import all Obend.Core.Proofs.Substitution.Defs
import all Obend.Core.Proofs.Substitution.Uses
import all Obend.Core.Proofs.TypedSubstitution
import all Obend.Core.RangeSafe
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
import all Obend.Doc.Render
import all Obend.Doc.Section
import all Obend.Doc.Structured
import all Obend.Elab.AutoCert
import all Obend.Elab.Gate
import all Obend.Elab.Prepare
import all Obend.Elab.Work
import all Obend.Equiv.Ahead
import all Obend.Equiv.Behaviour
import all Obend.Equiv.Fields
import all Obend.Equiv.Quote
import all Obend.Equiv.Reduction
import all Obend.Equiv.Simulation
import all Obend.Fold
import all Obend.Hardware.Accelerators
import all Obend.Hardware.PinoutEquiv
import all Obend.Hardware.SmallSignalMna
import all Obend.Hardware.ArrayBuild
import all Obend.Hardware.ArrayFold
import all Obend.Hardware.ArrayHypergraph
import all Obend.Hardware.ArrayKernel
import all Obend.Hardware.ArrayKernelOwnership
import all Obend.Hardware.ArrayKernelUnique
import all Obend.Hardware.ArrayTyping
import all Obend.Hardware.Codec
import all Obend.Hardware.Compiler
import all Obend.Hardware.PlaneSweepDrcLvs
import all Obend.Hardware.DigitalFilterAndArray
import all Obend.Hardware.OspcProver
import all Obend.Analysis.HyperbolicBalanceLaws
import all Obend.Analysis.NonlinearErrorTube
import all Obend.Category.GradedLogic
import all Obend.Category.Refines
import all Obend.Core.Cubical2LTT
import all Obend.Core.GradedCoreWeld
import all Obend.Core.GradedCoreWeldDefs
import all Obend.Core.GradedSessionMetatheory
import all Obend.Crypto.Sumcheck
import all Obend.Hardware.BalanceLawLowering
import all Obend.Hardware.Cic
import all Obend.Hardware.CircuitDae
import all Obend.Repair.DeltaLensRenew
import all Obend.Spec.BidirectionalSurfaceElab
import all Obend.SymbolicZk.CompileToPiop
import all Obend.SymbolicZk.CompileToPiopCore
import all Obend.SymbolicZk.SkolemChaseCore
import all Obend.Hardware.GeometryCAM
import all Obend.Hardware.Gpu
import all Obend.Hardware.Gpu.ArrayEmit
import all Obend.Hardware.Gpu.ArrayEmitCorrect
import all Obend.Hardware.Gpu.ArrayEncoding
import all Obend.Hardware.Gpu.ArrayMember
import all Obend.Hardware.Gpu.ArrayProduct
import all Obend.Hardware.Gpu.ArrayPrograms
import all Obend.Hardware.Gpu.ArrayReify
import all Obend.Hardware.Gpu.ArraySchedule
import all Obend.Hardware.Gpu.ArraySource
import all Obend.Hardware.Gpu.ArraySourceCore
import all Obend.Hardware.Gpu.BlockEmit
import all Obend.Hardware.Gpu.BlockLower
import all Obend.Hardware.Gpu.CollectiveArena
import all Obend.Hardware.Gpu.CollectiveArenaCorrect
import all Obend.Hardware.Gpu.CollectiveBlock
import all Obend.Hardware.Gpu.CollectiveBuildCorrect
import all Obend.Hardware.Gpu.CollectiveBuildFacts
import all Obend.Hardware.Gpu.CollectiveCompose
import all Obend.Hardware.Gpu.CollectiveCorrect
import all Obend.Hardware.Gpu.CollectiveExecute
import all Obend.Hardware.Gpu.CollectiveHierarchy
import all Obend.Hardware.Gpu.CollectiveReduceBuild
import all Obend.Hardware.Gpu.CollectiveReduceExec
import all Obend.Hardware.Gpu.CollectiveScanExec
import all Obend.Hardware.Gpu.CollectiveTrace
import all Obend.Hardware.Gpu.CollectiveTree
import all Obend.Hardware.Gpu.FoldCore
import all Obend.Hardware.Gpu.GoldilocksSource
import all Obend.Hardware.Gpu.Limbs
import all Obend.Hardware.Gpu.LimbsGoldilocks
import all Obend.Hardware.Gpu.LimbsShift
import all Obend.Hardware.Gpu.Memory
import all Obend.Hardware.Gpu.PhaseSemantics
import all Obend.Hardware.Gpu.SoacOptimize
import all Obend.Hardware.Gpu.SourceElem
import all Obend.Hardware.Gpu.SourceOps
import all Obend.Hardware.Gpu.SourceProtocol
import all Obend.Hardware.Gpu.StencilTile
import all Obend.Hardware.Gpu.Workgroup
import all Obend.Hardware.HDL
import all Obend.Hardware.Judge
import all Obend.Hardware.Magnetics
import all Obend.Hardware.MultiDStencilCorrect
import all Obend.Hardware.MultiDStencilGpuSource
import all Obend.Hardware.MultiDStencilTile
import all Obend.Hardware.OpenHypergraph
import all Obend.Hardware.PCB
import all Obend.Hardware.PlaceRoute
import all Obend.Hardware.Process
import all Obend.Hardware.ReductionMachine
import all Obend.Hardware.Retiming
import all Obend.Hardware.Synth
import all Obend.Hardware.Types
import all Obend.Hardware.VerilateRunner
import all Obend.Hardware.YosysLec
import all Obend.Intention
import all Obend.Judge.Class
import all Obend.Judge.Clearing
import all Obend.Judge.Computational
import all Obend.Judge.Lrat
import all Obend.Judge.RealAnalysis
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
import all Obend.Law.Proofs.Typing
import all Obend.Law.Run
import all Obend.Law.Std
import all Obend.Law.Syntax
import all Obend.Leaf.BytecodeRegisterJit
import all Obend.Leaf.Emit
import all Obend.Leaf.Flatten
import all Obend.Leaf.Served
import all Obend.Leaf.Specialize
import all Obend.Leaf.Static
import all Obend.Leaf.UpTo
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
import all Obend.Logic.SeparationFrame
import all Obend.Lower.Fragment
import all Obend.Lower.Inductive
import all Obend.Lower.Judge
import all Obend.Lower.LCNF
import all Obend.Lower.Proofs.Book
import all Obend.Lower.Proofs.Complete
import all Obend.Lower.Proofs.Hardware
import all Obend.Polis.CapTP
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
import all Obend.Slot.World
import all Obend.Spec.Annotated
import all Obend.Spec.C4
import all Obend.Spec.Contract
import all Obend.Spec.DataWire
import all Obend.Spec.Elaborate
import all Obend.Spec.FrontEnd
import all Obend.Spec.Law
import all Obend.Spec.LawCompile
import all Obend.Spec.LawDial
import all Obend.Spec.Parse
import all Obend.Spec.Proofs.C4
import all Obend.Spec.Proofs.LawCompile
import all Obend.Spec.Sha256
import all Obend.Spec.Syntax
import all Obend.Spec.Types
import all Obend.Tactic.Cases
import all Obend.Tactic.MonadicReduction
import all Obend.Tactic.SymDiffAndFlux
import all Obend.Tactic.Tooth
import all Obend.Vault.Law
import all Obend.Vault.Mandate
import all Obend.Vault.Page
import all Obend.Codec.Hex
import all Obend.Core.SortedArray
import all Obend.Hardware.Fabulous.TileEval
public import Obend.Hardware.MultiDStencilCorrect
public import Obend.Tactic.Tooth
public import Obend.AssertAxioms

/-!
# PDE accelerator bridge tests

Concrete vectors, universal instantiations, mutation witnesses and the axiom audit for
`Obend.Hardware.MultiDStencilCorrect`: the systolic RTL and the fused GPU kernel of a nonlinear
conservation law against the Q32 reference semantics, including denominators at every
normalization exponent around `k = 31`, where the pre-clamped GPU shift amounts matter.
-/

public section
namespace Obend.Tests.PdeAcceleratorBridge
open Obend.Core
open Obend.Analysis.HyperbolicPde
open Obend.Analysis.NonlinearMultiDPde
open Obend.Hardware.ArrayHypergraph (Word)
open Obend.Hardware.Gpu.ArraySource (Rhs Program Env)
open Obend.Hardware.Gpu.ArrayPrograms (BuildM sourceBuild)
open Obend.Hardware.Gpu.SoacOptimize
open Obend.Hardware.Gpu.StencilTile
open Obend.Hardware.HDL
open Obend.Hardware.YosysLec
open Obend.Hardware.MultiDStencilTile
open Obend.Hardware.MultiDStencilCorrect
open Obend.Tactic.SymDiffAndFlux
set_option autoImplicit false

/-! ## 1. Reciprocal datapaths on edge-case words -/

/-- Zero, the domain boundary `16`, normalization exponents `k = 31` (`1/2`, the only exponent
at which neither raw shift difference wraps), `k = 32` (`-1/4`), `k = 33` (`1/8`), `k = 29` (`2`),
a negative non-dyadic value, one, and the two extreme words. -/
def edgeWords : List Word :=
  [0#64, 16#64, ratToQ32Word (1/2), ratToQ32Word (-1/4), ratToQ32Word (1/8), ratToQ32Word 2,
   ratToQ32Word (-7/3), ratToQ32Word 1, 0xFFFFFFFFFFFFFFFF#64, 0x8000000000000000#64]

def rtlReciprocal (w : Word) : Word :=
  evalWireTableFrom (fun _ => w) (fun _ => 0#64) (fun _ => 0#64)
    (assignRtlExprs 0 (reciprocalRtlExprs 0 (.inputPort 0))) 28

def gpuReciprocalSource : Program :=
  sourceBuild (fun ins => do let r ← bindPdeReciprocal 3 (ins.getD 0 0); pure [r]) [3]

#guard (q32NormalizeLoop [32, 16, 8, 4, 2, 1] (ratToQ32Word (1/2)) 0).2 == 31
#guard (q32NormalizeLoop [32, 16, 8, 4, 2, 1] (ratToQ32Word (1/4)) 0).2 == 32
#guard (q32NormalizeLoop [32, 16, 8, 4, 2, 1] (ratToQ32Word (1/8)) 0).2 == 33
#guard (q32NormalizeLoop [32, 16, 8, 4, 2, 1] (ratToQ32Word 2) 0).2 == 29
#guard edgeWords.all fun w => rtlReciprocal w == evalQ32Reciprocal w
#guard edgeWords.all fun w => gpuReciprocalSource.eval (fun _ => [w, 16#64, w]) ==
  [[evalQ32Reciprocal w, evalQ32Reciprocal 16#64, evalQ32Reciprocal w]]
#guard (evalQ32Reciprocal (ratToQ32Word (1/2))).toInt - (ratToQ32Word 2).toInt == -1
#guard (evalQ32Reciprocal (ratToQ32Word (-1/4))).toInt - (ratToQ32Word (-4)).toInt == 2
#guard (evalQ32Reciprocal (ratToQ32Word 2)).toInt - (ratToQ32Word (1/2)).toInt == -1
#guard (evalQ32Reciprocal (ratToQ32Word (-7/3))).toInt - (ratToQ32Word (-3/7)).toInt == 1

example (ins regs env0 : Nat → Word) :
    evalWireTableFrom ins regs env0 (assignRtlExprs 7 (reciprocalRtlExprs 7 (.inputPort 0))) (7 + 28) =
      evalQ32Reciprocal (ins 0) :=
  (reciprocalRtlExprs_eval_eq ins regs env0 1 0 7 (.inputPort 0) rfl).2

/-- Every shift a source program executes has a count below the 64-bit word width. -/
def shiftCountsBelow64 : Program → Env → Bool
  | .ret _, _ => true
  | .letE rhs body, env =>
    (match rhs with
      | .map _ .shr [_, c] | .map _ .shl [_, c] => (env c).all fun w => decide (w.toNat < 64)
      | _ => true) &&
    shiftCountsBelow64 body (Obend.Hardware.Gpu.ArraySource.push (rhs.eval env) env)

/-- The magnitude select with both shift arms evaluated on raw differences: the hazard class the
pre-clamped `shrAmt`/`shlAmt` of `bindPdeReciprocal` removes. Inputs: exponent `k`, mantissa `x`. -/
def eagerShiftSource : Program :=
  sourceBuild (fun ins => do
    let k := ins.getD 0 0
    let x := ins.getD 1 0
    let mag ← bindPdeScalar 1 (scalarSelect (scalarLt (.input k) (.const 31#64))
      (.prim .shr (.input x) (scalarSub (.const 31#64) (.input k)) (.const 0#64))
      (.prim .shl (.input x) (scalarSub (.input k) (.const 31#64)) (.const 0#64)))
    pure [mag]) [1, 1]

#guard edgeWords.all fun w => shiftCountsBelow64 gpuReciprocalSource (fun _ => [w, 16#64, w])
#guard (List.range 4096).all fun i =>
  shiftCountsBelow64 gpuReciprocalSource (fun _ => (List.range 3).map fun j =>
    BitVec.ofNat 64 (i * 0x9E3779B97F4A7C15 + j * 0xC2B2AE3D27D4EB4F) >>> (i % 64))
#guard !shiftCountsBelow64 eagerShiftSource (fun c => if c == 1 then [32#64] else [1#64])
#guard !shiftCountsBelow64 eagerShiftSource (fun c => if c == 1 then [29#64] else [1#64])
#guard shiftCountsBelow64 eagerShiftSource (fun c => if c == 1 then [31#64] else [1#64])

/-! ## 2. Nonlinear multi-component specifications -/

/-- Isothermal Euler in one dimension: `(rho, m)` with flux `(m, m^2 / rho + g rho)`. -/
def isoEuler : ConservationLawSpec :=
  { name := "IsoEuler1D", coords := ["x"], vars := ["rho", "m"], params := [("g", 3/2)],
    domain := [.stateVar 0],
    fluxes := [[.var 1, .add (.mul (.mul (.var 1) (.var 1)) (.invSafe (.var 0))) (.mul (.param 0) (.var 0))]],
    aMax := 3, cfl := 1/4, limiter := .minmod }

/-- A two-dimensional two-component system with a reciprocal in the `x` flux, first-order. -/
def shear2D : ConservationLawSpec :=
  { name := "Shear2D", coords := ["x", "y"], vars := ["h", "u"], params := [("k", 1/2)],
    domain := [.stateVar 0],
    fluxes := [[.mul (.var 0) (.var 1), .add (.mul (.var 1) (.var 1)) (.mul (.param 0) (.invSafe (.var 0)))],
               [.neg (.var 1), .mul (.var 0) (.var 0)]],
    aMax := 4, cfl := 1/8, limiter := .firstOrder }

def burgers : ConservationLawSpec :=
  { name := "Burgers", coords := ["x"], vars := ["u"], params := [], domain := [],
    fluxes := [[.mul (.const (1/2)) (.mul (.var 0) (.var 0))]], aMax := 2, cfl := 1/4,
    limiter := .minmod }

example : isoEuler.checkValid = true ∧ checkPdeQ32Intervals isoEuler = true ∧
    checkPdeQ32Constants isoEuler = true := by decide +kernel
example : shear2D.checkValid = true ∧ checkPdeQ32Intervals shear2D = true := by decide +kernel
example : burgers.checkValid = true ∧ checkPdeQ32Intervals burgers = true := by decide +kernel
/-- The interval gate that feeds the RTL refinement refuses a reciprocal of a sign-indefinite state. -/
example : checkPdeQ32Intervals { isoEuler with domain := [] } = false := by decide +kernel

/-! ## 3. Bridge A: systolic RTL -/

def sampleInputs (i : Nat) : Word := if i == 0 then ratToQ32Word (3/2) else ratToQ32Word (-2/3)

#guard (buildSpecSystolicRtl isoEuler 0).wires.length == 36 && (buildSpecSystolicRtl isoEuler 0).regs.length == 2
#guard edgeWords.all fun w =>
  let ins : Nat → Word := fun i => if i == 0 then w else ratToQ32Word (-2/3)
  let m := buildSpecSystolicRtl isoEuler 0
  (evalModuleOutputs m (fun _ => 0#64) (stepModuleRegs m false ins (fun _ => 7#64))).map Prod.snd ==
    evalFluxSsaDagQ32 ins isoEuler.paramEnv (getOr (specializeFluxSweep isoEuler).axisFluxDags 0 ⟨[], []⟩)
#guard (List.range 2).all fun axis =>
  let m := buildSpecSystolicRtl shear2D axis
  moduleFaithful m && checkRtlModule m &&
  (evalModuleOutputs m (fun _ => 0#64) (stepModuleRegs m false sampleInputs (fun _ => 0#64))).map Prod.snd ==
    evalFluxSsaDagQ32 sampleInputs shear2D.paramEnv
      (getOr (specializeFluxSweep shear2D).axisFluxDags axis ⟨[], []⟩)
-- Under reset the pipeline registers hold their reset value, not the flux.
#guard (evalModuleOutputs (buildSpecSystolicRtl isoEuler 0) (fun _ => 0#64)
  (stepModuleRegs (buildSpecSystolicRtl isoEuler 0) true sampleInputs (fun _ => 7#64))).map Prod.snd ==
    [0#64, 0#64]

example (inputs nextInputs regState : Nat → Word) :
    (evalModuleOutputs (buildSpecSystolicRtl isoEuler 0) nextInputs
      (stepModuleRegs (buildSpecSystolicRtl isoEuler 0) false inputs regState)).map Prod.snd =
      evalFluxSsaDagQ32 inputs isoEuler.paramEnv
        (getOr (specializeFluxSweep isoEuler).axisFluxDags 0 ⟨[], []⟩) :=
  spec_systolicRtl_refines_q32 isoEuler 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    inputs nextInputs regState

example (inputs nextInputs regState : Nat → Word) :
    (evalModuleOutputs (buildSpecSystolicRtl shear2D 1) nextInputs
      (stepModuleRegs (buildSpecSystolicRtl shear2D 1) false inputs regState)).map Prod.snd =
      evalFluxSsaDagQ32 inputs shear2D.paramEnv
        (getOr (specializeFluxSweep shear2D).axisFluxDags 1 ⟨[], []⟩) :=
  spec_systolicRtl_refines_q32 shear2D 1 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    inputs nextInputs regState

example : moduleFaithful (buildSpecSystolicRtl isoEuler 0) = true :=
  spec_systolicRtl_yosysLec_faithful isoEuler 0

/-- The miter theorem instantiated: an `unsat` answer for the emitted module pins the registers
Yosys reads after a non-reset edge to the Q32 flux of the inputs it read before. -/
example (hUnsat : ∀ Y, ¬ (lecScript (buildSpecSystolicRtl isoEuler 0)).holds Y) (Y : LecAssign)
    (hh : Y.h = true) (ht : Y.t = true)
    (hrst : ∀ r ∈ (buildSpecSystolicRtl isoEuler 0).regs,
      Y.bit false (resetPortOf (buildSpecSystolicRtl isoEuler 0) r) = false) :
    (buildSpecSystolicRtl isoEuler 0).regs.map (fun r =>
      ((yosysBV (buildSpecSystolicRtl isoEuler 0).name r.name true r.width).eval
        ((lecScript (buildSpecSystolicRtl isoEuler 0)).env Y)).setWidth 64) =
      evalFluxSsaDagQ32 ((lecScript (buildSpecSystolicRtl isoEuler 0)).inpVal Y) isoEuler.paramEnv
        (getOr (specializeFluxSweep isoEuler).axisFluxDags 0 ⟨[], []⟩) :=
  spec_systolicRtl_lec_unsat_refines_q32 isoEuler 0 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) hUnsat Y hh ht hrst

/-! ## 4. Bridge B: fused GPU kernel, constant states, brick tiling -/

def sampleGrids (c : Nat) : List Word :=
  if c == 0 then [1, 3/2, 2, 5/4, 3/4, 1].map ratToQ32Word
  else [1/2, -1/3, 0, 2, -1, 1/4].map ratToQ32Word

#guard [StencilBoundary.periodic, .clamp].all fun b =>
  evalFused sampleGrids (buildSpecFusedGpuKernel isoEuler b [6] 0) == stepQ32Axis isoEuler b [6] 0 sampleGrids
#guard evalFused sampleGrids (buildSpecFusedGpuKernel shear2D .clamp [3, 2] 1) ==
  stepQ32Axis shear2D .clamp [3, 2] 1 sampleGrids
#guard evalFused sampleGrids (buildSpecFusedGpuKernel shear2D .periodic [2, 3] 0) ==
  stepQ32Axis shear2D .periodic [2, 3] 0 sampleGrids
-- Reciprocal denominators with `k ≥ 31` in every cell: `rho = 1/2`, `1/4`, `1/8`, `3/4`.
#guard let grids : Nat → List Word := fun c =>
    if c == 0 then [1/2, 1/4, 1/8, 1/2, 3/4, 1/2].map ratToQ32Word else sampleGrids 1
  evalFused grids (buildSpecFusedGpuKernel isoEuler .periodic [6] 0) == stepQ32Axis isoEuler .periodic [6] 0 grids
#guard (stepQ32Axis isoEuler .periodic [6] 0 sampleGrids).map (·.map (·.toInt)) ==
  [[5077904043, 6800364886, 5950319275, 6397711702, 5033164800, 2952790016],
   [430428797, -888606577, 1488112429, 790393288, 4487905280, -223696213]]
#guard stepQ32Axis isoEuler .periodic [6] 3 sampleGrids == [sampleGrids 0, sampleGrids 1]
#guard (List.range 6).all fun idx => (List.range 5).all fun slot =>
  pdeNeighborIdx .periodic [6] 0 idx slot == (idx + 6 + slot - 2) % 6
#guard pdeNeighborIdx .clamp [3, 2] 1 5 4 == 5 && pdeNeighborIdx .clamp [3, 2] 0 5 0 == 1

example (b : StencilBoundary) (dims : List Nat) (grids : Nat → List Word) :
    evalFused grids (buildSpecFusedGpuKernel isoEuler b dims 0) = stepQ32Axis isoEuler b dims 0 grids :=
  spec_fusedGpuKernel_eq_stepQ32Axis isoEuler b dims 0 grids (by decide +kernel) (by decide +kernel)

example (b : StencilBoundary) (dims : List Nat) (grids : Nat → List Word) :
    evalFused grids (buildSpecFusedGpuKernel shear2D b dims 1) = stepQ32Axis shear2D b dims 1 grids :=
  spec_fusedGpuKernel_eq_stepQ32Axis shear2D b dims 1 grids (by decide +kernel) (by decide +kernel)

#guard evalFused (fun c => List.replicate 6 (sampleInputs c)) (buildSpecFusedGpuKernel isoEuler .periodic [6] 0) ==
  [List.replicate 6 (sampleInputs 0), List.replicate 6 (sampleInputs 1)]
-- A non-constant state is changed by the kernel: constant-state preservation is not vacuous.
#guard evalFused sampleGrids (buildSpecFusedGpuKernel isoEuler .periodic [6] 0) != [sampleGrids 0, sampleGrids 1]

example (b : StencilBoundary) (u0 : Nat → Word) :
    evalFused (fun c => List.replicate (gridCellCount [4, 3]) (u0 c)) (buildSpecFusedGpuKernel shear2D b [4, 3] 1) =
      (List.range shear2D.numVars).map fun c => List.replicate (gridCellCount [4, 3]) (u0 c) :=
  spec_fusedGpuKernel_preserves_constant_state shear2D b [4, 3] 1 _ u0 (by decide +kernel)
    (by decide +kernel) (by decide) (fun _ _ => rfl)

def brickGrid : List Word := (List.range 15).map fun i => ratToQ32Word ((i * i % 7 : Nat) / 3 - 1)

#guard [StencilBoundary.periodic, .clamp].all fun b =>
  [evalMultiDBrickTiled [2, 2] b [5, 3] 2 (pdeCellStencilFn burgers [5, 3] 0) brickGrid] ==
    stepQ32Axis burgers b [5, 3] 0 (fun _ => brickGrid)
#guard [evalMultiDBrickTiled [3, 2] .clamp [5, 3] 2 (pdeCellStencilFn burgers [5, 3] 1) brickGrid] ==
  stepQ32Axis burgers .clamp [5, 3] 1 (fun _ => brickGrid)

example (b : StencilBoundary) (grids : Nat → List Word) :
    [evalMultiDBrickTiled [2, 2] b [5, 3] 2 (pdeCellStencilFn burgers [5, 3] 0) (grids 0)] =
      stepQ32Axis burgers b [5, 3] 0 grids :=
  (spec_brickTiled_stepQ32_eq burgers b [2, 2] [5, 3] 0 grids (by decide +kernel) (by decide) rfl
    (by decide) (by decide)).1

example : multiDBrickHbmReads [2, 2] 2 [5, 3] < (2 * 2 + 1) ^ 2 * gridCellCount [5, 3] :=
  (spec_brickTiled_stepQ32_eq burgers .clamp [2, 2] [5, 3] 0 (fun _ => []) (by decide +kernel)
    (by decide) rfl (by decide) (by decide)).2 (by decide) (by decide +kernel)

/-! ## 5. Mutation witnesses -/

def brokenReciprocal (d : Word) : Word := d
def brokenNodeSem (_ : Nat → Word) (_ : Nat → Rat) (_ : Array Word) (_ : FluxSsaNode) : Word := 0#64
def brokenLowerNode (_ _ : Nat) (_ : Array Nat) (_ : Nat → Rat) (_ : FluxSsaNode) : List RtlExpr :=
  [.const 0#64]
def brokenGpuReciprocal (_ d : Nat) : BuildM Nat := pure d
def brokenHalf (a : ScalarExpr) : ScalarExpr := a
def brokenNeighbor (_ : StencilBoundary) (_ : List Nat) (_ idx _ : Nat) : Nat := idx

#tooth reciprocalRtlExprs_eval_eq by mutation evalQ32Reciprocal := brokenReciprocal
#tooth evalWireTable_systolic_eq_evalFluxSsaDagQ32 by mutation lowerSsaNodeToRtl := brokenLowerNode
#tooth spec_systolicRtl_refines_q32 by mutation evalFluxSsaNodeQ32 := brokenNodeSem
#tooth spec_systolicRtl_yosysLec_faithful by mutation smtFaithful := fun _ => false
#tooth spec_systolicRtl_lec_unsat_refines_q32 by mutation lowerSsaNodeToRtl := brokenLowerNode
#tooth spec_fusedGpuKernel_eq_stepQ32Axis by mutation bindPdeReciprocal := brokenGpuReciprocal
#tooth spec_fusedGpuKernel_eq_stepQ32Axis by mutation scalarQ32Half := brokenHalf
#tooth spec_fusedGpuKernel_eq_stepQ32Axis by mutation pdeNeighborIdx := brokenNeighbor
#tooth spec_fusedGpuKernel_preserves_constant_state by mutation pdeNeighborIdx := fun _ _ _ _ _ => 0
#tooth spec_brickTiled_stepQ32_eq by mutation pdeWindowSlot := fun _ _ _ => 0

/-! ## 6. Axiom census, closed-theorem and computational-choice audit -/

private meta partial def auditComputationalChoice (e : Lean.Expr) :
    StateRefT Lean.NameSet Lean.Meta.MetaM Unit := do
  if (← Lean.Meta.isProof e) || (← Lean.Meta.isType e) then return
  match e with
  | .const name _ =>
      if name == ``Classical.choice then throwError "Computational choice: {name}"
      if (← get).contains name then return
      modify (·.insert name)
      unless (← Lean.collectAxioms name).contains ``Classical.choice do return
      let info ← Lean.getConstInfo name
      if info matches .ctorInfo _ | .recInfo _ | .inductInfo _ | .quotInfo _ then return
      match info.value? with
      | some body => auditComputationalChoice body
      | none => throwError "Cannot inspect choice-dependent computational body: {name}"
  | .app f a => auditComputationalChoice f; auditComputationalChoice a
  | .lam name ty body bi =>
      Lean.Meta.withLocalDecl name bi ty fun x => auditComputationalChoice (body.instantiate1 x)
  | .letE name ty val body _ =>
      auditComputationalChoice val
      Lean.Meta.withLetDecl name ty val fun x => auditComputationalChoice (body.instantiate1 x)
  | .mdata _ body => auditComputationalChoice body
  | .proj _ _ body => auditComputationalChoice body
  | _ => pure ()

run_cmd do
  let env ← Lean.getEnv
  let ownModules := [`Obend.Hardware.MultiDStencilCorrect, `Obend.Hardware.MultiDStencilGpuSource]
  for (name, info) in env.constants.map₁.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let some mod := env.header.moduleNames[idx.toNat]? | continue
    unless ownModules.contains mod do continue
    let axs ← Lean.Elab.Command.liftCoreM (Lean.collectAxioms name)
    if axs.toList.any Obend.AssertAxioms.isCompilerTrust then
      throwError "Compiler trust dependency in {name}"
    if axs.contains ``sorryAx then throwError "sorryAx dependency in {name}"
    if name.isInternal || name.isInternalDetail then continue
    if name.components.getLast? == some `sizeOf_spec then continue
    if info matches .thmInfo _ then
      if ← Lean.Elab.Command.liftTermElabM (Obend.AssertAxioms.closedStatement info.type) then
        throwError "Closed theorem in owned module: {name}"
  for name in [
      ``evalWireTableFrom,
      ``pdeNeighborIdx,
      ``pdeGridSample,
      ``stepQ32Axis,
      ``pdeWindowSlot,
      ``pdeCellStencilFn,
      ``bindPdeReciprocal,
      ``buildSpecFusedGpuKernel,
      ``buildSpecSystolicRtl
    ] do
    Lean.Elab.Command.liftTermElabM do
      let _ ← (auditComputationalChoice (Lean.mkConst name)).run {}
      pure ()
  Lean.logInfo "PdeAcceleratorBridge audit passed: 0 compiler-trust axioms, 0 sorryAx, 0 closed library theorems, 0 computational choice."

#assert_axioms_tree
end Obend.Tests.PdeAcceleratorBridge
