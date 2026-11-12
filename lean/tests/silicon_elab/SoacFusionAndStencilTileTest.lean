module
public import Obend.Hardware.Gpu.SoacOptimize
public import Obend.Hardware.Gpu.StencilTile
import all Obend.Hardware.HDL
import all Obend.Core.Term
import all Obend.Tactic.Cases
import all Obend.Core.Traverse
import all Obend.Core.TermTraverse
import all Obend.Equiv.Reduction
import all Obend.Equiv.Fields
import all Obend.Equiv.Ahead
import all Obend.Equiv.Simulation
import all Obend.Equiv.Behaviour
import all Obend.Logic.LateBinding
import all Obend.Core.Machine
import all Obend.Core.MachineFast
import all Obend.Core.Ty
import all Obend.Core.Data
import all Obend.Digest.Cshake256.Spec
import all Obend.Digest.Cshake256.Fast
import all Obend.Digest.Cshake256.Seam
import all Obend.Digest.Cshake256
import all Obend.Digest.HashBytes
import all Obend.Core.Digest
import all Obend.Law.Syntax
import all Obend.Law.Claim
import all Obend.Core.Assumptions
import all Obend.Core.AliasExposure
import all Obend.Core.FiniteBisimulation
import all Obend.Core.FinitePresentation
import all Obend.Core.ResourceSemantics
import all Obend.Core.RecursiveRows
import all Obend.Core.TypeGraph
import all Obend.Core.RowHit
import all Obend.Core.RowExposureInvariance
import all Obend.Core.TypeGraphResource
import all Obend.Core.TypeGraphAlias
import all Obend.Core.RowCongruence
import all Obend.Core.FieldCongruence
import all Obend.Core.FiniteRowLaws
import all Obend.Core.LegacyAgreement
import all Obend.Core.CanonicalExtension
import all Obend.Core.EquiRecursiveAgreement
import all Obend.Core.TypeGraphHead
import all Obend.Core.RecursiveAgreement
import all Obend.Core.Check
import all Obend.Core.Bidirectional
import all Obend.Core.Invariant
import all Obend.Core.MachineTyping
import all Obend.Core.RuntimeOrigins
import all Obend.Core.EquiRecursiveLookup
import all Obend.Core.Proofs.StepCases
import all Obend.Core.Proofs.Adequacy.Defs
import all Obend.Core.Proofs.Adequacy.Scoped
import all Obend.Core.Proofs.Preservation.Base.Weaken
import all Obend.Core.Proofs.Preservation.Base.Heads
import all Obend.Core.Proofs.Preservation.Base.Insert
import all Obend.Core.Proofs.Preservation.Base.Reusable
import all Obend.Core.Proofs.Preservation.Base.Values
import all Obend.Core.Proofs.BidirectionalCompleteness
import all Obend.AssertAxioms
import all Obend.Tactic.Tooth
import all Obend.Core.Proofs.Substitution.Defs
import all Obend.Core.Proofs.Substitution.Uses
import all Obend.Core.Proofs.TypedSubstitution
import all Obend.Slot.Protocol
import all Obend.Slot
import all Obend.Tactic.MonadicReduction
import all Obend.Elab.Work
import all Obend.Slot.Core4
import all Obend.Intention
import all Obend.Spec.C4
import all Obend.Law.Inherit
import all Obend.Kind
import all Obend.Core.Brand
import all Obend.Core.Nominal
import all Obend.Core.Code
import all Obend.Law.Run
import all Obend.Law.Proofs.Run
import all Obend.Equiv.Quote
import all Obend.Law.Std
import all Obend.Law.Proofs.Eval
import all Obend.Law.Proofs.Std
import all Obend.Law.Proofs.Claim
import all Obend.Law.Machine
import all Obend.Spec.Proofs.C4
import all Obend.Law.Proofs.Inherit
import all Obend.Core.Proofs.Adequacy.Source
import all Obend.Core.Proofs.Adequacy.Meaning
import all Obend.Core.Proofs.Adequacy.Graph
import all Obend.Core.Proofs.Adequacy.Birth
import all Obend.Core.Proofs.Adequacy.CasesControl
import all Obend.Core.Proofs.Adequacy.CasesEval
import all Obend.Core.Proofs.Adequacy.CasesReturn
import all Obend.Core.Proofs.Adequacy.Origins
import all Obend.Core.Proofs.Adequacy.Run
import all Obend.Core.Proofs.Adequacy.Safety
import all Obend.Core.Proofs.Adequacy.StepRaw
import all Obend.Core.Proofs.Adequacy.SafetyRaw
import all Obend.Core.Proofs.Adequacy.Progress
import all Obend.Core.Proofs.Adequacy.Sound
import all Obend.Core.Proofs.Completeness
import all Obend.Core.Capacity
import all Obend.Core.Proofs.Adequacy.Reach
import all Obend.Core.Proofs.DataSoundness
import all Obend.Core.Proofs.GroundExecution
import all Obend.Law.Proofs.Machine
import all Obend.Logic.Claim
import all Obend.Leaf.UpTo
import all Obend.Leaf.Flatten
import all Obend.Leaf.Emit
import all Obend.Hardware.Types
import all Obend.Hardware.Compiler
import all Obend.Hardware.OpenHypergraph
import all Obend.Hardware.ArrayFold
import all Obend.Hardware.ArrayHypergraph
import all Obend.Hardware.Gpu.Limbs
import all Obend.Hardware.Gpu
import all Obend.Hardware.Gpu.ArraySource
import all Obend.Hardware.Gpu.SoacOptimize
import all Obend.Hardware.ArrayKernelUnique
import all Obend.Hardware.ArrayKernel
import all Obend.Hardware.Gpu.CollectiveTree
import all Obend.Hardware.Gpu.CollectiveBlock
import all Obend.Hardware.Gpu.BlockLower
import all Obend.Hardware.Gpu.BlockEmit
import all Obend.Hardware.Gpu.Memory
import all Obend.Hardware.Gpu.Workgroup
import all Obend.Hardware.Gpu.SourceProtocol
import all Obend.Hardware.Gpu.ArraySchedule
import all Obend.Hardware.Gpu.ArrayEmit
import all Obend.Hardware.ArrayKernelOwnership
import all Obend.Hardware.Gpu.PhaseSemantics
import all Obend.Hardware.Gpu.CollectiveArena
import all Obend.Hardware.Gpu.CollectiveCorrect
import all Obend.Hardware.Gpu.CollectiveTrace
import all Obend.Hardware.Gpu.CollectiveHierarchy
import all Obend.Hardware.Gpu.CollectiveCompose
import all Obend.Hardware.Gpu.CollectiveExecute
import all Obend.Hardware.Gpu.CollectiveBuildFacts
import all Obend.Hardware.Gpu.CollectiveReduceExec
import all Obend.Hardware.Gpu.CollectiveReduceBuild
import all Obend.Hardware.Gpu.CollectiveScanExec
import all Obend.Hardware.Gpu.CollectiveBuildCorrect
import all Obend.Hardware.Gpu.CollectiveArenaCorrect
import all Obend.Hardware.Gpu.ArrayEmitCorrect
import all Obend.Hardware.Gpu.StencilTile
meta import all Obend.Hardware.Gpu.SoacOptimize
meta import all Obend.Hardware.Gpu.StencilTile
public section
namespace Obend.Hardware.Gpu.SoacFusionAndStencilTileTest
open Obend.Hardware.ArrayHypergraph Obend.Hardware.OpenHypergraph
open Obend.Hardware.Gpu.ArraySource Obend.Hardware.Gpu.SoacOptimize
open Obend.Hardware.Gpu.StencilTile
set_option autoImplicit false

def shift : FiniteFunction := ⟨4,4,[1,2,3,0]⟩
def pick : FiniteFunction := ⟨3,4,[3,1,0]⟩
def grid : Vec := [3#64,5#64,7#64,11#64]
def env : Env := fun _ => grid

def gatherChain : Program :=
  .letE (.gather shift 0)
    (.letE (.gather pick 0)
      (.letE (.literal [99#64]) (.ret [1])))

#guard gatherChain.eval env == [[3#64,7#64,5#64]]
#guard (normalizeProgram gatherChain).eval env == gatherChain.eval env
#guard letCount gatherChain == 3
#guard letCount (normalizeProgram gatherChain) == 1
#guard arenaWords env (normalizeProgram gatherChain) == 3
#guard (normalizeProgram gatherChain).scopedB 1

/-- The pullback guard must refuse a consumer miss, even if source slot zero is nonzero. -/
def gatherMiss : Program :=
  .letE (.gather ⟨1,4,[1]⟩ 0) (.letE (.gather ⟨2,1,[0,4]⟩ 0) (.ret [0]))
example : (normalizeProgram gatherMiss).eval env = [[5#64,0#64]] := by decide +kernel

def repeated : Program :=
  .letE (.map 4 (.scalar (.scale 2)) [0])
    (.letE (.map 4 (.scalar (.scale 2)) [1]) (.ret [0,1]))
#guard letCount (cseProgram repeated) == 1
#guard (cseProgram repeated).eval env == repeated.eval env

def identityCopies : Program :=
  .letE (.map 4 (.scalar (.scale 2)) [0])
    (.letE (.gather (FiniteFunction.id 4) 0)
      (.letE (.map 4 (.scalar (.scale 1)) [0]) (.ret [0])))
#guard letCount (normalizeProgram identityCopies) == 1
#guard (normalizeProgram identityCopies).eval env == identityCopies.eval env

def constantGather : Program :=
  .letE (.literal grid) (.letE (.gather pick 0) (.ret [0]))
example : (normalizeProgram constantGather).eval env = [[11#64,5#64,3#64]] := by decide +kernel
#guard letCount (normalizeProgram constantGather) == 1

def fourMaps (n : Nat) : Program :=
  .letE (.map n (.scalar (.scale 2)) [0])
    (.letE (.map n (.scalar (.scale 3)) [0])
      (.letE (.map n (.scalar (.scale 5)) [0])
        (.letE (.map n (.scalar (.scale 7)) [0]) (.ret [0]))))

#guard evalFused env (fuseVertical (liftArraySource (fourMaps 4))) == (fourMaps 4).eval env
example : globalWrites env (liftArraySource (fourMaps 1024)) = 4096 := by decide +kernel
example : globalWrites env (fuseVertical (liftArraySource (fourMaps 1024))) = 1024 := by decide +kernel
example : hbmTrafficWords (liftArraySource (fourMaps 1024)) env = 8192 := by decide +kernel
example : hbmTrafficWords (fuseVertical (liftArraySource (fourMaps 1024))) env = 2048 := by decide +kernel

def mappedReduction : FusedProgram :=
  .letE (mapKernel 4 [.var 0] (.prim (.scalar (.scale 2)) (.input 0) (.const 0#64) (.const 0#64)))
    (.letE (foldMapKernel .add 13#64 4 [.var 0] (.input 0)) (.ret [0]))
#guard evalFused env (fuseVertical mappedReduction) == [[65#64]]
#guard globalWrites env mappedReduction == 5
#guard globalWrites env (fuseVertical mappedReduction) == 1
#guard hbmTrafficWords mappedReduction env == 13
#guard hbmTrafficWords (fuseVertical mappedReduction) env == 5

def mappedScan : FusedProgram :=
  .letE (mapKernel 4 [.var 0] (.prim (.scalar (.scale 2)) (.input 0) (.const 0#64) (.const 0#64)))
    (.letE (scanMapKernel .add 13#64 4 .inclusive [.var 0] (.input 0)) (.ret [0]))
#guard evalFused env (fuseVertical mappedScan) == [[19#64,29#64,43#64,65#64]]
#guard globalWrites env (fuseVertical mappedScan) == 4

def stateAndNorm : TupleKernel :=
  ⟨4, .var 0, .prim (.scalar (.scale 2)) (.input 0) (.const 0#64) (.const 0#64),
    .prim (.scalar (.scale 2)) (.input 0) (.const 0#64) (.const 0#64), .mapFold .add 0#64⟩
#guard (fuseHorizontal (.separate stateAndNorm)).eval env == ([6#64,10#64,14#64,22#64],[52#64])
#guard horizontalReads (.separate stateAndNorm) == 8
#guard horizontalReads (fuseHorizontal (.separate stateAndNorm)) == 4
#guard evalTuple {stateAndNorm with mode := .maps} env == evalSeparate {stateAndNorm with mode := .maps} env

example : tiledHbmReads 64 1 1024 = 1056 := by decide +kernel
example : tiledHbmReads 64 2 1024 = 1088 := by decide +kernel
example : (2*1+1)*1024 = 3072 := by decide +kernel
example : (2*2+1)*1024 = 5120 := by decide +kernel
example : tileWidths 16 67 = [16,16,16,16,3] := by decide +kernel
example : tiledHbmReads 16 2 67 = 87 := by decide +kernel
example : tileWidths 64 3 = [3] := by decide +kernel
example : resolveStencilIdx .periodic 67 (-1) = 66 := by decide +kernel
example : resolveStencilIdx .clamp 67 99 = 66 := by decide +kernel
example : resolveStencilIdx .clamp 67 (-9) = 0 := by decide +kernel

def stencil3 : ScalarExpr :=
  .prim (.scalar .add)
    (.prim (.scalar .add) (.input 0) (.input 2) (.const 0#64))
    (.prim (.scalar (.scale 2)) (.input 1) (.const 0#64) (.const 0#64)) (.const 0#64)

def stencil5 : ScalarExpr :=
  .prim (.scalar .sub)
    (.prim (.scalar .add) (.input 0) (.input 4) (.const 0#64))
    (.prim (.scalar .add) (.input 1) (.input 3) (.const 0#64)) (.const 0#64)

def primeGrid : Vec := (List.range 67).map (fun i => BitVec.ofNat 64 (i*i+3*i+1))
#guard evalTiledHaloStencil 16 .periodic 2 (scalarStencil stencil5) primeGrid == evalStencil1D .periodic 2 (scalarStencil stencil5) primeGrid
#guard evalTiledHaloStencil 16 .clamp 2 (scalarStencil stencil5) primeGrid == evalStencil1D .clamp 2 (scalarStencil stencil5) primeGrid
#guard evalTiledHaloStencil 64 .periodic 1 (scalarStencil stencil3) grid == evalStencil1D .periodic 1 (scalarStencil stencil3) grid
#guard evalTiledHaloStencil 2 .clamp 7 (scalarStencil stencil3) grid == evalStencil1D .clamp 7 (scalarStencil stencil3) grid
#guard evalTiledHaloStencil 16 .periodic 2 (scalarStencil stencil5) [] == []
#guard (compileStencilGlobal .periodic 2 67 stencil5).eval (fun _ => primeGrid) == [evalStencil1D .periodic 2 (scalarStencil stencil5) primeGrid]
#guard evalFused (fun _ => primeGrid) (compileStencilFused .clamp 2 67 stencil5) == [evalStencil1D .clamp 2 (scalarStencil stencil5) primeGrid]
#guard letCount (normalizeProgram (compileStencilGlobal .periodic 1 4 stencil3)) < letCount (compileStencilGlobal .periodic 1 4 stencil3)
#guard globalWrites env (compileStencilFused .periodic 1 4 stencil3) == 4

#guard evalTiledHaloStencilExec 16 .periodic 2 (scalarStencil (minmodTvdNumerator 1 1)) primeGrid == evalStencil1D .periodic 2 (scalarStencil (minmodTvdNumerator 1 1)) primeGrid
#guard evalTiledHaloStencilExec 16 .clamp 2 (scalarStencil (minmodTvdNumerator 1 1)) primeGrid == evalStencil1D .clamp 2 (scalarStencil (minmodTvdNumerator 1 1)) primeGrid
#guard evalTiledHaloStencilExec 64 .periodic 1 (scalarStencil (rusanovNumerator 1 1)) grid == evalStencil1D .periodic 1 (scalarStencil (rusanovNumerator 1 1)) grid
#guard executeHaloPhases 1 4 (scalarStencil stencil3) (fun _ => loadHalo .periodic 1 grid 0 4) [.cooperativeLoad,.localCompute] #[] false == []
#guard (scalarMinmod (.const 3#64) (.const 5#64)).eval (fun _ => 0#64) == 3#64
#guard (scalarMinmod (.const (BitVec.ofInt 64 (-3))) (.const (BitVec.ofInt 64 (-5)))).eval (fun _ => 0#64) == BitVec.ofInt 64 (-3)
#guard (scalarMinmod (.const 3#64) (.const (BitVec.ofInt 64 (-5)))).eval (fun _ => 0#64) == 0#64

#guard globalWrites env (compileStencilFused .periodic 1 1024 (rusanovNumerator 1 1)) == 1024
#guard evalFused env (compileStencilFused .periodic 1 4 (rusanovNumerator 1 1)) == [evalStencil1D .periodic 1 (scalarStencil (rusanovNumerator 1 1)) grid]

def fusedBindings : FusedProgram → Nat
  | .ret _ => 0
  | .letE _ p => 1+fusedBindings p
#guard fusedBindings (liftArraySource (fourMaps 1024)) == 4
#guard fusedBindings (fuseVertical (liftArraySource (fourMaps 1024))) == 1

def shapeMismatch : Program :=
  .letE (.map 2 (.scalar (.scale 2)) [0]) (.letE (.map 4 (.scalar (.scale 3)) [0]) (.ret [0]))
#guard evalFused env (fuseVertical (liftArraySource shapeMismatch)) == [[18#64,30#64,0#64,0#64]]

def repeatedConsumers : FusedProgram :=
  .letE (.mapKernel 4 (.prim (.scalar .mac) (.var 0) (.var 1) (.var 2)))
    (.letE (.mapKernel 4 (unaryStream (.scalar (.scale 2)) (.var 0)))
      (.letE (.mapKernel 4 (unaryStream (.scalar (.scale 3)) (.var 1)))
        (.letE (.mapKernel 4 (unaryStream (.scalar (.scale 5)) (.var 2))) (.ret [0,1,2]))))
#guard fixedTraffic (verticalCandidate repeatedConsumers) > fixedTraffic repeatedConsumers
#guard fixedTraffic (fuseVertical repeatedConsumers) == fixedTraffic repeatedConsumers
#guard evalFused env (fuseVertical repeatedConsumers) == evalFused env repeatedConsumers

#tooth hbmTraffic_fuseVertical_le by mutation fuseVertical := verticalCandidate
#tooth dceProgram_sound by mutation renameProgram := fun _ p => p
#tooth normalizeProgram_sound by mutation dropBinder := fun replacement i => if i = 0 then replacement else i
#tooth composeIndexFn_sound by mutation composeIndexFn := fun f g => ⟨f.source,g.target,f.table.map (fun i => g.table.getD i 0)⟩
#tooth fuseVertical_sound by mutation KernelInput.bind := fun f _ => f 1
#tooth fuseVertical_sound by mutation FusedRhs.inline := fun f r => match r with
  | .mapKernel n e => .mapKernel n (e.bind f)
  | .foldKernel op shape _ e => .foldKernel op shape 0#64 (e.bind f)
  | .source rhs => .source rhs
#tooth tupleKernel_sound by mutation tupleValues := fun k env i =>
  let slots := unarySlots (k.input.eval env i)
  (k.left.eval slots,k.left.eval slots)
#tooth tiledHaloStencil_eq_spec by mutation loadHalo := fun b r grid start width =>
  ((List.range width).map fun (k : Nat) => grid.getD (resolveStencilIdx b grid.length ((start : Int)+k-r)) 0#64).toArray
#tooth tiledHaloStencil_eq_spec by mutation loadHalo := fun b r grid start width =>
  ((List.range (width+2*r)).map fun (k : Nat) => grid.getD (resolveStencilIdx b grid.length ((start : Int)+k)) 0#64).toArray
#tooth resolveStencilIdx_lt by mutation resolveStencilIdx := fun b n i => match b with
  | .periodic => (i % (n : Int)).toNat
  | .clamp => if i ≤ 0 then 0 else if (n-1 : Nat) ≤ i then n else i.toNat

#tooth tiledHaloStencil_eq_spec by mutation TiledStencilPlan.phases := fun _ => [.cooperativeLoad,.localCompute]

-- Audit this lane independently of inherited declarations, without hiding any
-- declarations from the full-tree census below.
run_cmd do
  let env ← Lean.getEnv
  let mut checked : Nat := 0
  for (name, info) in env.constants.map₁.toList do
    let own := (`Obend.Hardware.Gpu.SoacOptimize).isPrefixOf name
      || (`Obend.Hardware.Gpu.StencilTile).isPrefixOf name
    if own then
      let axioms ← Lean.collectAxioms name
      if axioms.toList.any Obend.AssertAxioms.isCompilerTrust then
        Lean.throwError m!"Owned declaration has compiler trust: {name}"
      if let .thmInfo _ := info then
        if !name.isInternal && !name.isInternalDetail then
          let closed ← Lean.Elab.Command.liftTermElabM fun _ => Obend.AssertAxioms.closedStatement info.type
          if closed then Lean.throwError m!"Closed owned theorem: {name}"
          checked := checked+1
    else if let .thmInfo _ := info then
      if !name.isInternal && !name.isInternalDetail then
        let axioms ← Lean.collectAxioms name
        if axioms.toList.any Obend.AssertAxioms.isCompilerTrust then
          Lean.logInfo m!"Inherited compiler-trust theorem: {name}"
  Lean.logInfo m!"Owned audit: {checked} universal theorems; zero compiler-trust dependencies; zero closed theorems"

#assert_axioms_tree
end Obend.Hardware.Gpu.SoacFusionAndStencilTileTest
