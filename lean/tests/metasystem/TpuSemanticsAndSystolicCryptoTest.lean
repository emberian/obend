module
public import Obend.Hardware.Tpu.Machine
public import Obend.Hardware.Tpu.CryptoSystolic
public meta import Obend.Hardware.Tpu.Machine
public meta import Obend.Hardware.Tpu.CryptoSystolic
public meta import Obend.Crypto.FastRing
public meta import Obend.Hardware.Gpu.NttSpec
public meta import Obend.Crypto.Multilinear
public meta import Obend.Apps.ZkNtt.Goldilocks
public meta import Obend.Crypto.DualSpine
-- The axiom census needs implementation bodies throughout this import cone.
import all Obend.Apps.ZkNtt.Goldilocks
import all Obend.Crypto.Multilinear
import all Obend.AssertAxioms
import all Obend.Tactic.Tooth
import all Obend.Crypto.FastRing
import all Obend.Hardware.Gpu.NttSpec
import all Obend.Hardware.Tpu.Machine
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
import all Obend.Hardware.ArrayKernelUnique
import all Obend.Hardware.ArrayKernel
import all Obend.Hardware.ArrayBuild
import all Obend.Hardware.Gpu.Limbs
import all Obend.Hardware.Gpu.LimbsGoldilocks
import all Obend.Hardware.Gpu.LimbsShift
import all Obend.Hardware.Gpu.GoldilocksSource
import all Obend.Judge.Class
import all Obend.Judge.Computational
import all Obend.Crypto.Transcript
import all Obend.Crypto.PikkuFoldLayered
import all Obend.Crypto.Sumcheck
import all Obend.Crypto.PCS
import all Obend.Crypto.DualSpine
import all Obend.Hardware.Tpu.CryptoSystolic
import all Obend.Category.Refines
import all Obend.Crypto.GameSoundness

public section
namespace Obend.Tests.TpuSemanticsAndSystolicCrypto
open Obend.Hardware.Tpu Obend.Crypto Obend.Crypto.Fast Obend.Apps.ZkNtt
open Obend.Hardware.Gpu.Ntt

#assert_axioms_tree

-- Full-depth accumulator bounds, with the boundary bytes that expose sign bugs.
#guard (mxuDot .unsigned8 (fun _ => 255) (fun _ => 255)).toNat == 8323200
#guard (mxuDot .signed8 (fun _ => 255) (fun _ => 127)).toInt32.toInt == -16256
#guard mxuTernaryByteDot (fun _ => .neg) (fun _ => 255) == -32640
#guard mxuTernaryByteDot (fun i => if i%2 == 0 then .pos else .neg) (fun i => i+128) == -64
#guard (mxuDot .bf16 (fun _ => 0x42fe) (fun _ => 0x42fe)).toNat == 0x49fc0400
#guard decodeBf16 0x8000 == BinaryFloat.zero true
#guard encodeFp32 (fpAdd (.infinity false) (.infinity true)) == 0x7fc00000
#guard roundShiftEven 5 1 == 2
#guard roundShiftEven 7 1 == 4

-- All eight byte planes contribute; reducing only the low word fails this vector.
def aWord (i : Nat) : Nat := if i%3 == 0 then goldilocksPrime-1 else 0x123456789abcdef0
def bWord (i : Nat) : Nat := if i%2 == 0 then 0xfedcba9876543210 else 0x80000000000000ff
#guard mxuGoldilocksDot aWord bWord == Sum.sum 128 (fun i => aWord i * bWord i) % goldilocksPrime
#guard (evalVpu .goldilocksReduce 0xffffffffffffffff 0xffffffffffffffff).toNat ==
  (2^128-1)%goldilocksPrime
#guard evalVpu .carry64 0xffffffffffffffff 1 == 1
#guard evalVpu .add32 0xffffffff 1 == 0
#guard evalVpu .shl64 1 63 == 0x8000000000000000

-- Independent reference DFT with a nontrivial fourth root.
def root4 : Nat := 281474976710656
def input4 (i : Nat) : Nat := i+1
#guard modPow root4 4 == 1
#guard (List.range 4).all fun k =>
  baileyMxuNtt 2 2 root4 input4 (k%2) (k/2) == dft 4 root4 input4 k


-- Native ternary bytes agree with the existing DualSpine commitment.
def ternaryRows : List (Nat → Ternary) := [fun _ => .pos, fun _ => .neg]
#guard mxuTernaryAjtai ternaryRows 65537 (fun _ => 255) == [32640, 32897]
#guard mxuTernaryAjtai ternaryRows 65537 (fun _ => 255) ==
  ajtaiCommit (ternaryAjtaiParams ternaryRows 65537 (by simp [ternaryRows]) (by decide))
    (byteWitness (fun _ => 255)) (by simp [ternaryAjtaiParams, byteWitness])

-- The X^128=-1 wrap must subtract the coefficient crossing degree 127.
def polyA (i : Fin 128) : Goldilocks := Goldilocks.ofNat (if i.val == 127 then 3 else 0)
def polyB (i : Fin 128) : Goldilocks := Goldilocks.ofNat (if i.val == 1 then 5 else 0)
#guard mxuRlweExternalProduct polyA polyB 0 == goldilocksPrime-15
#guard (mxuRlweExternalProduct polyA polyB 0 : Int) == polyMul polyA polyB 0
#guard mxuRlweExternalProduct polyA polyB 1 == 0

-- Two simultaneous, distinct DMA handles. Retire the second before the first.
def initial : TpuCoreState := TpuCoreState.initial 2 3 1 3 2

def copy0 : TpuInstr := .dma ⟨.hbm,0⟩ ⟨.vmem,0⟩ 0
def copy1 : TpuInstr := .dma ⟨.hbm,1⟩ ⟨.vmem,1⟩ 1
def safeCopies : TpuProg := [copy0, copy1, .wait 1 1, .wait 0 1, .finish]
def missingWait : TpuProg := [copy0, .transpose 1 0, .wait 0 1, .finish]
#guard checkDmaSemaphores 2 safeCopies
#guard !checkDmaSemaphores 2 missingWait
#guard (runEvents initial [.instruction copy0, .instruction (.transpose 1 0)]).error == some .dmaRace
#guard (runEvents initial [.instruction copy0, .instruction (.wait 0 0), .instruction (.transpose 1 0)]).error == some .dmaRace
#guard (runEvents initial [.instruction (.signal 0 1), .instruction .finish]).error == some .nonzeroExitSemaphore
#guard (runEvents initial [.instruction (.wait 0 1)]).error == some .semaphoreUnderflow
#guard (runEvents initial [.instruction copy0, .instruction copy0]).error == some .dmaRace
#guard !checkDmaSemaphores 2 [.signal 0 1, .finish]
#guard !checkDmaSemaphores 0 [.permute 0 0 #[0]]
#guard !checkDmaSemaphores 0 [.loadVReg 0 0 16]
#guard !checkDmaSemaphores 2 [copy0, .wait 0 0, .transpose 1 0, .wait 0 1]
#guard (runEvents initial [.instruction copy0, .instruction copy1, .retire 1, .retire 0,
  .instruction (.wait 1 1), .instruction (.wait 0 1), .instruction .finish]) == runSync initial safeCopies

-- Nonzero data demonstrates that retirement, rather than issue, writes VMEM.
def nonzeroInitial : TpuCoreState := { initial with hbm := #[Sized.ofFn (fun _ => 7), zeroTile] }
#guard ((stepAsync nonzeroInitial copy0).vmem[0]?.getD zeroTile).coeffs[0]! == 0
#guard ((retireDma (stepAsync nonzeroInitial copy0) 0).vmem[0]?.getD zeroTile).coeffs[0]! == 7
#guard (retireDma (stepAsync nonzeroInitial copy0) 0).semaphores[0]! == 1

/-- Inhabited multi-handle trace: the second copy retires first, then an XLU
instruction reads the first copy's nonzero payload after both waits. -/
def refinementProgram : TpuProg :=
  [copy0, copy1, .wait 1 1, .wait 0 1, .transpose 2 0, .finish]

def refinementTrace : List TpuEvent :=
  [.instruction copy0, .instruction copy1, .retire 1, .retire 0,
   .instruction (.wait 1 1), .instruction (.wait 0 1),
   .instruction (.transpose 2 0), .instruction .finish]

theorem outOfOrder_dma_compute_refinement :
    (runEvents nonzeroInitial refinementTrace).error = none ∧
    runEvents nonzeroInitial refinementTrace = runSync nonzeroInitial refinementProgram := by
  apply checkDmaSemaphores_async_refines_sync
  · refine ⟨rfl, rfl, rfl, ?_⟩
    simp [refinementProgram, copy0, copy1, InstrBound, tileBound, nonzeroInitial,
      initial, TpuCoreState.initial]
  · simp [checkDmaSemaphores, analyzeProgram, analyzeStep, footprintHazard, Array.getElem_modify,
      refinementProgram, copy0, copy1, nonzeroInitial, initial, TpuCoreState.initial]
    decide
  · unfold refinementTrace
    apply ValidTrace.instruction
    apply ValidTrace.instruction
    apply ValidTrace.retire
    · simp [stepAsync, stepBody, dmaHazard, readTile, copy0, copy1, nonzeroInitial, initial, TpuCoreState.initial]
    · simp [stepAsync, stepBody, dmaHazard, readTile, copy0, copy1, nonzeroInitial, initial, TpuCoreState.initial]
    · apply ValidTrace.retire
      · simp [retireDma, writeTile, stepAsync, stepBody, dmaHazard, readTile, copy0, copy1, nonzeroInitial, initial, TpuCoreState.initial]
      · simp [retireDma, writeTile, stepAsync, stepBody, dmaHazard, readTile, copy0, copy1, nonzeroInitial, initial, TpuCoreState.initial]
      · apply ValidTrace.instruction
        apply ValidTrace.instruction
        apply ValidTrace.instruction
        apply ValidTrace.instruction
        exact ValidTrace.nil _
  · rfl

#guard ((runEvents nonzeroInitial refinementTrace).vmem[2]?.getD zeroTile).coeffs[0]! == 7
#guard checkDmaSemaphores 1 [copy0, .dma ⟨.hbm,1⟩ ⟨.vmem,1⟩ 0,
  .signal 0 1, .wait 0 1, .wait 0 2, .transpose 2 0, .finish]
#print axioms checkDmaSemaphores_async_refines_sync

-- Kernel-body source covers MXU, XLU, VPU and explicit descriptor waits.
def matmulProgram : TpuProg :=
  [copy0, copy1, .wait 0 1, .wait 1 1, .mxu .unsigned8 2 0 1, .finish]
def transposeProgram : TpuProg :=
  [copy0, .wait 0 1, .transpose 1 0, .loadVReg 0 1 0, .vpu .mul64 1 0 0,
   .storeVReg 1 0 1, .transpose 2 1, .finish]
#guard (emitPallasTpuKernel matmulProgram).contains "preferred_element_type=jnp.int32"
#guard (emitPallasTpuKernel matmulProgram).contains "pltpu.make_async_copy"
#guard (emitPallasTpuKernel matmulProgram).contains ".wait()"
#guard (emitPallasTpuKernel transposeProgram).contains "tile[0].T"
#guard (emitPallasTpuKernel transposeProgram).contains "_vpu('mul64'"
#guard (emitPallasTpuKernel missingWait).startsWith "raise ValueError"


-- The emitted programs are the full byte-plane and Bailey instruction streams.
def goldilocksKernel : TpuProg :=
  [copy0, copy1, .wait 0 1, .wait 1 1] ++ goldilocksGemmProgram 2 0 1 3 ++ [.finish]
def baileyKernel : TpuProg := baileyNttProgram 5 0 1 2 3 6 ++ [.finish]
#guard (goldilocksGemmProgram 2 0 1 3).countP (fun i => match i with | .mxu _ _ _ _ => true | _ => false) == 64
#guard (baileyNttProgram 5 0 1 2 3 6).countP (fun i => match i with | .mxu _ _ _ _ => true | _ => false) == 128
#guard (emitPallasTpuKernel goldilocksKernel).contains "_vpu('goldilocksReduce'"
#guard (emitPallasTpuKernel baileyKernel).contains "_vpu('mulHigh64'"
#guard (emitPallasTpuKernel baileyKernel).contains "tile[0].T"

-- Full machine composition: every operand is p-1, so every output is 128.
-- This exercises all eight byte planes, 64 MXU tiles, and VPU carry/reduction.
def gemmInitial : TpuCoreState :=
  { TpuCoreState.initial 2 7 0 7 2 with
    hbm := Array.replicate 2 (Sized.ofFn fun _ => UInt64.ofNat (goldilocksPrime-1)) }
#guard let result := runSync gemmInitial goldilocksKernel
  result.error.isNone && ((result.vmem[2]?).map (fun tile => tile.coeffs.all (· == 128))).getD false



#print axioms mxuGoldilocksGemm_eq_specMatMul
#print axioms baileyMxuNtt_eq_specNtt
#print axioms mxuTernaryAjtai_eq_ajtaiCommit
#print axioms mxuRlweExternalProduct_eq_polyMul
#print axioms mxuDot_eq_exec
#print axioms mxuGoldilocksDot_eq_exec

#guard checkDmaSemaphores 2
    [.dma ⟨.hbm,0⟩ ⟨.vmem,0⟩ 0, .dma ⟨.hbm,1⟩ ⟨.vmem,1⟩ 1,
     .wait 1 1, .wait 0 1, .transpose 2 0, .finish]
#guard !(checkDmaSemaphores 1
    [.dma ⟨.hbm,0⟩ ⟨.vmem,0⟩ 0, .transpose 1 0, .wait 0 1])
example : analyzeStep ⟨[], #[0]⟩ .finish = some ⟨[], #[0]⟩ := by simp [analyzeStep]

#tooth analyzeStep_read_refuses by mutation analyzeStep := fun a _ => some a
#tooth analyzeStep_finish_drained by mutation analyzeStep := fun a _ => some a
#tooth stepAsync_failClosed by mutation stepAsync := fun s i => stepBody { s with error := none } i


#tooth radixSum_bytes by mutation byteLimb := fun x _ => x % 256
#tooth mxuGoldilocksDot_eq by mutation limbMxuDot := fun _ _ _ _ => 0
#tooth baileyMxuNtt_eq_specNtt by mutation baileyMxuNtt := fun _ _ _ _ _ _ => 0
#tooth signedByte_centered by mutation centeredByte := fun x => UInt64.ofNat x
#tooth mxuRlweExternalProduct_eq_polyMul by mutation negacyclicCoefficient := fun b k i =>
  (b ⟨(k.val+128-i)%128, Nat.mod_lt _ (by decide)⟩).val


#tooth checkDmaSemaphores_async_refines_sync by mutation checkDmaSemaphores := fun _ _ => true

end Obend.Tests.TpuSemanticsAndSystolicCrypto
