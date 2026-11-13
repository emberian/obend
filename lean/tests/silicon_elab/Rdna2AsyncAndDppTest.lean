module
public import Obend.Hardware.Gpu.Rdna2.AsyncRefinement
public import Obend.Hardware.Gpu.Rdna2.DppShuffle
public import Obend.Hardware.Gpu.Rdna2.Certified
-- The whole package import cone is opened privately for the axiom census.
import all Obend.Hardware.Gpu.Rdna2.Spec
import all Obend.Hardware.Gpu.Rdna2.Encodings
import all Obend.Hardware.Gpu.Rdna2.Insts.Scalar
import all Obend.Hardware.Gpu.Rdna2.Insts.Vector
import all Obend.Hardware.Gpu.Rdna2.Insts.Memory
import all Obend.Hardware.Gpu.Rdna2.Certified
import all Obend.Hardware.Gpu.Rdna2.Waitcnt
import all Init.Data.Array.QSort.Basic
import all Init.Data.String.Iterate
import all Init.Data.String.Legacy
import all Init.Data.String.Basic
import all Init.Data.String.TakeDrop
import all Init.Data.String.Slice
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String
import all Obend.Hardware.Gpu.Rdna2.Decode
import all Obend.Hardware.Gpu.Rdna2.Semantics
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
import all Obend.Hardware.Gpu.Rdna2.Host
import all Obend.Hardware.Gpu.Rdna2.Check
import all Obend.Hardware.Gpu.Rdna2.AsyncRefinement
import all Obend.Apps.ZkNtt.Goldilocks
import all Obend.Hardware.Gpu.Rdna2.DppShuffle

-- Certification adds this private cone to the existing package-wide axiom census.
import all Obend.Hardware.ArrayBuild
import all Obend.Hardware.ArrayKernel
import all Obend.Hardware.ArrayKernelOwnership
import all Obend.Hardware.ArrayKernelUnique
import all Obend.Hardware.ArrayTyping
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
import all Obend.Hardware.Gpu.BlockCore
import all Obend.Hardware.Gpu.BlockEmit
import all Obend.Hardware.Gpu.BlockLower
import all Obend.Hardware.Gpu.BlockPlan
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
import all Obend.Hardware.Gpu.GoldilocksSourceCorrect
import all Obend.Hardware.Gpu.LimbsGoldilocks
import all Obend.Hardware.Gpu.LimbsShift
import all Obend.Hardware.Gpu.Memory
import all Obend.Hardware.Gpu.NttKernel
import all Obend.Hardware.Gpu.NttSpec
import all Obend.Hardware.Gpu.PhaseSemantics
import all Obend.Hardware.Gpu.Rdna2.Block
import all Obend.Hardware.Gpu.Rdna2.Cert
import all Obend.Hardware.Gpu.Rdna2.CertSound
import all Obend.Hardware.Gpu.Rdna2.Equiv
import all Obend.Hardware.Gpu.Rdna2.Join
import all Obend.Hardware.Gpu.Rdna2.Lift
import all Obend.Hardware.Gpu.Rdna2.Lower
import all Obend.Hardware.Gpu.Rdna2.Natural
import all Obend.Hardware.Gpu.Rdna2.Residuals
import all Obend.Hardware.Gpu.Rdna2.Schedule
import all Obend.Hardware.Gpu.Rdna2.Sym
import all Obend.Hardware.Gpu.Rdna2.Term
import all Obend.Hardware.Gpu.SoacPrograms
import all Obend.Hardware.Gpu.Source
import all Obend.Hardware.Gpu.SourceElem
import all Obend.Hardware.Gpu.SourceOps
import all Obend.Hardware.Gpu.SourcePrograms
import all Obend.Hardware.Gpu.SourceProtocol
import all Obend.Hardware.Gpu.Workgroup
import all Obend.Hardware.RtlFold
import all Obend.Hardware.Square
import all Obend.Hardware.SquareGraphs

public section
namespace Obend.Tests.Rdna2AsyncAndDpp
open Obend.Hardware.Gpu.Rdna2
open Obend.Hardware.Gpu.Rdna2.Async
open Obend.Hardware.Gpu.Rdna2.Dpp
open Obend.Apps.ZkNtt
set_option autoImplicit false
set_option maxRecDepth 8192

/-! Real machine words, decoded through the generated AMD ISA tables. -/
def loadOlder : List UInt32 := [0xf4000200, 0xfa000000] -- s_load_dword s8, s[0:1], 0
def loadYounger : List UInt32 := [0xf4000240, 0xfa000004] -- s9, byte offset 4
def readOlder : List UInt32 := [0xbe8a0308] -- s_mov_b32 s10, s8
def vectorLoad : List UInt32 := [0xe0300000, 0x80040400] -- buffer_load_dword v4, ..., s[16:19]
def vectorRead : List UInt32 := [0x7e0a0304] -- v_mov_b32 v5, v4
def waitZero : List UInt32 := [0xbf8c0000]
def waitLgkmOne : List UInt32 := [0xbf8cc17f]
def finish : List UInt32 := [0xbf810000]

structure TestTurn where
  words : List UInt32
  completions : List Completion := []
  order : List Nat := []

def decodeTurns (ts : List TestTurn) : Except String (List Turn) :=
  ts.mapM fun t => match decodeInst t.words with
    | none => .error "fixture did not decode"
    | some (i, _) => .ok { before := t.completions, instruction := i, waitOrder := t.order }

def initial : WaveState :=
  let s : WaveState := GWave.init (({} : Memory).insert 0 7 |>.insert 1 11) 0 0
  writeSgpr (writeSgpr s 18 8) 19 0x30000000

def evaluate (ts : List TestTurn) : Except String (Except AsyncError AsyncWaveState) := do
  let turns ← decodeTurns ts
  return Async.run (AsyncWaveState.init initial) turns

def traps (ts : List TestTurn) (e : AsyncError) : Bool :=
  match evaluate ts with | .ok (.error actual) => actual == e | _ => false

/-- All architectural fields, not merely one observed output register. The test
programs only load, so memory insertion-order representation is unchanged. -/
def sameWave (a b : WaveState) : Bool :=
  a.sgpr == b.sgpr && a.vgpr == b.vgpr && a.exec == b.exec && a.scc == b.scc &&
  a.m0 == b.m0 && a.pc == b.pc && a.mem.toArray == b.mem.toArray &&
  a.halted == b.halted && a.err == b.err && a.ldsBase == b.ldsBase && a.ldsDwords == b.ldsDwords

def agrees (ts : List TestTurn) : Bool :=
  match decodeTurns ts with
  | .error _ => false
  | .ok turns =>
    match Async.run (AsyncWaveState.init initial) turns with
    | .error _ => false
    | .ok s => s.vmCnt == 0 && s.lgkmCnt == 0 && s.vsCnt == 0 && s.err.isNone &&
      sameWave s.toGWave (syncRun initial (turns.map (·.instruction)))

def guarded (order : List Nat) : List TestTurn :=
  [⟨loadOlder, [], []⟩, ⟨loadYounger, [], []⟩, ⟨vectorLoad, [], []⟩,
   ⟨waitZero, [], order⟩, ⟨readOlder, [], []⟩, ⟨vectorRead, [], []⟩, ⟨finish, [], []⟩]

#guard (decodeInst loadOlder).map (fun p => p.1.name) == some "S_LOAD_DWORD"
#guard (decodeInst loadYounger).map (fun p => p.1.field "SDATA") == some 9
#guard (decodeInst vectorLoad).map (fun p => p.1.name) == some "BUFFER_LOAD_DWORD"
#guard agrees (guarded [0, 0])
#guard agrees (guarded [1, 0])
#guard agrees [⟨loadOlder, [], []⟩, ⟨loadYounger, [], []⟩,
  ⟨vectorLoad, [.lgkm 0], []⟩, ⟨waitZero, [.vm, .lgkm 0], []⟩,
  ⟨readOlder, [], []⟩, ⟨vectorRead, [], []⟩, ⟨finish, [], []⟩]
#guard traps [⟨loadOlder, [], []⟩, ⟨readOlder, [], []⟩] .staleInFlightRead
#guard traps [⟨vectorLoad, [], []⟩, ⟨vectorRead, [], []⟩] .staleInFlightRead
#guard traps [⟨loadOlder, [], []⟩, ⟨loadYounger, [], []⟩,
  ⟨waitLgkmOne, [], [1]⟩, ⟨readOlder, [], []⟩] .staleInFlightRead
#guard traps [⟨loadOlder, [], []⟩, ⟨loadOlder, [], []⟩] .staleInFlightRead
#guard traps [⟨loadOlder, [], []⟩, ⟨waitZero, [], []⟩] .incompleteWait
#guard traps [⟨loadOlder, [], []⟩, ⟨waitZero, [], [1]⟩] .invalidRetirementIndex
#guard ((decodeProgram ((guarded [0, 0]).flatMap (·.words)).toArray).bind checkWaitcnt).toBool
#guard !((decodeProgram (loadOlder ++ loadYounger ++ waitLgkmOne ++ readOlder ++ waitZero ++ finish).toArray).bind checkWaitcnt).toBool

/-! Counterexample at arbitrary initial architectural state: after the younger
SMEM completion, the older destination remains pending even when LGKM_CNT = 1. -/
def olderWriteback (value : UInt32) : Writeback :=
  { destinations := [.s 8], sgprs := #[(8, value)] }
def youngerWriteback (value : UInt32) : Writeback :=
  { destinations := [.s 9], sgprs := #[(9, value)] }

theorem younger_first_leaves_older (s : WaveState) (a b : UInt32) :
    (complete { (AsyncWaveState.init s) with lgkmQueue := [olderWriteback a, youngerWriteback b] }
      (.lgkm 1)).map (fun t => (t.lgkmCnt, stale t { reads := [.s 8], writes := [] })) =
      .ok (1, true) := by rfl

/-! Masked, inactive, OOB, paired UInt64, butterfly and reduction vectors. -/
def laneNumbers : Lanes Nat := fun i => i.val + 1
def oldNumbers : Lanes Nat := fun _ => 999
def addMod (a b : Nat) : Nat := (a + b) % goldilocksPrime
def fieldValues : Lanes Nat := fun i => (goldilocksPrime - 1 + i.val) % goldilocksPrime

#guard sourceIndex (.quad_perm 1 0 3 2) 63 == some 62
#guard sourceIndex .row_mirror 16 == some 31
#guard sourceIndex .row_half_mirror 8 == some 15
#guard sourceIndex (.row_shl 1) 15 == none
#guard sourceIndex (.row_shr 1) 16 == none
#guard sourceIndex (.row_ror 1) 16 == some 31
#guard sourceIndex .row_bcast15 63 == some 47
#guard sourceIndex .row_bcast31 63 == some 31
#guard sourceIndex .wave_shr1 32 == some 31
#guard sourceIndex .wave_shl1 31 == some 32
#guard !rdna2Supported .row_bcast15 && !rdna2Supported .row_bcast31
#guard !rdna2Supported .wave_shl1 && !rdna2Supported .wave_shr1
#guard !rdna2Supported (.row_shl 0)
#guard shuffle 0 { fullCtrl .row_mirror with row_mask := 1 } allExec laneNumbers oldNumbers 16 == 999
#guard shuffle 0 { fullCtrl .row_mirror with bank_mask := 1 } allExec laneNumbers oldNumbers 4 == 999
#guard shuffle 0 { fullCtrl .row_mirror with bank_mask := 1 } allExec laneNumbers oldNumbers 0 == 16
#guard shuffle 0 (fullCtrl (.row_shr 1)) allExec laneNumbers oldNumbers 16 == 0
#guard shuffle 0 { op := .row_shr 1 } allExec laneNumbers oldNumbers 16 == 999
#guard shuffle 0 (fullCtrl (.quad_perm 1 0 3 2)) 1 laneNumbers oldNumbers 0 == 0
#guard shuffle 0 { op := .quad_perm 1 0 3 2 } 1 laneNumbers oldNumbers 0 == 999
#guard shuffle 0 { fullCtrl (.quad_perm 1 0 3 2) with fetch_inactive := true } 1 laneNumbers oldNumbers 0 == 2
#guard shuffle 0 (fullCtrl .row_mirror) 1 laneNumbers oldNumbers 1 == 999
#guard (List.finRange 4).all fun s => (List.finRange 64).all fun i =>
  dppRowButterfly s fieldValues (fun _ => 1) i == rowButterflySpec s fieldValues (fun _ => 1) i
#guard dppWave64ReduceAdd Nat.add 0 laneNumbers 63 == 2080
#guard rdna2Wave64ReduceAdd Nat.add 0 laneNumbers 63 == 2080
#guard dppWave64ReduceAdd addMod 0 fieldValues 63 == sumLanes addMod 0 fieldValues
#guard rdna2Wave64ReduceAdd addMod 0 fieldValues 63 == sumLanes addMod 0 fieldValues
#guard (List.finRange 64).all fun i =>
  dppShuffleU64 (fullCtrl .row_mirror) allExec
    (fun j => UInt64.ofNat (j.val * 4294967296 + 17)) (fun _ => 0) i ==
  shuffle 0 (fullCtrl .row_mirror) allExec
    (fun j => UInt64.ofNat (j.val * 4294967296 + 17)) (fun _ => 0) i

-- A terminal S_WAITCNT 0 does not drain vector stores: VM_CNT is not VS_CNT.
def storeWords : List UInt32 := [0xe0700000, 0x80040400]
#guard (decodeInst storeWords).map (fun p => p.1.name) == some "BUFFER_STORE_DWORD"
#guard ((decodeProgram (storeWords ++ waitZero ++ finish).toArray).bind checkWaitcnt).toBool
#guard match evaluate [⟨storeWords, [], []⟩, ⟨waitZero, [], []⟩] with
  | .ok (.ok s) => s.vmCnt == 0 && s.lgkmCnt == 0 && s.vsCnt == 1 && s.mem.get? 0 == some 7
  | _ => false
#guard !agrees [⟨storeWords, [], []⟩, ⟨waitZero, [], []⟩]
#guard (List.finRange 6).all fun st => (List.finRange 64).all fun i =>
  waveButterfly st fieldValues (fun _ => 1) i == waveButterflySpec st fieldValues (fun _ => 1) i

#guard agrees [⟨storeWords, [], []⟩, ⟨[0xbbfd0000], [], []⟩, ⟨finish, [], []⟩]
#guard agrees [⟨storeWords, [], []⟩, ⟨waitZero, [.vs], []⟩, ⟨finish, [], []⟩]

#guard addStep Nat.mul 0 { op := .row_shr 1 } (fun _ => 2) 0 == 2
#guard addStep Nat.mul 0 (fullCtrl (.row_shr 1)) (fun _ => 2) 0 == 0

#guard (shuffleRdna2Exec (fullCtrl .row_mirror) allExec
  (_root_.Vector.replicate 64 1) (_root_.Vector.replicate 64 0)).toBool
#guard !(shuffleRdna2Exec (fullCtrl .row_bcast15) allExec
  (_root_.Vector.replicate 64 1) (_root_.Vector.replicate 64 0)).toBool
#guard counterSafe Pending.empty { reads := [.s 8, .v 4], writes := [.s 10] }
#guard !counterSafe { vm := [[.v 4]], lgkm := [], smem := false }
  { reads := [.v 4], writes := [] }

/-- Run the executable block tracker on genuinely decoded machine words. -/
def acceptedBlock (ts : List TestTurn) : Bool :=
  match decodeTurns ts with
  | .ok ts => checkAsyncBlock (ts.map (·.instruction))
  | .error _ => false

#guard acceptedBlock (guarded [1, 0])
#guard !acceptedBlock [⟨loadOlder, [], []⟩, ⟨readOlder, [], []⟩]
#guard !acceptedBlock [⟨loadOlder, [], []⟩, ⟨loadYounger, [], []⟩,
  ⟨waitLgkmOne, [], [1]⟩, ⟨readOlder, [], []⟩, ⟨waitZero, [], [0]⟩]
#guard !acceptedBlock [⟨storeWords, [], []⟩, ⟨waitZero, [], []⟩]
#guard acceptedBlock [⟨storeWords, [], []⟩, ⟨[0xbbfd0000], [], []⟩]
#guard !acceptedBlock [⟨storeWords, [], []⟩, ⟨vectorLoad, [], []⟩,
  ⟨waitZero, [], []⟩, ⟨[0xbbfd0000], [], []⟩]
#guard checkAsyncBlock ReadWaitUse.block
#guard (decodeInst loadOlder).map (fun p => (p.1.access.reads, p.1.access.writes)) ==
  some (ReadWaitUse.load.access.reads, ReadWaitUse.load.access.writes)
#guard (decodeInst readOlder).map (fun p => (p.1.access.reads, p.1.access.writes)) ==
  some (ReadWaitUse.move.access.reads, ReadWaitUse.move.access.writes)
#guard match Async.run (AsyncWaveState.init ReadWaitUse.initial) ReadWaitUse.turns with
  | .ok s => readSgpr s.toGWave 10 == 7 && s.lgkmCnt == 0
  | .error _ => false

example (ts : List Turn) (s : AsyncWaveState)
    (hi : ts.map (·.instruction) = ReadWaitUse.block)
    (hr : Async.run (AsyncWaveState.init ReadWaitUse.initial) ts = .ok s) :
    s.vmQueue = [] ∧ s.lgkmQueue = [] ∧ s.vsQueue = [] ∧
      s.toGWave = syncRun ReadWaitUse.initial ReadWaitUse.block :=
  ReadWaitUse.load_wait_use_refines ts s hi hr

/-! Mutation sensitivity of universal contracts in BOTH modules. -/
#tooth waitcnt_safe_async_refines_sync by mutation checkAsyncBlock := fun _ => true
#tooth counterSafe_all_schedules by mutation counterSafe := fun _ _ => true
#tooth fifoWait_after_early by mutation fifoWait := fun _ q => q
#tooth younger_first_leaves_older by mutation stale := fun _ _ => false
#tooth rowPartner_eq_xor by mutation sourceIndex := fun _ i => some i.val
#tooth dppShuffleU64_eq_spec by mutation dppShuffleU64 := fun _ _ src _ => src
#tooth dppWave64ReduceAdd_eq_sum by mutation dppWave64ReduceAdd := fun _ _ x => x
#tooth invalid_source_behavior by mutation shuffle := fun _ _ _ _ old => old

/-- Real decoding exercises branches, loops, both store classes, and SGPR wait masks. -/
def storeCompletion (strict : Bool) (ws : List UInt32) : Bool :=
  ((decodeProgram ws.toArray).bind (checkVscntProg strict)).toBool

def globalStore : List UInt32 := [0xdc708000, 0x007f0200]
def bufferStore : List UInt32 := [0xe0700000, 0x80040400]

#guard (decodeInst globalStore).map (fun p => p.1.name) == some "GLOBAL_STORE_DWORD"
#guard (decodeInst globalStore).map (fun p => p.1.enc.name) == some "ENC_FLAT_GLBL"
#guard match decodeInst globalStore with
  | some (i, _) => i.access.reads.contains (.v 2) &&
      !(stepPending { vm := [[.v 2]], lgkm := [], smem := false } i).toBool
  | none => false
#guard (decodeInst bufferStore).map (fun p => p.1.name) == some "BUFFER_STORE_DWORD"
#guard storeCompletion false (bufferStore ++ finish)
#guard !storeCompletion true (bufferStore ++ finish)
#guard !storeCompletion false (bufferStore ++ [0xbf8a0000] ++ finish) -- barrier
#guard storeCompletion true (bufferStore ++ [0xbbfd0000, 0xbf8a0000] ++ finish)
#guard !storeCompletion false (globalStore ++ finish)
#guard storeCompletion true (globalStore ++ [0xbbfd0000] ++ finish)
#guard !storeCompletion true (globalStore ++ [0xbb800000] ++ finish) -- non-null SDST refused
#guard !storeCompletion true (globalStore ++ [0xbbfd0040] ++ finish) -- reserved SIMM16 refused
#guard !storeCompletion true (globalStore ++ [0xbb800001] ++ finish)
#guard !storeCompletion true (globalStore ++ [0xbbfd0001] ++ finish)
#guard !acceptedBlock [⟨storeWords, [], []⟩, ⟨[0xbb800000], [], []⟩]
#guard !acceptedBlock [⟨storeWords, [], []⟩, ⟨[0xbbfd0040], [], []⟩]
-- These opcodes must decode before the standalone completion gate refuses them.
def decodedRefusal (name : String) (ws : List UInt32) : Bool :=
  match decodeInst ws with
  | none => false
  | some (i, _) => i.name == name && !(stepVscnt true {} i).toBool

#guard decodedRefusal "GLOBAL_ATOMIC_ADD" [0xdcc88000, 0x007f0200]
#guard decodedRefusal "IMAGE_STORE" [0xf0200100, 0x00000000]
#guard decodedRefusal "TBUFFER_STORE_FORMAT_X" [0xe8040000, 0x80000000]
#guard decodedRefusal "SCRATCH_STORE_DWORD" [0xdc704000, 0x007f0200]
#guard decodedRefusal "S_SETPC_B64" [0xbe802000]
#guard decodedRefusal "S_SWAPPC_B64" [0xbe802100]
#guard decodedRefusal "S_RFE_B64" [0xbe802200]
#guard decodedRefusal "S_CALL_B64" [0xbb000000]
#guard decodedRefusal "S_TRAP" [0xbf920000]
#guard decodedRefusal "S_CODE_END" [0xbf9f0000]

#tooth stepVscnt_boundary_zero by mutation stepVscnt := fun _ p _ => .ok p
#tooth canIssue_boundary_store_empty by mutation canIssue := fun _ _ => true

-- Conditional edge skips the wait; the other path drains, but the join must refuse.
#guard !storeCompletion true (globalStore ++ [0xbf840001, 0xbbfd0000] ++ finish)
-- A clean predecessor reaches the exit first; the dirty predecessor must requeue it.
#guard !storeCompletion true ([0xbf840003] ++ globalStore ++ [0xbf820001, 0xbbfd0000] ++ finish)
#guard !storeCompletion false ([0xdc700000, 0x007f0200] ++ finish) -- flat_store_dword
#guard storeCompletion true ([0xdc700000, 0x007f0200, 0xbbfd0000] ++ finish)
-- Backedge accumulates pending stores; exit is checked after joining the loop state.
#guard !storeCompletion true (globalStore ++ [0xbf84fffd] ++ finish)
#guard storeCompletion true (globalStore ++ [0xbbfd0000, 0xbf84fffc] ++ finish)

attribute [local cbv_opaque] instIndex
attribute [local cbv_eval] instIndex_getD

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
set_option cbv.maxSteps 10000000 in
theorem awaitedGlobalStoreDump_vscnt_ok :
    checkVscntDump awaitedGlobalStoreDump = true ∧
    checkVscntBlockDump awaitedGlobalStoreDump = true := by cbv

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
set_option cbv.maxSteps 10000000 in
theorem unawaitedGlobalStoreDump_refused :
    checkVscntDump unawaitedGlobalStoreDump = false ∧
    checkVscntBlockDump unawaitedGlobalStoreDump = false ∧
    ∀ g, certifyDump g unawaitedGlobalStoreDump = false := by
  have hd : checkVscntDump unawaitedGlobalStoreDump = false := by cbv
  have hb : checkVscntBlockDump unawaitedGlobalStoreDump = false := by cbv
  refine ⟨hd, hb, ?_⟩
  intro g
  simp only [certifyDump, hd, Bool.and_false, Bool.false_and]


#guard checkWaitcntDump awaitedGlobalStoreDump
#guard checkWaitcntDump unawaitedGlobalStoreDump

#tooth instIndex_getD by mutation instructionEntries := fun _ => []
theorem unawaitedGlobalStoreDump_certify_refused (g : Obend.Hardware.ArrayHypergraph.ArrayGraph) :
    certifyDump g unawaitedGlobalStoreDump = false :=
  unawaitedGlobalStoreDump_refused.2.2 g

theorem unawaitedGlobalStoreDump_certifyBlock_refused
    (p : Obend.Hardware.ArrayKernel.Program) :
    certifyBlockDump p unawaitedGlobalStoreDump = false := by
  simp only [certifyBlockDump, unawaitedGlobalStoreDump_refused.2.1,
    Bool.and_false, Bool.false_and]

#tooth certifyBlockDump_vscnt by mutation certifyBlockDump := fun _ _ => true
#tooth certifyDump_vscnt by mutation certifyDump := fun _ _ => true
#print axioms CounterTrace.bounded
#print axioms CounterTrace.vscnt_boundary_store_empty
#print axioms canIssue_boundary_store_empty
#print axioms awaitedGlobalStoreDump_vscnt_ok
#print axioms unawaitedGlobalStoreDump_refused

#assert_axioms_tree
end Obend.Tests.Rdna2AsyncAndDpp
