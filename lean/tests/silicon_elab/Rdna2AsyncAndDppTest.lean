module
public import Obend.Hardware.Gpu.Rdna2.AsyncRefinement
public import Obend.Hardware.Gpu.Rdna2.DppShuffle
-- The whole package import cone is opened privately for the axiom census.
import all Obend.Hardware.Gpu.Rdna2.Spec
import all Obend.Hardware.Gpu.Rdna2.Encodings
import all Obend.Hardware.Gpu.Rdna2.Insts.C0
import all Obend.Hardware.Gpu.Rdna2.Insts.C1
import all Obend.Hardware.Gpu.Rdna2.Insts.C2
import all Obend.Hardware.Gpu.Rdna2.Insts.C3
import all Obend.Hardware.Gpu.Rdna2.Insts.C4
import all Obend.Hardware.Gpu.Rdna2.Insts.C5
import all Obend.Hardware.Gpu.Rdna2.Insts.C6
import all Obend.Hardware.Gpu.Rdna2.Insts.C7
import all Obend.Hardware.Gpu.Rdna2.Insts.C8
import all Obend.Hardware.Gpu.Rdna2.Insts.C9
import all Obend.Hardware.Gpu.Rdna2.Insts.C10
import all Obend.Hardware.Gpu.Rdna2.Insts.C11
import all Obend.Hardware.Gpu.Rdna2.Insts.C12
import all Obend.Hardware.Gpu.Rdna2.Insts
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
import all Obend.Hardware.Gpu.Rdna2.Waitcnt
import all Obend.Hardware.Gpu.Rdna2.AsyncRefinement
import all Obend.Apps.ZkNtt.Goldilocks
import all Obend.Hardware.Gpu.Rdna2.DppShuffle

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

#assert_axioms_tree
end Obend.Tests.Rdna2AsyncAndDpp
