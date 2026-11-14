module
/-
# PipelinedZkAndBinaryTowerTest — End-to-End Silicon & Algebra Verification

Exercises `Obend.Hardware.PipelinedZkCrypto` across all required gates:
1. **16-Cycle Back-to-Back Streaming Goldilocks Butterfly Trace (`#guard`s)**:
   16 pairwise-distinct `(u_t, v_t, w_t)` triples clocked at 1 butterfly/cycle from dirty initial
   registers, plus 4 drain cycles (`in_valid = 0`), checked cycle-for-cycle against `(u_t + v_t * w_t) % p`
   and `(u_t % p + p - (v_t * w_t) % p) % p`.
2. **Wiedemann Binary-Tower `GF(2^{64})` & `GF(2^{128})` Field Algebra & Hardware `#guard`s**:
   Multiplicative inverses `towerInv 6` / `towerInv 7` / `tower128Inv`, defining polynomial
   `X_k^2 + omega_{k-1} * X_k + 1 = 0`, and bit-exact combinational + 2-stage pipelined agreement of
   `gf2_64TowerMulRtlModule` with `towerMul 6`.
3. **Yosys/Z3 SMT-LIB2 Miter Soundness & Live Solver Gate**:
   Formal `lecScript_unsat_of_step` instantiations, emitted SV/SMT2 structural `#guard`s, and a
   host-aware `yosys` + `z3` miter check when tools are present on the host.
4. **Mutation Kills (`#tooth` x 7) & Imported-Tree Axiom Audit (`#assert_axioms_tree`)**.
-/
public import Obend.Hardware.PipelinedZkCrypto
public import Obend.Hardware.YosysLec
public import Obend.Tactic.Tooth
public import Obend.AssertAxioms

meta import all Obend.Hardware.PipelinedZkCrypto
meta import all Obend.Hardware.Retiming
meta import all Obend.Hardware.YosysLec

-- Full bodies across the transitive Obend import cone for `#tooth` and `#assert_axioms_tree`.
import all Obend.Analysis.Diff
import all Obend.Analysis.Equitable
import all Obend.Analysis.Flowpipe
import all Obend.Analysis.Groebner
import all Obend.Analysis.RealAnalysis
import all Obend.Analysis.SosLyapunov
import all Obend.Analysis.TaylorModel
import all Obend.Apps.ZkNtt.Goldilocks
import all Obend.AssertAxioms
import all Obend.Core.AliasExposure
import all Obend.Core.Assumptions
import all Obend.Core.Bidirectional
import all Obend.Core.Brand
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
import all Obend.Hardware.AgenticEDA
import all Obend.Hardware.Analog
import all Obend.Hardware.Circuits
import all Obend.Hardware.Codec
import all Obend.Hardware.Compiler
import all Obend.Hardware.DRC
import all Obend.Hardware.DSP
import all Obend.Hardware.Datasheet
import all Obend.Hardware.HDL
import all Obend.Hardware.Judge
import all Obend.Hardware.Magnetics
import all Obend.Hardware.PCB
import all Obend.Hardware.Photonics
import all Obend.Hardware.PipelinedZkCrypto
import all Obend.Hardware.PlaceRoute
import all Obend.Hardware.Process
import all Obend.Hardware.ReductionMachine
import all Obend.Hardware.Retiming
import all Obend.Hardware.Synth
import all Obend.Hardware.ThermalPassivity
import all Obend.Hardware.Types
import all Obend.Hardware.VerilateRunner
import all Obend.Hardware.YosysLec
import all Obend.Intention
import all Obend.Judge.Class
import all Obend.Judge.Clearing
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
import all Obend.Leaf.Emit
import all Obend.Leaf.Flatten
import all Obend.Leaf.Specialize
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
import all Obend.Lower.Fragment
import all Obend.Lower.Inductive
import all Obend.Lower.Judge
import all Obend.Lower.LCNF
import all Obend.Lower.Proofs.Book
import all Obend.Lower.Proofs.Complete
import all Obend.Lower.Proofs.Hardware
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
import all Obend.Tactic.Tooth
import all Obend.Vault.Law
import all Obend.Vault.Page
import all Obend.Analysis.SimplicialFeecFem
import all Obend.Core.Collect
import all Obend.Core.Proofs.Collect.Compact
import all Obend.Core.Proofs.Collect.Extract
import all Obend.Core.Proofs.Collect.Lockstep
import all Obend.Core.Proofs.Collect.Mark
import all Obend.Core.Proofs.Collect.Rename
import all Obend.Core.Proofs.Collect.Runs
import all Obend.Core.Proofs.Collect.Segment
import all Obend.Core.Proofs.Collect.Statements
import all Obend.Core.Proofs.Collect.Typing
import all Obend.Core.Proofs.Force
import all Obend.Core.Proofs.Preservation
import all Obend.Core.Proofs.Preservation.Base.Focus
import all Obend.Core.Proofs.Preservation.Cases.Activities
import all Obend.Core.Proofs.Preservation.Cases.Arithmetic
import all Obend.Core.Proofs.Preservation.Cases.Functions
import all Obend.Core.Proofs.Preservation.Cases.Pairs
import all Obend.Core.Proofs.Preservation.Cases.Records
import all Obend.Core.Proofs.Preservation.Cases.Split
import all Obend.Core.Proofs.Preservation.Cases.Sums
import all Obend.Core.RangeSafe
import all Obend.Hardware.Accelerators
import all Obend.Hardware.GeometryCAM
import all Obend.Leaf.BytecodeRegisterJit
import all Obend.Leaf.Served
import all Obend.Leaf.Static
import all Obend.Consensus.Simplex
import all Obend.Consensus.SimplexProtocol
import all Obend.Crypto.Multilinear
import all Obend.Crypto.Transcript
import all Obend.Judge.Computational
import all Obend.Logic.SeparationFrame
import all Obend.Polis.CapTP
import all Obend.Vault.Mandate

public section
namespace Obend.Tests.PipelinedZkAndBinaryTowerTest

open Obend.Apps.ZkNtt
open Obend.Hardware.HDL
open Obend.Hardware.Process
open Obend.Hardware.Retiming
open Obend.Hardware.VerilateRunner
open Obend.Hardware.YosysLec
open Obend.Hardware.PipelinedZkCrypto

set_option autoImplicit false

/-! ## 1. 16-Cycle Back-to-Back Streaming Goldilocks Butterfly Trace (`#guard`s) -/

/-- 16 pairwise-distinct `(u_t, v_t, w_t)` Goldilocks butterfly triples exercising boundary cases:
    `p - 1`, `p` (non-canonical 64-bit word `>= p`), `2^64 - 1`, `2^32`, carry-heavy limb products,
    underflow subtraction (`u < v * w mod p`), and arbitrary pseudorandom 64-bit words. -/
def glStream16 : List (BitVec 64 × BitVec 64 × BitVec 64) :=
  [ (0#64,                  1#64,                  1#64)
  , (1#64,                  0xFFFFFFFF00000000#64, 0xFFFFFFFF00000000#64)
  , (0xFFFFFFFF00000000#64, 0x0000000100000000#64, 0x0000000100000000#64)
  , (0xFFFFFFFF00000001#64, 0x123456789ABCDEF0#64, 0xFEDCBA9876543210#64)
  , (0xFFFFFFFFFFFFFFFF#64, 0xFFFFFFFFFFFFFFFF#64, 0xFFFFFFFFFFFFFFFF#64)
  , (0x00000000FFFFFFFF#64, 0xFFFFFFFF00000000#64, 0x00000000FFFFFFFF#64)
  , (0x8000000000000000#64, 0x8000000000000000#64, 0x0000000000000002#64)
  , (0x0123456789ABCDEF#64, 0x1111111122222222#64, 0x3333333344444444#64)
  , (0xCAFEBABEDEADBEEF#64, 0x0F0E0D0C0B0A0908#64, 0x8070605040302010#64)
  , (0x000000000000002A#64, 0xFFFFFFFF00000000#64, 0x0000000000000007#64)
  , (0x7FFFFFFF80000001#64, 0x7FFFFFFF80000002#64, 0x7FFFFFFF80000003#64)
  , (0xFFFFFFFF00000005#64, 0xFFFFFFFF00000009#64, 0xFFFFFFFF0000000B#64)
  , (0xAAAAAAAAAAAAAAAA#64, 0x5555555555555555#64, 0xC3C3C3C3C3C3C3C3#64)
  , (0x0000000200000003#64, 0xFFFFFFFE00000004#64, 0xFFFFFFFD00000005#64)
  , (0x9999999988888888#64, 0x7777777766666666#64, 0x5555555544444444#64)
  , (0xDEADC0DECAFE1234#64, 0xfeedface13579bdf#64, 0x2468ace0fdb97531#64) ]

#guard glStream16.length == 16
#guard glStream16.Nodup

/-- Dirty non-zero initial register bank proving Stage-4 outputs at `t + 4` are immune to stale pipeline state. -/
def dirtyInitRegs : Nat → BitVec 64
  | k => BitVec.ofNat 64 (0xBAD0000000000000 + 0x1337 * (k + 1))

/-- 16 active cycles (`in_valid = 1`) followed by 4 drain bubbles (`in_valid = 0`) with adversarial garbage data. -/
def glStream20Inputs : List (Nat → BitVec 64) :=
  (glStream16.map fun (u, v, w) => glButterflyInputs u v w 1#64) ++
  [ glButterflyInputs 0xDEAD#64 0xBEEF#64 0xCAFE#64 0#64
  , glButterflyInputs 0x1111#64 0x2222#64 0x3333#64 0#64
  , glButterflyInputs 0x4444#64 0x5555#64 0x6666#64 0#64
  , glButterflyInputs 0x7777#64 0x8888#64 0x9999#64 0#64 ]

def verifyButterflyCycle (t : Nat) : Bool :=
  match glStream16[t]? with
  | none => false
  | some (u, v, w) =>
    let trace := (glStream20Inputs.take (t + 4)).map (false, ·)
    let st    := runModuleTrace pipelinedGlButterflyRtlModule dirtyInitRegs trace
    let outs  := evalModuleOutputs pipelinedGlButterflyRtlModule (fun _ => 0xFFFF#64) st
    let expE  := BitVec.ofNat 64 ((u.toNat + v.toNat * w.toNat) % goldilocksPrime)
    let expO  := BitVec.ofNat 64
      ((u.toNat % goldilocksPrime + goldilocksPrime - (v.toNat * w.toNat) % goldilocksPrime) % goldilocksPrime)
    outs.lookup "out_even" == some expE &&
    outs.lookup "out_odd"  == some expO &&
    outs.lookup "out_valid" == some 1#64 &&
    decide ((st 13).toNat < goldilocksPrime) &&
    decide ((st 14).toNat < goldilocksPrime)

-- All 16 back-to-back streaming butterfly outputs match exact canonical Goldilocks arithmetic at t + 4:
#guard (List.range 16).all verifyButterflyCycle

-- Cycle 20 (t = 16 + 4) deasserts `out_valid = 0` when the first drain bubble exits Stage 4:
#guard
  let trace20 := (glStream20Inputs.take 20).map (false, ·)
  let st20    := runModuleTrace pipelinedGlButterflyRtlModule dirtyInitRegs trace20
  (evalModuleOutputs pipelinedGlButterflyRtlModule (fun _ => 0#64) st20).lookup "out_valid" == some 0#64

-- Structural RTL & Leiserson-Saxe retiming checks:
#guard checkRtlModuleW pipelinedGlButterflyRtlModule == true
#guard checkRetimingCert glButterflySyncGraph glButterflyUnpipelinedCert corner7nm_SS 3000 == false
#guard checkRetimingCert glButterflySyncGraph glButterfly4StageCert corner7nm_SS 3000 == true

/-! ## 2. Wiedemann Binary-Tower `GF(2^{64})` & `GF(2^{128})` Algebra & Hardware `#guard`s -/

def tower64Samples : List Tower64 :=
  [ 0x0000000000000001#64
  , 0x0000000000000002#64
  , 0x0123456789ABCDEF#64
  , 0xFEDCBA9876543210#64
  , 0xFFFFFFFFFFFFFFFF#64
  , 0x8000000000000001#64
  , 0xDEADBEEFCAFEBABE#64
  , 0x5A5A5A5AA5A5A5A5#64 ]

def tower128Samples : List Tower128 :=
  [ (0x0000000000000001#64, 0x0000000000000000#64)
  , (0x0000000000000000#64, 0x0000000000000001#64)
  , (0x0123456789ABCDEF#64, 0xFEDCBA9876543210#64)
  , (0xFFFFFFFFFFFFFFFF#64, 0xFFFFFFFFFFFFFFFF#64)
  , (0xCAFEBABEDEADBEEF#64, 0x13579BDF2468ACE0#64)
  , (0x8000000000000000#64, 0x0000000000000003#64) ]

-- Defining polynomial X_k^2 + omega_{k-1} * X_k + 1 = 0 across tower levels k = 0..6 (up to GF(2^128)):
#guard (List.range 7).all fun k =>
  let xk := towerOmega (k + 1)
  let om := towerJoin (towerOmega k) (towerZero k)
  towerAdd (k + 1) (towerAdd (k + 1) (towerMul (k + 1) xk xk) (towerMul (k + 1) om xk))
    (towerOne (k + 1)) == towerZero (k + 1)

-- GF(2^64) multiplicative inverses: a * a^{-1} = 1 and a^{-1} * a = 1 for every nonzero sample:
#guard tower64Samples.all fun a =>
  a != towerZero 6 &&
  towerMul 6 a (towerInv 6 a) == towerOne 6 &&
  towerMul 6 (towerInv 6 a) a == towerOne 6

-- GF(2^128) multiplicative inverses via both `towerInv 7` (`BitVec 128`) and `tower128Inv` (`BitVec 64 × BitVec 64`):
#guard tower128Samples.all fun a =>
  let a128 := towerJoin (k := 6) a.1 a.2
  a128 != towerZero 7 &&
  towerMul 7 a128 (towerInv 7 a128) == towerOne 7 &&
  tower128Mul a (tower128Inv a) == (1#64, 0#64) &&
  tower128Mul (tower128Inv a) a == (1#64, 0#64)

-- GF(2^128) associativity & distributivity spot check on nontrivial 128-bit elements:
#guard
  let x := towerJoin (k := 6) 0x0123456789ABCDEF#64 0xFEDCBA9876543210#64
  let y := towerJoin (k := 6) 0xCAFEBABEDEADBEEF#64 0x13579BDF2468ACE0#64
  let z := towerJoin (k := 6) 0xAAAAAAAAAAAAAAAA#64 0x5555555555555555#64
  towerMul 7 (towerMul 7 x y) z == towerMul 7 x (towerMul 7 y z) &&
  towerMul 7 x (towerAdd 7 y z) == towerAdd 7 (towerMul 7 x y) (towerMul 7 x z)

-- `gf2_64TowerMulRtlModule` well-formedness, zero-carry gate, combinational bit-exactness & 2-stage pipeline stream:
#guard checkRtlModuleW gf2_64TowerMulRtlModule == true
#guard checkModuleCarryFree gf2_64TowerMulRtlModule == true

#guard tower64Samples.all fun a =>
  tower64Samples.all fun b =>
    (evalModuleOutputs gf2_64TowerMulRtlModule (gf2_64Inputs a b 1#64) dirtyInitRegs).lookup
      "tower64_mul_out" == some (towerMul 6 a b)

#guard
  let pairs := tower64Samples.zip tower64Samples.reverse
  let insStream := pairs.map (fun (a, b) => gf2_64Inputs a b 1#64) ++
    [gf2_64Inputs 0#64 0#64 0#64, gf2_64Inputs 0#64 0#64 0#64]
  (List.range pairs.length).all fun t =>
    match pairs[t]? with
    | none => false
    | some (a, b) =>
      let st := runModuleTrace gf2_64TowerMulRtlModule dirtyInitRegs ((insStream.take (t + 2)).map (false, ·))
      let outs := evalModuleOutputs gf2_64TowerMulRtlModule (fun _ => 0#64) st
      outs.lookup "tower64_pipe_out" == some (towerMul 6 a b) &&
      outs.lookup "tower64_pipe_valid" == some 1#64

/-! ## 3. Formal Yosys/Z3 SMT-LIB2 Miter Theorems, Glue `#guard`s & Host-Aware Solver Check -/

theorem pipelinedGlButterfly_faithful : moduleFaithful pipelinedGlButterflyRtlModule :=
  moduleFaithful_of_checkWidths pipelinedGlButterflyRtlModule (by decide +kernel)

theorem gf2_64TowerMul_faithful : moduleFaithful gf2_64TowerMulRtlModule :=
  moduleFaithful_of_checkWidths gf2_64TowerMulRtlModule (by decide +kernel)

theorem pipelinedGlButterfly_lec_unsat
    (hagree : ∀ Y : LecAssign, Y.h = true → Y.t = true →
      pipelinedGlButterflyRtlModule.outputs.map (fun o =>
          (o.name,
            ((yosysBV pipelinedGlButterflyRtlModule.name o.name false o.width).eval
              ((lecScript pipelinedGlButterflyRtlModule).env Y)).setWidth 64)) =
        evalModuleOutputsW pipelinedGlButterflyRtlModule
          ((lecScript pipelinedGlButterflyRtlModule).inpVal Y)
          ((lecScript pipelinedGlButterflyRtlModule).regVal Y) ∧
      ∀ r ∈ pipelinedGlButterflyRtlModule.regs,
        (yosysBV pipelinedGlButterflyRtlModule.name r.name true r.width).eval
            ((lecScript pipelinedGlButterflyRtlModule).env Y) =
          (stepModuleRegs pipelinedGlButterflyRtlModule (Y.bit false "rst")
            ((lecScript pipelinedGlButterflyRtlModule).inpVal Y)
            ((lecScript pipelinedGlButterflyRtlModule).regVal Y) r.regIdx).setWidth r.width) :
    ∀ Y, ¬ (lecScript pipelinedGlButterflyRtlModule).holds Y :=
  lecScript_unsat_of_step pipelinedGlButterflyRtlModule
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) hagree

theorem gf2_64TowerMul_lec_unsat
    (hagree : ∀ Y : LecAssign, Y.h = true → Y.t = true →
      gf2_64TowerMulRtlModule.outputs.map (fun o =>
          (o.name,
            ((yosysBV gf2_64TowerMulRtlModule.name o.name false o.width).eval
              ((lecScript gf2_64TowerMulRtlModule).env Y)).setWidth 64)) =
        evalModuleOutputsW gf2_64TowerMulRtlModule
          ((lecScript gf2_64TowerMulRtlModule).inpVal Y)
          ((lecScript gf2_64TowerMulRtlModule).regVal Y) ∧
      ∀ r ∈ gf2_64TowerMulRtlModule.regs,
        (yosysBV gf2_64TowerMulRtlModule.name r.name true r.width).eval
            ((lecScript gf2_64TowerMulRtlModule).env Y) =
          (stepModuleRegs gf2_64TowerMulRtlModule (Y.bit false "rst")
            ((lecScript gf2_64TowerMulRtlModule).inpVal Y)
            ((lecScript gf2_64TowerMulRtlModule).regVal Y) r.regIdx).setWidth r.width) :
    ∀ Y, ¬ (lecScript gf2_64TowerMulRtlModule).holds Y :=
  lecScript_unsat_of_step gf2_64TowerMulRtlModule
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) hagree

def glButterflyLecLines : List String := (lecScript pipelinedGlButterflyRtlModule).print.splitOn "\n"
def gf2_64TowerLecLines : List String := (lecScript gf2_64TowerMulRtlModule).print.splitOn "\n"
def glButterflySvLines  : List String := (emitModuleSV pipelinedGlButterflyRtlModule).splitOn "\n"
def gf2_64TowerSvLines  : List String := (emitModuleSV gf2_64TowerMulRtlModule).splitOn "\n"

#guard glButterflySvLines.any (·.startsWith "module pipelined_gl_butterfly_4stage")
#guard gf2_64TowerSvLines.any (·.startsWith "module gf2_64_wiedemann_tower_mul")
#guard glButterflyLecLines.contains "(assert (|pipelined_gl_butterfly_4stage_t| s s1))"
#guard glButterflyLecLines.contains "(define-fun |rtl_out_out_even| () (_ BitVec 64) (|pipelined_gl_butterfly_4stage_n out_even| s))"
#guard glButterflyLecLines.contains "(define-fun |rtl_next_s4_out_even| () (_ BitVec 64) (|pipelined_gl_butterfly_4stage_n s4_out_even| s1))"
#guard gf2_64TowerLecLines.contains "(assert (|gf2_64_wiedemann_tower_mul_t| s s1))"
#guard gf2_64TowerLecLines.contains "(define-fun |rtl_out_tower64_mul_out| () (_ BitVec 64) (|gf2_64_wiedemann_tower_mul_n tower64_mul_out| s))"
#guard gf2_64TowerLecLines.contains "(assert (not (and true |lec_out_tower64_mul_out| |lec_out_tower64_pipe_out| |lec_out_tower64_pipe_valid| |lec_next_s1_p32| |lec_next_s1_q32| |lec_next_s1_valid| |lec_next_s2_pipe_out| |lec_next_s2_pipe_valid|)))"

/-- When `yosys`, `z3`, and `hardware/lec/smt_share.py` are available on the build/LEC host, run live
    Yosys SystemVerilog synthesis + Z3 SMT-LIB2 miter verification on `gf2_64TowerMulRtlModule` and
    assert `unsat` (and `sat` on a 1-bit mutated SV netlist). -/
def verifyLiveYosysZ3IfPresent : IO Unit := do
  let hasYosys ← (System.FilePath.mk "/usr/bin/yosys").pathExists
  let hasZ3    ← (System.FilePath.mk "/usr/bin/z3").pathExists
  let sharePy  := System.FilePath.mk "../hardware/lec/smt_share.py"
  let hasShare ← sharePy.pathExists
  if hasYosys && hasZ3 && hasShare then
    let tmpDir := "/tmp/obend_w5_c8_lec_elab"
    IO.FS.createDirAll tmpDir
    let svPath     := s!"{tmpDir}/gf2_64_wiedemann_tower_mul.sv"
    let yosPath    := s!"{tmpDir}/gf2_64_yosys.smt2"
    let rawPath    := s!"{tmpDir}/gf2_64_raw.smt2"
    let sharedPath := s!"{tmpDir}/gf2_64_shared.smt2"
    IO.FS.writeFile svPath (emitModuleSV gf2_64TowerMulRtlModule)
    let yosCmd :=
      s!"read_verilog -sv {svPath}; hierarchy -check -top gf2_64_wiedemann_tower_mul; " ++
      s!"proc; flatten; setattr -set keep 1 t:$dff %co w:* %i; opt_clean; write_smt2 {yosPath}"
    let rYos ← IO.Process.output { cmd := "/usr/bin/yosys", args := #["-q", "-p", yosCmd] }
    unless rYos.exitCode == 0 do
      throw <| IO.userError s!"yosys failed: {rYos.stderr}"
    let yosSmt ← IO.FS.readFile yosPath
    let leanHalf := (((lecScript gf2_64TowerMulRtlModule).print.splitOn "\n; --- counterexample").headD "") ++ "\n"
    IO.FS.writeFile rawPath (yosSmt ++ "\n" ++ leanHalf)
    let rSh ← IO.Process.output
      { cmd := "/usr/bin/python3"
        args := #[sharePy.toString, rawPath, sharedPath, "--yosys", "/usr/bin/yosys"] }
    unless rSh.exitCode == 0 do
      throw <| IO.userError s!"smt_share.py failed: {rSh.stderr}"
    let rZ3 ← IO.Process.output { cmd := "/usr/bin/z3", args := #[sharedPath] }
    let firstLine := (rZ3.stdout.splitOn "\n").headD ""
    unless firstLine.trimAscii.toString == "unsat" do
      throw <| IO.userError s!"expected Z3 `unsat` on gf2_64_wiedemann_tower_mul miter, got: {rZ3.stdout}"

#eval verifyLiveYosysZ3IfPresent

/-! ## 4. Mutation Sensitivity Kills (`#tooth` x 6) & Axiom Hygiene (`#assert_axioms_tree`) -/

-- Tooth 1: Dropping modular `+ p` underflow wrap-around in `glSubBV` breaks 4-cycle butterfly stream soundness:
#tooth Obend.Hardware.PipelinedZkCrypto.pipelinedGlButterfly_latency4_sound by mutation
  Obend.Hardware.PipelinedZkCrypto.glSubBV := fun va vb => evalAluOp .sub va vb

-- Tooth 2: Rubber-stamping Leiserson-Saxe retiming certification breaks the 0-stage vs 4-stage timing proof:
#tooth Obend.Hardware.PipelinedZkCrypto.glButterfly_retiming_closes_333MHz by mutation
  Obend.Hardware.Retiming.checkRetimingCert := fun _ _ _ _ => true

-- Tooth 3: Replacing the Wiedemann tower twist `towerMulOmega` with identity breaks associativity:
#tooth Obend.Hardware.PipelinedZkCrypto.towerMul_assoc by mutation
  Obend.Hardware.PipelinedZkCrypto.towerMulOmega := fun _ u => u

-- Tooth 4: Replacing recursive norm-reduction `towerInv` with identity breaks field inversion:
#tooth Obend.Hardware.PipelinedZkCrypto.towerMul_inv by mutation
  Obend.Hardware.PipelinedZkCrypto.towerInv := fun _ a => a

-- Tooth 5: Corrupting SWAR lane recombination breaks `gf2_64TowerMulRtlModule` bit-exactness:
#tooth Obend.Hardware.PipelinedZkCrypto.gf2_64TowerMulRtl_eq_towerMul by mutation
  Obend.Hardware.PipelinedZkCrypto.swarCombineBV := fun _ p q => evalAluOp .bitXor p q

-- Tooth 6: Corrupting the middle Karatsuba product `swarQ5BV` breaks 2-stage pipelined `GF(2^64)` soundness:
#tooth Obend.Hardware.PipelinedZkCrypto.gf2_64TowerMulRtl_pipe2_sound by mutation
  Obend.Hardware.PipelinedZkCrypto.swarQ5BV := fun a _ => a

#assert_axioms_tree

end Obend.Tests.PipelinedZkAndBinaryTowerTest
