module
public import Obend.Hardware.SwitchedCapRf
public import Obend.Analysis.HyperbolicPdeCert
public import Obend.Apps.SdrFt8Rx
public import Obend.Tactic.Tooth
public import Obend.AssertAxioms
meta import all Obend.Hardware.SwitchedCapRf
meta import all Obend.Analysis.HyperbolicPdeCert
meta import all Obend.Apps.SdrFt8Rx
meta import all Obend.Analysis.RealAnalysis
meta import all Obend.Analysis.Diff
meta import all Obend.Hardware.HDL
import all Obend.Analysis.Diff
import all Obend.Analysis.Equitable
import all Obend.Analysis.Flowpipe
import all Obend.Analysis.Groebner
import all Obend.Analysis.HyperbolicPdeCert
import all Obend.Analysis.RealAnalysis
import all Obend.Analysis.SosLyapunov
import all Obend.Analysis.TaylorModel
import all Obend.Apps.SdrFt8Rx
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
import all Obend.Elab.AutoCertTaylorSound
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
import all Obend.Hardware.Cic
import all Obend.Hardware.Circuits
import all Obend.Hardware.Codec
import all Obend.Hardware.Compiler
import all Obend.Hardware.Datasheet
import all Obend.Hardware.DRC
import all Obend.Hardware.DSP
import all Obend.Hardware.HDL
import all Obend.Hardware.Judge
import all Obend.Hardware.Magnetics
import all Obend.Hardware.PCB
import all Obend.Hardware.Photonics
import all Obend.Hardware.PlaceRoute
import all Obend.Hardware.Process
import all Obend.Hardware.ReductionMachine
import all Obend.Hardware.Retiming
import all Obend.Hardware.SwitchedCapRf
import all Obend.Hardware.Synth
import all Obend.Hardware.ThermalPassivity
import all Obend.Hardware.Types
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
import all Obend.Lower.Judge
import all Obend.Lower.Lower
import all Obend.Lower.Proofs.Sound
import all Obend.Lower.Proofs.Subst
import all Obend.Lower.Semantics
import all Obend.Lower.Syntax
import all Obend.Lower.Typing
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
import all Obend.Spec.Law
import all Obend.Spec.LawCompile
import all Obend.Spec.LawDial
import all Obend.Spec.Parse
import all Obend.Spec.Proofs.C4
import all Obend.Spec.Proofs.LawCompile
import all Obend.Spec.Syntax
import all Obend.Spec.Types
import all Obend.Tactic.Cases
import all Obend.Tactic.MonadicReduction
import all Obend.Tactic.Tooth
import all Obend.Vault.Law
import all Obend.Vault.Page
import all Obend.Analysis.SimplicialFeecFem
import all Obend.Apps.ZkNtt.Goldilocks
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
import all Obend.Core.Proofs.Settle
import all Obend.Core.RangeSafe
import all Obend.Hardware.Accelerators
import all Obend.Hardware.GeometryCAM
import all Obend.Leaf.BytecodeRegisterJit
import all Obend.Leaf.Served
import all Obend.Leaf.Static
import all Obend.Lower.Proofs.Book

/-!
# The switched-capacitor front end, the CORDIC weld and the hyperbolic judge, exercised

Concrete runs of `Obend.Hardware.SwitchedCapRf`, `Obend.Analysis.HyperbolicPdeCert` and the upgraded
`Obend.Apps.SdrFt8Rx`, and mutation teeth on their universal theorems: each `#tooth` replaces one
definition by a wrong one and reports that the stored proof no longer checks.
-/

public section
set_option maxRecDepth 100000
namespace Obend.Tests.SwitchedCapRfAndPdeCert

open Obend.Analysis Obend.Hardware.SwitchedCapRf Obend.Analysis.HyperbolicPde Obend.Apps.SdrFt8Rx
open Obend.Hardware.HDL

/-! ## The Tayloe detector -/

/-- 40 m band: 50 Ω source, 100 nF hold capacitors, 7.074 MHz LO: the aperture is 0.0071 time constants. -/
def frontEnd40m : TayloeFrontEndSpec :=
  ⟨50, 1 / 10000000, 1 / 7074000, 0, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- The same with 100 pF: 7.07 time constants, three halvings of the exponent. -/
def frontEndFast : TayloeFrontEndSpec :=
  ⟨50, 1 / 10000000000, 1 / 7074000, 3, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

example : (992 : Rat) / 1000 ≤ frontEnd40m.retentionLo ∧ frontEnd40m.retentionHi ≤ 993 / 1000 := by
  decide +kernel
example : 0 < frontEndFast.retentionLo ∧ frontEndFast.retentionHi ≤ 2 / 1000 := by decide +kernel

/-- The certified model's retention factor is inside the enclosure, for both. -/
example : frontEnd40m.retentionLo ≤ frontEnd40m.retention CanonicalRat ∧
    frontEnd40m.retention CanonicalRat ≤ frontEnd40m.retentionHi :=
  ⟨(frontEnd40m.retention_enclosure CanonicalRat).2.1, (frontEnd40m.retention_enclosure CanonicalRat).2.2.1⟩
example : frontEndFast.retention CanonicalRat < 1 :=
  rat_lt_of_le_of_lt (frontEndFast.retention_enclosure CanonicalRat).2.2.1
    (frontEndFast.retention_enclosure CanonicalRat).2.2.2

/-- Two periods at `α = 1/2`: two trajectories under one drive close their distance by `α^4 = 1/16`
in energy, and the `I` output ignores the `Q` drive. -/
example : TayloeState.energyDiff
      (TayloeState.run (1 / 2) [⟨1, 2, 3, 4⟩, ⟨0, 1, 0, 1⟩] ⟨8, 0, 0, 0⟩)
      (TayloeState.run (1 / 2) [⟨1, 2, 3, 4⟩, ⟨0, 1, 0, 1⟩] ⟨0, 0, 0, 0⟩) = 64 / 16 := by decide +kernel
example : (TayloeState.run (1 / 2) [⟨1, 2, 3, 4⟩, ⟨0, 1, 0, 1⟩] ⟨8, 0, 0, 0⟩).iOut
    = (TayloeState.run (1 / 2) [⟨1, 77, 3, -5⟩, ⟨0, 9, 0, 9⟩] ⟨8, 6, 0, 3⟩).iOut := by decide +kernel
/-- A drive that repeats after half a period (an even harmonic) leaves only the decaying initial `I`. -/
example : (TayloeState.run (1 / 2) [⟨5, 7, 5, 7⟩, ⟨-3, 2, -3, 2⟩] ⟨8, 0, 0, 0⟩).iOut = 8 / 4 := by
  decide +kernel

/-! ## Odd harmonics and the preselector -/

example : oddHarmonicGain 0 = 1 ∧ oddHarmonicGain 1 = 1 / 3 ∧ oddHarmonicGain 2 = -(1 / 5) ∧
    oddHarmonicGain 3 = -(1 / 7) ∧ oddHarmonicGain 4 = 1 / 9 := by decide +kernel
/-- At 1/3 duty (`cos² φ = 1/4`) the third harmonic is nulled instead: the envelope depends on the duty. -/
example : gateU (1 / 4) 1 = 0 := by decide +kernel
example : chebU (3 / 5) (2 * 2) = gateU (3 / 5 * (3 / 5)) 2 := (chebU_even (3 / 5) 2).1

/-- A third-order elliptic section between 50 Ω terminations, frequencies in units of the LO: the
trap `L = 30`, `C = 1/270` resonates at `ω = 3`, the third harmonic. -/
def preselector : List LadderElem := [.shuntGC 0 (1 / 50), .seriesTrap 30 (1 / 270), .shuntGC 0 (1 / 50)]

/-- A lossy ladder: series resistance and shunt conductance. -/
def lossyLadder : List LadderElem := [.seriesRL 5 10, .shuntGC (1 / 1000) (1 / 100)]

example : s11Sq 1 50 50 preselector + s21Sq 1 50 50 preselector = 1 := by decide +kernel
example : s11Sq 2 50 50 preselector + s21Sq 2 50 50 preselector = 1 := by decide +kernel
example : s21Sq 3 50 50 preselector = 0 ∧ s11Sq 3 50 50 preselector = 1 := by decide +kernel
example : s11Sq 1 50 50 lossyLadder + s21Sq 1 50 50 lossyLadder < 1 := by decide +kernel
example : 0 < s21Sq 1 50 50 lossyLadder := by decide +kernel
/-- The alias at `3·f_LO` is removed entirely; at `5·f_LO` it is below the detector's `1/25`. -/
example : compositeAliasPower 1 50 50 preselector 1 = 0 := by decide +kernel
example : compositeAliasPower 1 50 50 preselector 2 < 1 / 25 := by decide +kernel

/-! ## The CORDIC in all four quadrants, and the weld on every tone -/

example : cordicAtan2 10000 10000 = 785565 ∧ cordicAtan2 (-10000) 10000 = 2356362 ∧
    cordicAtan2 (-10000) (-10000) = -2356028 ∧ cordicAtan2 10000 (-10000) = -785231 := by decide +kernel
example : cordicAtan2 10000 0 = -293 ∧ cordicAtan2 0 9000 = 1571089 ∧ cordicAtan2 (-9000) 1 = 3141886 := by
  decide +kernel

/-- The radian enclosure, instantiated: the argument of `12000 + 5000j` (`0.394791…` rad) is within
3037 µrad of the CORDIC's `395083`. -/
example : ArgIn ((12000 : Int) : Rat) ((5000 : Int) : Rat)
    ((cordicAtan2 12000 5000 - 3037 : Int) / 1000000) ((cordicAtan2 12000 5000 + 3037 : Int) / 1000000) :=
  cordicAtan2_arg 12000 5000 (by decide)
example : cordicAtan2 12000 5000 = 395083 := by decide +kernel

/-- The ideal phasor of tone `k`, `20000·exp(j·k·2π/15)` rounded to integers. -/
def tonePhasor : Nat → Int × Int
  | 0 => (20000, 0) | 1 => (18271, 8135) | 2 => (13383, 14863) | 3 => (6180, 19021)
  | 4 => (-2091, 19890) | 5 => (-10000, 17321) | 6 => (-16180, 11756) | _ => (-19563, 4158)

example : InToneCone 0 20000 0 ∧ InToneCone 1 18271 8135 ∧ InToneCone 2 13383 14863 ∧
    InToneCone 3 6180 19021 ∧ InToneCone 4 (-2091) 19890 ∧ InToneCone 5 (-10000) 17321 ∧
    InToneCone 6 (-16180) 11756 ∧ InToneCone 7 (-19563) 4158 := by decide +kernel

/-- The weld on tone 5's phasor (a folded quadrant), through the theorem. -/
example : ft8Bin (cordicAtan2 (-10000) 17321) = 5 ∧ ft8Oob (cordicAtan2 (-10000) 17321) = false :=
  ft8_iq_cordic_slicer_exact_tone 5 (by decide) (-10000) 17321 (by decide) (by decide +kernel)

/-- And by evaluation on all eight. -/
example : [0, 1, 2, 3, 4, 5, 6, 7].all (fun k =>
    ft8Bin (cordicAtan2 (tonePhasor k).1 (tonePhasor k).2) == k) = true := by decide +kernel

/-- A phasor at a bin edge is in no tone's cone: the cones leave the CORDIC its error budget. -/
example : ¬ InToneCone 0 19563 4158 ∧ ¬ InToneCone 1 19563 4158 := by decide +kernel

/-! ## The unified module -/

example : checkRtlModuleW sdrFt8RxTopModule = true := sdrFt8RxTopModule_checkRtlModuleW
example : sdrFt8RxTopModule.wires.length = 73 ∧ sdrFt8RxTopModule.regs.length = 27 := by decide +kernel
/-- Without the strobe wire the embedded CICs and the discriminator read a wire that is not there:
the emission gate refuses. -/
example : checkRtlModuleW { sdrFt8RxTopModule with
    wires := sdrNcoModule.wires ++ shiftWires "i_" 23 4 cicInI sdrCicModule.wires } = false := by
  decide +kernel

/-- A register file with the symbol's correlation `-10000 + 17321j` (tone 5) in the discriminator's
accumulators (registers 4 and 5). -/
def discRegs : Nat → BitVec 64 := fun i =>
  if i = 4 then BitVec.ofInt 64 (-10000) else if i = 5 then BitVec.ofInt 64 17321 else 0#64

/-- The discriminator's angle wire is `cordicAtan2` of them, and the slicer presents tone 5. -/
example (inp : Nat → BitVec 64) :
    (evalWireTable inp discRegs sdrFt8DiscModule.wires angleWire).toInt = cordicAtan2 (-10000) 17321 :=
  disc_angle_eq_cordicAtan2 inp discRegs (by decide) (by decide)
example (inp : Nat → BitVec 64) :
    evalRtlExpr inp (evalWireTable inp discRegs sdrFt8DiscModule.wires) discRegs (binExpr (.wireRef angleWire))
      = BitVec.ofNat 64 5 :=
  (disc_tone_exact inp discRegs 5 (by decide) (by decide) (by decide) (by decide) (by decide +kernel)).1

/-- The same in the unified module (accumulators at registers 22 and 23, counter at 0, `sym_latch` high). -/
def topRegs : Nat → BitVec 64 := fun i =>
  if i = 22 then BitVec.ofInt 64 (-10000) else if i = 23 then BitVec.ofInt 64 17321 else 0#64
def latchInputs : Nat → BitVec 64 := fun i => if i = 5 then 1#64 else 0#64

example : stepModuleRegs sdrFt8RxTopModule false latchInputs topRegs 24 = BitVec.ofNat 64 5 :=
  top_tone_latch latchInputs topRegs 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide +kernel)

/-! ## The judge `hyperbolic-fvm@1` -/

example : hyperbolicPdeJudge.check 0 maxwellSystem maxwellCert = .ok :=
  (by decide +kernel : check maxwellSystem maxwellCert = .ok)
example : hyperbolicPdeJudge.check 7 phmSystem phmCert = .ok :=
  (by decide +kernel : check phmSystem phmCert = .ok)
example : Certified phmSystem phmCert :=
  hyperbolicPdeJudge.sound (r := 0) (o := phmSystem) (c := phmCert)
    (by decide +kernel : check phmSystem phmCert = .ok)

/-- The dual-number Jacobian of Burgers' flux `u²/2` at `u = 1` is `1`, at `u = 2` it is `2`. -/
example : burgersSystem.jacobian 0 0 = 1 ∧ ({ burgersSystem with state := [2] } : HyperbolicSystem).jacobian 0 0 = 2 := by
  decide +kernel

example : check maxwellSystem { maxwellCert with jac := [[0, 9 / 4], [2, 0]] }
    = .refused .jacobianMismatch [1, 0] := by decide +kernel
example : check phmSystem { phmCert with weights := [8, 8, -8, 8] } = .refused .weightNotPositive [2] := by
  decide +kernel
example : check phmSystem { phmCert with sym := [[1, 0, 0, 0], [0, 4, 0, 0], [0, 0, 4, 1], [0, 0, 0, 1]] }
    = .refused .symmetrizerMismatch [2, 3] := by decide +kernel
example : check { phmSystem with cfl := 1 / 2 } phmCert = .refused .cflViolation [] := by decide +kernel
/-- A CFL refusal is a refutation: no certificate has the meaning. -/
example (c : HyperbolicCert) : ¬ Certified { phmSystem with cfl := 1 / 2 } c :=
  check_refuted (c := phmCert) (k := .cflViolation) (p := []) (by decide +kernel) rfl c

/-- The wave splitting of Maxwell's Riemann problem `(1, 1/2) → (3, -1)` conserves the flux jump. -/
example : amdq 2 (matOf maxwellCert.eigVecs) (matOf maxwellCert.eigInv) (vecOf maxwellCert.eigVals)
      maxwellSystem.jump 0
    + apdq 2 (matOf maxwellCert.eigVecs) (matOf maxwellCert.eigInv) (vecOf maxwellCert.eigVals)
      maxwellSystem.jump 0
    = maxwellSystem.fluxAt [3, -1] 0 - maxwellSystem.fluxAt [1, 1 / 2] 0 := by decide +kernel

/-- One Rusanov step of Maxwell's equations on a four-cell periodic grid: the energy drops from
`41/2` to `61/8`. -/
def gridState : Nat → Vec := fun i c => if i = 0 ∧ c = 0 then 4 else if i = 2 ∧ c = 1 then 1 else if i = 1 ∧ c = 0 then 3 / 2 else 0

example : symEnergy maxwellSystem maxwellCert 4
      (rusanovStep 2 maxwellSystem.jacobian (3 / 2) (2 / 3) 4 gridState)
    ≤ symEnergy maxwellSystem maxwellCert 4 gridState := by decide +kernel

example : minmod 2 5 = 2 ∧ minmod (-3) (-1) = -1 ∧ minmod 2 (-1) = 0 ∧ minmod 4 4 = 4 := by decide +kernel

/-! ## Mutation teeth -/

/-- A CORDIC table with a wrong second entry. -/
def lutWrongEntry : List Int :=
  [785398, 473648, 244979, 124355, 62419, 31240, 15624, 7812, 3906, 1953, 977, 488]
#tooth cordicRun_arg by mutation cordicLutUrad := lutWrongEntry

/-- `π` off by 5 mrad in the quadrant fold. -/
def piWrong : Int := 3146593
#tooth cordicAtan2_arg by mutation cordicPiUrad := piWrong

/-- An "upper bound" on `exp` that is the lower polynomial. -/
def expHiWrong (y : Rat) : Rat := 1 + y + y * y / 2 + y * y * y / 6 + y * y * y * y / 24 + y * y * y * y * y / 40 - 1
#tooth TayloeFrontEndSpec.retention_enclosure by mutation TayloeFrontEndSpec.expHi := expHiWrong

/-- A capacitor that forgets its retention: the difference of two trajectories no longer scales. -/
def cycleNoRetention (α : Rat) (v : TayloeState) (w : TayloeDrive) : TayloeState :=
  ⟨v.v0 + (1 - α) * w.v0, α * v.v1 + (1 - α) * w.v1, α * v.v2 + (1 - α) * w.v2, α * v.v3 + (1 - α) * w.v3⟩
#tooth TayloeState.cycle_energyDiff by mutation TayloeState.cycle := cycleNoRetention

/-- A ladder whose series resistor generates power (sign of `R` flipped in the voltage drop). -/
def actActive (ω : Rat) : LadderElem → PortState → PortState
  | .seriesRL r l, s => ⟨s.vr - r * s.ir - ω * l * s.ii, s.vi - r * s.ii + ω * l * s.ir, s.ir, s.ii, s.k⟩
  | .shuntGC g c, s => ⟨s.vr, s.vi, s.ir + g * s.vr - ω * c * s.vi, s.ii + g * s.vi + ω * c * s.vr, s.k⟩
  | .seriesTrap _ _, s => s
  | .shuntTrap _ _, s => s
#tooth act_power_ge by mutation LadderElem.act := actActive

/-- Checkers that wave everything through. -/
def symBAll (_ : HyperbolicSystem) (_ : HyperbolicCert) (_ _ : Nat) : Bool := true
#tooth check_sound by mutation symB := symBAll
def cflBAll (_ : HyperbolicSystem) : Bool := true
#tooth check_sound by mutation cflB := cflBAll
def speedBAll (_ : HyperbolicSystem) (_ : HyperbolicCert) (_ : Nat) : Bool := true
#tooth check_sound by mutation speedB := speedBAll
def eigBAll (_ : HyperbolicSystem) (_ : HyperbolicCert) (_ _ : Nat) : Bool := true
#tooth check_sound by mutation eigB := eigBAll

/-- A minmod that keeps the larger slope. -/
def maxmod (a b : Rat) : Rat :=
  if 0 < a ∧ 0 < b then (if a ≤ b then b else a) else if a < 0 ∧ b < 0 then (if a ≤ b then a else b) else 0
#tooth minmod_tvd by mutation minmod := maxmod

/-- Slicer thresholds shifted by 5 mrad. -/
def thresholdsShifted : List Int := [214440, 633319, 1052198, 1471077, 1889956, 2308835, 2727714]
#tooth ft8_bin_of_tone by mutation ft8Thresholds := thresholdsShifted

/-- Tone cones widened to the full half bin: the CORDIC's error no longer fits. -/
def toneConeLoWide : Nat → Int × Int
  | 0 => (978146734, -207916036)
  | 1 => (977308027, 211823086)
  | 2 => (806659110, 591016988)
  | 3 => (496531518, 868018693)
  | 4 => (100549124, 994932095)
  | 5 => (-312819126, 949812716)
  | 6 => (-672098112, 740462105)
  | _ => (-915165239, 403078881)
#tooth ft8_iq_cordic_slicer_exact_tone by mutation toneConeLo := toneConeLoWide

#assert_axioms_tree

end Obend.Tests.SwitchedCapRfAndPdeCert
