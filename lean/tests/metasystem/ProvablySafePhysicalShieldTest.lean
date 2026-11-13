module
public import Obend.Hardware.SafePhysicalShield
public import Obend.Hardware.Device.DriftDiffusion
public import Obend.Hardware.SiliconOuroboros
public import Obend.Hardware.Analog
public import Obend.Teeth.Hardware.DeviceFixtures
public import Obend.Tactic.Tooth
public import Obend.AssertAxioms
meta import all Obend.Hardware.SafePhysicalShield
meta import all Obend.Hardware.Device.DriftDiffusion
meta import all Obend.Hardware.Device.Enclosure
meta import all Obend.Hardware.SiliconOuroboros
meta import all Obend.Hardware.DprStutter
meta import all Obend.Hardware.Analog
meta import all Obend.Analysis.Flowpipe
meta import all Obend.Analysis.RealAnalysis
meta import all Obend.Judge.ReflectiveGate
meta import all Obend.Judge.SvenvsCorrigibility
meta import all Obend.Judge.CertifierRatchet

-- Full bodies are needed for the imported-tree axiom audit and for the teeth.
import all Obend.Analysis.Diff
import all Obend.Analysis.Flowpipe
import all Obend.Analysis.RealAnalysis
import all Obend.AssertAxioms
import all Obend.Category.Refines
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
import all Obend.Elab.Work
import all Obend.Equiv.Ahead
import all Obend.Equiv.Behaviour
import all Obend.Equiv.Fields
import all Obend.Equiv.Quote
import all Obend.Equiv.Reduction
import all Obend.Equiv.Simulation
import all Obend.Fold
import all Obend.Hardware.Analog
import all Obend.Hardware.ArrayFold
import all Obend.Hardware.Device.Constants
import all Obend.Hardware.Device.DriftDiffusion
import all Obend.Hardware.Device.Enclosure
import all Obend.Hardware.Device.Sky130Diode
import all Obend.Hardware.Device.Wafer
import all Obend.Hardware.DprStutter
import all Obend.Hardware.Fabulous.Net
import all Obend.Hardware.HDL
import all Obend.Hardware.RtlFold
import all Obend.Hardware.SafePhysicalShield
import all Obend.Hardware.SiliconOuroboros
import all Obend.Intention
import all Obend.Judge.CertifierRatchet
import all Obend.Judge.Class
import all Obend.Judge.Clearing
import all Obend.Judge.Genealogy
import all Obend.Judge.Lrat
import all Obend.Judge.ReflectiveGate
import all Obend.Judge.SvenvsCorrigibility
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
import all Obend.Law.Run
import all Obend.Law.Std
import all Obend.Law.Syntax
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
import all Obend.Receipt
import all Obend.Receipt.Merkle
import all Obend.Run.Control
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
import all Obend.Spec.C4
import all Obend.Spec.DataWire
import all Obend.Spec.Proofs.C4
import all Obend.Tactic.Cases
import all Obend.Tactic.MonadicReduction
import all Obend.Tactic.Tooth
import all Obend.Teeth.Hardware.DeviceCertificates
import all Obend.Teeth.Hardware.DeviceFixtures
import all Obend.Analysis.Groebner
import all Obend.Analysis.SosLyapunov
import all Obend.Hardware.CircuitDae
import all Obend.Hardware.CurrentLoop
import all Obend.Judge.RealAnalysis

/-!
# The sampled hardware gatekeeper and the quasi-Fermi device certificate, exercised

Tier 2 for `Obend.Hardware.SafePhysicalShield` and the quasi-Fermi section of
`Obend.Hardware.Device.DriftDiffusion`. The thermal stage of the shield module (12-bit converter,
100 ms period, four zones) is driven through its sensor chain, its LUT, the three ICAP edges, a bus
fault and both outcomes of an upgrade; the two safety theorems are instantiated with the proposal left
universally quantified. The device half checks the flux identities on a table of rationals that obeys
the Bernoulli laws, the collapse of the term scale, and the judge's refutation and completeness
fields. The teeth mutate the `epsAdc` margin, the pad, the Picard check, the root mux, the reflective
gate, and the product-form flux and checker.
-/

public section
namespace Obend.Tests.ProvablySafePhysicalShield
open Obend.Analysis Obend.Judge
open Obend.Judge.SvenvsCorrigibility Obend.Judge.CertifierRatchet Obend.Judge.ReflectiveGate
open Obend.Hardware.HDL Obend.Hardware.DprStutter Obend.Hardware.SiliconOuroboros
open Obend.Hardware.SafePhysicalShield Obend.Hardware.SafePhysicalShield.SampledPhysicalPlantSpec
open Obend.Hardware.Device Obend.Teeth.Hardware.DeviceFixtures
set_option autoImplicit false
set_option maxRecDepth 16384

/-! ## 1. The sensor chain: 12-bit SAR conversion, zones, the `epsAdc` bound -/

example : thermalStage.adcCode 2000 = 2000 ∧ thermalStage.adcCode 5000 = 4095 := by decide +kernel
example : thermalStage.zoneOf (thermalStage.adcCode 2000) = 1 ∧ thermalStage.zoneOf (thermalStage.adcCode 3900) = 3 := by
  decide +kernel
example : thermalStage.estimate 2000 = 50 ∧ thermalStage.epsAdc = 21 / 40 ∧ thermalStage.pad = 6 / 5 := by decide +kernel

/-- A reading 25 m°C low (within the sensor's 0.5 °C): the estimate is within `epsAdc`, by the converter's theorem. -/
example : Obend.Analysis.ratAbs (thermalStage.estimate (thermalStage.adcCode 1999) - 50) ≤ thermalStage.epsAdc :=
  (adc_estimate_within_eps thermalStage thermalStage_wf (x := 50) (vInMv := 1999) (by decide +kernel) (by decide +kernel)).1

/-- The cell of the zone read contains the true state, whatever the reading within the contract. -/
example (vInMv : Nat) (hs : thermalStage.SensorReads 50 vInMv) :
    (50 : CanonicalRat) ∈ thermalStage.cell (thermalStage.zoneOf (thermalStage.adcCode vInMv)) :=
  state_in_cell thermalStage thermalStage_wf (by decide +kernel) hs

/-- A reading outside the contract is not a reading: 1 °C off is refused by `SensorReads`. -/
example : ¬ thermalStage.SensorReads 50 2040 := by decide +kernel

/-! ## 2. The check: which commands pass in which zone -/

example : thermalStage.cell 0 = ⟨6 / 5, 209 / 8⟩ ∧ thermalStage.tube 0 = ⟨0, 1093 / 40⟩ := by decide +kernel
example : thermalStage.cell 3 = ⟨3051 / 40, 494 / 5⟩ ∧ thermalStage.tube 3 = ⟨3003 / 40, 100⟩ := by decide +kernel
-- heater off in the coldest zone fails re-entry (the stage can cool below the core); full power in the hottest fails it
example : thermalStage.actionOk 0 0 = false ∧ thermalStage.actionOk 0 1 = true ∧ thermalStage.actionOk 0 3 = true := by
  decide +kernel
example : thermalStage.actionOk 3 0 = true ∧ thermalStage.actionOk 3 2 = true ∧ thermalStage.actionOk 3 3 = false := by
  decide +kernel
-- the declared 12 °C/s is tight: full power from the coldest zone reaches the tube's edge
example : thermalStage.actionOk 0 3 = true ∧ ({ thermalStage with speed := 11 } : SampledPhysicalPlantSpec).actionOk 0 3 = false := by
  decide +kernel

/-! ## 3. The gate on the live fabric: LUT accept, LUT reject, fence, quarantine -/

theorem genesis_gate (z : HWState) (a : HWAct) :
    cageAction ⟨z, thermalFabric, thermalRoot⟩ a =
      if policyOfRtl trickleOnlyRtl z a then a else thermalRoot z := by
  rw [cageAction_lowered (policyOfRtl trickleOnlyRtl) thermalFabric thermalRoot z a rfl]
  simp [thermalFabric]

-- the trickle command passes; full power proposed in zone 1 is overridden by the root (heater off)
example : cageAction ⟨1, thermalFabric, thermalRoot⟩ 1 = 1 := by rw [genesis_gate]; decide +kernel
example : cageAction ⟨1, thermalFabric, thermalRoot⟩ 3 = 0 := by rw [genesis_gate]; decide +kernel
example : cageAction ⟨0, thermalFabric, thermalRoot⟩ 0 = 1 := by rw [genesis_gate]; decide +kernel

/-- The override is explained: the fabric is active, so the live LUT rejected the proposal. -/
example : liveLut thermalFabric 1 3 = false := by
  have h : cageAction ⟨1, thermalFabric, thermalRoot⟩ 3 ≠ 3 := by rw [genesis_gate]; decide +kernel
  rcases override_implies_fenced_or_lut_reject thermalFabric thermalRoot 1 3 h with hp | hl
  · exact absurd rfl hp
  · exact hl

def isolated : ShieldStage := adminStep thermalStage thermalGenesis .isolate

theorem isolated_fenced : isolated.dpr.phase = .isolateClamped := by
  simp [isolated, adminStep, stepDprFabric, administer, thermalGenesis, thermalFabric]

/-- First ICAP edge: the fence is up, and every proposal, the trickle command included, gets the root. -/
example (vInMv : Nat) (a : HWAct) :
    gateAction thermalStage isolated vInMv a = thermalRoot (thermalStage.zoneOf (thermalStage.adcCode vInMv)) :=
  gate_fails_closed thermalStage isolated vInMv a (by rw [isolated_fenced]; decide)

def quarantined : ShieldStage := adminStep thermalStage thermalGenesis (.busFault #[])

theorem quarantined_fenced : quarantined.dpr.phase = .isolateClamped ∧
    quarantined.dpr.activeTiles = thermalGenesis.dpr.activeTiles := by
  have bad : decodeTileFrames thermalGenesis.dpr.activeTiles.size #[] = none := by decide
  have hph : thermalGenesis.dpr.phase = .active := rfl
  simp [quarantined, adminStep, bad, stepDprFabric, administer, hph]

/-- CRC-failing bus traffic: the slot is quarantined, the bank is kept, the root drives. -/
example (vInMv : Nat) (a : HWAct) :
    gateAction thermalStage quarantined vInMv a = thermalRoot (thermalStage.zoneOf (thermalStage.adcCode vInMv)) :=
  gate_fails_closed thermalStage quarantined vInMv a (by rw [quarantined_fenced.1]; decide)

/-! ## 4. Upgrades: a certified LUT is installed in three periods, an uncertifiable one never -/

def upgraded : ShieldStage :=
  adminStep thermalStage (adminStep thermalStage (adminStep thermalStage thermalGenesis .isolate)
    (.load trickleOrHalfRtl .fastDecideClosed false)) .release

theorem upgraded_live : upgraded.dpr.phase = .active ∧
    upgraded.dpr.activeTiles = lowerPolicyToTiles (policyOfRtl trickleOrHalfRtl) :=
  ota_install_completes thermalStage thermalGenesis_invariant rfl trickleOrHalfRtl .fastDecideClosed false
    trickleOrHalf_certified

/-- After the upgrade half power passes in zone 1; before it, it was overridden. -/
example : cageAction ⟨1, upgraded.dpr, thermalRoot⟩ 2 = 2 := by
  rw [cageAction_lowered (policyOfRtl trickleOrHalfRtl) upgraded.dpr thermalRoot 1 2 upgraded_live.2, upgraded_live.1]
  decide +kernel
example : cageAction ⟨1, thermalFabric, thermalRoot⟩ 2 = 0 := by rw [genesis_gate]; decide +kernel

/-- **No certificate installs the permit-all LUT**: a sound checker accepting it would make full power
in the hottest zone pass `actionOk`, and it does not. -/
theorem permitAll_never_certified (cert : FastProofCert) :
    FastKernel cert (shieldSequent thermalStage (policyOfRtl permitAllRtl)) = false := by
  cases h : FastKernel cert (shieldSequent thermalStage (policyOfRtl permitAllRtl)) with
  | false => rfl
  | true =>
    have hs := shieldSequent_encodes _ _ (fastKernel_sound _ _ h) 3 3 (by decide +kernel)
    exact absurd hs (by decide +kernel)

/-- Whatever certificate accompanies it, the permit-all candidate leaves the stage as it was. -/
example (cert : FastProofCert) (promote : Bool) :
    adminStep thermalStage thermalGenesis (.load permitAllRtl cert promote) = thermalGenesis :=
  rejected_ota_leaves_shield_untouched thermalStage thermalGenesis permitAllRtl cert promote
    (permitAll_never_certified cert)

/-! ## 5. The two safety theorems, the proposal universally quantified -/

example : thermalStage.Ts = 1 / 10 ∧ thermalStage.phys = ⟨0, 100⟩ ∧ thermalStage.core = ⟨6 / 5, 494 / 5⟩ := by decide +kernel

/-- One period from 50 °C read as 2000 mV: for every proposal and every trajectory of the plant under
the gated command, the temperature stays in `[0, 100]` °C, moves at most 1.2 °C, and ends in the core. -/
example (proposal : HWAct) (x : CanonicalRat → CanonicalRat) (hx0 : x 0 = 50)
    (hflow : InterSampleFlow thermalStage (thermalStage.zoneOf (thermalStage.adcCode 2000))
      (cageAction ⟨thermalStage.zoneOf (thermalStage.adcCode 2000), thermalFabric, thermalRoot⟩ proposal) x) :
    (∀ τ, 0 ≤ τ → τ ≤ thermalStage.Ts → x τ ∈ thermalStage.phys ∧ Obend.Analysis.ratAbs (x τ - x 0) ≤ 6 / 5) ∧
      x thermalStage.Ts ∈ thermalStage.core := by
  have h := sampled_shield_implies_continuous_tube thermalStage thermalStage_wf thermalFabric thermalRoot
    ⟨_, rfl, trickleOnly_passes⟩ thermalRoot_passes 50 (by decide +kernel) 2000 (by decide +kernel) proposal x hx0 hflow
  have e1 : thermalStage.speed * thermalStage.Ts = 6 / 5 := by decide +kernel
  rw [e1] at h
  exact h

/-- The same period mid-reconfiguration, with the fabric fenced: the statement does not change. -/
example (proposal : HWAct) (x : CanonicalRat → CanonicalRat) (hx0 : x 0 = 50)
    (hflow : InterSampleFlow thermalStage (thermalStage.zoneOf (thermalStage.adcCode 2000))
      (cageAction ⟨thermalStage.zoneOf (thermalStage.adcCode 2000), isolated.dpr, thermalRoot⟩ proposal) x) :
    ∀ τ, 0 ≤ τ → τ ≤ thermalStage.Ts → x τ ∈ thermalStage.phys := by
  have hs := adminStep_sound thermalStage thermalGenesis_invariant .isolate
  exact fun τ h0 h1 => ((sampled_shield_implies_continuous_tube thermalStage thermalStage_wf isolated.dpr thermalRoot
    hs.fabric.1 thermalRoot_passes 50 (by decide +kernel) 2000 (by decide +kernel) proposal x hx0 hflow).1 τ h0 h1).1

/-- Any valid trace from power-on, of any length: every instant in the envelope, the stage sound at the end. -/
example (evs : List ShieldStepEvent) (hv : ValidTrace thermalStage thermalGenesis evs) (k : Nat)
    (hk : k < evs.length) (τ : CanonicalRat) (h0 : 0 ≤ τ) (h1 : τ ≤ thermalStage.Ts) :
    (evs[k]).traj τ ∈ thermalStage.phys ∧ ShieldSound thermalStage (runShield thermalStage thermalGenesis evs) :=
  have h := continuous_plant_trace_safe_all_t thermalStage thermalStage_wf evs thermalGenesis thermalGenesis_invariant hv
  ⟨h.1 k hk τ h0 h1, h.2⟩

-- the five-period trace (idle, isolate, certified load, release, bus fault) is one such trace
example : thermalTrace.length = 5 ∧ ValidTrace thermalStage thermalGenesis thermalTrace :=
  ⟨rfl, thermalTrace_valid⟩
example : (thermalTrace[4]).traj (1 / 10) = 49 := by decide +kernel

/-- The trajectory class is not empty at any gated step from power-on. -/
example (vInMv : Nat) (hs : thermalStage.SensorReads 50 vInMv) (proposal : HWAct) :
    ∃ x, x 0 = 50 ∧ InterSampleFlow thermalStage (thermalStage.zoneOf (thermalStage.adcCode vInMv))
      (cageAction ⟨thermalStage.zoneOf (thermalStage.adcCode vInMv), thermalFabric, thermalRoot⟩ proposal) x := by
  have hcell := state_in_cell thermalStage thermalStage_wf (x := 50) (by decide +kernel) hs
  have hok := gate_action_ok thermalStage (dpr := thermalFabric) ⟨_, rfl, trickleOnly_passes⟩ thermalRoot_passes
    (thermalStage.zoneOf (thermalStage.adcCode vInMv)) proposal
  refine interSampleFlow_exists thermalStage hok ?_
  rw [Interval.mem_iff] at hcell ⊢
  have hp : (0 : CanonicalRat) ≤ thermalStage.pad := by decide +kernel
  simp only [tube]
  grind

/-! ## 6. The quasi-Fermi form: the flux identity, the scale, the judge -/

/-- A table of rationals obeying the Bernoulli laws on edge 0 of the slab mesh: `e^{−Δ}` stood for by
`1/2` with `Δ = 1` (`B(Δ) = 1`, since `(1/2)(B + 1) = B`), `e^{−δ}` by `1/2` with `1/B(−δ) = 1/2` at `δ = 1`. -/
def lawTable : String → CanonicalRat := fun v =>
  if v = "b0" then 1 else if v = "gn0" then 1 / 2 else if v = "en0" then 4 else if v = "en1" then 1 else 0

/-- The certificate that goes with `lawTable`: `ψ` drops by `V_t` and `φ_n` rises by `V_t` over edge 0,
densities `4 n_i` and `n_i`. -/
def lawSolution : DdQuasiFermiSolution where
  base := { slabSolution with
    psi := [badSpec.vt, 0, 0]
    n := [4 * slabSolution.ni, slabSolution.ni, slabSolution.ni] }
  phiN := [0, badSpec.vt, 0]
  phiP := [0, 0, 0]

-- the identity's five premises hold of that table, and the two fluxes agree as rationals
example : evalExpr lawTable (jnQ badSpec lawSolution 0) = evalExpr lawTable (jn badSpec lawSolution.base 0) :=
  jnQuasiFermi_eq_jn (eΔ := 1 / 2) (eδ := 1 / 2) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
example : evalExpr lawTable (jnQ badSpec lawSolution 0) ≠ 0 := by decide +kernel

-- `B(−x) = eˣ B(x)` on the stand-in, at `x = 1` with `2` standing for `e`
example : bernOf (-1) (2 : CanonicalRat)⁻¹ = 2 * bernOf 1 2 :=
  bernoulli_exp (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- On the slab at equilibrium the product-form flux scale is `0` on both edges (flat quasi-Fermi
levels), while the `(n, p, ψ)` scale is two terms of `c_N · 10¹⁶`. -/
example : scaleJnQ badSpec slabQuasiFermi slabQfEnv 0 = 0 ∧ scaleJnQ badSpec slabQuasiFermi slabQfEnv 1 = 0 :=
  ⟨scaleJnQ_eq_zero_of_flat _ (by decide +kernel), scaleJnQ_eq_zero_of_flat _ (by decide +kernel)⟩
example : (1000 : CanonicalRat) < scaleJn badSpec slabSolution slabEnv 0 := by decide +kernel

-- the certified bound on the slab: more than eight orders between the two forms
example : 1.0e8 * qfCurrentBound badSpec slabQuasiFermi slabQfEnv 1 ≤ classicalCurrentBound badSpec slabSolution slabEnv 1 := by
  decide +kernel

/-- On the diode (device A, 23 nodes, −0.3 V; `Obend/Teeth/Hardware/DeviceFixtures.lean`): the
`(n, p, ψ)` bound exceeds `10⁻⁹ A`, the quasi-Fermi bound is under `10⁻¹⁹ A`: ten orders. -/
example : 1.0e10 * quasiFermiBoundFar coarseForwardSpec coarseForward <
    classicalBoundAtContact coarseForwardSpec coarseForward.base := by
  have h := coarseForward_bounds
  grind

/-- A two-node mesh: `meshOk` fails. -/
def twoNodeSpec : DdSpec := { badSpec with xCm := [0, 1.0e-5] }

/-- **Refusal soundness of the quasi-Fermi judge**: the two-node object is refused by `.mesh`, a
refuting clause, so no certificate at all has `DdQuasiFermiMeaning` for it. -/
example (c' : DdQuasiFermiSolution) : ¬ DdQuasiFermiMeaning twoNodeSpec c' :=
  ddQuasiFermiJudge.refuted (r := 0) (o := twoNodeSpec) (c := slabQuasiFermi) (k := .mesh) (p := [])
    (show checkDdQuasiFermi twoNodeSpec slabQuasiFermi = .refused .mesh [] by decide +kernel) rfl c'

example (c' : DdSolution) : ¬ DdMeaning twoNodeSpec c' :=
  ddJudge.refuted (r := 0) (o := twoNodeSpec) (c := slabSolution) (k := .mesh) (p := [])
    (show checkDd twoNodeSpec slabSolution = .refused .mesh [] by decide +kernel) rfl c'

-- a refusal by a non-refuting clause claims nothing about other certificates
example : refutesClause (.boltzmann 0) = false ∧ refutesClause (.doping 1) = false := by decide

-- completeness on the stated fragment, and the planted certificate's refusal
example : ∃ c r, ddQuasiFermiJudge.check r badSpec c = .ok :=
  ddQuasiFermiJudge.complete rfl ⟨slabQuasiFermi, checkDdQuasiFermi_sound slabQuasiFermi_accepted⟩
example : isRefusedBoltzmann 0 (checkDdQuasiFermi badSpec badQuasiFermi) = true := badQuasiFermi_refused

/-! ## 7. Teeth -/

-- the `epsAdc` margin: with no quantization allowance the cell no longer contains the state
#tooth state_in_cell by mutation SampledPhysicalPlantSpec.epsAdc := fun p => p.epsSensor
-- the inter-sample pad: a core that is the whole envelope leaves no room for the excursion
#tooth tube_subset_phys by mutation SampledPhysicalPlantSpec.core := fun p => p.phys
-- the Picard check: re-entry alone does not enclose the period
#tooth flow_in_tube by mutation SampledPhysicalPlantSpec.actionOk := fun p z u =>
  match evalInterval [("x", p.tube z)] (p.field u) with
  | some F => Interval.subset (Interval.add (p.cell z) (Interval.mul (Interval.ofPoint p.Ts) F)) p.core
  | none => false
-- the root mux: a cage that forwards every proposal
#tooth sampled_shield_implies_continuous_tube by mutation cageAction := fun _ a => a
-- the fence: a cage that consults the LUT while reconfiguring
#tooth gate_fails_closed by mutation cageAction := fun cage a =>
  if (evalDecodedFabric cage.dpr.activeTiles (packInputs cage.plant a) cage.dpr.targetRegs)[0]?.getD false
  then a else cage.rootShield cage.plant
-- the reflective gate: loading the candidate without asking the checker
#tooth continuous_plant_trace_safe_all_t by mutation amendShieldPolicy := fun _ st candidate _ _ =>
  { st with dpr := stepDprFabric st.dpr (.loadFrames (compilePolicyFrames (policyOfRtl candidate))) }
#tooth rejected_ota_leaves_shield_untouched by mutation amendShieldPolicy := fun _ st candidate _ _ =>
  { st with dpr := stepDprFabric st.dpr (.loadFrames (compilePolicyFrames (policyOfRtl candidate))) }
-- the product-form flux without its `1/B(−δ)` factor is not the Scharfetter–Gummel flux
#tooth jnQuasiFermi_eq_jn by mutation jnQ := fun o c e =>
  .mul (.const (-(cN o c.base e) * deltaN o c e)) (.mul (nQ c e) (bPos e))
-- the hole flux with `B(Δ)` where `B(−Δ)` belongs
#tooth jpQuasiFermi_eq_jp by mutation jpQ := fun o c e =>
  .mul (.const (-(cP o c.base e) * deltaP o c e)) (.mul (pQ c e) (.mul (bPos e) (.var (gpName e))))
-- a node check that accepts everything
#tooth checkDdQuasiFermi_sound by mutation qfNodeOk := fun _ _ _ _ => true
-- a Bernoulli stand-in that is `0` at `0`
#tooth bernoulli_exp by mutation bernOf := fun x e =>
  if 0 < x then x / (e - 1) else if x < 0 then (-x) / (1 - e) else 0

#assert_axioms_tree
end Obend.Tests.ProvablySafePhysicalShield
end
