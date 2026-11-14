module
public import Obend.Judge.CertifierRatchet
public import Obend.Judge.ReflectiveGate
public import Obend.Hardware.SiliconOuroboros
public import Obend.Tactic.Tooth
public import Obend.AssertAxioms
import all Obend.Judge.SvenvsCorrigibility
import all Obend.Judge.CertifierRatchet
import all Obend.Judge.ReflectiveGate
import all Obend.Hardware.DprStutter
import all Obend.Hardware.SiliconOuroboros
meta import all Obend.Judge.SvenvsCorrigibility
meta import all Obend.Judge.CertifierRatchet
meta import all Obend.Judge.ReflectiveGate
meta import all Obend.Hardware.SiliconOuroboros
meta import all Obend.Hardware.DprStutter

-- Full bodies are needed for the imported-tree axiom audit.
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
import all Obend.Hardware.ArrayFold
import all Obend.Hardware.Fabulous.Net
import all Obend.Hardware.HDL
import all Obend.Hardware.RtlFold
import all Obend.Intention
import all Obend.Judge.Class
import all Obend.Judge.Clearing
import all Obend.Judge.Genealogy
import all Obend.Judge.Lrat
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
import all Obend.Apps.ZkNtt.Goldilocks
import all Obend.Consensus.Simplex
import all Obend.Consensus.SimplexProtocol
import all Obend.Crypto.Multilinear
import all Obend.Crypto.Transcript
import all Obend.Judge.Computational
import all Obend.Logic.SeparationFrame
import all Obend.Polis.CapTP
import all Obend.Vault.Mandate

public section
namespace Obend.Tests.SvenvsSiliconOuroboros
open Obend.Judge.SvenvsCorrigibility Obend.Judge.CertifierRatchet Obend.Judge.ReflectiveGate
open Obend.Hardware.HDL Obend.Hardware.DprStutter Obend.Hardware.SiliconOuroboros
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def resetFirewallRtl : RtlExpr := .alu .eq (.inputPort 1) (.const 1)
def rawFirewallRtl : RtlExpr :=
  .mux (.const 1) (.bitNot (.bitNot (.alu .add resetFirewallRtl (.const 0)))) (.const 0)
def expandedFirewallRtl : RtlExpr :=
  .alu .bitOr resetFirewallRtl
    (.alu .bitAnd (.alu .ult (.inputPort 0) (.const 2)) (.alu .eq (.inputPort 1) (.const 0)))
def pol₁ : Policy HWState HWAct := policyOfRtl rawFirewallRtl
def pol₂ : Policy HWState HWAct := policyOfRtl expandedFirewallRtl

def genesisFabric : DprFabric :=
  { specSlot := 1
    phase := .active
    activeTiles := lowerPolicyToTiles pol₁
    sram := compilePolicyFrames pol₁
    pending := none
    clampedOut := false
    inputs := packInputs 0 0
    targetRegs := #[false]
    neighbors := ⟨#[⟨65535#16, false, 0, 1, 2, 3⟩], #[false], #[⟨2,17#64,0⟩], false⟩ }

def gen₀ : SiliconOuroStage := ⟨BaseKernel, id, pol₁, ⟨0, genesisFabric, hwRoot⟩⟩
def proposal₁ : GenerationProposal := ⟨true, true, rawFirewallRtl, .embedBaseProof wdProofCert⟩
def proposal₂ : GenerationProposal := ⟨false, false, expandedFirewallRtl, .fastDecideClosed⟩
def assault : GenerationProposal := ⟨true, true, .const 1, .fastDecideClosed⟩
def gen₁ := stepOuroGeneration gen₀ proposal₁
def gen₂ := stepOuroGeneration gen₁ proposal₂
def gen₃ := stepOuroGeneration gen₂ assault

example : gateCount rawFirewallRtl = 5 := rfl
example : gateCount (rtlOuroOpt rawFirewallRtl) = 1 := rfl
example : gateCount (rtlOuroOpt rawFirewallRtl) < gateCount rawFirewallRtl := by decide
example : [pol₁ 0 0, pol₁ 0 1, pol₁ 2 0, pol₁ 2 1] = [false,true,false,true] := rfl
example : observedBoundaryPort genesisFabric = false := by decide
example : gen₀.cage.dpr.phase = .active := rfl

/-- Every one of the 256 finite cases is checked by a base derivation. -/
theorem first_certificate : gen₀.verifier proposal₁.cert
    (hwPolicySequent gen₀.activePol (policyOfRtl proposal₁.candPolRtl)) = true := by decide

theorem first_kernel : gen₁.verifier = FastKernel := by
  unfold gen₁ stepOuroGeneration
  rw [first_certificate]
  rfl

example : gen₁.rtlPass = rtlOuroOpt := by
  unfold gen₁ stepOuroGeneration
  rw [first_certificate]
  rfl

theorem first_policy : gen₁.activePol = pol₁ := by
  unfold gen₁ stepOuroGeneration
  rw [first_certificate]
  dsimp only [proposal₁, ↓reduceIte]
  exact policyOfRtl_pass rtlOuroOpt evalRtlExpr_rtlOuroOpt rawFirewallRtl

theorem second_certificate : gen₁.verifier proposal₂.cert
    (hwPolicySequent gen₁.activePol (policyOfRtl proposal₂.candPolRtl)) = true := by
  rw [first_kernel, first_policy]
  decide

theorem assault_rejected : gen₂.verifier assault.cert
    (hwPolicySequent gen₂.activePol (policyOfRtl assault.candPolRtl)) = false := by
  unfold gen₂ stepOuroGeneration
  rw [second_certificate]
  dsimp only [proposal₂, ↓reduceIte]
  rw [first_kernel]
  decide

example : gen₃ = gen₂ := generation_refused_before_icap _ _ assault_rejected

/-- Universal facts about the initial silicon, including its physical output
and fixed recovery operator; the subsequent trace uses the library theorem. -/
theorem genesis_invariant : SiliconStageSound gen₀ := by
  refine ⟨baseKernel_sound, fun _ _ _ _ => rfl, ?_, rfl, rfl, rfl, by decide, hw_root_recovery _⟩
  intro s a hs hp
  rcases bv2_cases s with rfl | rfl | rfl | rfl <;>
    rcases bv2_cases a with rfl | rfl | rfl | rfl <;>
    simp_all [gen₀, hwSafe, pol₁, policyOfRtl, rawFirewallRtl, resetFirewallRtl, evalRtlExpr, evalAluOp, hwStep]

theorem first_invariant : SiliconStageSound gen₁ :=
  (silicon_ouroboros_generation_safe gen₀ proposal₁ genesis_invariant).1

theorem second_invariant : SiliconStageSound gen₂ :=
  (silicon_ouroboros_generation_safe gen₁ proposal₂ first_invariant).1

example : gen₁.cage.dpr.phase = .active := first_invariant.phase
example : gen₂.cage.dpr.phase = .active := second_invariant.phase
example : Weaker gen₂.activePol pol₁ := by
  rw [← first_policy]
  exact (silicon_ouroboros_generation_safe gen₁ proposal₂ first_invariant).2

example : (gen₁.cage.dpr.neighbors.packets[0]?.map (·.hops)) = some 3 := by
  unfold gen₁ stepOuroGeneration
  rw [first_certificate]
  simp [siliconDoInstall, stepDprFabric, tickNeighbors, administer, gen₀, genesisFabric, proposal₁]
example : (gen₂.cage.dpr.neighbors.packets[0]?.map (·.hops)) = some 6 := by
  unfold gen₂ stepOuroGeneration
  rw [second_certificate]
  simp only [↓reduceIte]
  unfold gen₁ stepOuroGeneration
  rw [first_certificate]
  simp [siliconDoInstall, stepDprFabric, tickNeighbors, administer, gen₀, genesisFabric, proposal₁, proposal₂]
example : enveloped pol₁ hwRoot (fun _ => 0) 0 = 1 := rfl
example : enveloped pol₂ hwRoot (fun _ => 0) 0 = 0 := rfl
example : pol₂ 2 0 = false := rfl
example : pol₂ 1 0 = true := rfl
example : cageAction gen₂.cage 0 = 0 := by
  unfold cageAction
  rw [second_invariant.phase, second_invariant.fabric]
  unfold gen₂ stepOuroGeneration
  rw [second_certificate]
  unfold gen₁ stepOuroGeneration
  rw [first_certificate]
  rfl

example : checkFastProof .fastSym ⟨[.eqE (.bconst true) (.notE (.bconst false))],
    .eqE (.notE (.bconst false)) (.bconst true)⟩ = true := rfl
example : fastCertSize .fastSym < baseCertSize (symBaseProof (.bconst true) (.notE (.bconst false))) := by decide
example : checkProof wdProofCert wdSequent = true := by decide
example : checkFastProof .fastDecideClosed wdSequent = true := by decide
example : checkFastProof .fastDecideClosed ⟨[],.bconst false⟩ = false := rfl
example : checkFastProof .fastSym ⟨[.eqE (.bconst true) (.bconst false)], .eqE (.bconst true) (.bconst true)⟩ = false := rfl

/-- Corruption happens on the configuration bus after a legitimate proof check.
CRC rejection retains the active bank but leaves the physical fence closed. -/
def damagedFrames : Array TileFrame := (compilePolicyFrames pol₂).modify 0 fun f => { f with crc := f.crc ^^^ 1#64 }
def quarantined : DprFabric := siliconDoInstall gen₂.cage.dpr damagedFrames

theorem damaged_decode : decodeTileFrames gen₂.cage.dpr.activeTiles.size damagedFrames = none := by
  rw [second_invariant.bank]
  change decodeTileFrames 1 damagedFrames = none
  simp only [damagedFrames, compilePolicyFrames, lowerPolicyToTiles, encodeTileFrames, Array.map_singleton, Array.modify] 
  change decodeTileFrames 1 #[{ encodeTileFrame (lowerPolicyToTiles pol₂)[0] with
    crc := (encodeTileFrame (lowerPolicyToTiles pol₂)[0]).crc ^^^ 1#64 }] = none
  simp [decodeTileFrames, frame_crc_bit_flip_rejected]

example : quarantined.phase = .isolateClamped :=
  (silicon_do_install_quarantines _ _ second_invariant.phase damaged_decode).1
example : quarantined.activeTiles = gen₂.cage.dpr.activeTiles :=
  (silicon_do_install_quarantines _ _ second_invariant.phase damaged_decode).2.1
example : observedBoundaryPort quarantined = observedBoundaryPort gen₂.cage.dpr :=
  (silicon_do_install_quarantines _ _ second_invariant.phase damaged_decode).2.2
example : cageAction { gen₂.cage with dpr := quarantined } 0 = hwRoot gen₂.cage.plant := by
  apply cage_fails_closed
  change (siliconDoInstall gen₂.cage.dpr damagedFrames).phase ≠ .active
  rw [(silicon_do_install_quarantines _ _ second_invariant.phase damaged_decode).1]
  decide
example : (quarantined.neighbors.packets[0]?.map (·.hops)) = some 9 := by
  unfold quarantined siliconDoInstall
  simp only [stepDprFabric, tickNeighbors]
  unfold gen₂ stepOuroGeneration
  rw [second_certificate]
  unfold gen₁ stepOuroGeneration
  rw [first_certificate]
  simp [siliconDoInstall, stepDprFabric, tickNeighbors, administer, gen₀, genesisFabric, proposal₁, proposal₂]
example : ¬ SoundKernel acceptAllKernel := accept_all_kernel_unsound "ill-sorted"
example : ¬ KernelSoundnessWitness acceptAllKernel := (loeb_finite_obstruction "ill-sorted").2.2.2.2.2.2

/-- An arbitrary action stream can be interleaved with arbitrarily many forged
or valid generations, with no bounded-generation assumption. -/
example (events : Nat → OuroEvent) (n i : Nat) :
    SiliconStageSound (ouroRun gen₀ events n) ∧
      neighborCoordinate (ouroRun gen₀ events n).cage.dpr.specSlot i ≠ (ouroRun gen₀ events n).cage.dpr.specSlot := by
  have h := recursive_silicon_ouroboros_unconditional gen₀ events genesis_invariant n i
  exact ⟨h.1, h.2.2.2.2.1⟩

example : checkFastProof .fastDecideClosed
    ⟨[], .orE (.var "b" .boolTy) (.notE (.var "b" .boolTy))⟩ = true := by decide
example : checkFastProof .fastDecideClosed
    ⟨[], .eqE (.var "word" .bv4Ty) (.var "word" .bv4Ty)⟩ = true := by decide
example : checkFastProof .fastDecideClosed
    ⟨[], .bitE 0 (.var "word" .bv4Ty)⟩ = false := by decide
example : checkProof (.eqContext .notE (.var "a" .boolTy) (.var "b" .boolTy) .axHyp)
    ⟨[.eqE (.var "a" .boolTy) (.var "b" .boolTy)],
      .eqE (.notE (.var "a" .boolTy)) (.notE (.var "b" .boolTy))⟩ = true := by decide
example : checkProof .primitive
    ⟨[],.eqE (.lut4E 0xAAAA#16 (.bconst true) (.bconst false) (.bconst false) (.bconst false))
      (.bconst true)⟩ = true := by decide

example (events : Nat → CageEvent) (n : Nat) :
    hwSafe (cageRun gen₀ events n).cage.plant ∧
      DemonicRecovWithin (Det hwStep) hwRoot (fun s => s = 0) 1 (cageRun gen₀ events n).cage.plant := by
  have h := recursive_silicon_cage_unconditional gen₀ events genesis_invariant.clock n
  exact ⟨h.plant,h.corrigible⟩

example : SiliconClockSound (stepBusFault gen₂ damagedFrames) :=
  bus_fault_preserves _ _ second_invariant.clock
example : (stepBusFault gen₂ damagedFrames).cage.dpr.phase = .isolateClamped := by
  simp only [stepBusFault, damaged_decode, ↓reduceIte]
  exact (silicon_bad_frames_preserve_bank _ _ damaged_decode).1
example : SiliconClockSound (stepOuroClock (stepBusFault gen₂ damagedFrames) 0) :=
  compute_clock_preserves _ _ (bus_fault_preserves _ _ second_invariant.clock)

example (events : Nat → CageEvent) (n i : Nat) :
    (cageRun gen₀ events n).cage.dpr.neighbors.tiles = gen₀.cage.dpr.neighbors.tiles ∧
    neighborCoordinate gen₀.cage.dpr.specSlot i ≠ (cageRun gen₀ events n).cage.dpr.specSlot := by
  have h := recursive_silicon_cage_trace gen₀ events genesis_invariant.clock n i
  exact h.2.2.2

example (frames : Array TileFrame) :
    observedBoundaryPort (stepDprFabric gen₂.cage.dpr .isolateClamped) =
      observedBoundaryPort gen₂.cage.dpr ∧
    observedBoundaryPort (stepDprFabric (stepDprFabric gen₂.cage.dpr .isolateClamped) (.loadFrames frames)) =
      observedBoundaryPort gen₂.cage.dpr :=
  (install_intermediate_clocks gen₂ frames second_invariant).2.2

example : ∃ p, checkProof p ⟨[.eqE (.bconst true) (.notE (.bconst false))],
    .eqE (.notE (.bconst false)) (.bconst true)⟩ = true :=
  fastSym_conservative _ rfl

example : Derivable wdSequent ∧ checkProof wdProofCert wdSequent = true :=
  fastKernel_conservative_over_base _ _ _ _ .fastDecideClosed (by decide)

example (agent : SiliconCageState → HWAct) :
    InvariantR (Det hwStep) (fun s => s = 0)
      (fun s => cageAction ⟨s, gen₀.cage.dpr, hwRoot⟩ (agent ⟨s, gen₀.cage.dpr, hwRoot⟩))
      (CageFloor (Det hwStep) hwSafe (fun s => s = 0) hwRoot 1) := by
  apply toolAgent_silicon_cage_reachR_safe (Det hwStep) (fun s => s = 0) hwSafe
    (fun s => s = 0) hwRoot 1 gen₀.cage.dpr gen₀.activePol
  · intro s hs; subst s; exact ⟨by decide, hw_root_recovery 0⟩
  · exact genesis_invariant.fabric
  · intro s a t hs hp ht
    dsimp [Det] at ht; subst t
    exact ⟨genesis_invariant.policy s a hs.1 hp, hw_root_recovery _⟩
  · intro s t _ ht
    dsimp [Det] at ht; subst t
    exact ⟨by simp [hwSafe, hwStep, hwRoot], hw_root_recovery _⟩

#tooth Obend.Judge.CertifierRatchet.cgate_rejects by mutation
  Obend.Judge.SvenvsCorrigibility.cgate := fun _ _ cand => cand
#tooth cgate_run_safe_iff by mutation cgateRunOffers := fun _ x _ => x
#tooth checkProof_sem_sound by mutation checkProof := fun _ _ => true
#tooth fastKernel_sound by mutation checkFastProof := fun _ _ => true
#tooth evalRtlExpr_rtlOuroOpt by mutation rtlOuroOpt := fun _ => .const 1
#tooth evalDecodedFabric_lowerPolicyToTiles by mutation lowerPolicyToTiles :=
  fun _ => #[⟨0#16, false, 0, 1, 2, 3⟩]
#tooth silicon_do_install_stutter_safe by mutation siliconDoInstall := fun s _ => s
#tooth cage_fails_closed by mutation cageAction := fun _ a => a
#tooth silicon_ouroboros_generation_safe by mutation
  stepOuroGeneration := fun st p => { st with activePol := policyOfRtl p.candPolRtl }

#assert_axioms_tree
end Obend.Tests.SvenvsSiliconOuroboros
