module
-- Import proof bodies throughout the package cone for the standard axiom census.
import all Obend.Analysis.Diff
import all Obend.Analysis.Flowpipe
import all Obend.Analysis.RealAnalysis
import all Obend.AssertAxioms
import all Obend.Core.AliasExposure
import all Obend.Core.Assumptions
import all Obend.Core.Bidirectional
import all Obend.Core.Brand
import all Obend.Core.CanonicalExtension
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
import all Obend.Core.LegacyAgreement
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
import all Obend.Hardware.Accelerators
import all Obend.Hardware.GeometryCAM
import all Obend.Hardware.HDL
import all Obend.Hardware.Kinematics
import all Obend.Hardware.SymplecticVehicle6Dof
import all Obend.Intention
import all Obend.Judge.Class
import all Obend.Judge.Clearing
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
import all Init.Data.Rat.Basic
public section
namespace Obend.Tests.SymplecticVehicle6DofTest
open Obend Obend.Hardware.SymplecticVehicle6Dof
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

private def policy : VehiclePolicy :=
  ⟨⟨⟨-10,10⟩,⟨-10,10⟩,⟨-10,100⟩⟩,⟨1000,500,400⟩,1,2,1,3,1/2,100,2,2⟩
private def start : VehicleState :=
  ⟨⟨eye,zero⟩,⟨0,0,2⟩,zero,⟨10,zero⟩,⟨2,2,2,0,0,0⟩,
   [⟨4,2,zero,3⟩,⟨4,2,zero,3⟩],⟨⟨300,300,300⟩,4,⟨1,1,1⟩⟩⟩
private def nominalLoad : StructuralLoad := ⟨2,1/10,2,12,100,2⟩
private def burn : VehicleCommand :=
  ⟨1,⟨0,0,1⟩,⟨0,0,1/2⟩,[⟨2,1⟩,⟨2,1⟩],2,1,1,1,⟨0,0⟩,zero,zero,zero,
   ⟨1/10,1/10,2,1/8100000000,2,1/4⟩,nominalLoad,none⟩
private def ascent : VehicleTurn := ⟨burn,stepVehicle start burn⟩
private def coastBase : VehicleCommand :=
  { burn with draws := [⟨0,0⟩,⟨0,0⟩]
              heat := ⟨1/10,1/10,0,0,2,0⟩ }
private def separation : Separation :=
  let pre := stageView (poweredStep ascent.after coastBase)
  ⟨5,⟨1,1,1,0,0,0⟩,⟨0,0,1⟩,(separateStage pre (pre.mass-5) ⟨0,0,1⟩).2⟩
private def stageCommand : VehicleCommand := { coastBase with separation := some separation }
private def insertion : VehicleTurn := ⟨stageCommand,stepVehicle ascent.after stageCommand⟩
private def entryCommand : VehicleCommand :=
  { coastBase with omega := ⟨0,0,2⟩
                   increment := ⟨0,0,1⟩
                   externalForce := ⟨0,0,-1⟩
                   heat := ⟨1/10,1/10,4,1/8100000000,2,1/4⟩ }
private def entry : VehicleTurn := ⟨entryCommand,stepVehicle insertion.after entryCommand⟩
private def mission : VehicleMission := ⟨policy,start,#[ascent,insertion,entry]⟩
private def cert : VehicleCertificate := ⟨wireTag⟩

example : checkState policy start = true := by decide +kernel
example : checkTurn policy start ascent = true := by decide +kernel
example : checkTurn policy ascent.after insertion = true := by decide +kernel
example : checkTurn policy insertion.after entry = true := by decide +kernel
example : se3Vehicle6DofJudge.check 0 mission cert = .ok := by change (if cert.format == wireTag then judgeVehicle mission else .uncovered) = .ok; decide +kernel
example : SafeTrace policy start mission.turns.toList := by
  exact (se3Vehicle6DofJudge_sound mission cert 0 (by change (if cert.format == wireTag then judgeVehicle mission else .uncovered) = .ok; decide +kernel)).1
example : se3Vehicle6DofJudge.Fragment mission := se3Vehicle6DofJudge_fragment_inhabited mission
example : ascent.after.pose.rotation ≠ eye := by decide +kernel
example : insertion.after.dry.mass = 5 ∧ entry.after.thermal.ablator = 7/2 := by decide +kernel
example : normSq (gimbalDirection ⟨1/3,1/5⟩) = 1 := gimbalDirection_unit _
example : ¬ SO3 (eulerAttitude eye ⟨0,0,1⟩) := by decide +kernel

private def oneTurn (t : VehicleTurn) : VehicleMission := ⟨policy,start,#[t]⟩
private def drifted : VehicleTurn :=
  { ascent with after := { ascent.after with pose := ⟨matScale 2 eye,ascent.after.pose.pos⟩ } }
private def negativeTank : VehicleTurn :=
  { ascent with after := { ascent.after with tanks := [⟨-1,1,zero,3⟩] } }
private def overdraw : VehicleTurn :=
  { ascent with command := { burn with draws := [⟨5,1⟩,⟨2,1⟩] } }
private def gimbalViolation : VehicleTurn := { ascent with command := { burn with gimbal := ⟨2,0⟩ } }
private def mixtureViolation : VehicleTurn := { ascent with command := { burn with draws := [⟨1,0⟩,⟨1,0⟩] } }
private def lowFeedPolicy : VehiclePolicy := { policy with feedFloor := 4 }
private def wrongStageMass : Separation :=
  { separation with jettison := { separation.jettison with mass := 6 } }
private def mismatchedStage : VehicleTurn :=
  { insertion with command := { stageCommand with separation := some wrongStageMass } }
private def burnThrough : VehicleTurn :=
  { ascent with after := { ascent.after with thermal := ⟨ascent.after.thermal.kelvin,0,⟨1,1,1⟩⟩ } }
private def overTemperature : VehicleTurn :=
  { ascent with after := { ascent.after with thermal := ⟨⟨300,501,300⟩,3,⟨1,1,1⟩⟩ } }
private def overloaded : VehicleTurn :=
  { ascent with command := { burn with load := { nominalLoad with dynamicPressure := 1000 } } }
private def badSeparation : Separation :=
  { separation with jettison := { separation.jettison with momentum := zero } }
private def badStage : VehicleTurn :=
  { insertion with command := { stageCommand with separation := some badSeparation } }
private def outside : VehicleTurn :=
  { ascent with after := { ascent.after with pose := ⟨ascent.after.pose.rotation,⟨0,0,101⟩⟩ } }
private def disconnected : VehicleTurn :=
  { entry with after := { entry.after with momentum := zero } }

example : judgeVehicle (oneTurn drifted) = .refused .attitude [0] := by decide +kernel
example : judgeVehicle (oneTurn negativeTank) = .refused .mass [0] := by decide +kernel
example : judgeVehicle (oneTurn overdraw) = .refused .mass [0] := by decide +kernel
example : judgeVehicle (oneTurn gimbalViolation) = .refused .propulsion [0] := by decide +kernel
example : judgeVehicle (oneTurn mixtureViolation) = .refused .propulsion [0] := by decide +kernel
example : judgeVehicle (oneTurn burnThrough) = .refused .thermal [0] := by decide +kernel
example : judgeVehicle (oneTurn overTemperature) = .refused .thermal [0] := by decide +kernel
example : judgeVehicle (oneTurn overloaded) = .refused .structural [0] := by decide +kernel
example : judgeVehicle ⟨policy,start,#[ascent,badStage]⟩ = .refused .staging [1] := by decide +kernel
example : judgeVehicle (oneTurn outside) = .refused .corridor [0] := by decide +kernel
example : judgeVehicle ⟨policy,start,#[ascent,insertion,disconnected]⟩ = .refused .dynamics [2] := by decide +kernel

example : judgeVehicle ⟨lowFeedPolicy,start,#[ascent]⟩ = .refused .propulsion [0] := by decide +kernel
example : judgeVehicle ⟨policy,start,#[ascent,mismatchedStage]⟩ = .refused .staging [1] := by decide +kernel
example : SPD (vehicleInertia entry.after) := by
  exact vehicleInertia_spd policy entry.after
    ((se3Vehicle6DofJudge_sound mission cert 0 (by change (if cert.format == wireTag then judgeVehicle mission else .uncovered) = .ok; decide +kernel)).2.2 entry (by simp [mission]))

private def underreportedAxial : VehicleTurn :=
  { ascent with command := { burn with load := { nominalLoad with axialForceMagnitude := 0 } } }
example : judgeVehicle (oneTurn underreportedAxial) = .refused .structural [0] := by decide +kernel

example : se3Vehicle6DofJudge.check 0 mission ⟨"unsupported"⟩ = .uncovered := by
  change (if "unsupported" == wireTag then judgeVehicle mission else .uncovered) = .uncovered
  decide +kernel
example : centerOfMass ⟨4,zero⟩ [⟨2,⟨3,0,0⟩⟩] = ⟨1,0,0⟩ := by decide +kernel
example : centerOfMass ⟨4,zero⟩ [⟨1,⟨3,0,0⟩⟩] = ⟨3/5,0,0⟩ := by decide +kernel
example : (parallelAxis ⟨1,1,0⟩).b = -1 := by decide +kernel

-- Each experiment removes one executable safety clause while retaining the semantic predicate.
#tooth checkTurn_sound by
  mutation checkClause := fun p s t k => if k == .attitude then true else decide (ClauseHolds p s t k)
#tooth checkTurn_sound by
  mutation checkClause := fun p s t k => if k == .mass then true else decide (ClauseHolds p s t k)
#tooth checkTurn_sound by
  mutation checkClause := fun p s t k => if k == .propulsion then true else decide (ClauseHolds p s t k)
#tooth checkTurn_sound by
  mutation checkClause := fun p s t k => if k == .thermal then true else decide (ClauseHolds p s t k)
#tooth checkTurn_sound by
  mutation checkClause := fun p s t k => if k == .structural then true else decide (ClauseHolds p s t k)
#tooth checkTurn_sound by
  mutation checkClause := fun p s t k => if k == .staging then true else decide (ClauseHolds p s t k)
#tooth checkTurn_sound by
  mutation checkClause := fun p s t k => if k == .corridor then true else decide (ClauseHolds p s t k)
#tooth checkTurn_sound by
  mutation checkClause := fun p s t k => if k == .dynamics then true else decide (ClauseHolds p s t k)
#tooth cayleyDelta_so3 by
  mutation cayleyDelta := fun u => matAdd eye (skew3 u)
#tooth freeRigidBody_conserves_spatial_momentum by
  mutation freeRigidBody := fun s u => ⟨cayleyStep s.attitude u,s.bodyMomentum⟩
#tooth compositeInertia_lower_bound by
  mutation parallelAxis := fun r => matScale (-1) (outer r)
#tooth staging_conserves_total_mass_and_linear_momentum by
  mutation separateStage := fun pre m impulse =>
    (⟨m,add pre.momentum impulse,pre.pos⟩,⟨pre.mass-m,impulse,pre.pos⟩)
#tooth stepThermalNetwork_nonneg_kelvin by
  mutation stepThermalNetwork := fun s _ => ⟨⟨-1,s.kelvin.y,s.kelvin.z⟩,s.ablator,s.capacity⟩
#tooth checkTrace_iff by
  mutation checkTrace := fun p s _ => checkState p s

#tooth se3Vehicle6DofJudge_sound by
  mutation judgeVehicle := fun _ => .ok
#tooth checkTraceExec_eq_spec by
  mutation checkTraceExec := fun _ _ _ => true
#tooth stepThermalNetwork_passive by
  mutation stepThermalNetwork := fun s _ => ⟨⟨s.kelvin.x+1,s.kelvin.y,s.kelvin.z⟩,s.ablator,s.capacity⟩

private def fullInertia : InertiaTensor3 := ⟨4,5,6,1,1,1⟩
example : SylvesterPos fullInertia := by decide +kernel
example : SPD fullInertia.toMat := sylvester_spd fullInertia (by decide +kernel)
example : checkState policy { start with dryInertia := fullInertia } = true := by decide +kernel
example : ¬ SylvesterPos (⟨1,1,1,2,0,0⟩ : InertiaTensor3) := by decide +kernel
private def coupledThruster : GimbaledThruster := ⟨⟨1/3,1/5⟩,12,⟨1,2,3⟩⟩
example : normSq (gimbalDirection coupledThruster.angles) = 1 := gimbalDirection_unit _
example : coupledThruster.force.x ≠ 0 ∧ coupledThruster.force.y ≠ 0 ∧ coupledThruster.force.z ≠ 0 := by decide +kernel
example : (coupledThruster.torque zero).x ≠ 0 ∧ (coupledThruster.torque zero).y ≠ 0 ∧
    (coupledThruster.torque zero).z ≠ 0 := by decide +kernel
private def weightedHeat : ThermalState := ⟨⟨300,200,100⟩,4,⟨2,3,4⟩⟩
private def conduction : ThermalCommand := ⟨1,1,0,0,0,0⟩
example : ThermalCFL weightedHeat conduction := by decide +kernel
example : thermalEnergy (stepThermalNetwork weightedHeat conduction) = thermalEnergy weightedHeat := by decide +kernel
example : (stepThermalNetwork weightedHeat conduction).kelvin.x = 250 := by decide +kernel
example : (1 : Rat) ∈ accelerationSlice 0 0 1 2 := by decide +kernel
example : ¬ (3 : Rat) ∈ accelerationSlice 0 0 1 2 := by decide +kernel
example : ¬ boxSubset (sweptTube zero zero ⟨2,2,2⟩ 1) ⟨⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩ = true := by decide +kernel
example : (1 : Rat) ∈ accelerationSlice 0 0 1 4 := by
  have h := affineAccelerationSlice_encloses 0 0 1 3 1 4 (by decide +kernel) (by decide +kernel)
  have he : (0+0*1+1*(1*1)/2+3*(1*1*1)/6 : Rat) = 1 := by decide +kernel
  rw [he] at h; exact h
#tooth sylvester_spd by
  mutation SylvesterPos := fun j => 0 < j.ixx ∧ 0 < j.iyy ∧ 0 < j.izz
#tooth gimbalDirection_unit by
  mutation gimbalDirection := fun u => ⟨u.pitch,u.yaw,1⟩
#tooth gimbaled_torque_orthogonal by
  mutation GimbaledThruster.torque := fun g _ => g.force
#tooth stepThermalNetwork_energy_balance by
  mutation thermalEnergy := fun s => s.kelvin.x+s.kelvin.y+s.kelvin.z
#tooth accelerationSlice_encloses by
  mutation accelerationSlice := fun x v t _ => ⟨x+v*t,x+v*t⟩
#tooth turn_intersample_safe by
  mutation boxSubset := fun _ _ => true

-- The Rat representation carries proof dependencies on the standard axioms. The
-- computational functions must remain compilable: no choice-based Type extraction.
open Lean in
run_cmd do
  let env ← getEnv
  for n in [``stepVehicle, ``checkTraceExec, ``firstFault, ``judgeVehicle] do
    if isNoncomputable env n then
      throwError "nonconstructive executable: {n}"
  logInfo "Vehicle update, array checker, and refusal extraction are computable"
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for (name, info) in env.constants.map₁.toList do
    let some idx := env.getModuleIdxFor? name | continue
    unless env.header.moduleNames[idx.toNat]? == some `Obend.Hardware.SymplecticVehicle6Dof do continue
    if let .thmInfo _ := info then
      if !name.isInternal && !name.isInternalDetail && name.components.getLast? != some `sizeOf_spec then
        if ← liftTermElabM (Obend.AssertAxioms.closedStatement info.type) then
          throwError "Closed library theorem: {name}"
  logInfo "Obend.Hardware.SymplecticVehicle6Dof: zero closed theorems"
#assert_axioms_tree
end Obend.Tests.SymplecticVehicle6DofTest
