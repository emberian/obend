module
public import Obend.Law.AmendCli
public import Obend.AssertAxioms
public import Obend.Tactic.Tooth
import all Obend.AssertAxioms
import all Obend.Category.Refines
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
import all Obend.Hardware.ArrayFold
import all Obend.Hardware.DprStutter
import all Obend.Hardware.Fabulous.Net
import all Obend.Hardware.HDL
import all Obend.Hardware.RtlFold
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
import all Obend.Law.AmendCli
import all Obend.Law.Claim
import all Obend.Law.Contract
import all Obend.Law.Inherit
import all Obend.Law.Machine
import all Obend.Law.PointwiseRevise
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
import all Obend.Logic.SeparationFrame
import all Obend.Logic.SuperRefines
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
import all Obend.Slot.SupportSheaf
import all Obend.Slot.World
import all Obend.Spec.C4
import all Obend.Spec.DataWire
import all Obend.Spec.Proofs.C4
import all Obend.Tactic.Cases
import all Obend.Tactic.MonadicReduction
import all Obend.Tactic.Tooth

meta import all Obend.Law.AmendCli

public section
namespace Obend.Tests.PointwiseReviseAndAmend
open Obend.Law.PointwiseRevise Obend.Law.AmendCli
open Obend.Hardware.DprStutter Obend.Hardware.SiliconOuroboros
open Obend.Judge.SvenvsCorrigibility Obend.Judge.CertifierRatchet
open Obend.Logic Lean

set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

def constitutional : Clause 16 := ⟨"recovery", 100, 0xCCCC⟩
def oldFee : Clause 16 := ⟨"fee-one", 5, 0x5555⟩
def newFee : Clause 16 := ⟨"fee-two", 5, 0xAAAA⟩
def entrenchment : Clause 16 := ⟨"disable-recovery", 20, 0x3333⟩
def haltProduction : Clause 16 := ⟨"halt-production", 7, 0x0F0F⟩
def unbackedMint : Clause 16 := ⟨"mint-unbacked", 8, 0xFF00⟩

def initialWorld : World 16 := fun _ => ⟨6, [constitutional, oldFee]⟩
def initialFabric (k : Nat) : DprFabric :=
  { specSlot := k, phase := .active, activeTiles := modelTiles 6, sram := #[], pending := none,
    clampedOut := false, inputs := #[false, false, false, false], targetRegs := #[false],
    neighbors := ⟨#[⟨0xAAAA, false, 0, 1, 2, 3⟩], #[false], #[⟨9, 42, 0⟩], false⟩ }
def initial : LiveState := ⟨initialWorld, initialFabric, 0, 0⟩
def unaffected : ModuleCert 16 := ⟨[1, 2], fun _ => 6, "unaffected-consensus"⟩
def upgrade : AmendmentTurn 16 := ⟨0, [newFee]⟩
def hostile : AmendmentTurn 16 := ⟨0, [newFee, entrenchment]⟩
def restore : AmendmentTurn 16 := ⟨0, [oldFee]⟩

theorem initial_safe (k : Nat) : checkBedrock (initial.world k).model = true := by change checkBedrock 6 = true; decide
example : LiveSafe initial := ⟨initial_safe, fun _ => rfl, fun _ => rfl⟩
example : moduleUsable initial.world unaffected = true := by decide
example : ∃ v R, pointwiseRevise bedrock [constitutional, oldFee] [newFee] = .accepted v R :=
  ⟨7, [constitutional], by decide⟩

#guard pointwiseRevise bedrock [constitutional, oldFee] [newFee] == .accepted 7 [constitutional]
#guard pointwiseRevise bedrock [] [entrenchment] == .refused 6 [] 21
#guard pointwiseRevise bedrock [] [haltProduction] == .refused 6 [] 8
#guard pointwiseRevise bedrock [] [unbackedMint] == .refused 6 [] 9
#guard pointwiseRevise bedrock [] hostile.clauses == .refused 7 [newFee] 21
#guard pointwiseRevise bedrock [constitutional, oldFee] [] == .accepted 6 [constitutional, oldFee]

-- Weight dominates input order, including a conflicting pair of equal-weight laws.
#guard pointwiseRevise bedrock [oldFee, newFee] [] == .accepted 6 [oldFee]
#guard pointwiseRevise bedrock [newFee, oldFee] [] == .accepted 6 [oldFee]
#guard pointwiseRevise bedrock [oldFee, { newFee with priority := 9 }] [] ==
  .accepted 7 [{ newFee with priority := 9 }]

def first := executeLiveAmendment initial upgrade [unaffected]
def second := executeLiveAmendment first.1 hostile [unaffected]
def third := executeLiveAmendment second.1 restore [unaffected]

#guard first.2.evicted == [oldFee]
#guard first.2.skipped == ["unaffected-consensus"]
#guard (executeLiveAmendment initial upgrade [{ unaffected with expected := fun _ => 7 }]).2.skipped.isEmpty
#guard (executeLiveAmendment initial upgrade [{ unaffected with footprint := [0] }]).2.skipped.isEmpty
#guard first.2.frames.size == 1
#guard decodeTileFrames 1 first.2.frames == some (modelTiles 7)
#guard (first.1.fabric 0).phase == .active
#guard (first.1.fabric 0).activeTiles == modelTiles 7
#guard (first.1.fabric 0).neighbors.packets[0]!.hops == 3
#guard (first.1.fabric 1) == initial.fabric 1
#guard (first.1.world 1).clauses == [constitutional, oldFee]
#guard second.2.revision == .refused 7 [newFee] 21
#guard second.2.frames.isEmpty
#guard second.1.generations == 1
#guard (second.1.fabric 0) == first.1.fabric 0
#guard (third.1.world 0).model == 6
#guard third.1.generations == 2
#guard (third.1.fabric 0).neighbors.packets[0]!.hops == 6
#guard sumDeltas third.1.value.entries == 0
#guard deltaAt third.1.value.entries 1 == 3
#guard (executeTrace initial [upgrade, hostile, restore]).generations == 2
#guard (executeTrace initial [upgrade, hostile, restore]).value.entries == third.1.value.entries

-- Real parser, including escaped quotes and braces inside a clause's name.
def roundTrip (t : AmendmentTurn 16) : Bool :=
  match parseAmendBundleJson (renderAmendBundleJson t) with
  | .error _ => false
  | .ok u => u.slot == t.slot && u.clauses == t.clauses
#guard roundTrip upgrade
#guard roundTrip ⟨19, [⟨"quote\" and } and \\ and λ", 3, 65535⟩]⟩
#guard (parseAmendBundleJson "{\"version\":1,\"slot\":0,\"clauses\":[{\"name\":\"bad\",\"priority\":0,\"allowed\":65536}]}").toOption.isNone
#guard (parseAmendBundleJson "{\"version\":2,\"slot\":0,\"clauses\":[]}").toOption.isNone
#guard (parseAmendBundleJson "{\"version\":1,\"slot\":-1,\"clauses\":[]}").toOption.isNone
#guard (parseAmendBundleJson "{\"version\":1,\"slot\":0,\"clauses\":[").toOption.isNone

def jsonLifecycle : Bool :=
  match parseAmendBundleJson (renderAmendBundleJson upgrade) with
  | .error _ => false
  | .ok t =>
    let receipt := (executeLiveAmendment initial t [unaffected]).2
    match Json.parse (renderAmendReceiptJson receipt) with
    | .error _ => false
    | .ok j => (j.getObjValAs? String "status").toOption == some "accepted" &&
        (j.getObjValAs? Nat "witness").toOption == some 7 &&
        (j.getObjValAs? (Array Json) "frames").toOption.map Array.size == some 1
#guard jsonLifecycle
#guard ((Json.parse (renderAmendReceiptJson second.2)) >>= fun j =>
  j.getObjValAs? Nat "minimumCost").toOption == some 21

-- Unicode scalar and malformed framing boundaries in the bounded parser.
#guard roundTrip ⟨0, [⟨"é λ 🙂", 0, 192⟩]⟩
#guard (parseAmendBundleJson r#"{"version":1,"slot":0,"clauses":[{"name":"\uD83D\uDE42","priority":0,"allowed":192}]}"#).toOption.map
  (fun t => (t.clauses.head?).map Clause.name) == some (some "🙂")
#guard (parseAmendBundleJson r#"{"version":1,"slot":0,"clauses":[{"name":"\uD800","priority":0,"allowed":192}]}"#).toOption.isNone
#guard (parseAmendBundleJson r#"{"version":1,"slot":0,"slot":1,"clauses":[]}"#).toOption.isNone
#guard (parseAmendBundleJson r#"{"version":1,"slot":01,"clauses":[]}"#).toOption.isNone
#guard (parseAmendBundleJson r#"{"version":1,"slot":0,"clauses":[],}"#).toOption.isNone
#guard (parseAmendBundleJson r#"{"version":1,"slot":0,"clauses":[]} trailing"#).toOption.isNone
#guard (decodeBundleChars ⟨#[0xC0, 0x80]⟩ 4 0 []).toOption.isNone
#guard (decodeBundleChars ⟨#[0xED, 0xA0, 0x80]⟩ 4 0 []).toOption.isNone
#guard (decodeBundleChars ⟨#[0xF4, 0x90, 0x80, 0x80]⟩ 5 0 []).toOption.isNone
#guard pointwiseRevise bedrock [] [oldFee, {newFee with priority := 9}, entrenchment] ==
  .refused 7 [{newFee with priority := 9}] 27
#guard (traceActions initial 0 [upgrade, hostile, restore]).length == 6
#guard (traceActions initial 1 [upgrade, hostile, restore]).isEmpty

-- Concrete semantic failure witnesses: each floor component protects a real invariant.
example : ¬ DemonicRecovWithin (Det (protocolStep 4)) (protocolRecovery 4)
    (fun s => s = 0) 1 1 := by
  simp [DemonicRecovWithin, protocolStep, protocolRecovery, productionEnabled,
    recoveryEnabled, Det, Enabled, hwStep]
  decide
example : ¬ ViableKernel (protocolStep 2) hwSafe 0 := by
  intro h
  obtain ⟨V, hv, sub, live⟩ := h
  obtain ⟨a, ha⟩ := live 0 hv
  have hh := sub _ ha
  simp [protocolStep, productionEnabled, hwSafe] at hh
example : sumDeltas (rawValue 14) = 1 := by decide

example (ts : List (AmendmentTurn 16)) (count k : Nat) (s : HWState) (hs : hwSafe s) :
    let st := executeTrace initial (ts.take count)
    ViableKernel (protocolStep (st.world k).model) hwSafe s ∧
    DemonicRecovWithin (Det (protocolStep (st.world k).model))
      (protocolRecovery (st.world k).model) (fun x => x = 0) 1 s ∧
    sumDeltas st.value.entries = 0 ∧ (st.fabric k).phase = .active ∧
    (st.fabric k).activeTiles = modelTiles (st.world k).model :=
  executeTrace_protocol_safe initial ts ⟨initial_safe, fun _ => rfl, fun _ => rfl⟩ count k s hs

#tooth pointwiseRevise_entails_bedrock by mutation
  pointwiseRevise := fun B S N =>
    match choose (models N) S with
    | some v => .accepted v (retain S v)
    | none => .refused B.seed [] 0
#tooth pointwiseRevise_vacuous_persistence by mutation models := fun _ _ => true
#tooth pointwiseRevise_maximal_preservation by mutation loss := fun _ _ => 0
#tooth pointwiseRevise_refusal_optimal by mutation repairWitness := fun B _ => B.seed
#tooth pointwiseRevise_supportSheaf_frame_skip by mutation skipModule := fun _ _ => none
#tooth execute_acceptance_sound by mutation executeLiveAmendment := fun st t _ =>
  (st, ⟨t.slot, .accepted bedrock.seed [], [], [], #[]⟩)
#tooth checkedSkip_sound by mutation checkedSkip := fun _ _ c => some c
#tooth bedrock_recovery by mutation checkBedrock := fun v => productionEnabled v && backedValue v
#tooth bedrock_viable by mutation checkBedrock := fun v => recoveryEnabled v && backedValue v
#tooth bedrock_conserved by mutation checkBedrock := fun v => recoveryEnabled v && productionEnabled v

-- This gate is stricter than the whole-tree census: computational extractors
-- and the revision algebra must be constructive. Hardware trace proofs reuse
-- the existing standard-axiom library and are checked by the whole-tree census.
open Lean Elab Command in
run_cmd do
  let targets := [``pointwiseRevise, ``repairWitness, ``parseAmendBundleJson,
    ``executeLiveAmendment, ``executeTrace, ``feeLedger, ``protocolMeaning,
    ``pointwiseRevise_entails_bedrock, ``pointwiseRevise_entails_amendment,
    ``pointwiseRevise_accepts_iff, ``pointwiseRevise_vacuous_equivalence,
    ``pointwiseRevise_maximal_preservation, ``pointwiseRevise_refusal_optimal,
    ``pointwiseRevise_supportSheaf_frame_skip, ``pointwiseRevise_multiTurn_trace_safe,
    ``checkedSkip, ``checkedSkip_sound, ``execute_acceptance_sound, ``execute_refusal_sound]
  for n in targets do
    let axioms ← liftCoreM <| collectAxioms n
    for ax in axioms do
      unless [``propext, ``Quot.sound].contains ax do
        throwError m!"Constructive audit failed: {n} depends on {ax}"
  logInfo "Constructive extraction and theorem audit passed"
#assert_axioms_tree
end Obend.Tests.PointwiseReviseAndAmend
