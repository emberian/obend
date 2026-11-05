import Obend.Tactic.Tooth
import Obend.Vault.Escrow
import Obend.Spec.Syntax
import Obend.Spec.Parse
import Obend.Spec.Elaborate
import Obend.Spec.FrontEnd
import Obend.Format.Reader

open Obend.Core.Data (Data)
open Obend.Law
open Obend.Spec.Law
open Obend.Spec.LawCompile (reqOf)
open Obend.Spec.Syntax
open Obend.Spec.Elaborate
open Obend.Logic
open Obend.Vault.Escrow
open Obend.Format

set_option autoImplicit false

/-!
# Metasystem Verification Suite: Pluggable `FormatReader`, Isar Proof Blocks & Escrow Seam Closure

Covers:
1. `Obend.Vault.Escrow` non-trivial `escrowLaw` & `prepaidLeaseLaw`, `escrowCellContract` &
   `prepaidLeaseCellContract`, bridge theorems, and refusal teeth (overdraws, replay rollbacks,
   `settled` rollbacks, `writeOnce` violations).
2. Isar-style `claim ... by ...`, `law ... by ...`, and `contract ... for ... by ...` surface syntax,
   parser, `ObligationTree` elaboration (`elaborateIsarProofTree`), and `CellContract` elaboration
   (`elaborateCellContract`).
3. All 4 verified `FormatReader` instances (`obnb@1`, `usd-stage@1`, `dfa-policy@1`,
   `dreggnet-deploy@1`), their `data_roundtrip` theorems, `lowerToObend` elaboration through
   `Obend.Spec.Elaborate` & `Obend.Spec.FrontEnd.accept`, and `#tooth` mutation tests.
-/

/-! ## Part 1: `Escrow.lean` Seam Closure & Non-Trivial `LawExpr` / `CellContract` Verification -/

/-- `escrowKindCell` and `prepaidLeaseKindCell` enforce non-trivial laws, never `trivialLaw`. -/
theorem escrow_and_lease_kinds_nontrivial :
    escrowKindCell.law = escrowLaw ∧
    prepaidLeaseKindCell.law = prepaidLeaseLaw ∧
    escrowKindCell.law ≠ trivialLaw ∧
    prepaidLeaseKindCell.law ≠ trivialLaw := by
  refine ⟨rfl, rfl, by decide, by decide⟩

def sampleFacts : Facts := ⟨some 1, some 2, 100, 1⟩

def escrowAfterDepositA : EscrowState :=
  { status := upd openedEscrow.status .A .deposited
    amount := upd openedEscrow.amount .A 500
    recv   := openedEscrow.recv
    paid   := openedEscrow.paid }

theorem escrowDepositAOp : EscrowOp openedEscrow escrowAfterDepositA :=
  .deposit openedEscrow .A 500 rfl

def escrowAfterDepositB : EscrowState :=
  { status := upd escrowAfterDepositA.status .B .deposited
    amount := upd escrowAfterDepositA.amount .B 1200
    recv   := escrowAfterDepositA.recv
    paid   := escrowAfterDepositA.paid }

theorem escrowDepositBOp : EscrowOp escrowAfterDepositA escrowAfterDepositB :=
  .deposit escrowAfterDepositA .B 1200 rfl

def escrowSettledState : EscrowState :=
  { status := fun _ => .consumed
    amount := escrowAfterDepositB.amount
    recv   := fun p => escrowAfterDepositB.recv p + escrowAfterDepositB.amount p.other
    paid   := fun s => escrowAfterDepositB.paid s + escrowAfterDepositB.amount s }

theorem escrowSettleOp : EscrowOp escrowAfterDepositB escrowSettledState :=
  .settle escrowAfterDepositB rfl rfl

/-- Valid deposit and settle transitions satisfy `escrowLaw` and are admitted by `escrowCellContract`. -/
theorem escrow_valid_transitions_admitted :
    escrowLaw.denote sampleFacts (some (escrowStateToData openedEscrow))
      (escrowStateToData escrowAfterDepositA) = true ∧
    escrowLaw.denote sampleFacts (some (escrowStateToData escrowAfterDepositB))
      (escrowStateToData escrowSettledState) = true ∧
    Admits escrowCellContract.law (escrowStateToData openedEscrow)
      (escrowStateToData escrowAfterDepositA) (reqOf "alice" "alice" 0 10 writeO sampleFacts) ∧
    Admits escrowCellContract.law (escrowStateToData escrowAfterDepositB)
      (escrowStateToData escrowSettledState) (reqOf "alice" "alice" 0 10 writeO sampleFacts) :=
  ⟨escrowOp_satisfies_escrowLaw sampleFacts escrowDepositAOp,
   escrowOp_satisfies_escrowLaw sampleFacts escrowSettleOp,
   (escrowOp_admitted_by_contract sampleFacts escrowDepositAOp "alice" "alice" 0 10).1,
   (escrowOp_admitted_by_contract sampleFacts escrowSettleOp "alice" "alice" 0 10).1⟩

/-- Rolling back a settled escrow (`settled = 1`) to an unsettled state (`settled = 0`) is
    refused by `escrowLaw` and rejected by `escrowCellContract`. -/
theorem escrow_rollback_settled_rejected :
    escrowLaw.denote sampleFacts (some (escrowStateToData escrowSettledState))
      (escrowStateToData openedEscrow) = false ∧
    Refuses escrowCellContract.stepRel (escrowStateToData escrowSettledState)
      (escrowStateToData openedEscrow) (reqOf "mallory" "mallory" 0 10 writeO sampleFacts) "escrowLaw" ∧
    ¬ Admits escrowCellContract.law (escrowStateToData escrowSettledState)
      (escrowStateToData openedEscrow) (reqOf "mallory" "mallory" 0 10 writeO sampleFacts) :=
  escrow_unsettled_rollback_refused sampleFacts escrowSettledState openedEscrow rfl rfl
    "mallory" "mallory" 0 10

def sampleLeaseTerms : LeaseTerms where
  rent   := 250
  period := 10
  start  := 100
  count  := 4
  budget := 1000
  lessor := 1
  lessee := 2
  asset  := 0

def leaseSt0 : LeaseState := openLease sampleLeaseTerms
def leaseSt1 : LeaseState := advance sampleLeaseTerms leaseSt0

theorem sampleLease_dischargeOk :
    DischargeOk sampleLeaseTerms leaseSt0 105 250 0 := by
  refine ⟨.inr (by decide), rfl, by decide, rfl, by decide⟩

/-- Valid `PrepaidLease` `advance` transition satisfies `prepaidLeaseLaw` and is admitted by
    `prepaidLeaseCellContract`. -/
theorem prepaidLease_valid_advance_admitted :
    prepaidLeaseLaw.denote sampleFacts (some (leaseStateToData sampleLeaseTerms leaseSt0))
      (leaseStateToData sampleLeaseTerms leaseSt1) = true ∧
    Admits prepaidLeaseCellContract.law (leaseStateToData sampleLeaseTerms leaseSt0)
      (leaseStateToData sampleLeaseTerms leaseSt1) (reqOf "bob" "bob" 0 10 writeO sampleFacts) :=
  ⟨lease_advance_satisfies_prepaidLeaseLaw sampleFacts sampleLeaseTerms leaseSt0 105 250 0
     sampleLease_dischargeOk (by decide),
   (lease_advance_admitted_by_contract sampleFacts sampleLeaseTerms leaseSt0 105 250 0
     sampleLease_dischargeOk (by decide) "bob" "bob" 0 10).1⟩

def plantedOverdrawnLeaseState : LeaseState where
  nextDue         := 120
  dischargedCount := 2
  remaining       := 0
  drawn           := 1250 -- exceeds budget = 1000!

/-- Planted overdraw (`drawn = 1250 > budget = 1000`) is refused by `prepaidLeaseLaw` and
    rejected by `prepaidLeaseCellContract`. -/
theorem prepaidLease_planted_overdraw_rejected :
    prepaidLeaseLaw.denote sampleFacts (some (leaseStateToData sampleLeaseTerms leaseSt1))
      (leaseStateToData sampleLeaseTerms plantedOverdrawnLeaseState) = false ∧
    Refuses prepaidLeaseCellContract.stepRel (leaseStateToData sampleLeaseTerms leaseSt1)
      (leaseStateToData sampleLeaseTerms plantedOverdrawnLeaseState)
      (reqOf "mallory" "mallory" 0 10 writeO sampleFacts) "prepaidLeaseLaw" ∧
    ¬ Admits prepaidLeaseCellContract.law (leaseStateToData sampleLeaseTerms leaseSt1)
      (leaseStateToData sampleLeaseTerms plantedOverdrawnLeaseState)
      (reqOf "mallory" "mallory" 0 10 writeO sampleFacts) :=
  lease_overdraw_refused sampleFacts sampleLeaseTerms leaseSt1 plantedOverdrawnLeaseState
    (by decide) "mallory" "mallory" 0 10

/-- Planted replay rollback (`dischargedCount` decreasing from 1 to 0) is refused by
    `prepaidLeaseLaw` and rejected by `prepaidLeaseCellContract`. -/
theorem prepaidLease_planted_replay_rollback_rejected :
    prepaidLeaseLaw.denote sampleFacts (some (leaseStateToData sampleLeaseTerms leaseSt1))
      (leaseStateToData sampleLeaseTerms leaseSt0) = false ∧
    Refuses prepaidLeaseCellContract.stepRel (leaseStateToData sampleLeaseTerms leaseSt1)
      (leaseStateToData sampleLeaseTerms leaseSt0)
      (reqOf "mallory" "mallory" 0 10 writeO sampleFacts) "prepaidLeaseLaw" ∧
    ¬ Admits prepaidLeaseCellContract.law (leaseStateToData sampleLeaseTerms leaseSt1)
      (leaseStateToData sampleLeaseTerms leaseSt0)
      (reqOf "mallory" "mallory" 0 10 writeO sampleFacts) :=
  lease_rollback_dischargedCount_refused sampleFacts sampleLeaseTerms leaseSt1 leaseSt0
    (by decide) "mallory" "mallory" 0 10

/-- Planted mutation of `writeOnce "budget"` (changing `budget` from 1000 to 2000 after init)
    is refused by `prepaidLeaseLaw`. -/
def mutatedBudgetTerms : LeaseTerms := { sampleLeaseTerms with budget := 2000 }

example :
    prepaidLeaseLaw.denote sampleFacts (some (leaseStateToData sampleLeaseTerms leaseSt0))
      (leaseStateToData mutatedBudgetTerms leaseSt1) = false := by decide +kernel

#tooth escrow_rollback_settled_rejected by mutation
  Obend.Vault.Escrow.escrowLaw := Obend.Vault.Escrow.trivialLaw

#tooth prepaidLease_planted_overdraw_rejected by mutation
  Obend.Vault.Escrow.prepaidLeaseLaw := Obend.Vault.Escrow.trivialLaw

/-! ## Part 2: Isar-Style `contract` & Structured Proof Blocks in `.obend` -/

def sampleIsarObendSource : String :=
"edition ObjectiveBend 1

record Counter:
  count: Nat
  limit: Nat
  bump: Nat

spec BaseCounter for Counter:
  def bump() -> Nat:
    self.count + 1n
  claim monotoneBump(c: Counter) given c.count <= c.limit by weave: c.count <= c.count + 1n
    have hStep: c.count <= c.count + 1n by omega
    show c.count <= c.count + 1n by weave

law counterMonotone by omega: monotone(count) and new.count <= new.limit

contract CounterContract for Counter by frame:
  invariant: self.count <= self.limit
  law: monotone(count) and new.count <= new.limit
  have hMono: self.count <= self.count + 1n by omega
  show self.count <= self.limit by frame

def entry() -> Nat:
  fix(BaseCounter, {count: 0n, limit: 10n, bump: 0n}).bump
"

def checkIsarSourceElaboration : Bool :=
  match elaborateIsarSource "VaultIsarSpec" sampleIsarObendSource with
  | .ok (mod, tree, contracts) =>
      mod.name == "VaultIsarSpec" &&
      mod.contracts.length == 1 &&
      mod.lawMethods == [("counterMonotone", .omega)] &&
      contracts.length == 2 &&
      tree.nodeCount > 3 &&
      tree.methods.contains .weave &&
      tree.methods.contains .omega &&
      tree.methods.contains .frame
  | .error _ => false

#guard checkIsarSourceElaboration == true

/-- Verify `elaborateIsarProofTree` and `elaborateCellContract` directly in the kernel. -/
def sampleContractDecl : ContractDecl where
  name := "CounterContract"
  targetType := "Counter"
  invariant := some (.binary "<=" (.member (.var "self") "count") (.member (.var "self") "limit"))
  law := some (.and (.monotone "count") (.leROff (.field "count") (.field "limit") 0))
  method := some .frame
  steps := [
    .haveStep "hMono" (.binary "<=" (.member (.var "self") "count") (.binary "+" (.member (.var "self") "count") (.nat "1"))) .omega,
    .showStep (.binary "<=" (.member (.var "self") "count") (.member (.var "self") "limit")) .frame
  ]

#guard (elaborateContractProofTree sampleContractDecl).methods == [.frame, .omega, .frame, .frame]
#guard (elaborateContractProofTree sampleContractDecl).nodeCount == 4

def sampleObligationTree : Obend.Logic.ObligationTree :=
  .contractNode "CounterContract" "Counter" .frame
    (.stepNode "hMono" .omega (.boolean true)
      (.stepNode "show" .frame (.boolean true)
        (.leaf "CounterContract.preserves" .frame none)))

theorem sampleContractProofTree_properties :
    0 < sampleObligationTree.nodeCount ∧
    sampleObligationTree.methods = [.frame, .omega, .frame, .frame] :=
  ⟨Obend.Logic.ObligationTree.nodeCount_pos _, rfl⟩

/-- Negative test: unknown Isar proof method in `claim ... by ...` is rejected by parser. -/
def badIsarMethodSource : String :=
"edition ObjectiveBend 1
record Box:
  v: Nat
  id: Nat
spec S for Box:
  def id() -> Nat:
    self.v
  claim bad(b: Box) by magicWand: true
"

#guard (elaborateIsarSource "BadIsar" badIsarMethodSource).isOk == false

/-! ## Part 3: Concrete `FormatReader` Instances, Roundtrips & FrontEnd Acceptance -/

/-! ### 3.1 `obnbReader` (`"obnb@1"`) -/

def sampleObnbText : String :=
"---
format: obnb@1
title: QuantumWalkWorkbook
law: walkProgressLaw
field: progress
maxBound: 50
---
# Introduction
cell-obend: initStep:progress:3
cell-lean: walk_monotone_bridge:WorkbookSpec"

def sampleObnbAST : ObnbWorkbook where
  title := "QuantumWalkWorkbook"
  lawName := "walkProgressLaw"
  boundField := "progress"
  maxBound := 50
  cells := [
    .prose "Introduction" "Introduction",
    .obend "initStep" "progress" 3,
    .leanBridge "walk_monotone_bridge" "WorkbookSpec"
  ]

theorem obnb_roundtrip_concrete :
    obnbOfCoreData (obnbToCoreData sampleObnbAST) = some sampleObnbAST :=
  obnb_data_roundtrip sampleObnbAST

theorem sampleElaboratedCellContract_holds_top (d : Data) :
    Holds (elaborateCellContractFromFields "VaultIsarSpec" [("count", "Nat"), ("limit", "Nat")] sampleContractDecl).invariant d :=
  holds_top_invariant d

#guard obnbReader.ofCoreData (obnbReader.toCoreData sampleObnbAST) == some sampleObnbAST
#guard (obnbReader.parse sampleObnbText).toOption == some sampleObnbAST
#guard acceptsReaderAST obnbReader sampleObnbAST == true
#guard (elaborateLoweredModule (obnbReader.lowerToObend sampleObnbAST)).isOk == true
#guard (obnbReader.parse "format: wrong@1\ntitle: X").isOk == false

#tooth obnb_data_roundtrip by mutation
  Obend.Format.obnbToCoreData := fun _ => Data.record []

/-! ### 3.2 `usdStageReader` (`"usd-stage@1"`) -/

def sampleUsdText : String :=
"#usda 1.0
stage: CryoPackageStage
subLayers:substrate.usda,interposer.usda
maxThermalMk: 300000
def Xform Die0 10 20 5 1 2 4000
over Die0_ThermalOverride 3 0 0 1 0 4200"

def sampleUsdAST : UsdStage where
  stageName := "CryoPackageStage"
  subLayers := ["substrate.usda", "interposer.usda"]
  maxThermalMk := 300000
  baseXform := {
    layerName := "Die0"
    isOver := false
    posX := 10
    posY := 20
    posZ := 5
    velX := 1
    velY := 2
    thermalMk := 4000
  }
  overrides := [{
    layerName := "Die0_ThermalOverride"
    isOver := true
    posX := 3
    posY := 0
    posZ := 0
    velX := 1
    velY := 0
    thermalMk := 4200
  }]

theorem usdStage_roundtrip_concrete :
    usdStageOfCoreData (usdStageToCoreData sampleUsdAST) = some sampleUsdAST :=
  usdStage_data_roundtrip sampleUsdAST

#guard usdStageReader.ofCoreData (usdStageReader.toCoreData sampleUsdAST) == some sampleUsdAST
#guard (usdStageReader.parse sampleUsdText).toOption == some sampleUsdAST
#guard (usdStageReader.parse (usdStageReader.render sampleUsdAST)).toOption == some sampleUsdAST
#guard acceptsReaderAST usdStageReader sampleUsdAST == true
#guard (elaborateLoweredModule (usdStageReader.lowerToObend sampleUsdAST)).isOk == true
#guard (usdStageReader.parse "stage: NoHeader\ndef Xform A 0 0 0 0 0 0").isOk == false

#tooth usdStage_data_roundtrip by mutation
  Obend.Format.usdStageToCoreData := fun _ => Data.record []

/-! ### 3.3 `dfaPolicyReader` (`"dfa-policy@1"`) -/

def sampleDfaText : String :=
"format: dfa-policy@1
policy: PromptTranscriptConfinement
initial: 0
accepting: 2,3
transition: 0 1 2
transition: 2 1 3
hole: systemPromptSlot 77 0"

def sampleDfaAST : DfaPolicy where
  policyName := "PromptTranscriptConfinement"
  initialState := 0
  acceptingStates := [2, 3]
  transitions := [⟨0, 1, 2⟩, ⟨2, 1, 3⟩]
  holes := [⟨"systemPromptSlot", 77, 0⟩]

theorem dfaPolicy_roundtrip_concrete :
    dfaPolicyOfCoreData (dfaPolicyToCoreData sampleDfaAST) = some sampleDfaAST :=
  dfaPolicy_data_roundtrip sampleDfaAST

#guard dfaPolicyReader.ofCoreData (dfaPolicyReader.toCoreData sampleDfaAST) == some sampleDfaAST
#guard (dfaPolicyReader.parse sampleDfaText).toOption == some sampleDfaAST
#guard (dfaPolicyReader.parse (dfaPolicyReader.render sampleDfaAST)).toOption == some sampleDfaAST
#guard acceptsReaderAST dfaPolicyReader sampleDfaAST == true
#guard (elaborateLoweredModule (dfaPolicyReader.lowerToObend sampleDfaAST)).isOk == true
#guard (dfaPolicyReader.parse "policy: MissingHeader\ninitial: 0").isOk == false

#tooth dfaPolicy_data_roundtrip by mutation
  Obend.Format.dfaPolicyToCoreData := fun _ => Data.record []

/-! ### 3.4 `deploymentTopologyReader` (`"dreggnet-deploy@1"`) -/

def sampleDeployText : String :=
"format: dreggnet-deploy@1
topology: EnclaveVaultMesh
totalMandateCap: 5000
requiredTeePin: 9001
grain: IngressGrain 9001 1000
grain: SettlementGrain 9001 4000
channel: sturdySettle IngressGrain SettlementGrain 12"

def sampleDeployAST : DeploymentTopology where
  topologyName := "EnclaveVaultMesh"
  totalMandateCap := 5000
  requiredTeePin := 9001
  grains := [
    ⟨"IngressGrain", 9001, 1000⟩,
    ⟨"SettlementGrain", 9001, 4000⟩
  ]
  channels := [
    ⟨"sturdySettle", "IngressGrain", "SettlementGrain", 12⟩
  ]

theorem deploymentTopology_roundtrip_concrete :
    deploymentOfCoreData (deploymentToCoreData sampleDeployAST) = some sampleDeployAST :=
  deploymentTopology_data_roundtrip sampleDeployAST

#guard deploymentTopologyReader.ofCoreData (deploymentTopologyReader.toCoreData sampleDeployAST) == some sampleDeployAST
#guard (deploymentTopologyReader.parse sampleDeployText).toOption == some sampleDeployAST
#guard (deploymentTopologyReader.parse (deploymentTopologyReader.render sampleDeployAST)).toOption == some sampleDeployAST
#guard acceptsReaderAST deploymentTopologyReader sampleDeployAST == true
#guard (elaborateLoweredModule (deploymentTopologyReader.lowerToObend sampleDeployAST)).isOk == true
#guard (deploymentTopologyReader.parse "topology: NoHeader\ntotalMandateCap: 10").isOk == false

#tooth deploymentTopology_data_roundtrip by mutation
  Obend.Format.deploymentToCoreData := fun _ => Data.record []

/-! ## Part 4: Edge Cases (Empty Inputs, Boundary Values, `lean(...)` & `judge(...)` Methods) & Axiom Audit -/

-- Empty input rejection across all 4 FormatReaders
#guard (obnbReader.parse "").isOk == false
#guard (usdStageReader.parse "").isOk == false
#guard (dfaPolicyReader.parse "").isOk == false
#guard (deploymentTopologyReader.parse "").isOk == false

-- Corrupt Data decoding returns `none` cleanly
#guard obnbReader.ofCoreData (.natural 0) == none
#guard usdStageReader.ofCoreData (.natural 0) == none
#guard dfaPolicyReader.ofCoreData (.natural 0) == none
#guard deploymentTopologyReader.ofCoreData (.natural 0) == none

-- Boundary ASTs with empty collections / zero bounds pass roundtrip and FrontEnd.accept
def emptyCollectionsUsdAST : UsdStage :=
  { sampleUsdAST with subLayers := [], overrides := [], maxThermalMk := 0 }
def emptyCollectionsDfaAST : DfaPolicy :=
  { sampleDfaAST with acceptingStates := [], transitions := [], holes := [] }
def emptyCollectionsDeployAST : DeploymentTopology :=
  { sampleDeployAST with grains := [], channels := [], totalMandateCap := 0 }

#guard (usdStageReader.ofCoreData (usdStageReader.toCoreData emptyCollectionsUsdAST)) == some emptyCollectionsUsdAST
#guard acceptsReaderAST usdStageReader emptyCollectionsUsdAST == true
#guard (dfaPolicyReader.ofCoreData (dfaPolicyReader.toCoreData emptyCollectionsDfaAST)) == some emptyCollectionsDfaAST
#guard acceptsReaderAST dfaPolicyReader emptyCollectionsDfaAST == true
#guard (deploymentTopologyReader.ofCoreData (deploymentTopologyReader.toCoreData emptyCollectionsDeployAST)) == some emptyCollectionsDeployAST
#guard acceptsReaderAST deploymentTopologyReader emptyCollectionsDeployAST == true

-- Parameterized Isar methods (`lean(...)` and `judge(...)`) and rejection of empty arguments
#guard (parseIsarMethod "lean(escrow_solvent)").toOption == some (IsarMethod.lean "escrow_solvent")
#guard (parseIsarMethod "judge(Slot.usable)").toOption == some (IsarMethod.judge "Slot.usable")
#guard (Obend.Spec.Parse.checkIsarMethod "lean()").isOk == false
#guard (Obend.Spec.Parse.checkIsarMethod "judge()").isOk == false

-- Axiom audit: verify 0 sorryAx and 0 Classical.choice on all constructive CellContract, FormatReader & Isar theorems
#print axioms escrow_and_lease_kinds_nontrivial
#print axioms escrowOp_admitted_by_contract
#print axioms lease_advance_admitted_by_contract
#print axioms lease_overdraw_contract_refused
#print axioms lease_rollback_contract_refused
#print axioms escrow_rollback_contract_refused
#print axioms sampleContractProofTree_properties
#print axioms sampleElaboratedCellContract_holds_top
#print axioms obnb_data_roundtrip
#print axioms usdStage_data_roundtrip
#print axioms dfaPolicy_data_roundtrip
#print axioms deploymentTopology_data_roundtrip
#print axioms obnb_roundtrip_concrete
#print axioms usdStage_roundtrip_concrete
#print axioms dfaPolicy_roundtrip_concrete
#print axioms deploymentTopology_roundtrip_concrete

