import Obend.Spec.Elaborate
import Obend.Spec.FrontEnd
import Obend.Spec.Workspace
import Obend.Tactic.Weave
import Obend.Tactic.Tooth
import Obend.Tactic.MonadicReduction

open Obend.Spec.Syntax
open Obend.Spec.Elaborate
open Obend.Spec.FrontEnd
open Obend.Spec.Workspace
open Obend.Tactic.Weave
open Obend.Tactic.Tooth
open Obend.Tactic.MonadicReduction

set_option autoImplicit false

/-!
# Metasystem Verification Suite: Isar Proof-Script Verifier, External Judge Dispatch, Workspace Pin Propagation, `#weave` Chains & Dual-Pole `#tooth`

Covers:
1. `Obend.Spec.Elaborate` & `Obend.Spec.FrontEnd`: `verifyIsarProofScript`, `extractIsarJudgeTags`,
   `ElaboratedIsarCert`, `verifyIsarProofScript_sound`, `verifyCertJudgeTags`, and `checkModuleIsarCerts`.
2. `Obend.Spec.Workspace`: `WorkspaceModuleDep`, `checkWorkspaceAcyclic`, `checkModulePinsFresh`,
   `computeTransitiveStaleModulesFuel`, `computeStaleWorkspaceModules`,
   `directStaleModule_in_transitiveStale`, and `allPinsFresh_zero_stale`.
3. `Obend.Tactic.Weave`, `Obend.Tactic.Tooth`, & `Obend.Tactic.MonadicReduction`:
   `weave_chain`, `WeaveChainReceipt`, `checkWeaveChainReceipt`, `checkWeaveChainReceipt_sound`,
   `ToothSpec`, `verifyDualPoleTooth`, `verifyDualPoleTooth_sound`, and `monadic_reduce`.
-/

/-! ## Part 1: Structured Isar Proof-Script Verification & External Judge Tag Extraction -/

def invExpr : Expr :=
  .binary "<=" (.member (.var "self") "count") (.member (.var "self") "limit")

def stepExpr1 : Expr :=
  .binary "<=" (.member (.var "self") "count") (.binary "+" (.member (.var "self") "count") (.nat "1"))

/-- Valid contract whose Isar proof script ends with a `showStep` matching `c.conclusion`. -/
def validShowContract : ContractDecl where
  name := "ValidShowContract"
  targetType := "Counter"
  invariant := some invExpr
  method := some .frame
  steps := [
    ProofStep.haveStep "hStep" stepExpr1 (.byJudge "dfa-policy@1"),
    ProofStep.showStep invExpr .frame
  ]

/-- Valid contract whose Isar proof script ends with `ProofStep.byJudge`. -/
def validJudgeContract : ContractDecl where
  name := "ValidJudgeContract"
  targetType := "Stage"
  invariant := some invExpr
  method := some (.byJudge "usd-stage@1")
  steps := [
    ProofStep.haveStep "hKinematics" stepExpr1 (.byJudge "obnb@1"),
    ProofStep.byJudge "usd-stage@1"
  ]

/-- Valid contract whose Isar proof script ends with `ProofStep.byEval`. -/
def validEvalContract : ContractDecl where
  name := "ValidEvalContract"
  targetType := "Counter"
  invariant := some invExpr
  steps := [
    ProofStep.haveStep "hBound" stepExpr1 .byOmega,
    ProofStep.byEval
  ]

/-- Valid contract whose Isar proof script ends with `ProofStep.byOmega`. -/
def validOmegaContract : ContractDecl where
  name := "ValidOmegaContract"
  targetType := "Counter"
  invariant := some invExpr
  steps := [
    ProofStep.byOmega
  ]

/-- Invalid contract: empty `steps := []`. -/
def invalidEmptyStepsContract : ContractDecl where
  name := "InvalidEmptySteps"
  targetType := "Counter"
  invariant := some invExpr
  steps := []

/-- Invalid contract: ends with `haveStep` (no terminal discharge step). -/
def invalidNoTerminalDischargeContract : ContractDecl where
  name := "InvalidNoTerminal"
  targetType := "Counter"
  invariant := some invExpr
  steps := [
    ProofStep.haveStep "hOnly" stepExpr1 .byOmega
  ]

/-- Invalid contract: terminal `showStep` proposition does not match `c.conclusion`. -/
def invalidMismatchedShowContract : ContractDecl where
  name := "InvalidMismatchedShow"
  targetType := "Counter"
  invariant := some invExpr
  steps := [
    ProofStep.haveStep "hStep" stepExpr1 .byOmega,
    ProofStep.showStep stepExpr1 .frame
  ]

/-- Invalid contract: `haveStep` has an empty label `""`. -/
def invalidEmptyLabelContract : ContractDecl where
  name := "InvalidEmptyLabel"
  targetType := "Counter"
  invariant := some invExpr
  steps := [
    ProofStep.haveStep "" stepExpr1 .byOmega,
    ProofStep.byOmega
  ]

/-- Invalid contract: `byJudge` has an empty format tag `""`. -/
def invalidEmptyJudgeTagContract : ContractDecl where
  name := "InvalidEmptyJudgeTag"
  targetType := "Counter"
  invariant := some invExpr
  steps := [
    ProofStep.byJudge ""
  ]

/-- Edge-case contract where `c.invariant = none` (so `c.conclusion` defaults to `.bool true`)
    and terminal step is `showStep (.bool true) .frame`. -/
def validDefaultConclusionContract : ContractDecl where
  name := "ValidDefaultConclusion"
  targetType := "Counter"
  invariant := none
  steps := [
    ProofStep.showStep (.bool true) .frame
  ]

/-- Edge-case invalid contract where `c.invariant = none` (so `c.conclusion` defaults to `.bool true`)
    and terminal step is `showStep (.bool false) .frame`. -/
def invalidDefaultConclusionContract : ContractDecl where
  name := "InvalidDefaultConclusion"
  targetType := "Counter"
  invariant := none
  steps := [
    ProofStep.showStep (.bool false) .frame
  ]

#guard verifyIsarProofScript validShowContract == true
#guard verifyIsarProofScript validJudgeContract == true
#guard verifyIsarProofScript validEvalContract == true
#guard verifyIsarProofScript validOmegaContract == true
#guard verifyIsarProofScript validDefaultConclusionContract == true

#guard verifyIsarProofScript invalidEmptyStepsContract == false
#guard verifyIsarProofScript invalidNoTerminalDischargeContract == false
#guard verifyIsarProofScript invalidMismatchedShowContract == false
#guard verifyIsarProofScript invalidEmptyLabelContract == false
#guard verifyIsarProofScript invalidEmptyJudgeTagContract == false
#guard verifyIsarProofScript invalidDefaultConclusionContract == false

#guard extractIsarJudgeTags validShowContract.steps == ["dfa-policy@1"]
#guard extractIsarJudgeTags validJudgeContract.steps == ["obnb@1", "usd-stage@1"]
#guard extractIsarJudgeTags validEvalContract.steps == []
#guard extractIsarJudgeTags [] == []

theorem validShowContract_valid : verifyIsarProofScript validShowContract = true := by
  simp only [verifyIsarProofScript, verifyIsarSteps, validShowContract, lastStepOf,
    allStepsValid, validIsarStep, validIsarMethod, isTerminalDischargeStep,
    ContractDecl.conclusion, Option.getD, ProofStep.haveStep, ProofStep.showStep,
    IsarMethod.byJudge, exprEq_self]
  decide

theorem validShowContract_sound :
    validShowContract.steps ≠ [] ∧
    (∀ s ∈ validShowContract.steps, validIsarStep s = true) ∧
    (∀ label prop m, ProofStep.haveStep label prop m ∈ validShowContract.steps →
      label ≠ "" ∧ validIsarMethod m = true) ∧
    ∃ lastStep ∈ validShowContract.steps,
      lastStepOf validShowContract.steps = some lastStep ∧
      isTerminalDischargeStep validShowContract.conclusion lastStep = true ∧
      ((∃ m, lastStep = ProofStep.showStep validShowContract.conclusion m ∧ validIsarMethod m = true) ∨
       (∃ m, lastStep = ProofStep.byMethod m ∧ validIsarMethod m = true)) :=
  verifyIsarProofScript_sound validShowContract validShowContract_valid

def sampleModuleForCerts : Module where
  name := "JudgeDispatchMod"
  imports := []
  decls := [.record "Counter" [("count", "Nat"), ("limit", "Nat")] []]
  contracts := [validShowContract, validJudgeContract]

def sampleRegisteredJudge (tag : String) : Bool :=
  strEq tag "dfa-policy@1" || strEq tag "obnb@1" || strEq tag "usd-stage@1"

def samplePartialJudge (tag : String) : Bool :=
  strEq tag "dfa-policy@1"

#guard (checkModuleIsarCerts sampleRegisteredJudge sampleModuleForCerts).isOk == true
#guard (checkModuleIsarCerts samplePartialJudge sampleModuleForCerts).isOk == false
#guard (elaborateContractsWithCerts sampleRegisteredJudge sampleModuleForCerts).isOk == true
#guard (elaborateContractsWithCerts samplePartialJudge sampleModuleForCerts).isOk == false
#guard allJudgeTagsRegistered sampleRegisteredJudge ["dfa-policy@1", "obnb@1"] == true
#guard allJudgeTagsRegistered samplePartialJudge ["dfa-policy@1", "obnb@1"] == false
#guard verifyCertJudgeTags sampleRegisteredJudge (elaborateContractIsarCert sampleModuleForCerts validJudgeContract) == true
#guard verifyCertJudgeTags samplePartialJudge (elaborateContractIsarCert sampleModuleForCerts validJudgeContract) == false

theorem sampleCertJudgeTags_valid (m : Module) :
    verifyCertJudgeTags sampleRegisteredJudge
      (elaborateContractIsarCert m validJudgeContract) = true := by
  unfold verifyCertJudgeTags elaborateContractIsarCert
  decide

theorem sampleCertJudgeTags_sound (m : Module) :
    (elaborateContractIsarCert m validJudgeContract).scriptValid = true ∧
    (∀ tag ∈ (elaborateContractIsarCert m validJudgeContract).judgeTags,
      sampleRegisteredJudge tag = true) :=
  verifyCertJudgeTags_sound sampleRegisteredJudge
    (elaborateContractIsarCert m validJudgeContract) (sampleCertJudgeTags_valid m)

theorem sampleContractIsarCert_sound (m : Module) :
    validJudgeContract.steps ≠ [] ∧
    (∃ lastStep ∈ validJudgeContract.steps,
      lastStepOf validJudgeContract.steps = some lastStep ∧
      isTerminalDischargeStep validJudgeContract.conclusion lastStep = true) ∧
    (∀ tag, ProofStep.byJudge tag ∈ validJudgeContract.steps → sampleRegisteredJudge tag = true) ∧
    (∀ label prop tag,
      ProofStep.haveStep label prop (.byJudge tag) ∈ validJudgeContract.steps → sampleRegisteredJudge tag = true) :=
  verifyContractIsarCert_sound sampleRegisteredJudge m validJudgeContract (sampleCertJudgeTags_valid m)

#tooth verifyIsarProofScript_sound by mutation
  Obend.Spec.Elaborate.verifyIsarProofScript := fun _ => true

#tooth verifyIsarProofScript_sound by mutation
  Obend.Spec.Elaborate.isTerminalDischargeStep := fun _ _ => true

#tooth verifyIsarProofScript_sound by mutation
  Obend.Spec.Elaborate.exprEq := fun _ _ => true


/-! ## Part 2: Multi-Module Workspace Topological Dependency Graph & Stale-Pin Propagation -/

def depCore : WorkspaceModuleDep where
  moduleName := "Core"
  imports := []
  pins := []

def depUtils : WorkspaceModuleDep where
  moduleName := "Utils"
  imports := []
  pins := [("Core", "versionBlock", "0xaaa1")]

def depVault : WorkspaceModuleDep where
  moduleName := "Vault"
  imports := ["Core"]
  pins := [("Core", "escrowInv", "0x1111")]

def depApp : WorkspaceModuleDep where
  moduleName := "App"
  imports := ["Vault", "Utils"]
  pins := [("Utils", "helperSpec", "0x2222")]

def depDashboard : WorkspaceModuleDep where
  moduleName := "Dashboard"
  imports := ["App"]
  pins := []

def sampleWorkspaceDeps : List WorkspaceModuleDep :=
  [depCore, depUtils, depVault, depApp, depDashboard]

/-- All live exports match the pinned hashes. -/
def freshLiveExports : List LiveBlockExport :=
  [("Core", "versionBlock", "0xaaa1"),
   ("Core", "escrowInv", "0x1111"),
   ("Utils", "helperSpec", "0x2222")]

/-- Upstream `Core#^escrowInv` hash changed from `0x1111` to `0x9999`, while `versionBlock` and `helperSpec` stay fresh. -/
def rotatedEscrowLiveExports : List LiveBlockExport :=
  [("Core", "versionBlock", "0xaaa1"),
   ("Core", "escrowInv", "0x9999"),
   ("Utils", "helperSpec", "0x2222")]

-- Topological acyclicity checks (positive & negative edge cases)
#guard checkWorkspaceAcyclic [] == true
#guard checkWorkspaceAcyclic sampleWorkspaceDeps == true
#guard checkWorkspaceAcyclic sampleWorkspaceDeps.reverse == true

def cyclicSelfDep : List WorkspaceModuleDep :=
  [{ moduleName := "SelfLoop", imports := ["SelfLoop"], pins := [] }]

def cyclicTwoCycle : List WorkspaceModuleDep :=
  [{ moduleName := "ModA", imports := ["ModB"], pins := [] },
   { moduleName := "ModB", imports := ["ModA"], pins := [] }]

def missingImportDep : List WorkspaceModuleDep :=
  [{ moduleName := "ModA", imports := ["GhostMod"], pins := [] }]

/-- Duplicate module declaration where the second entry has a self-loop or missing import. -/
def duplicateMaskedCycleDep : List WorkspaceModuleDep :=
  [{ moduleName := "ModA", imports := [], pins := [] },
   { moduleName := "ModA", imports := ["ModA"], pins := [] }]

#guard checkWorkspaceAcyclic cyclicSelfDep == false
#guard checkWorkspaceAcyclic cyclicTwoCycle == false
#guard checkWorkspaceAcyclic missingImportDep == false
#guard checkWorkspaceAcyclic duplicateMaskedCycleDep == false

-- Pin freshness & transitive stale propagation checks
#guard checkModulePinsFresh freshLiveExports depVault == true
#guard checkModulePinsFresh rotatedEscrowLiveExports depVault == false
#guard checkModulePinsFresh rotatedEscrowLiveExports depUtils == true

#guard computeStaleWorkspaceModules sampleWorkspaceDeps freshLiveExports == []
#guard computeDirectStaleModules sampleWorkspaceDeps rotatedEscrowLiveExports == ["Vault"]
#guard computeTransitiveStaleModulesFuel 0 sampleWorkspaceDeps ["Vault"] == ["Vault"]
#guard computeTransitiveStaleModulesFuel 1 sampleWorkspaceDeps ["Vault"] == ["Vault", "App"]
#guard computeTransitiveStaleModulesFuel 2 sampleWorkspaceDeps ["Vault"] == ["Vault", "App", "Dashboard"]
#guard computeStaleWorkspaceModules sampleWorkspaceDeps rotatedEscrowLiveExports == ["Vault", "App", "Dashboard"]

/-- Diamond dependency graph where two stale upstream branches (`BranchA`, `BranchB`) converge
    on `DiamondSink`, plus `PinOnlyConsumer` which pins a `#^block` of `DiamondSink` without
    listing `DiamondSink` in `imports`. -/
def diamondWorkspaceDeps : List WorkspaceModuleDep :=
  [{ moduleName := "Root", imports := [], pins := [("External", "rootPin", "0xold")] },
   { moduleName := "BranchA", imports := ["Root"], pins := [] },
   { moduleName := "BranchB", imports := ["Root"], pins := [] },
   { moduleName := "DiamondSink", imports := ["BranchA", "BranchB"], pins := [] },
   { moduleName := "PinOnlyConsumer", imports := [], pins := [("DiamondSink", "sinkBlock", "0x5555")] }]

def diamondLiveExports : List LiveBlockExport :=
  [("External", "rootPin", "0xnew"),
   ("DiamondSink", "sinkBlock", "0x5555")]

#guard checkWorkspaceAcyclic diamondWorkspaceDeps == true
#guard computeStaleWorkspaceModules diamondWorkspaceDeps diamondLiveExports ==
  ["Root", "BranchA", "BranchB", "DiamondSink", "PinOnlyConsumer"]

theorem vault_direct_stale_in_transitive :
    depVault.moduleName ∈ computeTransitiveStaleModulesFuel 3 sampleWorkspaceDeps
      (computeDirectStaleModules sampleWorkspaceDeps rotatedEscrowLiveExports) ∧
    depVault.moduleName ∈ computeStaleWorkspaceModules sampleWorkspaceDeps rotatedEscrowLiveExports :=
  directStaleModule_in_transitiveStale 3 sampleWorkspaceDeps rotatedEscrowLiveExports depVault
    (by decide) rfl

theorem app_downstream_stale_in_transitive :
    depApp.moduleName ∈ computeTransitiveStaleModulesFuel 2 sampleWorkspaceDeps
      (computeDirectStaleModules sampleWorkspaceDeps rotatedEscrowLiveExports) :=
  downstream_stale_in_transitiveStale 1 sampleWorkspaceDeps rotatedEscrowLiveExports
    depVault depApp (by decide) (by decide) rfl (by decide)

theorem sampleWorkspace_all_fresh_zero_stale :
    computeDirectStaleModules sampleWorkspaceDeps freshLiveExports = [] ∧
    computeTransitiveStaleModulesFuel 5 sampleWorkspaceDeps
      (computeDirectStaleModules sampleWorkspaceDeps freshLiveExports) = [] ∧
    computeStaleWorkspaceModules sampleWorkspaceDeps freshLiveExports = [] := by
  apply allPinsFresh_zero_stale 5 sampleWorkspaceDeps freshLiveExports
  intro m hm
  simp only [sampleWorkspaceDeps, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl <;> decide

#tooth directStaleModule_in_transitiveStale by mutation
  Obend.Spec.Workspace.computeStaleWorkspaceModules := fun _ _ => []

#tooth downstream_stale_in_transitiveStale by mutation
  Obend.Spec.Workspace.collectNewlyStaleModules := fun _ _ => []

#tooth allPinsFresh_zero_stale by mutation
  Obend.Spec.Workspace.computeStaleWorkspaceModules := fun _ _ => ["bogus"]

/-! ## Part 3: `#weave` Chained-Step Tactic, `WeaveChainReceipt`, `MonadicReduction` & Dual-Pole `#tooth` -/

/-- Test `weave_chain` on a multi-step algebraic & linear arithmetic goal using proof terms. -/
theorem weave_chain_algebraic_demo (a b c : Nat) (h1 : a ≤ b) (h2 : b ≤ c) :
    2 * (a + 3) ≤ 2 * c + 6 := by
  weave_chain [Nat.le_trans h1 h2]

/-- Test `weave_chain` chaining 4 intermediate propositional `have` obligations `P_1 → P_2 → P_3 → P_4`. -/
theorem weave_chain_prop_obligations_demo (a b c d e : Nat)
    (h1 : a ≤ b) (h2 : b ≤ c) (h3 : c ≤ d) (h4 : d ≤ e) :
    3 * (a + 2) ≤ 3 * e + 6 := by
  weave_chain [a ≤ c, a ≤ d, a ≤ e, a + 2 ≤ e + 2]

/-- Test `monadic_reduce` on chained `Option`, `Except`, and `StateT` computations. -/
theorem monadic_reduce_option_except_demo (x : Nat) :
    ((some x >>= fun a => some (a + 2)) >>= fun b => some (b * 3)) = some ((x + 2) * 3) ∧
    (((Except.ok x : Except String Nat) >>= fun a => .ok (a + 1)) >>= fun b => .ok (b + 4)) =
      .ok (x + 1 + 4) ∧
    ((do let s ← get; set (s + 5); pure (s * 2) : StateT Nat Option Nat).run x) =
      some (x * 2, x + 5) := by
  refine ⟨?_, ?_, ?_⟩ <;> monadic_reduce <;> rfl

def validWeaveReceipt : WeaveChainReceipt where
  initialProp := "count <= limit"
  goalProp := "count <= limit + 2"
  steps := [
    { label := "h1", sourceProp := "count <= limit", targetProp := "count <= limit + 1", method := "omega", discharged := true },
    { label := "h2", sourceProp := "count <= limit + 1", targetProp := "count <= limit + 2", method := "omega", discharged := true }
  ]

def emptyWeaveReceipt : WeaveChainReceipt where
  initialProp := "P"
  goalProp := "P"
  steps := []

def brokenLinkWeaveReceipt : WeaveChainReceipt where
  initialProp := "P1"
  goalProp := "P3"
  steps := [
    { label := "h1", sourceProp := "P1", targetProp := "P2", discharged := true },
    { label := "h2", sourceProp := "WRONG", targetProp := "P3", discharged := true }
  ]

def undischargedWeaveReceipt : WeaveChainReceipt where
  initialProp := "P1"
  goalProp := "P2"
  steps := [
    { label := "h1", sourceProp := "P1", targetProp := "P2", discharged := false }
  ]

def emptyLabelWeaveReceipt : WeaveChainReceipt where
  initialProp := "P1"
  goalProp := "P2"
  steps := [
    { label := "", sourceProp := "P1", targetProp := "P2", discharged := true }
  ]

#guard checkWeaveChainReceipt validWeaveReceipt == true
#guard checkWeaveChainReceipt emptyWeaveReceipt == false
#guard checkWeaveChainReceipt brokenLinkWeaveReceipt == false
#guard checkWeaveChainReceipt undischargedWeaveReceipt == false
#guard checkWeaveChainReceipt emptyLabelWeaveReceipt == false

def demoPropInterp (count limit : Nat) : String → Prop
  | "count <= limit" => count ≤ limit
  | "count <= limit + 1" => count ≤ limit + 1
  | "count <= limit + 2" => count ≤ limit + 2
  | _ => False

theorem validWeaveReceipt_derives_goal (count limit : Nat) (h0 : count ≤ limit) :
    count ≤ limit + 2 := by
  have hsound := (checkWeaveChainReceipt_sound validWeaveReceipt (by decide)).2.2 (demoPropInterp count limit)
  apply hsound _ h0
  intro s hs _ hsrc
  simp only [validWeaveReceipt, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl
  · change count ≤ limit at hsrc
    change count ≤ limit + 1
    omega
  · change count ≤ limit + 1 at hsrc
    change count ≤ limit + 2
    omega


#tooth checkWeaveChainReceipt_sound by mutation
  Obend.Tactic.Weave.checkWeaveChainReceipt := fun _ => true

/-- Dual-Pole Tooth Obligation Checker tests (`ToothSpec`, `verifyDualPoleTooth`, `verifyDualPoleTooth_sound`). -/
def boundedTransitionEval (p : Nat × Nat) : Bool :=
  decide (p.1 ≤ p.2) && decide (p.2 ≤ 100)

def validBoundedToothSpec : ToothSpec (Nat × Nat) where
  name := "boundedMonotoneTooth"
  eval := boundedTransitionEval
  posFixture := (10, 25)
  negFixtures := [(30, 10), (50, 150), (101, 102)]

def vacuousTrueToothSpec : ToothSpec (Nat × Nat) where
  name := "vacuousTrueTooth"
  eval := fun _ => true
  posFixture := (10, 25)
  negFixtures := [(30, 10)]

def overlyStrictFalseToothSpec : ToothSpec (Nat × Nat) where
  name := "overlyStrictFalseTooth"
  eval := fun _ => false
  posFixture := (10, 25)
  negFixtures := [(30, 10)]

#guard verifyDualPoleTooth validBoundedToothSpec == true
#guard verifyDualPoleTooth vacuousTrueToothSpec == false
#guard verifyDualPoleTooth overlyStrictFalseToothSpec == false

theorem validBoundedToothSpec_sound :
    validBoundedToothSpec.eval validBoundedToothSpec.posFixture = true ∧
    validBoundedToothSpec.negFixtures.all (fun x => !validBoundedToothSpec.eval x) = true ∧
    (∀ x ∈ validBoundedToothSpec.negFixtures, validBoundedToothSpec.eval x = false) :=
  verifyDualPoleTooth_sound validBoundedToothSpec rfl

#tooth verifyDualPoleTooth_sound by mutation
  Obend.Tactic.Tooth.verifyDualPoleTooth := fun _ => true

/-! ## Part 4: Axiom Audit (`0 sorryAx`, `0 Classical.choice`) -/

#print axioms verifyIsarProofScript_sound
#print axioms isTerminalDischargeStep_showStep_eq
#print axioms isTerminalDischargeStep_sound
#print axioms mem_extractIsarJudgeTags_iff
#print axioms verifyCertJudgeTags_sound
#print axioms verifyContractIsarCert_sound
#print axioms directStaleModule_in_transitiveStale
#print axioms downstream_stale_in_transitiveStale
#print axioms allPinsFresh_zero_stale
#print axioms checkWeaveChainReceipt_sound
#print axioms verifyDualPoleTooth_sound
#print axioms validShowContract_sound
#print axioms sampleCertJudgeTags_sound
#print axioms sampleContractIsarCert_sound
#print axioms vault_direct_stale_in_transitive
#print axioms app_downstream_stale_in_transitive
#print axioms sampleWorkspace_all_fresh_zero_stale
#print axioms validWeaveReceipt_derives_goal
#print axioms validBoundedToothSpec_sound

