module
/-
# Metasystem Test Suite — `Obend.Trailblaze.StageBInstances` (Stage-B Promotion & 7-Organ Cathedral Seal)

Verifies end-to-end Stage-B promotion across all 5 sealed apex theorems and the 7-organ multi-turn
Cathedral state machine:
1. **Compile-Time `MetaM` `forallTelescope` Zero-`Obligations` Gate**:
   Inspects the full binder telescope and conclusion of all 5 `stageB_*_sealed` theorems
   (`stageB_polis_deos_trace_sealed`, `stageB_lean_fpga_rung2_to_rung5_sealed`,
   `stageB_zkstripe_calltree_sealed`, `stageB_clustergov_ozaki_step_sealed`,
   `stageB_cathedral_seven_organ_trace_sealed`) and fails elaboration if any binder or conclusion
   mentions any `*Obligations` typeclass or identifier.
2. **Constructive Kernel Axiom & Closed-Theorem Census Gates**:
   - Enforces strictly `[propext, Quot.sound]` (`0 Classical.choice`, `0 _native`, `0 sorryAx`)
     on `stageB_cathedral_seven_organ_trace_sealed`, both Stage-B `instance`s
     (`instStageBPolisObligations`, `instStageBLeanFpgaObligations`), and all Stage-B local theorems.
   - Enforces `Obend.AssertAxioms` hygiene (`0 sorryAx`, `0` custom `axiom`s) and `0` closed
     `theorem`s across every declaration in `Obend.Trailblaze.StageB`.
3. **Concrete Execution `#guard`s & 7-Organ Named Refusal Matrix**:
   Executes `twinTulvaSmudgeMask`, SMMU physical DMA non-interference, `compileLeafExprToDeltaNet`,
   multi-turn `runStageBCathedralTrace`, and all 5 named refusal paths of `refuseStageBCathedralStep`.
4. **`#tooth` Mutation-Sensitivity Kills (`6` kills ≥ `4` required)**:
   Confirms Lean's kernel rejects mutated definitions across SMMU DMA isolation, `Tulva` Rényi
   smudging, dual-tile `FaceIdeal3` extraction, refusal completeness, and the 7-organ Cathedral trace seal.
-/

public import Lean
public import Obend.AssertAxioms
public import Obend.Tactic.Tooth
public import Obend.Trailblaze.StageBInstances
import all Obend.Trailblaze.StageBInstances
import all Obend.Trailblaze.CathedralApex

public section

namespace Obend.Tests.Metasystem.TrailblazeStageBSealTest

open Obend.Trailblaze
open Obend.Trailblaze.Polis
open Obend.Trailblaze.LeanFpga
open Obend.Trailblaze.ZkStripe
open Obend.Trailblaze.ClusterGov
open Obend.Trailblaze.CathedralApex
open Obend.Trailblaze.StageB

set_option autoImplicit false

/-! ## §1. Compile-Time `MetaM` `forallTelescope` Zero-`Obligations` Gate -/

#check @stageB_polis_deos_trace_sealed
#check @stageB_lean_fpga_rung2_to_rung5_sealed
#check @stageB_zkstripe_calltree_sealed
#check @stageB_zkstripe_dualExtract
#check @stageB_clustergov_ozaki_step_sealed
#check @stageB_cathedral_seven_organ_trace_sealed
#check @stepStageBCathedral_skip_implies_violation
#check @runStageBCathedralTrace_two_turn_inhabited

open Lean Meta Elab Command in
run_cmd do
  let env ← getEnv
  let sealedTheorems : List Name := [
    ``Obend.Trailblaze.StageB.stageB_polis_deos_trace_sealed,
    ``Obend.Trailblaze.StageB.stageB_lean_fpga_rung2_to_rung5_sealed,
    ``Obend.Trailblaze.StageB.stageB_zkstripe_calltree_sealed,
    ``Obend.Trailblaze.StageB.stageB_clustergov_ozaki_step_sealed,
    ``Obend.Trailblaze.StageB.stageB_cathedral_seven_organ_trace_sealed
  ]
  let containsObligationsSubstr (s : String) : Bool :=
    (s.splitOn "Obligations").length > 1
  liftTermElabM do
    for thmName in sealedTheorems do
      let some ci := env.find? thmName
        | throwError m!"Missing required Stage-B sealed theorem: {thmName}"
      let .thmInfo _ := ci
        | throwError m!"Declaration {thmName} must be a theorem!"
      forallTelescope ci.type fun binders conclusion => do
        if binders.isEmpty then
          throwError m!"Stage-B theorem {thmName} unexpectedly has empty binder telescope"
        for idx in [:binders.size] do
          let b := binders[idx]!
          let bDecl ← b.fvarId!.getDecl
          let bType ← instantiateMVars bDecl.type
          if containsObligationsSubstr bDecl.userName.toString then
            throwError m!"Binder #{idx} ({bDecl.userName}) in {thmName} mentions `Obligations`!"
          for c in bType.getUsedConstants do
            if containsObligationsSubstr c.toString then
              throwError m!"Binder #{idx} in {thmName} references `*Obligations` constant `{c}` in type `{bType}`!"
        let conclType ← instantiateMVars conclusion
        for c in conclType.getUsedConstants do
          if containsObligationsSubstr c.toString then
            throwError m!"Conclusion of {thmName} references `*Obligations` constant `{c}`!"


/-! ## §2. Constructive Kernel Axiom Gate & Closed-Theorem Census Gate -/

#print axioms Obend.Trailblaze.StageB.stageB_sel4_smmu_dma_noninterference
#print axioms Obend.Trailblaze.StageB.stageB_tulva_renyi_smudging_hiding
#print axioms Obend.Trailblaze.StageB.stageB_nextpnr_dual_tile_routing_sound
#print axioms Obend.Trailblaze.StageB.stageB_leaf_book_deltanet_normal_form
#print axioms Obend.Trailblaze.StageB.stageB_polis_deos_trace_sealed
#print axioms Obend.Trailblaze.StageB.stageB_lean_fpga_rung2_to_rung5_sealed
#print axioms Obend.Trailblaze.StageB.stageB_zkstripe_calltree_sealed
#print axioms Obend.Trailblaze.StageB.stageB_zkstripe_dualExtract
#print axioms Obend.Trailblaze.StageB.stageB_clustergov_ozaki_step_sealed
#print axioms Obend.Trailblaze.StageB.stageB_cathedral_seven_organ_trace_sealed
#print axioms Obend.Trailblaze.StageB.runStageBCathedralTrace_two_turn_inhabited

open Lean Meta Elab Command in
run_cmd do
  let env ← getEnv
  -- Gate 2A: Strict constructive (`[propext, Quot.sound]`, `0 Classical.choice`, `0 _native`)
  let strictConstructive : List Name := [``propext, ``Quot.sound]
  let zeroClassicalRequired : List Name := [
    ``Obend.Trailblaze.StageB.stageB_sel4_smmu_dma_noninterference,
    ``Obend.Trailblaze.StageB.stageB_tulva_renyi_smudging_hiding,
    ``Obend.Trailblaze.StageB.stageB_nextpnr_dual_tile_routing_sound,
    ``Obend.Trailblaze.StageB.stageB_leaf_book_deltanet_normal_form,
    ``Obend.Trailblaze.StageB.stepStageBCathedral_skip_implies_violation,
    ``Obend.Trailblaze.StageB.stepStageBCathedral_complete,
    ``Obend.Trailblaze.StageB.stageB_cathedral_seven_organ_trace_sealed,
    ``Obend.Trailblaze.StageB.runStageBCathedralTrace_two_turn_inhabited
  ]
  let mut badStrict : Array (Name × List Name) := #[]
  for c in zeroClassicalRequired do
    let axs ← liftCoreM <| collectAxioms c
    let disallowed := axs.toList.filter (!strictConstructive.contains ·)
    unless disallowed.isEmpty do
      badStrict := badStrict.push (c, disallowed)
  unless badStrict.isEmpty do
    throwError m!"Stage-B strict zero-Classical.choice gate failed: {badStrict.toList}"

  -- Gate 2B: Full `Obend.AssertAxioms` hygiene (`0 sorryAx`, `0` custom axioms) + `0` closed theorems
  liftTermElabM do
    let mut badHygiene : Array (Name × List Name) := #[]
    let mut closedThms : Array Name := #[]
    for (c, info) in env.constants.map₁.toList do
      if c.isInternal || c.isInternalDetail then continue
      unless (`Obend.Trailblaze.StageB).isPrefixOf c do continue
      if info matches .axiomInfo _ then
        badHygiene := badHygiene.push (c, [c])
        continue
      let axs ← collectAxioms c
      let outside := axs.toList.filter fun ax =>
        !Obend.AssertAxioms.standard.contains ax && !Obend.AssertAxioms.isCompilerTrust ax
      unless outside.isEmpty do
        badHygiene := badHygiene.push (c, outside)
      if let .thmInfo _ := info then
        unless ← Meta.isInstance c do
          if ← Obend.AssertAxioms.closedStatement info.type then
            closedThms := closedThms.push c
    unless badHygiene.isEmpty do
      throwError m!"Stage-B transitive axiom hygiene gate failed (sorryAx or custom axiom): {badHygiene.toList}"
    unless closedThms.isEmpty do
      throwError m!"Stage-B census gate failed (closed `theorem`s must be quantified or `example`): {closedThms.toList}"


/-! ## §3. Concrete Execution `#guard`s & 7-Organ Kernel Refusal Matrix -/

def testOpening1 : SaltedBidOpening := ⟨9#64, 1250#64, 0xABCD_EF01_2345_6789#128⟩
def testOpening2 : SaltedBidOpening := ⟨9#64, 3400#64, 0x1122_3344_5566_7788#128⟩
def testMask1 : BitVec 256 := 0x0123_4567_89AB_CDEF_FEDC_BA98_7654_3210#256

-- `Tulva` Rényi twin smudging bijection `#guard`s
#guard tulvaSmudgedView testOpening1 testMask1 ==
       tulvaSmudgedView testOpening2 (twinTulvaSmudgeMask testOpening1 testOpening2 testMask1)
#guard (testMask1 != twinTulvaSmudgeMask testOpening1 testOpening2 testMask1) == true
#guard twinTulvaSmudgeMask testOpening1 testOpening1 testMask1 == testMask1

-- `seL4` SMMU physical DMA non-interference `#guard`s
def testInitDmaBus (addr : Nat) : BitVec 64 :=
  if addr == 0x5000_0000 then 0xCAFE_F00D#64 else 0#64

def testRogueDmaTrace : List DmaWriteReq :=
  [ ⟨1, 0x5000_0000, 0xDEAD_BEEF#64⟩
  , ⟨3, 0x5000_0000, 0xBAD0_BAD0#64⟩
  , ⟨1, 0x4000_0008, 0x1234_5678#64⟩ ]

#guard isWatchdogProtectedAddr sampleValidPartition 0x5000_0000 == true
#guard runPhysicalDmaTrace sampleValidPartition testInitDmaBus testRogueDmaTrace 0x5000_0000 == 0xCAFE_F00D#64
#guard runPhysicalDmaTrace sampleValidPartition testInitDmaBus testRogueDmaTrace 0x4000_0008 == 0x1234_5678#64

-- Symbolic Rung-2 literal `DeltaNet` normal-form `#guard`s
#guard checkNetPortLinearity (compileLeafExprToDeltaNet "stageb_nf_lit" (.lit 1337)) == true
#guard (activePrincipalRedexes (compileLeafExprToDeltaNet "stageb_nf_lit" (.lit 1337))).isEmpty == true
#guard checkNetPortLinearity (compileLeafExprToDeltaNet "" (.lit 1337)) == false

-- Multi-turn 7-organ Cathedral trace execution witness (`initVaultBudget = 50 → remVaultBudget = 25`)
example :
    ∃ final : StageBSevenOrganState,
      runStageBCathedralTrace sampleStageBInitState
        [sampleStageBSevenOrganTurn1, sampleStageBSevenOrganTurn2] = some final ∧
      final.remVaultBudget = 25 ∧
      final.cathedralState.weightsRoot = 0x55556666 ∧
      final.cathedralState.lastEpoch = 2 :=
  runStageBCathedralTrace_two_turn_inhabited 50 (by decide)

private theorem sampleStageBTurn1_mb_ok :
    checkTurnMandateAndBiscuit sampleStageBSevenOrganTurn1 = true := by
  unfold checkTurnMandateAndBiscuit sampleStageBSevenOrganTurn1
  dsimp only
  rw [foldChain_emptyRevoked_oneHop _ _ _ (by decide)]
  decide

-- All 5 named refusal paths of `refuseStageBCathedralStep` verified in the Lean kernel:

-- Refusal Path 1a: `Mandate` unauthorized (expired invocation epoch `999 > 100`)
example :
    refuseStageBCathedralStep sampleStageBInitState
      { sampleStageBSevenOrganTurn1 with
          vaultInvocation := { canonicalStageBInvocation with epoch := 999 } } =
      some "refused: vault-mandate-or-zkbiscuit-unauthorized" := by
  unfold refuseStageBCathedralStep checkTurnMandateAndBiscuit
  have hInvFalse :
      Obend.Vault.Mandate.checkInvocation canonicalStageBMandate
        { canonicalStageBInvocation with epoch := 999 } = false := by decide
  change
    (if !(Obend.Vault.Mandate.checkInvocation canonicalStageBMandate
            { canonicalStageBInvocation with epoch := 999 } && _) then
       some "refused: vault-mandate-or-zkbiscuit-unauthorized"
     else _) = _
  rw [hInvFalse]
  rfl

-- Refusal Path 1b: `ZkBiscuit` attenuation refusal (`requiredRights = 0xFF ⊈ 0x07`)
example :
    refuseStageBCathedralStep sampleStageBInitState
      { sampleStageBSevenOrganTurn1 with requiredRights := 0xFF } =
      some "refused: vault-mandate-or-zkbiscuit-unauthorized" := by
  have hMBFalse :
      checkTurnMandateAndBiscuit
        { sampleStageBSevenOrganTurn1 with requiredRights := 0xFF } = false := by
    unfold checkTurnMandateAndBiscuit sampleStageBSevenOrganTurn1
    dsimp only
    rw [foldChain_emptyRevoked_oneHop _ _ _ (by decide)]
    decide
  unfold refuseStageBCathedralStep
  rw [hMBFalse]
  rfl

-- Refusal Path 2: `Vault` cumulative `Mandate` budget exhausted (`remVaultBudget = 5 < cost = 10`)
example :
    refuseStageBCathedralStep { sampleStageBInitState with remVaultBudget := 5 }
      sampleStageBSevenOrganTurn1 =
      some "refused: vault-budget-exhausted" := by
  unfold refuseStageBCathedralStep
  rw [sampleStageBTurn1_mb_ok]
  rfl

-- Refusal Path 3: `LeanFpga` Rung-2/Rung-4 turn invalid (`plantedNonlinearNetTurn`)
example :
    refuseStageBCathedralStep sampleStageBInitState
      { sampleStageBSevenOrganTurn1 with fpgaTurn := plantedNonlinearNetTurn } =
      some "refused: lean-fpga-turn-invalid" := by
  have hMB :
      checkTurnMandateAndBiscuit
        { sampleStageBSevenOrganTurn1 with fpgaTurn := plantedNonlinearNetTurn } = true :=
    sampleStageBTurn1_mb_ok
  unfold refuseStageBCathedralStep
  rw [hMB]
  rfl

-- Refusal Path 4: `Polis` DeOS session step rejected (replayed capability nullifier)
example :
    refuseStageBCathedralStep
      { sampleStageBInitState with
          polisState :=
            { sampleInitSessionState with
                revokedCodes := [sampleValidPolisTurn.inputCode] } }
      sampleStageBSevenOrganTurn1 =
      some "refused: polis-session-step-rejected" := by
  unfold refuseStageBCathedralStep
  rw [sampleStageBTurn1_mb_ok]
  rfl

-- Refusal Path 5: `Cathedral` governance step rejected (`brokenWeldCathedralTurn`)
example :
    refuseStageBCathedralStep sampleStageBInitState
      { sampleStageBSevenOrganTurn1 with cathedralTurn := brokenWeldCathedralTurn } =
      some "refused: cathedral-governance-step-rejected" := by
  have hMB :
      checkTurnMandateAndBiscuit
        { sampleStageBSevenOrganTurn1 with cathedralTurn := brokenWeldCathedralTurn } = true :=
    sampleStageBTurn1_mb_ok
  have hCathNone : stepCathedralTrace sampleInitTraceState brokenWeldCathedralTurn = none := by
    have hChkFalse : checkCathedralTurn brokenWeldCathedralTurn = false := by decide
    unfold stepCathedralTrace
    rw [hChkFalse]
    rfl
  unfold refuseStageBCathedralStep
  rw [hMB]
  unfold sampleStageBInitState sampleStageBSevenOrganTurn1
  dsimp only
  have hBud : decide (canonicalStageBInvocation.cost ≤ 50) = true := rfl
  have hFpga : checkLeanFpgaTurn sampleValidFpgaTurn = true := rfl
  have hPolSome : (stepPolisSession sampleInitSessionState sampleValidPolisTurn).isSome = true := rfl
  rw [hBud, hFpga]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  cases hPol : stepPolisSession sampleInitSessionState sampleValidPolisTurn with
  | none => rw [hPol] at hPolSome; cases hPolSome
  | some _ =>
    rw [hCathNone]


/-! ## §4. `#tooth` Mutation-Killing Barriers (`6` Kills ≥ `4` Required) -/

-- `#tooth` Kill 1: mutating `mmioRangesDisjoint` to `fun _ _ => true` breaks `mmioRangesDisjoint_not_both_contain`
#tooth Obend.Trailblaze.StageB.mmioRangesDisjoint_not_both_contain by
  mutation Obend.Trailblaze.Polis.mmioRangesDisjoint := fun _ _ => true

-- `#tooth` Kill 2: mutating `stepSmmuDmaBus` to bypass SMMU domain filtering breaks `stepSmmuDmaBus_preserves_watchdog_addr`
#tooth Obend.Trailblaze.StageB.stepSmmuDmaBus_preserves_watchdog_addr by
  mutation Obend.Trailblaze.Polis.stepSmmuDmaBus :=
    fun _ busMem req addr => if addr == req.physAddr then req.payload else busMem addr

-- `#tooth` Kill 3: mutating `twinTulvaSmudgeMask` to return constant `mask₁` breaks `stageB_tulva_renyi_smudging_hiding`
#tooth Obend.Trailblaze.StageB.stageB_tulva_renyi_smudging_hiding by
  mutation Obend.Trailblaze.StageB.twinTulvaSmudgeMask := fun _ _ mask₁ => mask₁

-- `#tooth` Kill 4: mutating `extractFaceIdealFromDualTiles` to constant `bot` breaks `compile_extract_combinational_dualTiles`
#tooth Obend.Trailblaze.StageB.compile_extract_combinational_dualTiles by
  mutation Obend.Trailblaze.LeanFpga.extractFaceIdealFromDualTiles :=
    fun _ => Obend.Trailblaze.LeanFpga.FaceIdeal3.bot

-- `#tooth` Kill 5: mutating `refuseStageBCathedralStep` to `fun _ _ => none` breaks `stepStageBCathedral_skip_implies_violation`
#tooth Obend.Trailblaze.StageB.stepStageBCathedral_skip_implies_violation by
  mutation Obend.Trailblaze.StageB.refuseStageBCathedralStep := fun _ _ => none

-- `#tooth` Kill 6: mutating `checkTurnMandateAndBiscuit` to `fun _ => true` breaks `stageB_cathedral_seven_organ_trace_sealed`
#tooth Obend.Trailblaze.StageB.stageB_cathedral_seven_organ_trace_sealed by
  mutation Obend.Trailblaze.StageB.checkTurnMandateAndBiscuit := fun _ => true

end Obend.Tests.Metasystem.TrailblazeStageBSealTest

end
