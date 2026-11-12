import Obend.Reasons.UnifiedEquilibrium
import Obend.Vault.SwarmLedgerSeams
import Obend.AssertAxioms

/-!
# `tests/metasystem/ReasonsAndSwarmSeamsTest.lean` — End-to-End Verification Suite (Chasm C5)

Exercises all 5 concrete deliverables closing Chasms 8, 9, and 10:
1. Declarative Gelfond–Lifschitz stable equilibrium (`IsGLStableModel`), the VGRS–GL sandwich
   theorem (`glStable_sandwiched_by_wf`), Stratified Datalog uniqueness (`totalWF_unique_glStable`,
   `stratified_implies_totalWF`, `stratified_unique_glStable`), and `stableEquilibriumJudge`
   (`"gl-equilibrium@1"`).
2. Typed `LinkRole` graph seam isolation (`write_in_disjoint_role_preserves_role_law`,
   `brief_write_preserves_linked_box_law`, `dev_backlink_detects_unlisted_merged_lane`).
3. `Reasons`-routed telemetry & floor-breach ingestion (`ingestTelemetryObservation`,
   `telemetry_defeats_lane_dispatch_without_refusing_fact`).
4. Vault `_kind` doctrine succession as a `Genealogy.Habitat` (`vaultDoctrineHabitat`,
   `vaultDoctrine_admits_tightening`, `vaultDoctrine_refuses_loosening`).
5. Complete multi-field constructive `LawDial` repair (`synthesizePassingDelta`,
   `synthesizePassingDelta_sound`, `synthesizePassingDelta_complete`,
   `synthesizePassingDelta_none_unsat`).
-/

namespace Obend.Tests.ReasonsAndSwarmSeamsTest

open Obend
open Obend.Core.Data (Data)
open Obend.Spec.Law (LawExpr LawRef Facts)
open Obend.Judge
open Obend.Reasons.UnifiedEquilibrium
open Obend.Vault.SwarmLedgerSeams

-- ============================================================================
-- 1. Unified `Reasons` / Stratified Datalog / Gelfond–Lifschitz Equilibria
-- ============================================================================

def fleetStratifiedProgram : Reasons.Program :=
  { facts := ["fleet_online", "box_down_persvati"]
    rules := [
      { name := "usable_bb2"
        concl := "usable_bb2"
        pos := ["fleet_online"]
        neg := ["box_down_bb2"] },
      { name := "usable_persvati"
        concl := "usable_persvati"
        pos := ["fleet_online"]
        neg := ["box_down_persvati"] },
      { name := "dispatch_ready"
        concl := "dispatch_ready"
        pos := ["usable_bb2"]
        neg := [] }
    ] }

-- Stratified normal Datalog program has a total 2-valued WF model and unique GL equilibrium:
example : glEquilibriumFormat = "gl-equilibrium@1" := rfl
example : checkTotalWF fleetStratifiedProgram = true := rfl
example :
    stableEquilibriumJudge.check 0 fleetStratifiedProgram (Reasons.wf fleetStratifiedProgram).1 = .ok := rfl
example :
    Reasons.statusIn (Reasons.wf fleetStratifiedProgram) "dispatch_ready" = .supported := rfl
example :
    Reasons.statusIn (Reasons.wf fleetStratifiedProgram) "usable_persvati" = .unsupported := rfl

-- Even mutual-defeat program (`a ← not b`, `b ← not a`): partial WF sandwich, two credulous GL models:
example : Reasons.wf competingChoiceProgram = ([], ["a", "b"]) := rfl
example : checkTotalWF competingChoiceProgram = false := rfl
example : stableEquilibriumJudge.check 0 competingChoiceProgram ["a"] = .ok := rfl
example : stableEquilibriumJudge.check 0 competingChoiceProgram ["b"] = .ok := rfl
example : stableEquilibriumJudge.check 0 competingChoiceProgram [] ≠ .ok := by intro h; cases h
example : stableEquilibriumJudge.check 0 competingChoiceProgram ["a", "b"] ≠ .ok := by intro h; cases h

-- Odd self-defeating loop (`p ← not p`): no GL stable model exists; refused at every candidate:
example : stableEquilibriumJudge.check 0 (oddLoopProgram "p") [] ≠ .ok := by intro h; cases h
example : stableEquilibriumJudge.check 0 (oddLoopProgram "p") ["p"] ≠ .ok := by intro h; cases h

-- Universal theorem signatures verified against the kernel:
#check @glStable_sandwiched_by_wf
#check @totalWF_unique_glStable
#check @stratified_implies_totalWF
#check @stratified_unique_glStable
#check @oddLoop_refused_by_judge

-- ============================================================================
-- 2. Typed Link Roles (`FINDINGS 6, 8`)
-- ============================================================================

def testFacts : Facts :=
  { subject := some 1, caller := none, height := 42, turn := 7 }

def bb2BoxPage : RolePage :=
  { name := "bb2"
    state := Vault.stateOf ["online"] [("online", 1)]
    links := [] }

def activeLanePage : RolePage :=
  { name := "lane-c5"
    state := Vault.stateOf ["merged"] [("merged", 1)]
    links := [
      { role := .box, target := "bb2" },
      { role := .brief, target := "brief-v1" },
      { role := .mergedLane, target := "DEV" }
    ] }

def devHubUnlisted : RolePage :=
  { name := "DEV"
    state := Vault.stateOf ["epoch"] [("epoch", 3)]
    links := [] }

def devHubListed : RolePage :=
  editRoleLinks devHubUnlisted .listed ["lane-c5"]

def swarmStore : List RolePage :=
  [bb2BoxPage, activeLanePage, devHubUnlisted]

def boxOnlineLaw : LawExpr :=
  .eqC (.field "online") 1

-- Editing `.brief` links (even pointing to an absent brief page) preserves `linked[box]` laws identically:
example :
    evalRoleLinkLaw testFacts boxOnlineLaw swarmStore activeLanePage .box = true := rfl
example :
    evalRoleLinkLaw testFacts boxOnlineLaw swarmStore
      (editRoleLinks activeLanePage .brief ["brief-v2", "unindexed-note"]) .box = true := rfl

-- `DEV`'s `linked_by[merged_lane]` backlink audit catches unlisted merged lanes and admits once listed:
example :
    checkBacklinkRoleLaw testFacts devMergedLaneBacklinkLaw swarmStore
      devHubUnlisted .mergedLane .listed = false := rfl
example :
    checkBacklinkRoleLaw testFacts devMergedLaneBacklinkLaw swarmStore
      devHubListed .mergedLane .listed = true := rfl

#check @write_in_disjoint_role_preserves_role_law
#check @brief_write_preserves_linked_box_law
#check @dev_backlink_detects_unlisted_merged_lane

-- ============================================================================
-- 3. `Reasons`-Routed Telemetry & Floor Breaches (`FINDINGS 14, 20`)
-- ============================================================================

def persvatiInitial : Reasons.State :=
  mkBoxDispatchState "persvati"

def persvatiAfterTimeout : Except String Reasons.State :=
  ingestTelemetryObservation persvatiInitial
    (.boxUnreachable "persvati" "ssh connect timeout" "fleet-probe")

example : persvatiInitial.status (dispatchToAtom "persvati") = .supported := rfl
example : persvatiAfterTimeout.isOk = true := rfl
example :
    (persvatiAfterTimeout.toOption.map fun s =>
      (s.status (boxUsableAtom "persvati"),
       s.status (dispatchToAtom "persvati"),
       Reasons.whyNot s (dispatchToAtom "persvati"))) =
    some (.unsupported, .unsupported,
      ["dispatch_persvati is defeated by box_unreachable(persvati) (supported)"]) := rfl

-- Tally breach telemetry is likewise recorded as an observation without refusal:
example :
    (ingestTelemetryObservation persvatiInitial
      (.tallyBreach "laptop_builds" 1 0 "audit")).isOk = true := rfl

#check @telemetry_defeats_lane_dispatch_without_refusing_fact

-- ============================================================================
-- 4. Vault `_kind` Law Succession as a `Genealogy.Habitat` (`FINDINGS 19`, `G4`)
-- ============================================================================

def cleanDoctrineState : DoctrineState :=
  { current :=
      { counters := [("laptop_builds", 0), ("git_add_all", 0), ("silent_rewrites", 0)]
        presentLines := ["gate", "tooth"]
        stepsFromHome := 1 }
    auditLog := [] }

def tightenedDoctrineGate : Genealogy.Gate vaultDoctrineHabitat :=
  mkDoctrineGate "reground-g4-tightened"
    [ .corrigibilityHome 8,
      .maxCounter "laptop_builds" 0,
      .maxCounter "git_add_all" 0,
      .mandatoryLine "gate",
      .maxCounter "silent_rewrites" 0,
      .mandatoryLine "tooth" ]

def loosenedDoctrineGate : Genealogy.Gate vaultDoctrineHabitat :=
  mkDoctrineGate "reground-loosened-laptop-builds"
    [ .corrigibilityHome 8,
      .maxCounter "laptop_builds" 1,
      .maxCounter "git_add_all" 0,
      .mandatoryLine "gate" ]

def noBedrockDoctrineGate : Genealogy.Gate vaultDoctrineHabitat :=
  mkDoctrineGate "reground-dropped-corrigibility"
    [ .maxCounter "laptop_builds" 0,
      .maxCounter "git_add_all" 0,
      .mandatoryLine "gate" ]

-- Tightening in `Reground` is admitted; loosening a floor or dropping corrigibility is refused:
example :
    checkDoctrineSuccession genesisDoctrineGate cleanDoctrineState tightenedDoctrineGate = true := rfl
example :
    checkDoctrineSuccession genesisDoctrineGate cleanDoctrineState loosenedDoctrineGate = false := rfl
example :
    checkDoctrineSuccession genesisDoctrineGate cleanDoctrineState noBedrockDoctrineGate = false := rfl

#check @checkDoctrineSuccession_sound
#check @vaultDoctrine_admits_tightening
#check @vaultDoctrine_refuses_loosening

-- ============================================================================
-- 5. Complete Multi-Field Constructive `LawDial` Repair (`THESIS.md:56-57`)
-- ============================================================================

-- 5a. Coupled multi-field difference-constraint + monotone repair (`a + 2 <= b`, `b <= 10`):
def coupled2Keys : List String := ["a", "b"]
def coupled2Laws : List (String × LawExpr) :=
  [ ("mono_a", .monotone "a"),
    ("a_plus_2_le_b", .leROff (.field "a") (.field "b") (-2)),
    ("b_le_10", .leC (.field "b") 10) ]
def coupled2Old : Data := stateFromEnv coupled2Keys (fun k => if k == "a" then 4 else 1)
def coupled2Cur : Data := stateFromEnv coupled2Keys (fun k => if k == "a" then 2 else 1)

def coupled2Repair : Option PassingDelta :=
  synthesizePassingDelta coupled2Keys coupled2Laws testFacts coupled2Old coupled2Cur .write 10

example : (coupled2Repair.map (·.edits)) = some [("a", 4), ("b", 6)] := rfl
example :
    (coupled2Repair.map fun d =>
      allLawsHold coupled2Laws testFacts coupled2Old d.targetState .write) = some true := rfl

#guard
  (coupled2Repair.map fun d =>
    Vault.judge (Vault.stateTy coupled2Keys) "vault" coupled2Laws coupled2Old d.targetState
      (Vault.requestBy "ember" "lane-c5" .write testFacts)) == some .admitted

-- 3-field chained repair (`monotone a`, `a <= b`, `b + 2 <= c`, `c <= 10`) admitted by `Vault.judge`:
def coupled3Keys : List String := ["a", "b", "c"]
def coupled3Laws : List (String × LawExpr) :=
  [ ("mono_a", .monotone "a"),
    ("a_le_b", .leR (.field "a") (.field "b")),
    ("b_plus_2_le_c", .leROff (.field "b") (.field "c") (-2)),
    ("c_le_10", .leC (.field "c") 10) ]
def coupled3Old : Data := Vault.stateOf coupled3Keys [("a", 4), ("b", 1), ("c", 1)]
def coupled3Cur : Data := Vault.stateOf coupled3Keys [("a", 2), ("b", 1), ("c", 1)]

def coupled3Repair : Option PassingDelta :=
  synthesizePassingDelta coupled3Keys coupled3Laws testFacts coupled3Old coupled3Cur .write 10

#guard (coupled3Repair.map (·.edits)) == some [("a", 4), ("b", 4), ("c", 6)]
#guard
  (coupled3Repair.map fun d =>
    Vault.judge (Vault.stateTy coupled3Keys) "vault" coupled3Laws coupled3Old d.targetState
      (Vault.requestBy "ember" "lane-c5" .write testFacts)) == some .admitted

-- 5b. Upper+lower coupled system where naive oscillation from `old = {a:5, b:5}` fails without Kleene least-fixpoint:
def oscKeys : List String := ["a", "b"]
def oscLaws : List (String × LawExpr) :=
  [ ("a_le_b", .leR (.field "a") (.field "b")),
    ("b_le_2", .leC (.field "b") 2) ]
def oscOld : Data := stateFromEnv oscKeys (fun _ => 5)

def oscRepair : Option PassingDelta :=
  synthesizePassingDelta oscKeys oscLaws testFacts oscOld oscOld .write 10

example : (oscRepair.map (·.edits)) = some [("a", 0), ("b", 0)] := rfl
example :
    (oscRepair.map fun d =>
      allLawsHold oscLaws testFacts oscOld d.targetState .write) = some true := rfl

#guard
  (oscRepair.map fun d =>
    Vault.judge (Vault.stateTy oscKeys) "vault" oscLaws oscOld d.targetState
      (Vault.requestBy "ember" "lane-c5" .write testFacts)) == some .admitted

-- 5c. Contradictory laws return `none` (certifying bounded unsatisfiability):
def unsatLaws : List (String × LawExpr) :=
  [ ("eq_5", .eqC (.field "a") 5),
    ("le_3", .leC (.field "a") 3) ]

example :
    synthesizePassingDelta ["a"] unsatLaws testFacts
      (stateFromEnv ["a"] (fun _ => 0))
      (stateFromEnv ["a"] (fun _ => 0))
      .write 10 = none := rfl

#check @synthesizePassingDelta_sound
#check @synthesizePassingDelta_complete
#check @synthesizePassingDelta_none_unsat

-- Kernel axiom census: verifies zero unproved or custom axioms across the entire imported closure.
#assert_axioms_tree

end Obend.Tests.ReasonsAndSwarmSeamsTest
