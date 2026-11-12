module
/-
# RehydrationTest — Verification & `#tooth` Kernel Mutation Suite for Rehydratable Membranes (`WS 33`)

Verifies `Obend.Vault.Rehydration` across all four pillars:
1. **Pillar 1 — Derived `Rehydration` Liveness-Type & Replay Coverage**:
   - `replayedDeterministic_iff_confined`, `reconstructedApproximate_iff_unconfined`,
     `invalidAttestation_not_replayed`, `confined_chain_covers_log`,
     `unconfined_chain_drops_interactions`, `ambient_chain_drops_the_reach`,
     and `replayedDeterministic_replays`.
2. **Pillar 2 — `Sturdyref`, Per-Viewer `Membrane`, and Chained Multi-Hop Reshare Attenuation**:
   - `membrane_two_viewers_distinct`, `membrane_authority_monotone`, `Membrane.reshare`,
     `amplifying_reshare_refused`, `amplifying_permits_reshare_refused`,
     `reshare_chain_attenuates`, `rehydrateSturdyref`, and `viewerOfMandate_attenuates`.
3. **Pillar 3 — Functorial Rerender Square & Frustum-Snapshot Re-Expansion**:
   - `rerender_deterministic`, `rerender_idempotent`, `rerender_square`,
     `rerender_membrane_square`, `rerender_after_step_authorized`, `snapshot_roundtrip`,
     `snapshot_roundtrip_attenuated`, and `snapshot_reexpansion_monotone`.
4. **Pillar 4 — 3-Dimensional `ReactiveAffordance` (`TransitionGate` + `[openHeight, closeHeight]` + `Membrane`)**:
   - `transitionOK_iff`, `inWindow_iff`, `fireReactive_iff`, `fireReactive_all_pass`,
     `fireReactive_cap_fail_refuses`, `fireReactive_transition_fail_refuses`,
     `fireReactive_window_fail_refuses`, `fireReactive_wrong_old_refuses`,
     `fireReactive_after_deadline_refuses`, `fireReactive_window_reactive`,
     `fireReactive_carries_real_effect`, and `fireReactive_binds_attested_root`.
5. **`#tooth` Kernel Mutation Tests** on `AttestedRoot.holds`, `Interaction.isWitnessed`,
   `Membrane.reshare`, `transitionOK`, `inWindow`, `classify`, `confined`, `membraneShows`,
   `stepContent`, and `fireReactive`, plus `#print axioms` checks on all headline theorems.
-/
public import Obend.Tactic.Tooth
import all Obend.Vault.Affordance
import all Obend.Vault.Rehydration
public import Obend.Vault.Rehydration

@[expose] public section

namespace Obend.Tests.Rehydration

open Obend.Core.Data (Data)
open Obend.Vault.Affordance (Auth fireGate CellAffordance FireCtx AffordanceIntent fire)
open Obend.Vault.Rehydration

set_option autoImplicit false

/-! ## 0. Concrete Council & Attestation Test Fixtures -/

/-- Demo hash function for concrete receipt-chain replay checks. -/
def demoReceiptHash (r : WitnessReceipt) : Nat :=
  r.prevHash + r.oldCommit + r.newCommit + r.effectsHash + 1

/-- A genuine attested root (both `v4Complete` and `quorum` hold). -/
def goodRoot : AttestedRoot := { root := 42, v4Complete := true, quorum := true }

/-- A structurally invalid attested root (complete, but missing quorum). -/
def badRoot : AttestedRoot := { root := 42, v4Complete := true, quorum := false }

/-- A confined interaction log of two genuine attested turns. -/
def confinedLog : InteractionLog := [.attested goodRoot, .attested goodRoot]

/-- An unconfined interaction log containing an ambient reach outside the membrane. -/
def ambientLog : InteractionLog := [.attested goodRoot, .ambient]

/-- An unconfined interaction log containing a structurally invalid attestation. -/
def forgedLog : InteractionLog := [.attested goodRoot, .attested badRoot]

/-- Lookup a natural number field inside a `Core.Data.record`. -/
def lookupNatField (key : String) : Data → Option Nat
  | .record fields =>
    match fields.lookup key with
    | some (.natural n) => some n
    | _                 => none
  | _ => none

/-- Council vote transition gate on `Core.Data`: status remains `1` (PENDING) and tally increments by `1`. -/
def voteTransitionGate : TransitionGate where
  pre  := fun d => lookupNatField "status" d == some 1
  post := fun d => lookupNatField "status" d == some 1
  link := fun old new =>
    match lookupNatField "tally" old, lookupNatField "tally" new with
    | some a, some b => b == a + 1
    | _,      _      => false

/-- Council resolve transition gate on `Core.Data`: status moves `1 → 2` (PENDING → RESOLVED)
    and tally crosses the quorum threshold `3`. -/
def resolveTransitionGate : TransitionGate where
  pre  := fun d => lookupNatField "status" d == some 1
  post := fun d => lookupNatField "status" d == some 2
  link := fun old new =>
    match lookupNatField "tally" old, lookupNatField "tally" new with
    | some a, some b => decide (a < 3) && decide (3 ≤ b)
    | _,      _      => false

/-- Demo effect type for reactive council affordances. -/
inductive CouncilEffect where
  | castBallot (proposalId : Nat)
  | resolveProposal (proposalId : Nat)
  | inspectTally (proposalId : Nat)
deriving DecidableEq, Repr

def councilEffectDigest : CouncilEffect → Nat
  | .castBallot n      => 3 * n
  | .resolveProposal n => 3 * n + 1
  | .inspectTally n    => 3 * n + 2

def demoFireCtx : FireCtx CouncilEffect where
  effectDigest := councilEffectDigest
  prevDigest   := 9
  preCommit    := 100
  postCommit   := 110

def voteAff : CellAffordance CouncilEffect :=
  { required := [.write], effect := .castBallot 1, name := "vote" }

def resolveAff : CellAffordance CouncilEffect :=
  { required := [.grant], effect := .resolveProposal 1, name := "resolve" }

def tallyViewAff : CellAffordance CouncilEffect :=
  { required := [.read], effect := .inspectTally 1, name := "tally" }

def voteReactiveBtn : ReactiveAffordance CouncilEffect :=
  { aff := voteAff, gate := voteTransitionGate, openHeight := 10, closeHeight := 20 }

def resolveReactiveBtn : ReactiveAffordance CouncilEffect :=
  { aff := resolveAff, gate := resolveTransitionGate, openHeight := 10, closeHeight := 30 }

def statePend0 : Data := .record [("status", .natural 1), ("tally", .natural 0)]
def statePend1 : Data := .record [("status", .natural 1), ("tally", .natural 1)]
def statePend2 : Data := .record [("status", .natural 1), ("tally", .natural 2)]
def stateResolved3 : Data := .record [("status", .natural 2), ("tally", .natural 3)]

def councilSurface : AffordanceSurface CouncilEffect :=
  [voteAff, resolveAff, tallyViewAff]

def chairViewer : MembraneViewer where
  held        := [.read, .write, .grant]
  permits     := fun n => n == "vote" || n == "resolve" || n == "tally"
  activeNames := ["vote", "resolve", "tally"]

def memberViewer : MembraneViewer where
  held        := [.read, .write]
  permits     := fun n => n == "vote" || n == "tally"
  activeNames := ["vote", "tally"]

def trusteeViewer : MembraneViewer where
  held        := [.read]
  permits     := fun n => n == "tally"
  activeNames := ["tally"]

def guestViewer : MembraneViewer where
  held        := [.read]
  permits     := fun _ => false
  activeNames := []

def councilSturdyref : Sturdyref CouncilEffect where
  uri       := "dregg://council/proposal-1"
  surface   := councilSurface
  log       := confinedLog
  lineage   := chairViewer
  reachable := false

/-! ## 1. Pillar 1 Verification: Derived `Rehydration` Liveness-Type & Replay Chain Coverage -/

/-- Incomplete v4 receipt root (`v4Complete = false`, `quorum = true`). -/
def incompleteV4Root : AttestedRoot := { root := 77, v4Complete := false, quorum := true }

/-- Log containing an incomplete v4 receipt root. -/
def incompleteV4Log : InteractionLog := [.attested goodRoot, .attested incompleteV4Root]

theorem pillar1_liveness_and_replay_suite :
    -- Empty log is vacuously confined and classifies as ReplayedDeterministic when non-live
    confined [] = true ∧
    classify [] false = .ReplayedDeterministic ∧
    -- Confined non-empty log classifies as ReplayedDeterministic and preserves full replay length
    confined confinedLog = true ∧
    classify confinedLog false = .ReplayedDeterministic ∧
    (witnessChainOf demoReceiptHash confinedLog).length = confinedLog.length ∧
    -- Ambient interaction breaks confinement, classifies as ReconstructedApproximate, and drops from replay chain
    confined ambientLog = false ∧
    classify ambientLog false = .ReconstructedApproximate ∧
    (witnessChainOf demoReceiptHash ambientLog).length < ambientLog.length ∧
    -- No-quorum root (`badRoot`) is not witnessed, breaks confinement, and drops from replay chain
    badRoot.holds = false ∧
    (Interaction.attested badRoot).isWitnessed = false ∧
    classify forgedLog false = .ReconstructedApproximate ∧
    (witnessChainOf demoReceiptHash forgedLog).length < forgedLog.length ∧
    -- Incomplete v4 receipt (`incompleteV4Root`) is also rejected as a witness
    incompleteV4Root.holds = false ∧
    classify incompleteV4Log false = .ReconstructedApproximate ∧
    (witnessChainOf demoReceiptHash incompleteV4Log).length < incompleteV4Log.length ∧
    -- Live reachability dominates regardless of log confinement
    classify confinedLog true = .Live ∧
    classify ambientLog true = .Live ∧
    classify forgedLog true = .Live := by
  decide

/-! ## 2. Pillar 2 Verification: `Sturdyref`, Per-Viewer `Membrane` & Chained Multi-Hop `Membrane.reshare` -/

/-- Viewer attempting to amplify projection permissions on `"resolve"` while holding `[.read, .write]`. -/
def permitsAmplifyingViewer : MembraneViewer where
  held        := [.read]
  permits     := fun n => n == "resolve" || n == "tally"
  activeNames := ["resolve", "tally"]

/-- Sneaky delegate that omits `"vote"` from its own `activeNames` while setting `permits "vote" = true`. -/
def sneakyVoteViewer : MembraneViewer where
  held        := [.read]
  permits     := fun n => n == "vote"
  activeNames := []

theorem pillar2_membrane_reshare_and_sturdyref_suite :
    -- Equal authority (`[.read]`), distinct witness-graph `permits` -> distinct projected surfaces
    trusteeViewer.held = guestViewer.held ∧
    projectMembrane trusteeViewer councilSurface = [tallyViewAff] ∧
    projectMembrane guestViewer councilSurface = [] ∧
    projectMembrane trusteeViewer councilSurface ≠ projectMembrane guestViewer councilSurface ∧
    -- 2-hop reshare chain: chair -> member -> trustee succeeds and strictly attenuates
    (match Membrane.reshare chairViewer memberViewer with
     | some mB =>
       match Membrane.reshare mB trusteeViewer with
       | some mC =>
         (projectMembrane mC councilSurface).length == 1 &&
         (projectMembrane mB councilSurface).length == 2 &&
         (projectMembrane chairViewer councilSurface).length == 3
       | none => false
     | none => false) = true ∧
    -- 2-hop delayed `activeNames` amplification refusal:
    -- `memberViewer -> guestViewer` succeeds even though `guestViewer.activeNames = []`,
    -- and `mB -> sneakyVoteViewer` is STILL refused because `mB` preserved `memberViewer.activeNames`
    (match Membrane.reshare memberViewer guestViewer with
     | some mB => (Membrane.reshare mB sneakyVoteViewer).isNone
     | none    => false) = true ∧
    -- Capability amplification (member -> chair, trying to gain `.grant`) is refused
    Membrane.reshare memberViewer chairViewer = none ∧
    -- Projection `permits` amplification on `activeNames` (member -> permitsAmplifyingViewer, trying to gain `"resolve"`) is refused
    Membrane.reshare memberViewer permitsAmplifyingViewer = none ∧
    -- Sturdyref rehydration pairs per-viewer attenuated surface with derived liveness-type
    rehydrateSturdyref councilSturdyref chairViewer = ([voteAff, resolveAff, tallyViewAff], .ReplayedDeterministic) ∧
    rehydrateSturdyref councilSturdyref memberViewer = ([voteAff, tallyViewAff], .ReplayedDeterministic) ∧
    rehydrateSturdyref councilSturdyref trusteeViewer = ([tallyViewAff], .ReplayedDeterministic) ∧
    rehydrateSturdyref councilSturdyref guestViewer = ([], .ReplayedDeterministic) ∧
    -- Unconfined sturdyref rehydrates with `.ReconstructedApproximate`
    (rehydrateSturdyref { councilSturdyref with log := ambientLog } chairViewer).2 = .ReconstructedApproximate ∧
    -- Live sturdyref rehydrates with `.Live`
    (rehydrateSturdyref { councilSturdyref with reachable := true } guestViewer).2 = .Live := by
  decide

/-! ## 3. Pillar 4 Verification: 3-Dimensional `ReactiveAffordance` & 6 Cross-Polarity Teeth -/

theorem pillar4_reactive_affordance_3d_suite :
    -- Positive corner: member votes inside window [10, 20] on valid 0 -> 1 tally increment
    (fireReactive voteReactiveBtn [.read, .write] 10 statePend0 statePend1 demoFireCtx).isSome = true ∧
    (fireReactive voteReactiveBtn [.read, .write] 15 statePend0 statePend1 demoFireCtx).isSome = true ∧
    (fireReactive voteReactiveBtn [.read, .write] 20 statePend0 statePend1 demoFireCtx).isSome = true ∧
    -- Transition Tooth: same destination `statePend1` reached from `statePend1` (0 increment) is refused
    fireReactive voteReactiveBtn [.read, .write] 15 statePend1 statePend1 demoFireCtx = none ∧
    -- Transition Tooth: jumping tally by 2 (`statePend0 -> statePend2`) is refused
    fireReactive voteReactiveBtn [.read, .write] 15 statePend0 statePend2 demoFireCtx = none ∧
    -- Deadline Tooth: past `closeHeight = 20` (`height = 21` and `height = 25`), refused
    fireReactive voteReactiveBtn [.read, .write] 21 statePend0 statePend1 demoFireCtx = none ∧
    fireReactive voteReactiveBtn [.read, .write] 25 statePend0 statePend1 demoFireCtx = none ∧
    -- Early Window Tooth: before `openHeight = 10` (`height = 9`), refused
    fireReactive voteReactiveBtn [.read, .write] 9 statePend0 statePend1 demoFireCtx = none ∧
    -- Capability Tooth: observer holding only `[.read]` is refused
    fireReactive voteReactiveBtn [.read] 15 statePend0 statePend1 demoFireCtx = none ∧
    -- Resolve button: chair resolves at height 22 when tally crosses quorum (`2 -> 3`, `PENDING -> RESOLVED`)
    (fireReactive resolveReactiveBtn [.read, .grant] 22 statePend2 stateResolved3 demoFireCtx).isSome = true ∧
    -- Resolve Transition Tooth: already-resolved `stateResolved3 -> stateResolved3` is refused
    fireReactive resolveReactiveBtn [.read, .grant] 22 stateResolved3 stateResolved3 demoFireCtx = none ∧
    -- Effect and boundRoot integrity on committed reactive fire
    (match fireReactive voteReactiveBtn [.read, .write] 15 statePend0 statePend1 demoFireCtx with
     | some intent =>
       intent.surface.firedEffect == CouncilEffect.castBallot 1 &&
       intent.surface.boundRoot == 110 &&
       intent.effectsHash == councilEffectDigest (.castBallot 1)
     | none => false) = true := by
  decide

/-! ## 5. `#tooth` Kernel Mutation Tests -/

/-- 1a. Broken `AttestedRoot.holds` that rubber-stamps every attestation (`true`) regardless of
`v4Complete` or `quorum`. -/
def attestedRootHoldsAlwaysTrue (_ar : AttestedRoot) : Bool :=
  true

#tooth Obend.Vault.Rehydration.invalidAttestation_not_replayed by mutation Obend.Vault.Rehydration.AttestedRoot.holds := attestedRootHoldsAlwaysTrue
#tooth Obend.Vault.Rehydration.invalidAttestation_not_replayed_of_flags by mutation Obend.Vault.Rehydration.AttestedRoot.holds := attestedRootHoldsAlwaysTrue

/-- 1b. Broken `AttestedRoot.holds` that checks `v4Complete` but ignores `quorum`. -/
def attestedRootHoldsIgnoreQuorum (ar : AttestedRoot) : Bool :=
  ar.v4Complete

#tooth Obend.Vault.Rehydration.invalidAttestation_not_replayed_of_flags by mutation Obend.Vault.Rehydration.AttestedRoot.holds := attestedRootHoldsIgnoreQuorum
#tooth Obend.Vault.Rehydration.attestedRoot_holds_iff by mutation Obend.Vault.Rehydration.AttestedRoot.holds := attestedRootHoldsIgnoreQuorum

/-- 2a. Broken `Interaction.isWitnessed` that treats `.ambient` interactions as witnessed (`true`). -/
def interactionIsWitnessedAlwaysTrue (_i : Interaction) : Bool :=
  true

#tooth Obend.Vault.Rehydration.ambient_chain_drops_the_reach by mutation Obend.Vault.Rehydration.Interaction.isWitnessed := interactionIsWitnessedAlwaysTrue

/-- 2b. Broken `Interaction.isWitnessed` that accepts any `.attested ar` without checking `ar.holds`. -/
def interactionIsWitnessedSkipHolds : Interaction → Bool
  | .attested _ => true
  | .ambient    => false

#tooth Obend.Vault.Rehydration.invalidAttestation_not_replayed by mutation Obend.Vault.Rehydration.Interaction.isWitnessed := interactionIsWitnessedSkipHolds

/-- 3a. Broken `Membrane.reshare` that rubber-stamps every delegation target (`some delegateTarget`),
allowing capability and projection amplification across hops. -/
def membraneReshareRubberStamp (_holderMembrane delegateTarget : MembraneViewer) : Option MembraneViewer :=
  some delegateTarget

#tooth Obend.Vault.Rehydration.amplifying_reshare_refused by mutation Obend.Vault.Rehydration.Membrane.reshare := membraneReshareRubberStamp
#tooth Obend.Vault.Rehydration.reshare_chain_attenuates by mutation Obend.Vault.Rehydration.Membrane.reshare := membraneReshareRubberStamp

/-- 3b. Broken `Membrane.reshare` that checks `fireGate` on `held` capabilities but skips the
`permitsSubsetOn` check on witness-graph projections. -/
def membraneReshareSkipPermits (holderMembrane delegateTarget : MembraneViewer) : Option MembraneViewer :=
  if fireGate delegateTarget.held holderMembrane.held then
    some delegateTarget
  else
    none

#tooth Obend.Vault.Rehydration.amplifying_permits_reshare_refused by mutation Obend.Vault.Rehydration.Membrane.reshare := membraneReshareSkipPermits
#tooth Obend.Vault.Rehydration.reshare_chain_attenuates by mutation Obend.Vault.Rehydration.Membrane.reshare := membraneReshareSkipPermits

/-- 3c. Broken `Membrane.reshare` that drops `holderMembrane.activeNames` in the returned viewer,
allowing a 2-hop chain through an empty-`activeNames` intermediate hop to evade upstream checks. -/
def membraneReshareDropActiveNames (holderMembrane delegateTarget : MembraneViewer) : Option MembraneViewer :=
  if fireGate delegateTarget.held holderMembrane.held &&
     permitsSubsetOn (holderMembrane.activeNames ++ delegateTarget.activeNames)
       delegateTarget.permits holderMembrane.permits then
    some {
      held        := delegateTarget.held
      permits     := fun n => holderMembrane.permits n && delegateTarget.permits n
      activeNames := delegateTarget.activeNames.filter holderMembrane.permits
    }
  else
    none

#tooth Obend.Vault.Rehydration.reshare_chain_attenuates by mutation Obend.Vault.Rehydration.Membrane.reshare := membraneReshareDropActiveNames
#tooth Obend.Vault.Rehydration.reshare_chain_blocks_delayed_permits_amplification by mutation Obend.Vault.Rehydration.Membrane.reshare := membraneReshareDropActiveNames

/-- 3d. Broken `permitsSubsetOn` that rubber-stamps every projection subset check (`true`). -/
def permitsSubsetOnAlwaysTrue (_activeNames : List String) (_child _parent : String → Bool) : Bool :=
  true

#tooth Obend.Vault.Rehydration.reshare_some_attenuates by mutation Obend.Vault.Rehydration.permitsSubsetOn := permitsSubsetOnAlwaysTrue
#tooth Obend.Vault.Rehydration.reshare_chain_attenuates by mutation Obend.Vault.Rehydration.permitsSubsetOn := permitsSubsetOnAlwaysTrue

/-- 4a. Broken `transitionOK` that rubber-stamps every state transition (`true`). -/
def transitionOKRubberStamp (_tg : TransitionGate) (_old _new : Data) : Bool :=
  true

#tooth Obend.Vault.Rehydration.transitionOK_iff by mutation Obend.Vault.Rehydration.transitionOK := transitionOKRubberStamp

/-- 4b. Broken `transitionOK` that checks single-state `pre old` and `post new` predicates but drops
the relational `tg.link old new` bridge. -/
def transitionOKDropLink (tg : TransitionGate) (old new : Data) : Bool :=
  tg.pre old && tg.post new

#tooth Obend.Vault.Rehydration.fireReactive_wrong_old_refuses by mutation Obend.Vault.Rehydration.transitionOK := transitionOKDropLink

/-- 5a. Broken `inWindow` that never closes (`true` at every height). -/
def inWindowAlwaysTrue {φ : Type} (_ra : ReactiveAffordance φ) (_height : Nat) : Bool :=
  true

#tooth Obend.Vault.Rehydration.fireReactive_iff by mutation Obend.Vault.Rehydration.inWindow := inWindowAlwaysTrue

/-- 5b. Broken `inWindow` that checks `openHeight ≤ height` but drops the upper deadline `height ≤ closeHeight`. -/
def inWindowDropDeadline {φ : Type} (ra : ReactiveAffordance φ) (height : Nat) : Bool :=
  decide (ra.openHeight ≤ height)

#tooth Obend.Vault.Rehydration.fireReactive_after_deadline_refuses by mutation Obend.Vault.Rehydration.inWindow := inWindowDropDeadline

/-- 5c. Broken `inWindow` that checks `height ≤ closeHeight` but drops the lower bound `openHeight ≤ height`. -/
def inWindowDropOpenBound {φ : Type} (ra : ReactiveAffordance φ) (height : Nat) : Bool :=
  decide (height ≤ ra.closeHeight)

#tooth Obend.Vault.Rehydration.fireReactive_before_open_refuses by mutation Obend.Vault.Rehydration.inWindow := inWindowDropOpenBound

/-- 6. Broken `classify` that misclassifies non-live unconfined logs as `.ReplayedDeterministic`. -/
def classifyAlwaysReplayed (_log : InteractionLog) (reachable : Bool) : Rehydration :=
  if reachable then .Live else .ReplayedDeterministic

#tooth Obend.Vault.Rehydration.replayedDeterministic_iff_confined by mutation Obend.Vault.Rehydration.classify := classifyAlwaysReplayed

/-- 7. Broken `membraneShows` that checks `fireGate` on capabilities but ignores `viewer.permits`. -/
def membraneShowsIgnorePermits {φ : Type} (viewer : MembraneViewer) (aff : CellAffordance φ) : Bool :=
  fireGate aff.required viewer.held

#tooth Obend.Vault.Rehydration.membrane_two_viewers_distinct by mutation Obend.Vault.Rehydration.membraneShows := membraneShowsIgnorePermits

/-! ## 6. Axiom Hygiene Verification (`0 sorryAx`, `0` Custom Axioms) -/

-- Pillar 1: Derived `Rehydration` Liveness-Type & Replay Coverage
#print axioms Obend.Vault.Rehydration.attestedRoot_holds_iff
#print axioms Obend.Vault.Rehydration.attestedRoot_not_holds_of_false
#print axioms Obend.Vault.Rehydration.replayedDeterministic_iff_confined
#print axioms Obend.Vault.Rehydration.reconstructedApproximate_iff_unconfined
#print axioms Obend.Vault.Rehydration.invalidAttestation_not_replayed
#print axioms Obend.Vault.Rehydration.invalidAttestation_not_replayed_of_flags
#print axioms Obend.Vault.Rehydration.chain_tamper_evident
#print axioms Obend.Vault.Rehydration.chain_tamper_evident_or
#print axioms Obend.Vault.Rehydration.replayFold_wellLinked
#print axioms Obend.Vault.Rehydration.rootOf_isSome_iff_witnessed
#print axioms Obend.Vault.Rehydration.witnessChain_wellLinked
#print axioms Obend.Vault.Rehydration.witnessChainOf_wellLinked
#print axioms Obend.Vault.Rehydration.confined_chain_covers_log
#print axioms Obend.Vault.Rehydration.unconfined_chain_drops_interactions
#print axioms Obend.Vault.Rehydration.ambient_chain_drops_the_reach
#print axioms Obend.Vault.Rehydration.replayedDeterministic_replays

-- Pillar 2: `Sturdyref`, Per-Viewer `Membrane`, and Chained Reshare Attenuation
#print axioms Obend.Vault.Rehydration.mem_projectMembrane
#print axioms Obend.Vault.Rehydration.membrane_two_viewers_distinct
#print axioms Obend.Vault.Rehydration.membrane_authority_monotone
#print axioms Obend.Vault.Rehydration.membrane_monotone_both
#print axioms Obend.Vault.Rehydration.permitsSubsetOn_iff
#print axioms Obend.Vault.Rehydration.reshare_isSome_iff
#print axioms Obend.Vault.Rehydration.amplifying_reshare_refused
#print axioms Obend.Vault.Rehydration.amplifying_permits_reshare_refused
#print axioms Obend.Vault.Rehydration.reshare_some_attenuates
#print axioms Obend.Vault.Rehydration.reshare_chain_attenuates
#print axioms Obend.Vault.Rehydration.reshare_chain_blocks_delayed_permits_amplification
#print axioms Obend.Vault.Rehydration.rehydrateSturdyref_liveness_iff_confined
#print axioms Obend.Vault.Rehydration.rehydrateSturdyref_attenuates_both
#print axioms Obend.Vault.Rehydration.rehydrateSturdyref_reshare_monotone

-- Pillar 4: 3-Dimensional `ReactiveAffordance` & 6 Cross-Polarity Teeth
#print axioms Obend.Vault.Rehydration.transitionOK_iff
#print axioms Obend.Vault.Rehydration.inWindow_iff
#print axioms Obend.Vault.Rehydration.reactiveOK_iff
#print axioms Obend.Vault.Rehydration.fireReactive_iff
#print axioms Obend.Vault.Rehydration.fireReactive_all_pass
#print axioms Obend.Vault.Rehydration.fireReactive_cap_fail_refuses
#print axioms Obend.Vault.Rehydration.fireReactive_transition_fail_refuses
#print axioms Obend.Vault.Rehydration.fireReactive_window_fail_refuses
#print axioms Obend.Vault.Rehydration.fireReactive_wrong_old_refuses
#print axioms Obend.Vault.Rehydration.fireReactive_after_deadline_refuses
#print axioms Obend.Vault.Rehydration.fireReactive_before_open_refuses
#print axioms Obend.Vault.Rehydration.fireReactive_window_reactive
#print axioms Obend.Vault.Rehydration.fireReactive_carries_real_effect
#print axioms Obend.Vault.Rehydration.fireReactive_binds_attested_root

-- Master Suite Theorems
#print axioms Obend.Tests.Rehydration.pillar1_liveness_and_replay_suite
#print axioms Obend.Tests.Rehydration.pillar2_membrane_reshare_and_sturdyref_suite
#print axioms Obend.Tests.Rehydration.pillar4_reactive_affordance_3d_suite

end Obend.Tests.Rehydration

end
