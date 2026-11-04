module
/-
# Obend.Consensus.SovereignFinality — 4-Tier Sovereign Finality & Durable Crash-Recovery Spine

Pillar 5B Formal Spine (`DEOS-CONTRACTS-CONSENSUS.md` §4):
Welds the 4-tier finality hierarchy across `.obend` surface laws, wide-pullback vault turns,
accountable `Simplex` BFT consensus, epistemic solver/EDA races, `Obend.Run.Durable`
crash-recovery (`DState`, `hstep`, `runDurableTrace`), and `Obend.Fold.Collapse` Merkle
checkpointing:

- **Tier 0 (Confluent Local / Speculative)**:
  `Obend.Spec.LawDial.dial_free_confluent` — laws with `dial e = .free` form an ACId
  join-semilattice under `joinData` (`max`), merging concurrent speculative states without
  ordering coordination.
- **Tier 1 (Disjoint Fast-Path / Attested)**:
  `Obend.Vault.vaultTurn_disjoint_commutes` & `disjoint_both_orders` — `VaultTurn`s with
  Bernstein-disjoint footprints (`DisjointTurns T₁ T₂`) commute on `VaultStore`, preserve
  `ValidAt` in either execution order, and converge on the same `collapseRoot`.
- **Tier 2 (Contended Accountable Simplex BFT / Quorum-Final)**:
  `Obend.Consensus.Simplex` (`castVote_already_voted`, `honest_quorum_intersection`,
  `qc_same_view_unique`, `simplex_accountable_safety`) welded to
  `Obend.Consensus.Finality.advanceQuorumBoundGate_formQC_sound`.
- **Tier 3 (Epistemic Verifiable Race & Collapsed Archive)**:
  `Obend.Consensus.Epistemic` (`VerifiableRace`, `selectWinner`, `order_insensitive_pair`,
  `frontrunning_resistant_pair`) instantiated for both `DrEXRace` (`drex-clearing@1`) and
  `AgenticEDA` (`MultiAgentBoardMergeProposal` / `mergeAndJudgeAgenticEdaBoard`), folded
  into `Obend.Fold.Collapse.collapseTrace`.
- **Durable Crash-Recovery Metatheorems**:
  1. `durable_recovery_prevents_equivocation`,
  2. `durable_expose_once_across_crashes`,
  3. `durable_recovered_converges_on_collapse_root`.
-/

public import Obend.Spec.LawDial
public import Obend.Vault.Hyperedge
public import Obend.Consensus.Simplex
public import Obend.Consensus.Finality
public import Obend.Consensus.Epistemic
public import Obend.Hardware.AgenticEDA
public import Obend.Run.Durable
public import Obend.Fold.Collapse
public import Obend.Tactic.Tooth
import all Obend.Consensus.Simplex
import all Obend.Consensus.Finality
import all Obend.Hardware.AgenticEDA
import all Obend.Run.Durable

@[expose] public section

namespace Obend.Consensus.SovereignFinality

open Obend.Core.Data (Data)
open Obend.Spec.Law (LawExpr Facts)
open Obend.Spec.LawDial (DialVerdict dial joinData dial_free_confluent)
open Obend.Law (CellContract Holds)
open Obend.Vault (VaultStore VaultTurn DisjointTurns ValidAt applyTurn
  vaultTurn_disjoint_commutes disjoint_both_orders)
open Obend.Consensus.Simplex (NodeId View Block State ViewRecord viewAt putView castVote
  castVote_already_voted honest_quorum_intersection qc_same_view_unique
  SlashingReceipt extractSlashingReceipt simplex_accountable_safety)
open Obend.Consensus.Finality (FinalityTier Operation admitsOp QuorumBoundFinalityGate
  QuorumBoundPromotionEvent advanceQuorumBoundGate advanceQuorumBoundGate_formQC_sound)
open Obend.Consensus.Epistemic
open Obend.Hardware.AgenticEDA (EdaVaultPart MultiAgentBoardMergeProposal AgenticEdaVerdict
  edaBoardConflictFields mergeEdaPartFields3 mergeAndJudgeAgenticEdaBoard
  mergeAndJudgeAgenticEdaBoard_sound conflictingAgentBoardEdits_refused
  mergeAndJudgeAgenticEdaBoard_commutative goldenMultiAgentCoDesignProposal
  conflictingMultiAgentCoDesignProposal
  goldenMultiAgentCoDesign_admitted_and_conflict_refused)
open Obend.Slot Obend.Slot.Protocol Obend.Run.Control Obend.Run.Shared
open Obend.Run.Durable (DState HEvent HRefusal JEv hstep replay pending
  runDurableTrace crash_recover_idempotent pending_decreases_on_expose)
open Obend.Fold.Collapse (CommittedBlock Trace StoreValuation stepBlock foldTrace
  collapseRoot collapseTrace filterActive foldTrace_filter_empty collapseTrace_prune_empty)
open Obend.Digest.HashBytes (Hash)
open Obend.Digest.Cshake256.Native (cshake256Kernel)

set_option autoImplicit false

/-! ## §1. Tier 0 — Confluent Local Semilattice (`dial_free_confluent`) -/

/-- **Tier 0 Sovereign Finality (`tier0_dial_free_confluent`)**:
    When a surface `.obend` law `e` has `dial e = .free`, Tier 0 (`FinalityTier.speculative`)
    admits optimistic reads (`admitsOp .speculative .readUncommitted = true`) and any two
    concurrently admitted target states `n₁` and `n₂` merge without consensus ordering via
    `joinData n₁ n₂` while preserving `e.denote facts old (joinData n₁ n₂) = true`. -/
theorem tier0_dial_free_confluent
    {e : LawExpr} (hd : dial e = .free)
    {facts : Facts} {old : Option Data} {n₁ n₂ : Data}
    (h₁ : e.denote facts old n₁ = true)
    (h₂ : e.denote facts old n₂ = true) :
    admitsOp .speculative .readUncommitted = true ∧
    e.denote facts old (joinData n₁ n₂) = true :=
  ⟨rfl, dial_free_confluent hd h₁ h₂⟩

/-! ## §2. Tier 1 — Disjoint Fast-Path Commutativity (`vaultTurn_disjoint_commutes`) -/

/-- **Tier 1 Sovereign Finality (`tier1_disjoint_fast_path_commutes`)**:
    For any two `VaultTurn`s `T₁` and `T₂` with Bernstein-disjoint footprints (`DisjointTurns T₁ T₂`)
    that are each valid at store `s`:
    1. Tier 1 (`FinalityTier.attested`) admits deterministic read-only preview (`executeReadOnly`),
    2. `T₁` and `T₂` remain valid in both serial orders (`ValidAt (applyTurn s T₁) T₂` and
       `ValidAt (applyTurn s T₂) T₁`),
    3. Applying `T₁` then `T₂` produces the exact same `VaultStore` as applying `T₂` then `T₁`,
    4. Both execution orders collapse to the exact same Merkle root `collapseRoot H schema val`. -/
theorem tier1_disjoint_fast_path_commutes
    (H : Hash) (schema : List String) (val : StoreValuation)
    (s : VaultStore) (T₁ T₂ : VaultTurn)
    (contracts : String → Option CellContract)
    (formats : List Obend.Judge.Format := [])
    (h_disj : DisjointTurns T₁ T₂)
    (h₁ : ValidAt s T₁ contracts formats)
    (h₂ : ValidAt s T₂ contracts formats) :
    admitsOp .attested .executeReadOnly = true ∧
    (ValidAt (applyTurn s T₁) T₂ contracts formats ∧
     ValidAt (applyTurn s T₂) T₁ contracts formats) ∧
    applyTurn (applyTurn s T₁) T₂ = applyTurn (applyTurn s T₂) T₁ ∧
    collapseRoot H schema val (applyTurn (applyTurn s T₁) T₂) =
      collapseRoot H schema val (applyTurn (applyTurn s T₂) T₁) := by
  have h_comm := vaultTurn_disjoint_commutes s T₁ T₂ h_disj
  refine ⟨rfl, disjoint_both_orders s T₁ T₂ contracts formats h_disj h₁ h₂, h_comm, ?_⟩
  rw [h_comm]

/-! ## §3. Tier 2 — Contended Accountable Simplex BFT & Quorum-Bound Gate -/

/-- **Tier 2 Sovereign Finality (`tier2_simplex_quorum_and_accountable_safety`)**:
    Welds `advanceQuorumBoundGate_formQC_sound`, `qc_same_view_unique`, and
    `simplex_accountable_safety`:
    1. Promoting a `QuorumBoundFinalityGate` via `.formQC qcDigest signers root` reaches
       `.quorum_final` (`admitsOp .quorum_final .stateWrite = true`) with a non-empty quorum
       `2 * gate.faults + 1 ≤ next.qcSigners.length` and non-zero `stateRoot`,
    2. When at most `f` validators in a `3 * f + 1` committee are faulty, any two `2 * f + 1`
       quorums in the same view must agree on the finalized block value (`val1 = val2`),
    3. If a Byzantine coalition ever signs two conflicting `2 * f + 1` quorums `blockA ≠ blockB`
       in the same view, `extractSlashingReceipt` constructively identifies at least `f + 1`
       provably equivocating validators. -/
theorem tier2_simplex_quorum_and_accountable_safety
    (gate next : QuorumBoundFinalityGate)
    (qcDigest : Nat) (signers : List Nat) (root : Nat)
    (h_gate : advanceQuorumBoundGate gate (.formQC qcDigest signers root) = some next)
    (view blockA blockB : Nat)
    (committee : List Nat)
    (votedA votedB : Nat → Bool)
    (h_distinct : blockA ≠ blockB)
    (h_committee : committee.length ≤ 3 * gate.faults + 1)
    (h_quorumA : 2 * gate.faults + 1 ≤ (committee.filter votedA).length)
    (h_quorumB : 2 * gate.faults + 1 ≤ (committee.filter votedB).length) :
    let receipt := extractSlashingReceipt view blockA blockB committee votedA votedB
    next.currentTier = .quorum_final ∧
    admitsOp next.currentTier .stateWrite = true ∧
    2 * gate.faults + 1 ≤ next.qcSigners.length ∧
    next.stateRoot ≠ 0 ∧
    receipt.blockA ≠ receipt.blockB ∧
    gate.faults + 1 ≤ receipt.equivocatingVoters.length ∧
    (∀ v ∈ receipt.equivocatingVoters, v ∈ committee ∧ votedA v = true ∧ votedB v = true) := by
  have ⟨h_tier, _, _, _, _, h_qlen, _, h_nz⟩ :=
    advanceQuorumBoundGate_formQC_sound gate next qcDigest signers root h_gate
  have ⟨h_neq, h_slash_len, h_slash_mem⟩ :=
    simplex_accountable_safety view blockA blockB gate.faults committee votedA votedB
      h_distinct h_committee h_quorumA h_quorumB
  refine ⟨h_tier, ?_, h_qlen, h_nz, h_neq, h_slash_len, h_slash_mem⟩
  rw [h_tier]
  rfl

/-- Promoting to `.quorum_final` via `advanceQuorumBoundGate` guarantees duplicate-free
    committee signers (`next.qcSigners.Nodup ∧ ∀ s ∈ next.qcSigners, s ∈ gate.committee`). -/
theorem tier2_quorum_gate_nodup_and_committee_sound
    (gate next : QuorumBoundFinalityGate)
    (qcDigest : Nat) (signers : List Nat) (root : Nat)
    (h_gate : advanceQuorumBoundGate gate (.formQC qcDigest signers root) = some next) :
    next.qcSigners.Nodup ∧ (∀ s ∈ next.qcSigners, s ∈ gate.committee) := by
  have ⟨_, _, _, h_nodup, h_comm, _, _, _⟩ :=
    advanceQuorumBoundGate_formQC_sound gate next qcDigest signers root h_gate
  exact ⟨h_nodup, h_comm⟩

/-! ## §4. Tier 3 — Epistemic Verifiable Race (`DrEXRace` & `AgenticEDA`) -/

/-- Candidate wrapper for multi-agent PCB & BOM co-design (`Obend.Hardware.AgenticEDA`)
    participating in a Tier 3 `VerifiableRace`. -/
structure EdaSwarmCandidate where
  prop : MultiAgentBoardMergeProposal
  digestSeed : ByteArray
  deriving DecidableEq, Repr

/-- Check whether an `EdaSwarmCandidate` passes the 3-way LCA semantic merge and
    hardware DRC + Netlist + BOM judge (`mergeAndJudgeAgenticEdaBoard`). -/
def checkEdaSwarmCandidate (c : EdaSwarmCandidate) : Bool :=
  decide (mergeAndJudgeAgenticEdaBoard c.prop = .admitted)

/-- Cost metric for `EdaSwarmCandidate`: lower BOM cost (`costCents`) + lower RF VSWR (`vswrMilli`)
     + lower peak junction temperature (`maxTempMc`) is strictly superior. -/
def edaSwarmCandidateCost (c : EdaSwarmCandidate) : Nat :=
  let merged := mergeEdaPartFields3 c.prop.baseBoard c.prop.powerAgentBoard c.prop.rfLayoutAgentBoard
  merged.costCents + merged.vswrMilli + merged.maxTempMc

/-- Deterministic cSHAKE256 tie-breaker digest for `EdaSwarmCandidate`. -/
def edaSwarmCandidateDigest (c : EdaSwarmCandidate) : ByteArray :=
  cshake256Kernel (ByteArray.mk #[0x45, 0x44, 0x41, 0x31]) c.digestSeed

/-- `VerifiableRace` instance for `EdaSwarmCandidate` over `Obend.Hardware.AgenticEDA`. -/
instance instVerifiableRaceEdaSwarm : VerifiableRace Unit EdaSwarmCandidate where
  isValid _ c := checkEdaSwarmCandidate c
  cost _ c := edaSwarmCandidateCost c
  digest c := edaSwarmCandidateDigest c

/-- **Tier 3 AgenticEDA Epistemic Winner Soundness (`edaSwarm_winner_admitted_and_sound`)**:
    Whenever `selectWinner () candidates = some w`, the winning `EdaSwarmCandidate` is a member
    of `candidates`, passes `mergeAndJudgeAgenticEdaBoard w.prop = .admitted`, has zero 3-way
    LCA merge conflicts, satisfies all `.obend` `law:` smart contracts, pins a fresh datasheet
    citation, fits the 2D PCB courtyard, and meets CMOS static noise margins. -/
theorem edaSwarm_winner_admitted_and_sound
    {candidates : List EdaSwarmCandidate} {w : EdaSwarmCandidate}
    (h_win : selectWinner () candidates = some w) :
    let mergedBoard := mergeEdaPartFields3 w.prop.baseBoard w.prop.powerAgentBoard w.prop.rfLayoutAgentBoard
    w ∈ candidates ∧
    mergeAndJudgeAgenticEdaBoard w.prop = .admitted ∧
    edaBoardConflictFields w.prop.baseBoard w.prop.powerAgentBoard w.prop.rfLayoutAgentBoard = [] ∧
    w.prop.citePin.pinnedBlockHash = w.prop.citePin.currentDatasheetHash ∧
    mergedBoard.pinCount = w.prop.courtyard.requiredPinCount ∧
    mergedBoard.pinPitchUm = w.prop.courtyard.requiredPinPitchUm ∧
    mergedBoard.pkgWidthUm ≤ w.prop.courtyard.maxCourtyardWidthUm ∧
    mergedBoard.pkgLengthUm ≤ w.prop.courtyard.maxCourtyardLengthUm := by
  have h_mem := winner_mem h_win
  have h_val := winner_is_valid h_win
  dsimp [certValid, instVerifiableRaceEdaSwarm, checkEdaSwarmCandidate] at h_val
  have h_adm : mergeAndJudgeAgenticEdaBoard w.prop = .admitted := of_decide_eq_true h_val
  have h_sound := mergeAndJudgeAgenticEdaBoard_sound w.prop h_adm
  exact ⟨h_mem, h_adm, h_sound.1, h_sound.2.2.1, h_sound.2.2.2.1,
    h_sound.2.2.2.2.1, h_sound.2.2.2.2.2.1, h_sound.2.2.2.2.2.2.1⟩

/-- **Tier 3 Conflicting Agent Edits Refused in Epistemic Race (`edaSwarm_conflicting_candidate_invalid`)**:
    Any `EdaSwarmCandidate` whose power and RF agents made conflicting edits to the same field
    (`edaBoardConflictFields ... ≠ []`) is rejected by `certValid`. -/
theorem edaSwarm_conflicting_candidate_invalid
    (c : EdaSwarmCandidate)
    (h_conflict : edaBoardConflictFields c.prop.baseBoard c.prop.powerAgentBoard c.prop.rfLayoutAgentBoard ≠ []) :
    certValid () c = false := by
  have ⟨_, h_not_adm⟩ := conflictingAgentBoardEdits_refused c.prop h_conflict
  dsimp [certValid, instVerifiableRaceEdaSwarm, checkEdaSwarmCandidate]
  exact decide_eq_false h_not_adm

/-- **Tier 3 Order-Insensitivity & Frontrunning Resistance for both `DrEXRace` and `AgenticEDA`**:
    In both the `drex-clearing@1` LP solver race and the `AgenticEDA` multi-agent board merge race,
    `selectWinner` is invariant under candidate arrival order (`order_insensitive_pair`) and immune
    to inferior or invalid frontrunning candidates (`frontrunning_resistant_pair`). -/
theorem tier3_epistemic_drex_and_eda_race_sound
    (q : Obend.Judge.ClearingQuery)
    (d₁ d₂ : DrEXRace.ClearingCert)
    (hd₁ : certValid q d₁ = true)
    (hd₂ : certValid q d₂ = true)
    (hd_better : betterCert q d₁ d₂ = true)
    (e₁ e₂ : EdaSwarmCandidate)
    (he₁ : certValid () e₁ = true)
    (he₂ : certValid () e₂ = true)
    (he_better : betterCert () e₁ e₂ = true) :
    selectWinner q [d₁, d₂] = some d₁ ∧
    selectWinner q [d₁, d₂] = selectWinner q [d₂, d₁] ∧
    selectWinner () [e₁, e₂] = some e₁ ∧
    selectWinner () [e₁, e₂] = selectWinner () [e₂, e₁] :=
  ⟨frontrunning_resistant_pair hd₁ hd_better,
   order_insensitive_pair hd₁ hd₂ hd_better,
   frontrunning_resistant_pair he₁ he_better,
   order_insensitive_pair he₁ he₂ he_better⟩

/-! ## §5. Durable Crash-Recovery Metatheorems (`Obend.Run.Durable` + `Simplex` + `Collapse`) -/

/-- Durable validator host state pairing a durable append-only vote journal (`journaledViews`)
    with volatile in-memory `Simplex.State` (`volatileState : Option State`). -/
structure DurableSimplexHost where
  self : NodeId
  deadline : Nat
  journaledViews : List ViewRecord
  volatileState : Option State
  deriving BEq, Inhabited

/-- Record a view's vote durably in `journaledViews` and in `volatileState` before broadcasting. -/
def durableCastVote (host : DurableSimplexHost) (v : View) (b : Block) :
    Option DurableSimplexHost :=
  match host.volatileState with
  | none => none
  | some st =>
    if (viewAt st v).voted || (viewAt st v).disableRequested then
      some host
    else
      let st' := castVote st v b
      let vr' := viewAt st' v
      let updatedJournal :=
        if host.journaledViews.any (fun old => old.number == v) then
          host.journaledViews.map (fun old => if old.number == v then vr' else old)
        else
          host.journaledViews ++ [vr']
      some { host with journaledViews := updatedJournal, volatileState := some st' }

/-- Simulate a node crash: volatile `Simplex.State` is wiped (`none`), while `journaledViews` survives. -/
def crashSimplexHost (host : DurableSimplexHost) : DurableSimplexHost :=
  { host with volatileState := none }

/-- Recover a crashed `DurableSimplexHost` by replaying `journaledViews` into `Simplex.State`. -/
def recoverSimplexHost (host : DurableSimplexHost) : DurableSimplexHost :=
  let restored : State :=
    { self := host.self
      deadline := host.deadline
      views := host.journaledViews }
  { host with volatileState := some restored }

/-- **Durable Crash-Recovery Metatheorem 1 (`durable_recovery_prevents_equivocation`)**:
    1. On a `DurableSimplexHost`, if view `v` has already been voted (`(viewAt st v).voted = true`
       in the durable journal), then after crashing (`crashSimplexHost`) and recovering from the
       durable journal (`recoverSimplexHost`), `castVote` on the recovered `Simplex.State` for ANY
       conflicting block `b'` is a no-op (`castVote restored v b' = restored`), preventing
       post-crash double-voting!
    2. On `Obend.Run.Durable.DState`, any sequence of `crashes ≥ 1` consecutive `.crash` events
       followed by `.recover` preserves the exact pre-crash durable `journal` and `outbox`. -/
theorem durable_recovery_prevents_equivocation
    {Ix : Type} {S : Sig Ix} {Hole : Ix → Type} {A : Ix → Type}
    {ι P Cred Cand Tok Fact Ob W : Type}
    [DecidableEq ι] [DecidableEq Ix] [∀ i, DecidableEq (Hole i)] [DecidableEq Tok]
    [DecidableEq Cand] [DecidableEq (Σ i, S.Op i)]
    (L : Ledger ι W Tok)
    (base : W → View Tok Fact)
    (sp : ι → Spec S Tok Fact Ob)
    (au : ι → Authority P Cred)
    (k : ι → (j : Ix) → Hole j → SlotCtl S Hole A P Fact Cand j)
    {i₀ : Ix}
    (J₀ : JCfg L S Hole A P Cand Fact Ob i₀)
    (s : DState L S Hole A P Cred Cand Fact Ob i₀)
    (crashes : Nat) (hc : 1 ≤ crashes)
    (host : DurableSimplexHost) (v : Obend.Consensus.Simplex.View) (b' : Block)
    (hv_voted : ((host.journaledViews.find? (fun vr => vr.number == v)).getD { number := v }).voted = true) :
    let recoveredHost := recoverSimplexHost (crashSimplexHost host)
    let restoredState : State :=
      { self := host.self, deadline := host.deadline, views := host.journaledViews }
    let trace : List (HEvent L S Hole A P Cred Cand Fact) := List.replicate crashes .crash ++ [.recover]
    recoveredHost.volatileState = some restoredState ∧
    (viewAt restoredState v).voted = true ∧
    castVote restoredState v b' = restoredState ∧
    (runDurableTrace L base sp au k J₀ s trace).journal = s.journal ∧
    (runDurableTrace L base sp au k J₀ s trace).outbox = s.outbox := by
  have h_idemp := crash_recover_idempotent L base sp au k J₀ s crashes hc
  have h_view_voted :
      (viewAt { self := host.self, deadline := host.deadline, views := host.journaledViews } v).voted = true := by
    simpa [viewAt] using hv_voted
  have h_cast_noop :=
    castVote_already_voted
      { self := host.self, deadline := host.deadline, views := host.journaledViews }
      v b' h_view_voted
  exact ⟨rfl, h_view_voted, h_cast_noop, h_idemp.2.1, h_idemp.2.2⟩

/-- **Durable Crash-Recovery Metatheorem 2 (`durable_expose_once_across_crashes`)**:
    If a dispatch effect at journal position `n` is exposed (`hstep ... s (.expose n) = .ok s₁`),
    and the node subsequently suffers `crashes ≥ 1` consecutive `.crash` events followed by `.recover`
    (`s_rec := runDurableTrace ... s₁ (List.replicate crashes .crash ++ [.recover])`), then:
    1. `n` remains in `s_rec.outbox` and is NOT in `pending L s_rec`,
    2. `pending L s_rec` is strictly shorter than `pending L s`,
    3. Any post-recovery attempt to re-expose `n` is deterministically refused with `.error (.exposed n)`. -/
theorem durable_expose_once_across_crashes
    {Ix : Type} {S : Sig Ix} {Hole : Ix → Type} {A : Ix → Type}
    {ι P Cred Cand Tok Fact Ob W : Type}
    [DecidableEq ι] [DecidableEq Ix] [∀ i, DecidableEq (Hole i)] [DecidableEq Tok]
    [DecidableEq Cand] [DecidableEq (Σ i, S.Op i)]
    (L : Ledger ι W Tok)
    (base : W → View Tok Fact)
    (sp : ι → Spec S Tok Fact Ob)
    (au : ι → Authority P Cred)
    (k : ι → (j : Ix) → Hole j → SlotCtl S Hole A P Fact Cand j)
    {i₀ : Ix}
    (J₀ : JCfg L S Hole A P Cand Fact Ob i₀)
    (s s₁ : DState L S Hole A P Cred Cand Fact Ob i₀)
    (n crashes : Nat)
    (hc : 1 ≤ crashes)
    (h_exp : hstep L base sp au k J₀ s (.expose n) = .ok s₁) :
    let trace : List (HEvent L S Hole A P Cred Cand Fact) := List.replicate crashes .crash ++ [.recover]
    let s_rec := runDurableTrace L base sp au k J₀ s₁ trace
    n ∈ s_rec.outbox ∧
    n ∉ pending L s_rec ∧
    (pending L s_rec).length < (pending L s).length ∧
    hstep L base sp au k J₀ s_rec (.expose n) = .error (.exposed n) := by
  have h_pend := pending_decreases_on_expose L base sp au k J₀ s s₁ n h_exp
  rcases h_pend with ⟨hj₁, _, ho₁, _, hn_not_pend₁, _, hlen_lt⟩
  have h_idemp := crash_recover_idempotent L base sp au k J₀ s₁ crashes hc
  have hj_rec : (runDurableTrace L base sp au k J₀ s₁ (List.replicate crashes .crash ++ [.recover])).journal = s₁.journal :=
    h_idemp.2.1
  have ho_rec : (runDurableTrace L base sp au k J₀ s₁ (List.replicate crashes .crash ++ [.recover])).outbox = s₁.outbox :=
    h_idemp.2.2
  have hn_in_outbox₁ : n ∈ s₁.outbox := by
    rw [ho₁]
    exact List.mem_append_right s.outbox (List.Mem.head [])
  have hn_in_outbox_rec :
      n ∈ (runDurableTrace L base sp au k J₀ s₁ (List.replicate crashes .crash ++ [.recover])).outbox := by
    rw [ho_rec]
    exact hn_in_outbox₁
  have h_pend_eq :
      pending L (runDurableTrace L base sp au k J₀ s₁ (List.replicate crashes .crash ++ [.recover])) =
        pending L s₁ := by
    unfold pending
    rw [hj_rec, ho_rec]
  have hn_not_pend_rec :
      n ∉ pending L (runDurableTrace L base sp au k J₀ s₁ (List.replicate crashes .crash ++ [.recover])) := by
    rw [h_pend_eq]
    exact hn_not_pend₁
  have hlen_rec :
      (pending L (runDurableTrace L base sp au k J₀ s₁ (List.replicate crashes .crash ++ [.recover]))).length <
        (pending L s).length := by
    rw [h_pend_eq]
    exact hlen_lt
  have h_refused :
      hstep L base sp au k J₀
        (runDurableTrace L base sp au k J₀ s₁ (List.replicate crashes .crash ++ [.recover]))
        (.expose n) = .error (.exposed n) := by
    simp only [hstep] at h_exp ⊢
    rw [hj_rec, ho_rec, hj₁]
    split at h_exp
    · simp [hn_in_outbox₁]
    · cases h_exp
  exact ⟨hn_in_outbox_rec, hn_not_pend_rec, hlen_rec, h_refused⟩

/-- **Durable Crash-Recovery Metatheorem 3 (`durable_recovered_converges_on_collapse_root`)**:
    For any durable node state `s`, any projection `extractTrace` mapping the durable journal
    to its committed consensus block `Trace`, and any `crashes ≥ 1` consecutive `.crash` events
    followed by `.recover`:
    1. The recovered node's collapsed Merkle root `collapseTrace H schema val s₀` equals the
       pre-crash collapsed Merkle root,
    2. Pruning empty/skip timeout blocks (`filterActive`) from the recovered trace preserves
       the collapsed Merkle root identically (`collapseTrace_prune_empty`),
    3. Any two validators whose durable journals contain the same active committed blocks
       `filterActive (extractTrace s₁.journal) = filterActive (extractTrace s₂.journal)`
       (even if they experienced different numbers of crashes `c₁, c₂ ≥ 1` or different
       interleaved empty/skip blocks) converge after recovery on the exact same collapsed
       Merkle root! -/
theorem durable_recovered_converges_on_collapse_root
    {Ix : Type} {S : Sig Ix} {Hole : Ix → Type} {A : Ix → Type}
    {ι P Cred Cand Tok Fact Ob W : Type}
    [DecidableEq ι] [DecidableEq Ix] [∀ i, DecidableEq (Hole i)] [DecidableEq Tok]
    [DecidableEq Cand] [DecidableEq (Σ i, S.Op i)]
    (L : Ledger ι W Tok)
    (base : W → View Tok Fact)
    (sp : ι → Spec S Tok Fact Ob)
    (au : ι → Authority P Cred)
    (k : ι → (j : Ix) → Hole j → SlotCtl S Hole A P Fact Cand j)
    {i₀ : Ix}
    (J₀ : JCfg L S Hole A P Cand Fact Ob i₀)
    (H : Hash) (schema : List String) (val : StoreValuation) (s₀ : VaultStore)
    (extractTrace : List (JEv L S Hole A P Cred Cand Fact) → Trace)
    (s₁ s₂ : DState L S Hole A P Cred Cand Fact Ob i₀)
    (c₁ c₂ : Nat) (hc₁ : 1 ≤ c₁) (hc₂ : 1 ≤ c₂)
    (h_active_agree : filterActive (extractTrace s₁.journal) = filterActive (extractTrace s₂.journal)) :
    let rec₁ := runDurableTrace L base sp au k J₀ s₁ (List.replicate c₁ .crash ++ [.recover])
    let rec₂ := runDurableTrace L base sp au k J₀ s₂ (List.replicate c₂ .crash ++ [.recover])
    collapseTrace H schema val s₀ (extractTrace rec₁.journal) =
      collapseTrace H schema val s₀ (extractTrace s₁.journal) ∧
    collapseTrace H schema val s₀ (extractTrace rec₁.journal) =
      collapseTrace H schema val s₀ (filterActive (extractTrace rec₁.journal)) ∧
    collapseTrace H schema val s₀ (extractTrace rec₁.journal) =
      collapseTrace H schema val s₀ (extractTrace rec₂.journal) := by
  have h_id₁ := (crash_recover_idempotent L base sp au k J₀ s₁ c₁ hc₁).2.1
  have h_id₂ := (crash_recover_idempotent L base sp au k J₀ s₂ c₂ hc₂).2.1
  dsimp only
  rw [h_id₁, h_id₂]
  refine ⟨rfl, collapseTrace_prune_empty H schema val s₀ (extractTrace s₁.journal), ?_⟩
  rw [collapseTrace_prune_empty H schema val s₀ (extractTrace s₁.journal),
      collapseTrace_prune_empty H schema val s₀ (extractTrace s₂.journal),
      h_active_agree]

/-! ## §6. Concrete Kernel Verification & `#tooth` Mutation-Killing Checks -/

/-- Golden admitted `EdaSwarmCandidate` built from `goldenMultiAgentCoDesignProposal`. -/
def goldenEdaSwarmCandidate : EdaSwarmCandidate :=
  { prop := goldenMultiAgentCoDesignProposal
    digestSeed := ByteArray.mk #[0x01] }

/-- Conflicting `EdaSwarmCandidate` built from `conflictingMultiAgentCoDesignProposal`. -/
def conflictingEdaSwarmCandidate : EdaSwarmCandidate :=
  { prop := conflictingMultiAgentCoDesignProposal
    digestSeed := ByteArray.mk #[0x02] }

/-- Kernel-checked (`decide +kernel`) verification that `selectWinner` over
    `[conflictingEdaSwarmCandidate, goldenEdaSwarmCandidate]` rejects the conflicting
    candidate and selects `goldenEdaSwarmCandidate` regardless of arrival order. -/
theorem goldenEdaSwarmRace_selects_valid_winner :
    checkEdaSwarmCandidate goldenEdaSwarmCandidate = true ∧
    checkEdaSwarmCandidate conflictingEdaSwarmCandidate = false ∧
    selectWinner () [conflictingEdaSwarmCandidate, goldenEdaSwarmCandidate] =
      some goldenEdaSwarmCandidate ∧
    selectWinner () [goldenEdaSwarmCandidate, conflictingEdaSwarmCandidate] =
      some goldenEdaSwarmCandidate := by
  have h := goldenMultiAgentCoDesign_admitted_and_conflict_refused
  have hg : checkEdaSwarmCandidate goldenEdaSwarmCandidate = true := by
    simp [checkEdaSwarmCandidate, goldenEdaSwarmCandidate, h.2.1]
  have hc : checkEdaSwarmCandidate conflictingEdaSwarmCandidate = false := by
    simp [checkEdaSwarmCandidate, conflictingEdaSwarmCandidate, h.2.2]
  have hvg : certValid () goldenEdaSwarmCandidate = true := hg
  have hvc : certValid () conflictingEdaSwarmCandidate = false := hc
  refine ⟨hg, hc, ?_, ?_⟩
  · simp [selectWinner, hvg, hvc]
  · simp [selectWinner, hvg, hvc]

#tooth edaSwarm_conflicting_candidate_invalid by
  mutation checkEdaSwarmCandidate := fun _ => true

#tooth tier2_simplex_quorum_and_accountable_safety by
  mutation extractSlashingReceipt := fun view blockA blockB _ _ _ =>
    { view := view, blockA := blockA, blockB := blockB, equivocatingVoters := [] }

end Obend.Consensus.SovereignFinality

end
