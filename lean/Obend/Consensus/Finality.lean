module
/-
# Obend.Consensus.Finality — 4-Tier Finality Ladder and Promotion State Machine

Absorbs `minidregg/Theory/Finality.lean` and `NEXT-MATHEMATICA.md:130` into Obend's
consensus architecture.

## 4-Tier Finality Ladder:
1. `speculative` (Tier 0): Local turn proposal, optimistic execution, read uncommitted.
2. `attested`    (Tier 1): Peer or leader attestation, deterministic execution preview (read-only).
3. `quorum_final` (Tier 2): 2f+1 Quorum Certificate (QC) formed in Simplex BFT, state-write committed.
4. `collapsed`   (Tier 3): Merkle folded into canonical root, immutable archive, non-repudiable receipt.

## Core Metatheorems:
- `rank_injective`: Distinct tiers have distinct rank ordinals.
- `speculative_bot` & `collapsed_top`: Ladder bounded between speculative and collapsed.
- `admitsOp_mono`: Permissions monotonically expand as finality advances.
- `reachable_no_downgrade`: Along any valid sequence of promotions, finality never weakens.
- `downgrade_not_a_step` & `downgrade_unreachable`: Downgrades (e.g. quorum_final -> speculative) are refuted.
- `joinTier_dominates`: Multi-cell turn commits at the lattice join of its written cells' tiers.
-/

public import Obend.Core.Data
public import Obend.Vault.Hyperedge

@[expose] public section
namespace Obend.Consensus.Finality

open Obend.Core.Data
open Obend.Vault

set_option autoImplicit false

/-! ## §1. The 4-Tier Finality Ladder -/

/-- The 4-tier finality ladder for Obend consensus and execution. -/
inductive FinalityTier where
  | speculative   -- Tier 0: Turn proposed, local optimistic branch, read uncommitted
  | attested      -- Tier 1: Leader / peer attested, execute read-only preview
  | quorum_final  -- Tier 2: Quorum certificate (QC) formed, state-write committed
  | collapsed     -- Tier 3: Merkle folded into root, immutable archive, sealed receipt
  deriving DecidableEq, Inhabited

namespace FinalityTier

/-- Ordinal rank of each tier on the ladder. -/
def rank : FinalityTier → Nat
  | .speculative  => 0
  | .attested     => 1
  | .quorum_final => 2
  | .collapsed    => 3

theorem rank_injective : Function.Injective rank := by
  intro a b h
  cases a <;> cases b <;> first | rfl | revert h; decide

instance : LE FinalityTier where
  le a b := a.rank ≤ b.rank

instance : LT FinalityTier where
  lt a b := a.rank < b.rank

instance (a b : FinalityTier) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a.rank ≤ b.rank))

instance (a b : FinalityTier) : Decidable (a < b) :=
  inferInstanceAs (Decidable (a.rank < b.rank))

theorem le_refl (t : FinalityTier) : t ≤ t :=
  Nat.le_refl t.rank

theorem le_trans {a b c : FinalityTier} (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c :=
  Nat.le_trans h1 h2

theorem le_antisymm {a b : FinalityTier} (h1 : a ≤ b) (h2 : b ≤ a) : a = b :=
  rank_injective (Nat.le_antisymm h1 h2)

theorem le_total (a b : FinalityTier) : a ≤ b ∨ b ≤ a :=
  Nat.le_total a.rank b.rank

theorem speculative_bot (t : FinalityTier) : FinalityTier.speculative ≤ t := by
  cases t <;> decide

theorem collapsed_top (t : FinalityTier) : t ≤ FinalityTier.collapsed := by
  cases t <;> decide

def max (a b : FinalityTier) : FinalityTier :=
  if a ≤ b then b else a

def min (a b : FinalityTier) : FinalityTier :=
  if a ≤ b then a else b

theorem le_max_left (a b : FinalityTier) : a ≤ max a b := by
  unfold max
  split
  · rename_i h; exact h
  · exact le_refl a

theorem le_max_right (a b : FinalityTier) : b ≤ max a b := by
  unfold max
  split
  · exact le_refl b
  · rename_i h
    cases le_total b a with
    | inl hba => exact hba
    | inr hab => contradiction

end FinalityTier

/-! ## §2. Proximity to Execution: Permitted Operations -/

/-- Classes of operations permitted at different tiers of the finality ladder. -/
inductive Operation where
  | readUncommitted   -- Dirty read / optimistic query
  | executeReadOnly   -- Deterministic preview / dry run without state mutation
  | stateWrite        -- Mutate cell state / commit deltas to VaultStore
  | immutableArchive  -- Fold into Merkle root / historical archive / prune ephemeral data
  deriving DecidableEq

/-- The minimum tier required to permit an operation. -/
def minTier : Operation → FinalityTier
  | .readUncommitted  => .speculative
  | .executeReadOnly  => .attested
  | .stateWrite       => .quorum_final
  | .immutableArchive => .collapsed

/-- Check if an operation is permitted at a given finality tier. -/
def admitsOp (t : FinalityTier) (op : Operation) : Bool :=
  decide (minTier op ≤ t)

theorem admitsOp_mono {t₁ t₂ : FinalityTier} {op : Operation}
    (hle : t₁ ≤ t₂) (hadm : admitsOp t₁ op = true) : admitsOp t₂ op = true := by
  simp only [admitsOp, decide_eq_true_iff] at hadm ⊢
  exact FinalityTier.le_trans hadm hle

/-! ### Concrete Operation Boundaries -/

theorem speculative_admits_readUncommitted : admitsOp .speculative .readUncommitted = true := by decide
theorem speculative_refuses_executeReadOnly : admitsOp .speculative .executeReadOnly = false := by decide
theorem speculative_refuses_stateWrite : admitsOp .speculative .stateWrite = false := by decide
theorem speculative_refuses_immutableArchive : admitsOp .speculative .immutableArchive = false := by decide

theorem attested_admits_executeReadOnly : admitsOp .attested .executeReadOnly = true := by decide
theorem attested_refuses_stateWrite : admitsOp .attested .stateWrite = false := by decide

theorem quorum_final_admits_stateWrite : admitsOp .quorum_final .stateWrite = true := by decide
theorem quorum_final_refuses_immutableArchive : admitsOp .quorum_final .immutableArchive = false := by decide

theorem collapsed_admits_immutableArchive : admitsOp .collapsed .immutableArchive = true := by decide
theorem collapsed_admits_all (op : Operation) : admitsOp .collapsed op = true := by
  cases op <;> decide

/-! ## §3. Promotion State Machine & No-Downgrade Invariant -/

/-- Events driving promotion transitions between finality tiers. -/
inductive PromotionEvent where
  | proposeTurn (turnId : ByteArray)
  | attestTurn (signer : ByteArray)
  | formQC (qcDigest : ByteArray)
  | collapseRoot (merkleRoot : ByteArray)

/-- Deterministic promotion step along the finality ladder. -/
def promoteStep : FinalityTier → PromotionEvent → Option FinalityTier
  | .speculative,   .attestTurn _    => some .attested
  | .attested,      .formQC _        => some .quorum_final
  | .quorum_final,  .collapseRoot _  => some .collapsed
  | _, _ => none

/-- Single-step finality relation: transitions must never weaken the tier. -/
def FinalityStep (a b : FinalityTier) : Prop := a ≤ b

instance (a b : FinalityTier) : Decidable (FinalityStep a b) :=
  inferInstanceAs (Decidable (a ≤ b))

/-- Reflexive-transitive closure of finality steps. -/
inductive FinalitySteps : FinalityTier → FinalityTier → Prop where
  | refl (t : FinalityTier) : FinalitySteps t t
  | tail {t₁ t₂ t₃ : FinalityTier} : FinalitySteps t₁ t₂ → FinalityStep t₂ t₃ → FinalitySteps t₁ t₃

/-- Promotion steps are always admissible finality steps. -/
theorem promoteStep_sound {t : FinalityTier} {ev : PromotionEvent} {t' : FinalityTier}
    (h : promoteStep t ev = some t') : FinalityStep t t' := by
  cases t <;> cases ev <;> simp [promoteStep] at h
  all_goals (subst h; decide)

/-- **No Downgrade**: along any sequence of finality steps, the tier never weakens. -/
theorem reachable_no_downgrade {t₀ t : FinalityTier} (hrun : FinalitySteps t₀ t) : t₀ ≤ t := by
  induction hrun with
  | refl => exact FinalityTier.le_refl _
  | tail _ hstep ih => exact FinalityTier.le_trans ih hstep

/-- Tooth 1: weakening `quorum_final` to `speculative` is not an admissible step. -/
theorem downgrade_not_a_step : ¬ FinalityStep .quorum_final .speculative := by decide

/-- Tooth 2: weakening `collapsed` to `attested` is not an admissible step. -/
theorem collapsed_downgrade_not_a_step : ¬ FinalityStep .collapsed .attested := by decide

/-- Tooth 3: no sequence of finality events can reach `speculative` from `quorum_final`. -/
theorem downgrade_unreachable : ¬ FinalitySteps .quorum_final .speculative :=
  fun hrun => absurd (reachable_no_downgrade hrun) (by decide)

/-- Collapsed state is terminal / absorbing under promotions. -/
theorem collapsed_is_terminal (t : FinalityTier) (hrun : FinalitySteps .collapsed t) :
    t = .collapsed := by
  have h := reachable_no_downgrade hrun
  cases t <;> revert h <;> decide

/-! ## §4. Commit at the Lattice Join of Written Cells -/

/-- Lattice join of a list of finality tiers. -/
def joinTier : List FinalityTier → FinalityTier
  | [] => .speculative
  | t :: ts => FinalityTier.max t (joinTier ts)

theorem joinTier_dominates (ts : List FinalityTier) (t : FinalityTier) (h : t ∈ ts) :
    t ≤ joinTier ts := by
  induction ts with
  | nil => contradiction
  | cons x xs ih =>
    cases h with
    | head =>
      unfold joinTier
      exact FinalityTier.le_max_left t (joinTier xs)
    | tail _ hmem =>
      unfold joinTier
      have hle_tail := ih hmem
      have hle_max := FinalityTier.le_max_right x (joinTier xs)
      exact FinalityTier.le_trans hle_tail hle_max

/-- The commit tier for a multi-cell turn writing cells of specified tiers.
    A turn that performs state writes must achieve AT LEAST `quorum_final`,
    as well as dominating every cell's individual finality requirement. -/
def turnCommitTier (cells : List FinalityTier) : FinalityTier :=
  FinalityTier.max .quorum_final (joinTier cells)

theorem turnCommitTier_dominates_cells (cells : List FinalityTier) (t : FinalityTier) (h : t ∈ cells) :
    t ≤ turnCommitTier cells := by
  have h1 := joinTier_dominates cells t h
  have h2 := FinalityTier.le_max_right .quorum_final (joinTier cells)
  exact FinalityTier.le_trans h1 h2

theorem turnCommitTier_admits_stateWrite (cells : List FinalityTier) :
    admitsOp (turnCommitTier cells) .stateWrite = true := by
  have hq : FinalityTier.quorum_final ≤ turnCommitTier cells :=
    FinalityTier.le_max_left .quorum_final (joinTier cells)
  exact admitsOp_mono hq quorum_final_admits_stateWrite

/-! ## §5. Verified Finality Gate Record -/

/-- Finality tracking gate for turns climbing the finality ladder. -/
structure FinalityGate where
  turnId : ByteArray
  currentTier : FinalityTier
  attestations : List ByteArray
  qc : Option ByteArray
  merkleRoot : Option ByteArray

/-- Well-formedness invariants for a finality gate at each tier. -/
def FinalityGate.WellFormed (gate : FinalityGate) : Prop :=
  (gate.currentTier.rank ≥ 1 → gate.attestations ≠ []) ∧
  (gate.currentTier.rank ≥ 2 → gate.qc.isSome = true) ∧
  (gate.currentTier.rank ≥ 3 → gate.merkleRoot.isSome = true)

/-- Initialize a fresh finality gate for a newly proposed speculative turn. -/
def FinalityGate.init (turnId : ByteArray) : FinalityGate where
  turnId := turnId
  currentTier := .speculative
  attestations := []
  qc := none
  merkleRoot := none

theorem FinalityGate.init_wf (turnId : ByteArray) : (FinalityGate.init turnId).WellFormed := by
  unfold FinalityGate.init FinalityGate.WellFormed FinalityTier.rank
  refine ⟨by intro h; contradiction, by intro h; contradiction, by intro h; contradiction⟩

/-- Advance a finality gate along an authorized event. -/
def advanceGate (gate : FinalityGate) (ev : PromotionEvent) : Option FinalityGate :=
  match gate, ev with
  | ⟨turnId, .speculative, _, _, _⟩, .attestTurn signer =>
    some ⟨turnId, .attested, [signer], none, none⟩
  | ⟨turnId, .attested, atts, _, _⟩, .formQC qcDigest =>
    some ⟨turnId, .quorum_final, atts, some qcDigest, none⟩
  | ⟨turnId, .quorum_final, atts, qc, _⟩, .collapseRoot rootDigest =>
    some ⟨turnId, .collapsed, atts, qc, some rootDigest⟩
  | _, _ => none

/-- Gate advancement strictly advances finality. -/
theorem advanceGate_advances (gate : FinalityGate) (ev : PromotionEvent) (next : FinalityGate)
    (hadv : advanceGate gate ev = some next) : gate.currentTier ≤ next.currentTier := by
  cases gate with
  | mk turnId currentTier atts qc root =>
    cases currentTier <;> cases ev <;> simp [advanceGate] at hadv
    all_goals (obtain rfl := hadv; dsimp only [FinalityGate.currentTier]; decide)

end Obend.Consensus.Finality
