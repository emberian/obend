module
/-
# Obend.Consensus.Finality — 4-Tier Finality Ladder Bound to `SimplexProtocol.FinCert` & cSHAKE256

Binds Obend's 4-tier finality ladder directly to `SimplexProtocol` (`Protocol`, `Sent`,
`FinCert`, `Finalized`, `Reach`) and SP 800-185 cSHAKE256 `Digest` (`ByteArray`) state roots.

## 4-Tier Finality Ladder:
1. `speculative`  (Tier 0): Local turn proposal, optimistic execution, read uncommitted.
2. `attested`     (Tier 1): Leader proposal attested in `SimplexProtocol.Sent`, read-only preview.
3. `quorum_final` (Tier 2): `SimplexProtocol.FinCert` verified (`cert.checks P sent = true`),
                            witnessing `n - f` committee `finalize` votes (`Finalized P sent`),
                            state-write committed.
4. `collapsed`    (Tier 3): Finalized chain digest + vault Merkle state root folded via
                            domain-separated `cshake256Kernel` into canonical `collapsedRoot`.

## Core Metatheorems:
- `rank_injective`, `speculative_bot`, `collapsed_top`, `admitsOp_mono`, `reachable_no_downgrade`,
  `downgrade_not_a_step`, `downgrade_unreachable`, `collapsed_is_terminal`.
- `joinTier_dominates`, `turnCommitTier_dominates_cells`, `turnCommitTier_admits_write`.
- `D5` (two-mode coordination): a write commits below the BFT floor only with a verified
  I-confluence pushout witness (`PushoutWitness`: the operation is the join with a delta under an
  I-confluent invariant). `admitAtTier_sound`: admitted below `quorum_final` means witnessed;
  `admitAtGate_sound`: admitted at a `SimplexFinalityGate` means witnessed or a checking `FinCert`
  (`n - f` finalize votes, `Finalized`). Witnessed operations commute and keep the invariant along
  any order of any number of them (`confluent_diamond`, `applyWitnessed_perm`,
  `applyWitnessed_keeps`); `docMerge_tombstones_join`: `Doc.Merge`'s pushout is that join on
  tombstones. `nonconfluent_debit_refused_below_byzantine`: a balance debit carries no witness in
  any semilattice (`PushoutWitness.idempotent`), so it is refused at Tier 0 and Tier 1.
  Policy names (`minidregg` `Theory/Finality.lean`): `speculative` is `LocalOptimistic`,
  `attested` `EquivocationBounded`, `quorum_final` `Byzantine`.
- `advanceSimplexGate_quorum_final_sound`: `.quorum_final` promotion requires a checking
  `SimplexProtocol.FinCert` and implies `SimplexProtocol.Finalized`.
- `quorum_final_gates_unique_per_height`: over any reachable `SimplexProtocol.Reach P sent`,
  any two `.quorum_final` gates whose `FinCert` chains have equal height certify the exact
  same finalized block sequence (`cert₁.chain.blocks = cert₂.chain.blocks`).
- `advanceSimplexGate_collapsed_binds_cshake`: `.collapsed` promotion deterministically binds
  the SP 800-185 `cshake256Bytes` fold of the finalized chain digest and vault state root.
- `chainDigest_binds`: the chain digest serializes each block by `Entry.encode` (8-byte view,
  32-byte payload), so equal digests mean equal blocks or a cSHAKE256 collision.
-/

public import Obend.Core.Data
public import Obend.Vault.Hyperedge
public import Obend.Consensus.SimplexProtocol
public import Obend.Digest.Cshake256.Seam
import Obend.Doc.Merge
import Obend.Tactic.Tooth

public section

/- `Obend.Doc.Graph` (imported privately, for the `Doc.Merge` bridge only, so its instances do not
reach this module's importers) declares its own `DecidableEq ByteArray`, whose body the kernel does
not see from here; the gates below decide byte equality by core's instance, so their decisions
reduce (`§7`). -/
attribute [-instance] Obend.Doc.instDecidableEqByteArray_obend

namespace Obend.Consensus.Finality

open Obend.Core.Data
open Obend.Vault
open Obend.Consensus.Simplex (NodeId)
open Obend.Consensus.SimplexProtocol (Protocol Sent Entry Chain Msg FinCert Finalized Reach
  encodeEntries_injective)
open Obend.Digest.Cshake256 (cshake256Bytes)
open Obend.Digest.Cshake256.Native (bytesOfList bytesOfList_toList cshake256Kernel
  cshake256Kernel_toList)

set_option autoImplicit false

/-! ## §1. The 4-Tier Finality Ladder -/

/-- The 4-tier finality ladder for Obend consensus and execution. -/
inductive FinalityTier where
  | speculative   -- Tier 0: Turn proposed, local optimistic branch, read uncommitted
  | attested      -- Tier 1: Leader / peer attested, execute read-only preview
  | quorum_final  -- Tier 2: Quorum certificate (FinCert) formed, state-write committed
  | collapsed     -- Tier 3: cSHAKE256 / Merkle folded into root, immutable archive
  deriving Repr, Inhabited

deriving instance @[expose] DecidableEq for FinalityTier

namespace FinalityTier

/-- Ordinal rank of each tier on the ladder. -/
@[expose] def rank : FinalityTier → Nat
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
  | confluentWrite    -- Join a pushout-witnessed delta into merged state: no BFT message
  | immutableArchive  -- Fold into cSHAKE256 Merkle root / historical archive
  deriving Repr

deriving instance @[expose] DecidableEq for Operation

/-- The minimum tier required to permit an operation. -/
@[expose] def minTier : Operation → FinalityTier
  | .readUncommitted  => .speculative
  | .executeReadOnly  => .attested
  | .stateWrite       => .quorum_final
  | .confluentWrite   => .speculative
  | .immutableArchive => .collapsed

/-- Check if an operation is permitted at a given finality tier. -/
@[expose] def admitsOp (t : FinalityTier) (op : Operation) : Bool :=
  decide (minTier op ≤ t)

theorem admitsOp_mono {t₁ t₂ : FinalityTier} {op : Operation}
    (hle : t₁ ≤ t₂) (hadm : admitsOp t₁ op = true) : admitsOp t₂ op = true := by
  simp only [admitsOp, decide_eq_true_iff] at hadm ⊢
  exact FinalityTier.le_trans hadm hle

theorem quorum_final_admits_stateWrite : admitsOp .quorum_final .stateWrite = true := by decide

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

theorem downgrade_not_a_step : ¬ FinalityStep .quorum_final .speculative := by decide

theorem collapsed_downgrade_not_a_step : ¬ FinalityStep .collapsed .attested := by decide

theorem downgrade_unreachable : ¬ FinalitySteps .quorum_final .speculative :=
  fun hrun => absurd (reachable_no_downgrade hrun) (by decide)

theorem collapsed_is_terminal (t : FinalityTier) (hrun : FinalitySteps .collapsed t) :
    t = .collapsed := by
  have h := reachable_no_downgrade hrun
  cases t <;> revert h <;> decide

/-! ## §4. Commit at the Lattice Join of Written Cells -/

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

/-! ### The coordination class of a write (`D5`, two-mode coordination)

A write commits at the BFT floor unless it carries a verified pushout witness: the operation is the
join with a delta in a semilattice replicas merge in, under an invariant that survives the join
(I-confluence, Bailis et al., VLDB 2014). Two replicas that apply witnessed operations from one state
reach one state and keep the invariant, so such a write needs no BFT message. -/

/-- A join-semilattice replicas merge in. -/
structure JoinSemilattice (S : Type) where
  join : S → S → S
  comm : ∀ a b, join a b = join b a
  assoc : ∀ a b c, join (join a b) c = join a (join b c)
  idem : ∀ a, join a a = a

/-- **I-confluence**: the invariant survives the join of any two states that satisfy it. -/
def IConfluent {S : Type} (L : JoinSemilattice S) (I : S → Prop) : Prop :=
  ∀ a b, I a → I b → I (L.join a b)

/-- **A pushout witness** for an operation: it is the join with a delta that satisfies an
I-confluent invariant. -/
structure PushoutWitness {S : Type} (L : JoinSemilattice S) (I : S → Prop) (apply : S → S) where
  delta : S
  apply_eq : ∀ s, apply s = L.join s delta
  delta_inv : I delta
  iconf : IConfluent L I

/-- An operation a turn commits: its effect on the merged state, the tiers of the cells it writes,
and the pushout witness it carries, if any. -/
structure TurnOp {S : Type} (L : JoinSemilattice S) (I : S → Prop) where
  apply : S → S
  cells : List FinalityTier
  pushout : Option (PushoutWitness L I apply)

section Coordination

variable {S : Type} {L : JoinSemilattice S} {I : S → Prop}

/-- The tier a write cannot commit below: Tier 0 with a pushout witness, the BFT floor without. -/
def TurnOp.floor (op : TurnOp L I) : FinalityTier :=
  match op.pushout with
  | some _ => .speculative
  | none => .quorum_final

/-- The operation class a write is admitted as. -/
def TurnOp.writeOp (op : TurnOp L I) : Operation :=
  match op.pushout with
  | some _ => .confluentWrite
  | none => .stateWrite

/-- A turn commits at the join of the cells it writes, floored by its coordination class. -/
def turnCommitTier (op : TurnOp L I) : FinalityTier :=
  FinalityTier.max op.floor (joinTier op.cells)

/-- Commit admission at a tier. -/
def admitAtTier (t : FinalityTier) (op : TurnOp L I) : Bool :=
  decide (turnCommitTier op ≤ t)

theorem turnCommitTier_dominates_cells (op : TurnOp L I) (t : FinalityTier) (h : t ∈ op.cells) :
    t ≤ turnCommitTier op :=
  FinalityTier.le_trans (joinTier_dominates op.cells t h) (FinalityTier.le_max_right _ _)

theorem turnCommitTier_floor (op : TurnOp L I) : op.floor ≤ turnCommitTier op :=
  FinalityTier.le_max_left _ _

/-- An operation without a pushout witness commits at the BFT floor or above. -/
theorem turnCommitTier_unwitnessed (op : TurnOp L I) (h : op.pushout = none) :
    FinalityTier.quorum_final ≤ turnCommitTier op := by
  have hf : op.floor = .quorum_final := by
    simp only [TurnOp.floor, h]
  have := turnCommitTier_floor op
  rwa [hf] at this

/-- Every commit tier admits the write as its class: a state write at the BFT floor, a confluent
write at Tier 0. -/
theorem turnCommitTier_admits_write (op : TurnOp L I) :
    admitsOp (turnCommitTier op) op.writeOp = true := by
  cases hp : op.pushout with
  | none =>
    have hw : op.writeOp = .stateWrite := by simp only [TurnOp.writeOp, hp]
    rw [hw]
    exact admitsOp_mono (turnCommitTier_unwitnessed op hp) quorum_final_admits_stateWrite
  | some _ =>
    have hw : op.writeOp = .confluentWrite := by simp only [TurnOp.writeOp, hp]
    rw [hw]
    exact admitsOp_mono (FinalityTier.speculative_bot _) (by decide)

/-- **Soundness of the relaxation**: a write admitted below the BFT floor carries a pushout witness. -/
theorem admitAtTier_sound {t : FinalityTier} {op : TurnOp L I} (h : admitAtTier t op = true)
    (ht : t < .quorum_final) : ∃ w, op.pushout = some w := by
  cases hp : op.pushout with
  | some w => exact ⟨w, rfl⟩
  | none =>
    have ha : turnCommitTier op ≤ t := of_decide_eq_true h
    exact absurd (FinalityTier.le_trans (turnCommitTier_unwitnessed op hp) ha) (Nat.not_le.mpr ht)

/-- A witnessed operation keeps the invariant. -/
theorem PushoutWitness.keeps {f : S → S} (w : PushoutWitness L I f) {s : S} (hs : I s) : I (f s) := by
  rw [w.apply_eq]
  exact w.iconf _ _ hs w.delta_inv

/-- A witnessed operation is idempotent: joining a delta twice joins it once. -/
theorem PushoutWitness.idempotent {f : S → S} (w : PushoutWitness L I f) (s : S) : f (f s) = f s := by
  rw [w.apply_eq (f s), w.apply_eq s, L.assoc, L.idem]

/-- **Witnessed operations commute**: replicas that apply two witnessed operations from one state
reach one state in either order, and it is the join of the two branches (the pushout of the span). -/
theorem confluent_diamond {f g : S → S} (wf : PushoutWitness L I f) (wg : PushoutWitness L I g)
    (s : S) : f (g s) = g (f s) ∧ L.join (f s) (g s) = g (f s) := by
  rw [wf.apply_eq (g s), wg.apply_eq s, wg.apply_eq (f s), wf.apply_eq s]
  constructor
  · rw [L.assoc s wg.delta wf.delta, L.comm wg.delta wf.delta, ← L.assoc s wf.delta wg.delta]
  · have hab : L.join (L.join s wf.delta) s = L.join s wf.delta := by
      rw [L.assoc, L.comm wf.delta s, ← L.assoc, L.idem]
    rw [← L.assoc (L.join s wf.delta) s wg.delta, hab]

/-- Witnessed operations applied in order. -/
def applyWitnessed : List ((f : S → S) × PushoutWitness L I f) → S → S
  | [], s => s
  | x :: xs, s => applyWitnessed xs (x.1 s)

/-- **Any number of witnessed operations keep the invariant**, in the order a replica applied them. -/
theorem applyWitnessed_keeps : ∀ (ops : List ((f : S → S) × PushoutWitness L I f)) {s : S},
    I s → I (applyWitnessed ops s)
  | [], _, hs => hs
  | x :: xs, _, hs => applyWitnessed_keeps xs (x.2.keeps hs)

/-- **Replicas converge whatever the order**: two replicas that apply the same witnessed operations
in any two orders reach the same state. -/
theorem applyWitnessed_perm {ops ops' : List ((f : S → S) × PushoutWitness L I f)}
    (h : ops.Perm ops') (s : S) : applyWitnessed ops s = applyWitnessed ops' s := by
  induction h generalizing s with
  | nil => rfl
  | cons x _ ih => simp only [applyWitnessed]; exact ih _
  | swap x y l => simp only [applyWitnessed]; rw [(confluent_diamond x.2 y.2 s).1]
  | trans _ _ ih₁ ih₂ => exact (ih₁ s).trans (ih₂ s)

end Coordination

/-! ### The semilattices the merge layers join in -/

/-- Pointwise disjunction: the semilattice of tombstone and edge sets of `Obend.Doc` pages. -/
def pointwiseOr (α : Type) : JoinSemilattice (α → Bool) where
  join f g := fun a => f a || g a
  comm f g := funext fun a => Bool.or_comm (f a) (g a)
  assoc f g h := funext fun a => Bool.or_assoc (f a) (g a) (h a)
  idem f := funext fun a => Bool.or_self (f a)

/-- **`Doc.Merge`'s pushout is that join on tombstones**: the merge of two pages kills exactly the
atoms either killed (`Obend.Doc.Graph.merge_isPushout`). Private: `Doc.Merge` is a private import. -/
private theorem docMerge_tombstones_join (A B : Obend.Doc.Graph) :
    (Obend.Doc.Graph.merge A B).isDead = (pointwiseOr _).join A.isDead B.isDead :=
  funext fun a => Obend.Doc.Graph.isDead_merge A B a

/-- Tombstones only within an allowed set: I-confluent under `pointwiseOr`. -/
def KillsWithin {α : Type} (allowed : α → Prop) (t : α → Bool) : Prop :=
  ∀ a, t a = true → allowed a

theorem killsWithin_iconfluent {α : Type} (allowed : α → Prop) :
    IConfluent (pointwiseOr α) (KillsWithin allowed) := by
  intro f g hf hg a ha
  simp only [pointwiseOr, Bool.or_eq_true] at ha
  exact ha.elim (hf a) (hg a)

/-- A tombstoning of the atoms `δ` kills, all within `allowed`: a witnessed write. -/
def tombstoneOp {α : Type} (allowed : α → Prop) (δ : α → Bool) (hδ : KillsWithin allowed δ) :
    TurnOp (pointwiseOr α) (KillsWithin allowed) where
  apply t := (pointwiseOr α).join t δ
  cells := []
  pushout := some ⟨δ, fun _ => rfl, hδ, killsWithin_iconfluent allowed⟩

/-- `max` on naturals: high-water marks, version counters. -/
def maxNat : JoinSemilattice Nat where
  join := max
  comm := Nat.max_comm
  assoc := Nat.max_assoc
  idem a := Nat.max_eq_left (Nat.le_refl a)

/-! ### A balance debit is never confluent -/

/-- A balance debit of `k` units: one leg of a bounded-budget or custody transfer. -/
def balanceDebit (k b : Nat) : Nat := b - k

/-- **A debit has no pushout witness, in any semilattice**: a witnessed operation is idempotent
(`PushoutWitness.idempotent`), and debiting `k > 0` twice from `2k` leaves `0`, not `k`. -/
theorem balanceDebit_no_pushout {L : JoinSemilattice Nat} {I : Nat → Prop} {k : Nat} (hk : 0 < k)
    (w : PushoutWitness L I (balanceDebit k)) : False := by
  have h := w.idempotent (2 * k)
  simp only [balanceDebit] at h
  omega

/-- **A non-confluent balance debit is refused at Tier 0 and Tier 1**: whatever semilattice and
invariant it is presented under, a write whose effect debits `k > 0` carries no pushout witness, so
it commits at the BFT floor, and `admitAtTier` refuses it at `speculative` (`LocalOptimistic`) and
at `attested` (`EquivocationBounded`). -/
theorem nonconfluent_debit_refused_below_byzantine {L : JoinSemilattice Nat} {I : Nat → Prop} {k : Nat}
    (hk : 0 < k) (op : TurnOp L I) (hop : op.apply = balanceDebit k) :
    admitAtTier .speculative op = false ∧ admitAtTier .attested op = false := by
  have hnone : op.pushout = none := by
    cases hp : op.pushout with
    | none => rfl
    | some w => exact (balanceDebit_no_pushout hk (hop ▸ w)).elim
  have hq := turnCommitTier_unwitnessed op hnone
  constructor
  · exact decide_eq_false fun h => absurd (FinalityTier.le_trans hq h) (by decide)
  · exact decide_eq_false fun h => absurd (FinalityTier.le_trans hq h) (by decide)

#tooth nonconfluent_debit_refused_below_byzantine by mutation TurnOp.floor :=
  fun _ => FinalityTier.speculative

/-! ## §5. Basic Finality Gate Record -/

structure FinalityGate where
  turnId : ByteArray
  currentTier : FinalityTier
  attestations : List ByteArray
  qc : Option ByteArray
  merkleRoot : Option ByteArray

def FinalityGate.WellFormed (gate : FinalityGate) : Prop :=
  (gate.currentTier.rank ≥ 1 → gate.attestations ≠ []) ∧
  (gate.currentTier.rank ≥ 2 → gate.qc.isSome = true) ∧
  (gate.currentTier.rank ≥ 3 → gate.merkleRoot.isSome = true)

def FinalityGate.init (turnId : ByteArray) : FinalityGate where
  turnId := turnId
  currentTier := .speculative
  attestations := []
  qc := none
  merkleRoot := none

theorem FinalityGate.init_wf (turnId : ByteArray) : (FinalityGate.init turnId).WellFormed := by
  unfold FinalityGate.init FinalityGate.WellFormed FinalityTier.rank
  refine ⟨by intro h; contradiction, by intro h; contradiction, by intro h; contradiction⟩

def advanceGate (gate : FinalityGate) (ev : PromotionEvent) : Option FinalityGate :=
  match gate, ev with
  | ⟨turnId, .speculative, _, _, _⟩, .attestTurn signer =>
    some ⟨turnId, .attested, [signer], none, none⟩
  | ⟨turnId, .attested, atts, _, _⟩, .formQC qcDigest =>
    some ⟨turnId, .quorum_final, atts, some qcDigest, none⟩
  | ⟨turnId, .quorum_final, atts, qc, _⟩, .collapseRoot rootDigest =>
    some ⟨turnId, .collapsed, atts, qc, some rootDigest⟩
  | _, _ => none

theorem advanceGate_advances (gate : FinalityGate) (ev : PromotionEvent) (next : FinalityGate)
    (hadv : advanceGate gate ev = some next) : gate.currentTier ≤ next.currentTier := by
  cases gate with
  | mk turnId currentTier atts qc root =>
    cases currentTier <;> cases ev <;> simp [advanceGate] at hadv
    all_goals (obtain rfl := hadv; dsimp only [FinalityGate.currentTier]; decide)

/-! ## §6. `SimplexProtocol.FinCert` + cSHAKE256 `Digest` Finality Gate -/

/-- Canonical 32-byte digest carrier. -/
abbrev Digest := ByteArray

/-- Domain customization tag for hashing finalized `SimplexProtocol.Chain` blocks. -/
def simplexChainDomain : Digest :=
  "OBEND-SIMPLEX-CHAIN-V1".toUTF8

/-- Domain customization tag for collapsing `(chainDigest || vaultStateRoot)` into Tier 3. -/
def collapseRootDomain : Digest :=
  "OBEND-COLLAPSE-ROOT-V1".toUTF8

/-- Canonical byte serialization of `c.blocks` (view dummies are left out, so finalized chains of
    equal height have one digest): each block is its 41-byte `Entry.encode`, the payload at its
    full 256 bits. -/
def encodeFinalizedBlocks (c : Chain) : ByteArray :=
  bytesOfList (c.blocks.flatMap Entry.encode)

/-- cSHAKE256 digest of a finalized chain's block sequence. -/
def chainDigest (c : Chain) : Digest :=
  cshake256Kernel simplexChainDomain (encodeFinalizedBlocks c)

theorem chainDigest_eq_spec (c : Chain) :
    (chainDigest c).data.toList =
      cshake256Bytes simplexChainDomain.data.toList (c.blocks.flatMap Entry.encode) := by
  unfold chainDigest encodeFinalizedBlocks
  rw [cshake256Kernel_toList, bytesOfList_toList]

/-- **The chain digest binds the finalized blocks at their full width**: two chains whose blocks
    are canonical (8-byte views, 256-bit payloads) and whose digests agree carry the same blocks,
    or the two serializations are a cSHAKE256 collision. -/
def chainDigest_extract {c₁ c₂ : Chain}
    (h₁ : c₁.blocks.all Entry.canonical = true) (h₂ : c₂.blocks.all Entry.canonical = true)
    (hEq : chainDigest c₁ = chainDigest c₂) :
    PSum (PLift (c₁.blocks = c₂.blocks))
      (Obend.Digest.HashBytes.CollisionPair (cshake256Bytes simplexChainDomain.data.toList)
        (fun x => x = c₁.blocks.flatMap Entry.encode ∨ x = c₂.blocks.flatMap Entry.encode)) :=
  Obend.Digest.HashBytes.extractBinding _ _ _ (encodeEntries_injective h₁ h₂) (by
    rw [← chainDigest_eq_spec, ← chainDigest_eq_spec, hEq])

theorem chainDigest_binds {c₁ c₂ : Chain}
    (h₁ : c₁.blocks.all Entry.canonical = true) (h₂ : c₂.blocks.all Entry.canonical = true)
    (hEq : chainDigest c₁ = chainDigest c₂) :
    c₁.blocks = c₂.blocks ∨
      Obend.Digest.HashBytes.CollisionAmong (cshake256Bytes simplexChainDomain.data.toList)
        (fun x => x = c₁.blocks.flatMap Entry.encode ∨ x = c₂.blocks.flatMap Entry.encode) :=
  Obend.Digest.HashBytes.bindingResult (chainDigest_extract h₁ h₂ hEq)

/-- Domain-separated cSHAKE256 fold of `(chainDigest || vaultStateRoot)` for `.collapsed`. -/
def foldCollapsedRoot (cDigest vaultRoot : Digest) : Digest :=
  cshake256Kernel collapseRootDomain (bytesOfList (cDigest.data.toList ++ vaultRoot.data.toList))

theorem foldCollapsedRoot_eq_spec (cDigest vaultRoot : Digest) :
    (foldCollapsedRoot cDigest vaultRoot).data.toList =
      cshake256Bytes collapseRootDomain.data.toList
        (cDigest.data.toList ++ vaultRoot.data.toList) := by
  unfold foldCollapsedRoot
  rw [cshake256Kernel_toList, bytesOfList_toList]

/-- Events promoting a `SimplexFinalityGate` against `(P : Protocol, sent : Sent)`. -/
inductive SimplexPromotionEvent where
  | attestProposal (leader : NodeId) (view : Nat) (chain : Chain) (vaultRoot : Digest)
  | finalizeWithCert (cert : FinCert) (vaultRoot : Digest)
  | collapseArchive (vaultRoot : Digest)

deriving instance @[expose] DecidableEq for SimplexPromotionEvent

/-- Finality gate bound to `SimplexProtocol.FinCert` and cSHAKE256 `Digest` roots. -/
structure SimplexFinalityGate where
  turnId        : Digest
  currentTier   : FinalityTier
  attestedView  : Option Nat := none
  finCert       : Option FinCert := none
  vaultRoot     : Option Digest := none
  collapsedRoot : Option Digest := none

deriving instance @[expose] DecidableEq for SimplexFinalityGate

/-- Initialize a speculative `SimplexFinalityGate` for `turnId`. -/
def SimplexFinalityGate.init (turnId : Digest) : SimplexFinalityGate :=
  { turnId := turnId, currentTier := .speculative }

/-- Advance `SimplexFinalityGate` against `SimplexProtocol`:
    - Tier 0 → Tier 1 (`attestProposal`): verifies `leader ∈ P.committee`, `leader = P.leader view`,
      the leader's `.propose` message is in `sent`, and `vaultRoot` is a 32-byte digest.
    - Tier 1 → Tier 2 (`finalizeWithCert`): verifies `cert.checks P sent = true` (`n - f` distinct
      committee `finalize` votes in `sent`) and matching 32-byte `vaultRoot`.
    - Tier 2 → Tier 3 (`collapseArchive`): requires `gate.finCert = some cert` and matching
      `gate.vaultRoot = some vaultRoot`, folding `chainDigest cert.chain` and `vaultRoot` via
      `foldCollapsedRoot` (SP 800-185 cSHAKE256). -/
def advanceSimplexGate
    (P : Protocol) (sent : Sent)
    (gate : SimplexFinalityGate)
    (ev : SimplexPromotionEvent) : Option SimplexFinalityGate :=
  match gate.currentTier, ev with
  | .speculative, .attestProposal leader view chain vRoot =>
    if decide (leader ∈ P.committee ∧ leader = P.leader view ∧
               (⟨leader, view, .propose, .block chain⟩ : Msg) ∈ sent ∧
               vRoot.size = 32) then
      some { gate with
        currentTier  := .attested
        attestedView := some view
        vaultRoot    := some vRoot }
    else
      none
  | .attested, .finalizeWithCert cert vRoot =>
    if cert.checks P sent && decide (gate.vaultRoot = some vRoot ∧ vRoot.size = 32) then
      some { gate with
        currentTier := .quorum_final
        finCert     := some cert
        vaultRoot   := some vRoot }
    else
      none
  | .quorum_final, .collapseArchive vRoot =>
    match gate.finCert, gate.vaultRoot with
    | some cert, some existingRoot =>
      if decide (vRoot = existingRoot ∧ vRoot.size = 32) then
        let cRoot := foldCollapsedRoot (chainDigest cert.chain) vRoot
        some { gate with
          currentTier   := .collapsed
          collapsedRoot := some cRoot }
      else
        none
    | _, _ => none
  | _, _ => none

/-- `advanceSimplexGate` monotonically advances `currentTier` along `FinalityTier`. -/
theorem advanceSimplexGate_advances
    (P : Protocol) (sent : Sent)
    (gate next : SimplexFinalityGate) (ev : SimplexPromotionEvent)
    (h : advanceSimplexGate P sent gate ev = some next) :
    gate.currentTier ≤ next.currentTier := by
  cases htier : gate.currentTier <;> cases ev <;>
    simp [advanceSimplexGate, htier] at h
  · rcases h with ⟨_, rfl⟩
    dsimp only
    decide
  · rcases h with ⟨_, rfl⟩
    dsimp only
    decide
  · cases hcert : gate.finCert <;> cases hroot : gate.vaultRoot <;>
      simp [hcert, hroot] at h
    rcases h with ⟨_, rfl⟩
    dsimp only
    decide

/-- Promoting to `.quorum_final` via `advanceSimplexGate` guarantees `cert.checks P sent = true`,
    `Finalized P sent cert.view cert.chain`, and a 32-byte `vaultRoot`. -/
theorem advanceSimplexGate_quorum_final_sound
    (P : Protocol) (sent : Sent)
    (gate next : SimplexFinalityGate)
    (cert : FinCert) (vRoot : Digest)
    (h : advanceSimplexGate P sent gate (.finalizeWithCert cert vRoot) = some next) :
    next.currentTier = .quorum_final ∧
    next.finCert = some cert ∧
    cert.checks P sent = true ∧
    Finalized P sent cert.view cert.chain ∧
    next.vaultRoot = some vRoot ∧
    vRoot.size = 32 := by
  cases htier : gate.currentTier <;>
    simp [advanceSimplexGate, htier] at h
  rcases h with ⟨⟨hchecks, _, hsz⟩, rfl⟩
  exact ⟨rfl, rfl, hchecks, FinCert.checks_implies_finalized hchecks, rfl, hsz⟩

/-- **Unique Finalized Chain Digest Per Height**:
    Over any reachable `SimplexProtocol.Reach P sent`, any two `.quorum_final` promotions
    whose `FinCert` chains have equal block height certify identical block sequences AND
    identical `chainDigest` values! -/
theorem quorum_final_gates_unique_per_height
    {P : Protocol} {sent : Sent} (hr : Reach P sent)
    {gate₁ next₁ gate₂ next₂ : SimplexFinalityGate}
    {cert₁ cert₂ : FinCert} {root₁ root₂ : Digest}
    (h₁ : advanceSimplexGate P sent gate₁ (.finalizeWithCert cert₁ root₁) = some next₁)
    (h₂ : advanceSimplexGate P sent gate₂ (.finalizeWithCert cert₂ root₂) = some next₂)
    (h_height : cert₁.chain.height = cert₂.chain.height) :
    cert₁.chain.blocks = cert₂.chain.blocks ∧
    chainDigest cert₁.chain = chainDigest cert₂.chain := by
  have hc₁ := (advanceSimplexGate_quorum_final_sound P sent gate₁ next₁ cert₁ root₁ h₁).2.2.1
  have hc₂ := (advanceSimplexGate_quorum_final_sound P sent gate₂ next₂ cert₂ root₂ h₂).2.2.1
  have hblocks := FinCert.unique_per_height_reach hr hc₁ hc₂ h_height
  refine ⟨hblocks, ?_⟩
  unfold chainDigest encodeFinalizedBlocks
  rw [hblocks]

/-- Promoting to `.collapsed` binds the exact SP 800-185 `cshake256Bytes` fold of
    `chainDigest cert.chain` and `vRoot`. -/
theorem advanceSimplexGate_collapsed_binds_cshake
    (P : Protocol) (sent : Sent)
    (gate next : SimplexFinalityGate) (vRoot : Digest)
    (h : advanceSimplexGate P sent gate (.collapseArchive vRoot) = some next) :
    ∃ cert : FinCert,
      gate.finCert = some cert ∧
      next.currentTier = .collapsed ∧
      next.collapsedRoot = some (foldCollapsedRoot (chainDigest cert.chain) vRoot) ∧
      (foldCollapsedRoot (chainDigest cert.chain) vRoot).data.toList =
        cshake256Bytes collapseRootDomain.data.toList
          ((chainDigest cert.chain).data.toList ++ vRoot.data.toList) := by
  cases htier : gate.currentTier <;>
    simp [advanceSimplexGate, htier] at h
  cases hcert : gate.finCert <;> cases hroot : gate.vaultRoot <;>
    simp [hcert, hroot] at h
  rename_i cert existingRoot
  rcases h with ⟨⟨rfl, _⟩, rfl⟩
  exact ⟨cert, rfl, rfl, rfl, foldCollapsedRoot_eq_spec (chainDigest cert.chain) vRoot⟩

/-! ## §6b. Commit admission at a Simplex gate -/

section GateAdmission

variable {S : Type} {L : JoinSemilattice S} {I : S → Prop}

/-- **Commit admission at a Simplex finality gate**: a witnessed write is admitted at any tier its
cells allow, with no BFT message; any other write needs the gate's `FinCert` to check against the
protocol and the messages sent (`n - f` distinct committee finalize votes). -/
def admitAtGate (P : Protocol) (sent : Sent) (gate : SimplexFinalityGate) (op : TurnOp L I) : Bool :=
  admitAtTier gate.currentTier op &&
    match op.pushout with
    | some _ => true
    | none =>
      match gate.finCert with
      | some cert => cert.checks P sent
      | none => false

/-- **A write without a pushout witness is admitted only on a checking `FinCert`**: the gate is at
the BFT floor or above and its certificate witnesses `n - f` finalize votes (`Finalized`). -/
theorem admitAtGate_unwitnessed_sound {P : Protocol} {sent : Sent} {gate : SimplexFinalityGate}
    {op : TurnOp L I} (h : admitAtGate P sent gate op = true) (hp : op.pushout = none) :
    FinalityTier.quorum_final ≤ gate.currentTier ∧
      ∃ cert, gate.finCert = some cert ∧ cert.checks P sent = true ∧
        Finalized P sent cert.view cert.chain := by
  unfold admitAtGate at h
  rw [Bool.and_eq_true] at h
  obtain ⟨ha, hc⟩ := h
  refine ⟨FinalityTier.le_trans (turnCommitTier_unwitnessed op hp) (of_decide_eq_true ha), ?_⟩
  rw [hp] at hc
  cases hcert : gate.finCert with
  | none => simp [hcert] at hc
  | some cert =>
    rw [hcert] at hc
    have hchk : cert.checks P sent = true := hc
    exact ⟨cert, rfl, hchk, FinCert.checks_implies_finalized hchk⟩

/-- **Universal soundness of gate admission**: an admitted write either carries a pushout witness
(and commutes with every other witnessed write, `confluent_diamond`) or was finalized by `n - f`
committee votes. -/
theorem admitAtGate_sound {P : Protocol} {sent : Sent} {gate : SimplexFinalityGate} {op : TurnOp L I}
    (h : admitAtGate P sent gate op = true) :
    (∃ w, op.pushout = some w) ∨
      (FinalityTier.quorum_final ≤ gate.currentTier ∧
        ∃ cert, gate.finCert = some cert ∧ cert.checks P sent = true ∧
          Finalized P sent cert.view cert.chain) := by
  cases hp : op.pushout with
  | some w => exact .inl ⟨w, rfl⟩
  | none => exact .inr (admitAtGate_unwitnessed_sound h hp)

end GateAdmission

#tooth admitAtGate_unwitnessed_sound by mutation admitAtGate :=
  fun _ _ gate op => admitAtTier gate.currentTier op

/-! ## §7. The promotions above are inhabited -/

example : promoteStep .speculative (.attestTurn ByteArray.empty) = some .attested := rfl

example :
    (advanceSimplexGate ⟨[0, 1, 2, 3], 1, (· == 3), by decide, by decide, by decide⟩
      [⟨0, 1, .finalize, .block [.block 1 7]⟩, ⟨1, 1, .finalize, .block [.block 1 7]⟩,
       ⟨2, 1, .finalize, .block [.block 1 7]⟩]
      { turnId := ByteArray.empty, currentTier := .attested,
        vaultRoot := some (bytesOfList (List.replicate 32 0)) }
      (.finalizeWithCert ⟨1, [.block 1 7], [0, 1, 2]⟩ (bytesOfList (List.replicate 32 0)))).isSome
      = true := by
  decide

/-- A witnessed tombstoning commits at Tier 0. -/
example : admitAtTier .speculative
    (tombstoneOp (fun n : Nat => n = 3) (fun n => n == 3)
      (fun a h => by simpa using h)) = true := by
  decide

/-- A debit of 7 under the bounded high-water invariant: no witness, so refused at Tier 0 and admitted
at a gate whose `FinCert` checks (3 of 4 finalize votes, `n - f` with `f = 1`). -/
def sampleDebit : TurnOp maxNat (· ≤ 100) := ⟨balanceDebit 7, [], none⟩

example : admitAtTier .speculative sampleDebit = false := by decide

example :
    admitAtGate ⟨[0, 1, 2, 3], 1, (· == 3), by decide, by decide, by decide⟩
      [⟨0, 1, .finalize, .block [.block 1 7]⟩, ⟨1, 1, .finalize, .block [.block 1 7]⟩,
       ⟨2, 1, .finalize, .block [.block 1 7]⟩]
      { turnId := ByteArray.empty, currentTier := .quorum_final,
        finCert := some ⟨1, [.block 1 7], [0, 1, 2]⟩ }
      sampleDebit = true := by
  decide

/-- The same gate without its certificate refuses the debit. -/
example :
    admitAtGate ⟨[0, 1, 2, 3], 1, (· == 3), by decide, by decide, by decide⟩ []
      { turnId := ByteArray.empty, currentTier := .quorum_final } sampleDebit = false := by
  decide

end Obend.Consensus.Finality
end
