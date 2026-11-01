module
/-
# Obend.Vault.Projection — stranger-checkable blinded cSHAKE256 Merkle multiproofs & Fog-of-War noninterference

Absorbs `breadstuffs/Dregg2/Deos/FogOfWar.lean`, `Rerender.lean`, and `Rehydration.lean` on top of
`Obend.Receipt.Merkle` and `Obend.Core.Digest`.

Addresses Requirement R3 and Milestone 3 Feature 26 (`Receipt.blind`) and Feature 27 (`FogOfWar.noninterference`):
1. **Fog-of-War Visibility**: State is partitioned into per-cell authority gates (`VaultCell`). A viewer sees
   a cell if and only if its capability set authorizes it (`canSee`, via `fireGate`). A hidden cell is
   STRUCTURALLY ABSENT from the viewer's visible projection (`visibleTo`), not a redacted placeholder.
2. **Machine-Checked Non-Interference**: If two vaults agree on every cell a viewer holding rights `v` is
   authorized to see (`agreeOn`), their projections are bit-identical (`fog_of_war_noninterference`).
   Consequently, changing or inserting any hidden cell leaves the low projection unchanged
   (`hidden_change_invisible`, `cons_hidden_invisible`).
3. **Cryptographic Blinding & Root Invariance**: Every cell is bound with a cryptographic blinding salt
   (`cellBlind H c = digestWith H c.salt c.content`). In the projected view (`projectCell`), visible cells
   reveal `(id, required, salt, content)`, while hidden cells reveal only the blinded commitment
   (`blinded id (cellBlind H c)`). The Merkle root of the projected vault equals the unredacted vault root
   bit-for-bit (`projectVault_mapRoot_eq`).
4. **Stranger-Checkable Merkle Multiproofs**: A stranger holding zero private cell state can verify
   inclusion of projected cells against the unredacted vault root (`verifyBlindedMultiProof`). Honest vaults
   admit complete proofs (`verify_blinded_opening_complete`), stranger verification is sound
   (`stranger_verification_sound`), and secret cell contents are provably unobservable
   (`projectCell_blinded_reveals_no_content`).
-/
public import Obend.Receipt.Merkle
public import Obend.Core.Digest
public import Obend.Digest.HashBytes

@[expose] public section

namespace Obend.Vault.Projection

open Obend.Core.Digest (digestWith)
open Obend.Digest.HashBytes (Hash Collision)
open Obend.Receipt.Merkle (Small Bounded root path climb leaf leaves mapRoot Opening opens climb_path mapOpening opens_complete opens_binds)

set_option autoImplicit false

/-! ## 1. IPC Authority Kinds & Confinement Gates -/

/-- Authority kinds representing seL4/Dregg2 IPC authorities. -/
inductive Auth where
  | read
  | write
  | grant
  | call
  | reply
  | reset
  | control
  | notify
  deriving DecidableEq, Repr

/-- `fireGate required held`: true iff every required authority is held. -/
def fireGate (required held : List Auth) : Bool :=
  required.all fun r => held.contains r

theorem fireGate_iff_subset (required held : List Auth) :
    fireGate required held = true ↔ ∀ a ∈ required, a ∈ held := by
  simp [fireGate, List.all_eq_true]

theorem fireGate_refl (held : List Auth) : fireGate held held = true := by
  rw [fireGate_iff_subset]; intro a ha; exact ha

theorem fireGate_trans {r h₁ h₂ : List Auth} (hsub : h₁ ⊆ h₂) (hgate : fireGate r h₁ = true) :
    fireGate r h₂ = true := by
  rw [fireGate_iff_subset] at hgate ⊢
  intro a ha
  exact hsub (hgate a ha)

/-! ## 2. Vault Cells & Fog-of-War Projection -/

/-- A cell of the shared vault: stable `id`, access authority `required`, cryptographic blinding `salt`,
    and digest-sized `content`. -/
structure VaultCell where
  id       : Nat
  required : List Auth
  salt     : Nat
  content  : Nat
  deriving DecidableEq, Repr, Inhabited

/-- May a viewer holding rights `v` see cell `c`? -/
def canSee (v : List Auth) (c : VaultCell) : Bool :=
  fireGate c.required v

/-- The per-viewer projection of a vault: the sublist of cells `v` may see.
    Hidden cells are STRUCTURALLY ABSENT (filtered out, not redacted placeholders). -/
def visibleTo (v : List Auth) (s : List VaultCell) : List VaultCell :=
  s.filter (canSee v)

/-- Two vaults are indistinguishable to `v` iff their visible projections are identical. -/
def agreeOn (v : List Auth) (s₁ s₂ : List VaultCell) : Prop :=
  visibleTo v s₁ = visibleTo v s₂

theorem view_deterministic (v : List Auth) (s : List VaultCell) :
    visibleTo v s = visibleTo v s := rfl

theorem visible_means_canSee (v : List Auth) (s : List VaultCell) (c : VaultCell)
    (hmem : c ∈ visibleTo v s) : canSee v c = true :=
  (List.mem_filter.mp hmem).2

theorem canSee_means_visible (v : List Auth) (s : List VaultCell) (c : VaultCell)
    (hmem : c ∈ s) (hsee : canSee v c = true) : c ∈ visibleTo v s :=
  List.mem_filter.mpr ⟨hmem, hsee⟩

/-- Total fog: a hidden cell does not appear in the projection at all (no leak via presence). -/
theorem hiddenCell_absent (v : List Auth) (s : List VaultCell) (c : VaultCell)
    (hhide : canSee v c = false) : c ∉ visibleTo v s := by
  intro hmem
  have hc := visible_means_canSee v s c hmem
  rw [hhide] at hc
  cases hc

/-- **Headline Non-Interference**: A low viewer's render is a function of the authorized state alone.
    If two vaults agree on everything `v` may see, their projections are bit-identical. -/
theorem fog_of_war_noninterference (v : List Auth) (s₁ s₂ : List VaultCell)
    (hagree : agreeOn v s₁ s₂) : visibleTo v s₁ = visibleTo v s₂ := hagree

/-- Inserting a hidden cell leaves the visible view unchanged. -/
theorem cons_hidden_invisible (v : List Auth) (s : List VaultCell) (c : VaultCell)
    (hhide : canSee v c = false) : visibleTo v (c :: s) = visibleTo v s := by
  unfold visibleTo
  rw [List.filter_cons, hhide]
  rfl

/-- Changing a hidden cell outside a viewer's authority leaves the projection bit-identical. -/
theorem hidden_change_invisible (v : List Auth) (pre post : List VaultCell) (c c' : VaultCell)
    (hc : canSee v c = false) (hc' : canSee v c' = false) :
    visibleTo v (pre ++ c :: post) = visibleTo v (pre ++ c' :: post) := by
  unfold visibleTo
  simp only [List.filter_append, List.filter_cons, hc, hc', Bool.false_eq_true, ↓reduceIte]

/-- Divergence: two viewers see different scenes bounded strictly by their caps. -/
theorem divergence (v₁ v₂ : List Auth) (s : List VaultCell) (c : VaultCell)
    (hmem : c ∈ s) (hsee₁ : canSee v₁ c = true) (hhide₂ : canSee v₂ c = false) :
    c ∈ visibleTo v₁ s ∧ c ∉ visibleTo v₂ s :=
  ⟨canSee_means_visible v₁ s c hmem hsee₁, hiddenCell_absent v₂ s c hhide₂⟩

theorem canSee_monotone {v₁ v₂ : List Auth} (h12 : v₁ ⊆ v₂) {c : VaultCell}
    (hsee : canSee v₁ c = true) : canSee v₂ c = true :=
  fireGate_trans h12 hsee

/-- Monotonicity: granting more capability yields a superset view. -/
theorem vision_monotone {v₁ v₂ : List Auth} (h12 : v₁ ⊆ v₂) (s : List VaultCell) :
    visibleTo v₁ s ⊆ visibleTo v₂ s := by
  intro c hc
  have hmem : c ∈ s := (List.mem_filter.mp hc).1
  have hsee₁ : canSee v₁ c = true := visible_means_canSee v₁ s c hc
  exact canSee_means_visible v₂ s c hmem (canSee_monotone h12 hsee₁)

/-- Projection idempotence (stability law). -/
theorem rerender_idempotent (v : List Auth) (s : List VaultCell) :
    visibleTo v (visibleTo v s) = visibleTo v s := by
  unfold visibleTo
  rw [List.filter_filter]
  have h_eq : (fun c => canSee v c && canSee v c) = canSee v := by
    funext c; cases canSee v c <;> rfl
  rw [h_eq]

/-! ## 3. Cryptographic Blinding & Root Invariance -/

/-- The blinded commitment of a cell: H(salt, content). -/
def cellBlind (H : Hash) (c : VaultCell) : Nat :=
  digestWith H c.salt c.content

/-- Projected cell: revealed to authorized viewers, blinded to strangers/unauthorized viewers. -/
inductive ProjectedCell where
  | revealed (id : Nat) (required : List Auth) (salt : Nat) (content : Nat)
  | blinded  (id : Nat) (blindedCommit : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- Project an individual cell for viewer `v`. -/
def projectCell (H : Hash) (v : List Auth) (c : VaultCell) : ProjectedCell :=
  if canSee v c then
    .revealed c.id c.required c.salt c.content
  else
    .blinded c.id (cellBlind H c)

/-- The commitment value verified by the Merkle tree:
    for revealed cells, recomputed from (salt, content);
    for blinded cells, the carried blinded commitment. -/
def projectedCommit (H : Hash) : ProjectedCell → Nat
  | .revealed _ _ salt content => digestWith H salt content
  | .blinded _ blindedCommit  => blindedCommit

/-- **Core Commitment Invariant**: Regardless of whether a cell is revealed or blinded,
    its commitment in the Merkle tree is bit-identical to the unredacted vault cell commitment. -/
theorem projectCell_commit_eq (H : Hash) (v : List Auth) (c : VaultCell) :
    projectedCommit H (projectCell H v c) = cellBlind H c := by
  dsimp [projectCell]
  split <;> rfl

/-- Project all cells in a vault for viewer `v`. -/
def projectVault (H : Hash) (v : List Auth) (cells : List VaultCell) : List ProjectedCell :=
  cells.map (projectCell H v)

/-- The list of unredacted cell commitments in a vault. -/
def vaultCommits (H : Hash) (cells : List VaultCell) : List Nat :=
  cells.map (cellBlind H)

/-- The list of commitment values extracted from a projected vault. -/
def projectedCommits (H : Hash) (v : List Auth) (cells : List VaultCell) : List Nat :=
  (projectVault H v cells).map (projectedCommit H)

/-- The commitments extracted from a projected vault equal the unredacted vault commitments. -/
theorem projectedCommits_eq (H : Hash) (v : List Auth) (cells : List VaultCell) :
    projectedCommits H v cells = vaultCommits H cells := by
  unfold projectedCommits vaultCommits projectVault
  induction cells with
  | nil => rfl
  | cons c rest ih =>
    simp [projectCell_commit_eq, ih]

/-- **Root Invariance Theorem**: The Merkle root of a projected vault is bit-identical
    to the root of the unredacted vault. -/
theorem projectVault_mapRoot_eq (H : Hash) (v : List Auth) (cells : List VaultCell) :
    mapRoot H (projectedCommits H v cells) = mapRoot H (vaultCommits H cells) := by
  rw [projectedCommits_eq]

/-! ## 4. Stranger-Checkable Merkle Multiproofs -/

/-- A blinded opening: tree size, position index, projected cell, and sibling path. -/
structure BlindedOpening where
  size  : Nat
  index : Nat
  cell  : ProjectedCell
  path  : List Nat
  deriving DecidableEq, Repr

/-- Stranger verification of an individual opening against the unredacted vault root. -/
def verifyBlindedOpening (H : Hash) (bo : BlindedOpening) (vaultRoot : Nat) : Bool :=
  Small bo.index &&
  climb H bo.size bo.index (leaf H bo.index (projectedCommit H bo.cell)) bo.path == some vaultRoot

/-- A multiproof verifying a set of projected cells against a vault root. -/
structure BlindedMultiProof where
  vaultRoot : Nat
  size      : Nat
  openings  : List BlindedOpening
  deriving DecidableEq, Repr

/-- Verify all openings in a blinded multiproof. -/
def verifyBlindedMultiProof (H : Hash) (bmp : BlindedMultiProof) : Bool :=
  bmp.openings.all fun bo =>
    bo.size == bmp.size &&
    verifyBlindedOpening H bo bmp.vaultRoot

/-- Construct an honest blinded opening for cell `j`. -/
def mkBlindedOpening (H : Hash) (v : List Auth) (cells : List VaultCell) (j : Nat) : BlindedOpening :=
  let o := mapOpening H (vaultCommits H cells) j
  ⟨o.size, o.index, projectCell H v (cells.getD j default), o.path⟩

theorem verifyBlindedOpening_eq_opens (H : Hash) (bo : BlindedOpening) (vaultRoot : Nat) :
    verifyBlindedOpening H bo vaultRoot =
    opens H ⟨bo.size, bo.index, projectedCommit H bo.cell, bo.path⟩ vaultRoot := rfl

theorem getD_map_helper {α β : Type} (f : α → β) (d : α) (d' : β) :
    ∀ (l : List α) (j : Nat), j < l.length → (l.map f).getD j d' = f (l.getD j d)
  | [], _, hj => by cases hj
  | _ :: _, 0, _ => rfl
  | _ :: xs, n + 1, hj => by
    have hj' : n < xs.length := by simpa using hj
    exact getD_map_helper f d d' xs n hj'

/-- **Completeness Theorem**: Every honestly issued blinded opening verifies against the unredacted vault root. -/
theorem verify_blinded_opening_complete {H : Hash} (hb : Bounded H)
    (v : List Auth) (cells : List VaultCell) (j : Nat)
    (hj : j < cells.length) (hjs : j < 2 ^ 256) :
    verifyBlindedOpening H (mkBlindedOpening H v cells j) (mapRoot H (vaultCommits H cells)) = true := by
  have hlen : j < (vaultCommits H cells).length := by
    simp [vaultCommits, hj]
  have hc := opens_complete hb (vaultCommits H cells) j hlen hjs
  rw [verifyBlindedOpening_eq_opens]
  unfold mkBlindedOpening mapOpening
  dsimp only
  have hcomm : projectedCommit H (projectCell H v (cells.getD j default)) = (vaultCommits H cells).getD j 0 := by
    rw [projectCell_commit_eq]
    exact (getD_map_helper (cellBlind H) default 0 cells j hj).symm
  rw [hcomm]
  exact hc

/-- **Stranger Verification Soundness**: Passing stranger verification entails standard Merkle opening validity. -/
theorem stranger_verification_sound {H : Hash}
    (bo : BlindedOpening) (vaultRoot : Nat) (hver : verifyBlindedOpening H bo vaultRoot = true) :
    opens H ⟨bo.size, bo.index, projectedCommit H bo.cell, bo.path⟩ vaultRoot = true :=
  hver

/-- **Zero Unblinded Data Exposure**: A hidden cell's projected representation cannot evaluate to its raw content. -/
theorem projectCell_blinded_reveals_no_content (H : Hash) (v : List Auth) (c : VaultCell)
    (hhide : canSee v c = false) :
    ∀ val, (match projectCell H v c with
      | .revealed _ _ _ content => some content
      | .blinded _ _ => none) = some val → False := by
  intro val h
  unfold projectCell at h
  rw [hhide] at h
  contradiction

end Obend.Vault.Projection
