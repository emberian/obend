module
/-
# Obend.Fold.Collapse — Symbolic-to-Collapsed Merkle Folding

Takes a consensus trace (a sequence of committed blocks / VaultTurns) and folds it into
a single canonical collapsed Merkle root commitment using cSHAKE256.

Metatheorems proved:
1. `foldTrace_append`: Trace rollup compositionality / associativity.
2. `collapseTrace_deterministic`: Trace determinism.
3. `collapseRoot_congr`: Semantic store agreement entails identical collapsed roots.
4. `foldTrace_filter_empty`: Pruning preservation for empty/timeout blocks.
5. `collapseTrace_prune_empty`: Collapsed root invariance under empty block pruning.
6. `collapseRoot_binds`: Stranger-checkable binding of folded cells against root.
7. `consensusAdmission`: Audited fold Admission instance for consensus traces.
-/

public import Obend.Receipt.Merkle
public import Obend.Vault.Hyperedge
public import Obend.Fold
public import Obend.Core.Digest
public import Obend.Digest.HashBytes

@[expose] public section

namespace Obend.Fold.Collapse

open Obend.Core.Digest (digestWith deployed)
open Obend.Digest.HashBytes (Hash Collision)
open Obend.Receipt.Merkle (Bounded root leaf leaves mapRoot Opening opens mapOpening Commit)
open Obend.Vault (VaultStore emptyStore updateStore VaultTurn applyTurn)

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-! ## 1. Committed Consensus Blocks and Traces -/

/-- A committed consensus block carrying an optional VaultTurn.
    An empty turn represents a view timeout / skip block without state mutations. -/
structure CommittedBlock where
  height : Nat
  view   : Nat
  turn   : Option VaultTurn
  qcHash : Nat := 0
  deriving Inhabited

abbrev Trace := List CommittedBlock

/-- Single-step store transition induced by a committed block. -/
def stepBlock (s : VaultStore) (b : CommittedBlock) : VaultStore :=
  match b.turn with
  | some t => applyTurn s t
  | none   => s

/-- State transition rollup: fold a sequence of committed blocks over an initial store. -/
def foldTrace (s : VaultStore) (trace : Trace) : VaultStore :=
  trace.foldl stepBlock s

/-- Direct turn sequence fold over a vault store. -/
def foldTurns (s : VaultStore) (turns : List VaultTurn) : VaultStore :=
  turns.foldl applyTurn s

/-! ## 2. Merkle Root Collapse -/

/-- Valuation mapping a cell key to its digest-sized commitment in a store. -/
abbrev StoreValuation := VaultStore → String → Nat

/-- Extract the schema values in canonical order. -/
def storeValues (schema : List String) (val : StoreValuation) (s : VaultStore) : List Nat :=
  schema.map (val s)

/-- Compute the collapsed Merkle root commitment over a folded vault store. -/
def collapseRoot (H : Hash) (schema : List String) (val : StoreValuation) (s : VaultStore) : Nat :=
  mapRoot H (storeValues schema val s)

/-- Roll up a consensus trace from an initial store into a collapsed canonical Merkle root. -/
def collapseTrace (H : Hash) (schema : List String) (val : StoreValuation)
    (s₀ : VaultStore) (trace : Trace) : Nat :=
  collapseRoot H schema val (foldTrace s₀ trace)

/-! ## 3. Metatheorem 1: Associativity & Compositionality -/

/-- **Associativity / Compositionality**: Trace rollup can be segmented into epochs
    and composed associatively. -/
theorem foldTrace_append (s : VaultStore) (t₁ t₂ : Trace) :
    foldTrace s (t₁ ++ t₂) = foldTrace (foldTrace s t₁) t₂ := by
  simp [foldTrace, List.foldl_append]

theorem foldTurns_append (s : VaultStore) (t₁ t₂ : List VaultTurn) :
    foldTurns s (t₁ ++ t₂) = foldTurns (foldTurns s t₁) t₂ := by
  simp [foldTurns, List.foldl_append]

theorem foldTrace_cons (s : VaultStore) (b : CommittedBlock) (rest : Trace) :
    foldTrace s (b :: rest) = foldTrace (stepBlock s b) rest := rfl

/-! ## 4. Metatheorem 2: Determinism -/

/-- Determinism of `foldTrace`: identical inputs yield identical post-states. -/
theorem foldTrace_deterministic {s₁ s₂ : VaultStore} {t₁ t₂ : Trace}
    (hs : s₁ = s₂) (ht : t₁ = t₂) :
    foldTrace s₁ t₁ = foldTrace s₂ t₂ := by
  subst hs; subst ht; rfl

/-- Stores agreeing on the schema valuation produce bit-identical collapsed Merkle roots. -/
theorem collapseRoot_congr {H : Hash} {schema : List String} {val : StoreValuation}
    {s₁ s₂ : VaultStore} (h_agree : ∀ k ∈ schema, val s₁ k = val s₂ k) :
    collapseRoot H schema val s₁ = collapseRoot H schema val s₂ := by
  unfold collapseRoot storeValues
  have h_map : schema.map (val s₁) = schema.map (val s₂) := by
    induction schema with
    | nil => rfl
    | cons k ks ih =>
      simp only [List.map_cons, List.cons.injEq]
      exact ⟨h_agree k (by simp), ih (fun x hx => h_agree x (by simp [hx]))⟩
  rw [h_map]

/-- **Trace Determinism**: Identical traces starting from identical initial stores
    collapse to identical Merkle roots. -/
theorem collapseTrace_deterministic (H : Hash) (schema : List String) (val : StoreValuation)
    {s₁ s₂ : VaultStore} {t₁ t₂ : Trace} (hs : s₁ = s₂) (ht : t₁ = t₂) :
    collapseTrace H schema val s₁ t₁ = collapseTrace H schema val s₂ t₂ := by
  subst hs; subst ht; rfl

/-- **Semantic Determinism**: Distinct traces producing semantically agreeing stores
    collapse to the same Merkle root. -/
theorem collapseTrace_semantic_determinism (H : Hash) (schema : List String) (val : StoreValuation)
    (s₀ : VaultStore) (t₁ t₂ : Trace)
    (h_agree : ∀ k ∈ schema, val (foldTrace s₀ t₁) k = val (foldTrace s₀ t₂) k) :
    collapseTrace H schema val s₀ t₁ = collapseTrace H schema val s₀ t₂ := by
  exact collapseRoot_congr h_agree

/-! ## 5. Metatheorem 3: Pruning Preservation -/

/-- Filter active blocks containing state mutations. -/
def filterActive (trace : Trace) : Trace :=
  trace.filter (fun b => b.turn.isSome)

/-- **Pruning Preservation for Empty Blocks**: Interleaved timeout or skip blocks
    do not alter the rolled-up state. -/
theorem foldTrace_filter_empty (trace : Trace) (s : VaultStore) :
    foldTrace s trace = foldTrace s (filterActive trace) := by
  induction trace generalizing s with
  | nil => rfl
  | cons b rest ih =>
    simp only [foldTrace, List.foldl_cons]
    cases hb : b.turn with
    | none =>
      have hstep : stepBlock s b = s := by simp [stepBlock, hb]
      have hfilt : filterActive (b :: rest) = filterActive rest := by
        simp [filterActive, hb]
      rw [hstep, hfilt]
      exact ih s
    | some t =>
      have hfilt : filterActive (b :: rest) = b :: filterActive rest := by
        simp [filterActive, hb]
      rw [hfilt]
      simp only [foldTrace, List.foldl_cons]
      exact ih (stepBlock s b)

/-- **Collapsed Root Invariance under Empty Block Pruning**: Pruning empty/timeout blocks
    leaves the collapsed Merkle root bit-identical. -/
theorem collapseTrace_prune_empty (H : Hash) (schema : List String) (val : StoreValuation)
    (s₀ : VaultStore) (trace : Trace) :
    collapseTrace H schema val s₀ trace = collapseTrace H schema val s₀ (filterActive trace) := by
  unfold collapseTrace
  rw [foldTrace_filter_empty]

/-! ## 6. Metatheorem 4: Stranger-Checkable Merkle Binding -/

/-- Create an opening for a schema key against a collapsed Merkle root. -/
def openCell (H : Hash) (schema : List String) (val : StoreValuation) (s : VaultStore) (k : String) :
    Option Opening :=
  (Commit.mk schema (fun st key => val st key)).opening H s k

/-- **Stranger-Checkable Collapsed Merkle Binding**: An opening that verifies against
    `collapseRoot` carries the folded store's true value, or the hash collides. -/
theorem collapseRoot_binds {H : Hash} (hb : Bounded H) (schema : List String) (val : StoreValuation)
    (s : VaultStore) (o : Opening) (k : String)
    (h_open : opens H o (collapseRoot H schema val s) = true)
    (h_sz : o.size = schema.length) (h_idx : o.index < schema.length)
    (h_key : schema[o.index] = k) :
    o.value = val s k ∨ Collision H := by
  let hc : Commit VaultStore String := ⟨schema, fun st key => val st key⟩
  have h_root : collapseRoot H schema val s = hc.dated H s := rfl
  rw [h_root] at h_open
  have hop := Commit.opens_val hb hc s h_open (by dsimp [hc]; exact h_sz) (by dsimp [hc]; exact h_idx)
  rcases hop with he | hcol
  · left
    dsimp [hc] at he
    rw [he, h_key]
  · right
    exact hcol

/-! ## 7. Integration with Obend.Fold.Admission -/

inductive ConsensusRow where
  | commit (b : CommittedBlock)
  | observeWorld (w : VaultStore)

/-- Consensus Trace Rollup Admission: instantiating `Obend.Fold.Admission`. -/
def consensusAdmission (_schema : List String) (_val : StoreValuation) :
    Obend.Fold.Admission VaultStore Nat ConsensusRow String Unit where
  step := fun (w, r) row =>
    match row with
    | .commit b => .ok (stepBlock w b, b.height)
    | .observeWorld w' => .ok (w', r)
  reads := fun (w, _) row =>
    match row with
    | .commit b =>
      match b.turn with
      | some t => t.readPins.map (·.cell)
      | none   => []
    | .observeWorld _ => []
  look := fun w cell =>
    (w cell).isSome
  moves := fun row =>
    match row with
    | .commit b => b.turn.isSome
    | .observeWorld _ => true
  observe := fun w' => .observeWorld w'
  allowed := fun _ _ => true
  keeps_world := by
    intro ⟨w, r⟩ row ⟨w', r'⟩ hm hs
    cases row with
    | commit b =>
      cases hturn : b.turn with
      | none =>
        simp [hturn, stepBlock] at hs
        exact hs.1.symm
      | some t =>
        simp [hturn] at hm
    | observeWorld w_obs =>
      simp at hm
  step_of_reads := by
    intro ⟨w, r⟩ w' row hm hreads
    cases row with
    | commit b =>
      cases hturn : b.turn with
      | none =>
        simp [hturn, stepBlock, Except.map]
      | some t =>
        simp [hturn] at hm
    | observeWorld w_obs =>
      simp at hm
  observe_ok := by
    intro w w' l ha
    rfl

end Obend.Fold.Collapse
