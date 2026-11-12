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
import all Obend.Receipt.Merkle
public import Obend.Vault.Hyperedge
public import Obend.Fold
public import Obend.Core.Digest
public import Obend.Digest.HashBytes
public import Obend.Equiv.Improvement

public section

namespace Obend.Fold.Collapse

open Obend.Core.Digest (digestWith deployed)
open Obend.Digest.HashBytes (Hash Collision CollisionAmong)
open Obend.Receipt.Merkle (Bounded root leaf leaves mapRoot Opening opens mapOpening Commit
  Digest256 SaltedLeaf256 defaultSaltedLeaf256 saltedTreeRoot256 BlindedMultiproof256
  strictlyAscendingInBounds buildBlindedMultiproof256 verifyBlindedMultiproof256
  verifyBlindedMultiproof256_complete ScopedCollision256 multiproofScopePreimages
  extractMultiproofCollision evalBlindedNode256 simulateBlindedNode256
  saltedSubtreeRoot256 blindedMultiproof_redaction_nonleakage
  cshakeMultiproofHash cshakeMultiproofHash_length_32)
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
@[expose] def stepBlock (s : VaultStore) (b : CommittedBlock) : VaultStore :=
  match b.turn with
  | some t => applyTurn s t
  | none   => s

/-- State transition rollup: fold a sequence of committed blocks over an initial store. -/
@[expose] def foldTrace (s : VaultStore) (trace : Trace) : VaultStore :=
  trace.foldl stepBlock s

/-- Direct turn sequence fold over a vault store. -/
def foldTurns (s : VaultStore) (turns : List VaultTurn) : VaultStore :=
  turns.foldl applyTurn s

/-! ## 2. Merkle Root Collapse -/

/-- Valuation mapping a cell key to its digest-sized commitment in a store. -/
abbrev StoreValuation := VaultStore → String → Nat

/-- Extract the schema values in canonical order. -/
@[expose] def storeValues (schema : List String) (val : StoreValuation) (s : VaultStore) : List Nat :=
  schema.map (val s)

/-- Compute the collapsed Merkle root commitment over a folded vault store. -/
@[expose] def collapseRoot (H : Hash) (schema : List String) (val : StoreValuation) (s : VaultStore) : Nat :=
  mapRoot H (storeValues schema val s)

/-- Roll up a consensus trace from an initial store into a collapsed canonical Merkle root. -/
@[expose] def collapseTrace (H : Hash) (schema : List String) (val : StoreValuation)
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

theorem collapseRoot_binds_scoped {H : Hash} (hb : Bounded H) (schema : List String) (val : StoreValuation)
    (s : VaultStore) (o : Opening) (k : String)
    (h_open : opens H o (collapseRoot H schema val s) = true)
    (h_sz : o.size = schema.length) (h_idx : o.index < schema.length)
    (h_key : schema[o.index] = k) :
    o.value = val s k ∨
      Obend.Digest.HashBytes.CollisionAmong H (fun m =>
        m ∈ Obend.Receipt.Merkle.openingPreimages H o ++
            Obend.Receipt.Merkle.openingPreimages H
              (mapOpening H ((Commit.mk schema (fun st key => val st key)).values s) o.index)) := by
  let hc : Commit VaultStore String := ⟨schema, fun st key => val st key⟩
  have h_root : collapseRoot H schema val s = hc.dated H s := rfl
  rw [h_root] at h_open
  have hop := Commit.opens_val hb hc s h_open (by dsimp [hc]; exact h_sz) (by dsimp [hc]; exact h_idx)
  rcases hop with he | hcol
  · left; dsimp [hc] at he; rw [he, h_key]
  · exact .inr hcol

/-- **Stranger-Checkable Collapsed Merkle Binding**: An opening that verifies against
    `collapseRoot` carries the folded store's true value, or the hash collides. -/
theorem collapseRoot_binds {H : Hash} (hb : Bounded H) (schema : List String) (val : StoreValuation)
    (s : VaultStore) (o : Opening) (k : String)
    (h_open : opens H o (collapseRoot H schema val s) = true)
    (h_sz : o.size = schema.length) (h_idx : o.index < schema.length)
    (h_key : schema[o.index] = k) :
    o.value = val s k ∨ Collision H :=
  (collapseRoot_binds_scoped hb schema val s o k h_open h_sz h_idx h_key).imp_right
    Obend.Digest.HashBytes.CollisionAmong.global

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

/-! ## 8. Connecting Static Record/Extension Collapse to Sands Improvement (`collapse_reduces_ticks`) -/

open Obend.Core.Term (Term extendFields)
open Obend.Equiv (CValue Settled Run CV EvalImproves StrictEvalImproves cv_of_value)

/-- Fold a tower of static record extension layers over a base field list. -/
@[expose] def foldExtendTower (base : List (String × Term)) (layers : List (List (String × Term))) :
    List (String × Term) :=
  layers.foldl extendFields base

theorem foldExtendTower_append (base : List (String × Term))
    (l₁ l₂ : List (List (String × Term))) :
    foldExtendTower base (l₁ ++ l₂) = foldExtendTower (foldExtendTower base l₁) l₂ := by
  simp [foldExtendTower, List.foldl_append]

/-- Construct the uncollapsed syntax tree `.extend (... (.extend (.record base) l₁) ...) lₙ`
for a tower of static extension layers. -/
@[expose] def termExtendTower (base : List (String × Term)) (layers : List (List (String × Term))) : Term :=
  layers.foldl (fun acc fs => .extend acc fs) (.record base)

/-- Recursively extract and collapse a static `.record` / `.extend` tower of arbitrary depth. -/
def collapseExtendTerm : Term → Option (List (String × Term))
  | .record fs => some fs
  | .extend i fs =>
    match collapseExtendTerm i with
    | some inh => some (extendFields inh fs)
    | none => none
  | _ => none

theorem collapseExtendTerm_foldl (layers : List (List (String × Term))) :
    ∀ (t : Term) (base : List (String × Term)),
      collapseExtendTerm t = some base →
      collapseExtendTerm (layers.foldl (fun acc fs => .extend acc fs) t) =
        some (foldExtendTower base layers) := by
  induction layers with
  | nil =>
    intro t base h
    simpa [foldExtendTower] using h
  | cons fs rest ih =>
    intro t base h
    simp only [List.foldl_cons, foldExtendTower]
    refine ih (.extend t fs) (extendFields base fs) ?_
    simp [collapseExtendTerm, h]

/-- `collapseExtendTerm` collapses any `termExtendTower base layers` to `some (foldExtendTower base layers)`. -/
theorem collapseExtendTerm_termExtendTower (base : List (String × Term))
    (layers : List (List (String × Term))) :
    collapseExtendTerm (termExtendTower base layers) = some (foldExtendTower base layers) :=
  collapseExtendTerm_foldl layers (.record base) base rfl

/-- Statically collapse a known record or multi-layer extension projection by resolving
the target field directly when present. -/
@[expose] def collapseProjection : Term → Term
  | .get g name =>
    match collapseExtendTerm g with
    | some fs =>
      match fs.find? (fun f => f.1 == name) with
      | some (_, x) => x
      | none => .get (.record fs) name
    | none => .get g name
  | .extend i fs =>
    match collapseExtendTerm (.extend i fs) with
    | some merged => .record merged
    | none => .extend i fs
  | t => t

theorem collapseProjection_record_eq {fs : List (String × Term)} {name : String} {x : Term}
    (hfind : fs.find? (fun f => f.1 == name) = some (name, x)) :
    collapseProjection (.get (.record fs) name) = x := by
  simp [collapseProjection, collapseExtendTerm, hfind]

theorem collapseProjection_extend_eq {inh fs : List (String × Term)} {name : String} {x : Term}
    (hfind : (extendFields inh fs).find? (fun f => f.1 == name) = some (name, x)) :
    collapseProjection (.get (.extend (.record inh) fs) name) = x := by
  simp [collapseProjection, collapseExtendTerm, hfind]

theorem collapseProjection_tower_eq {base : List (String × Term)}
    {layers : List (List (String × Term))} {name : String} {x : Term}
    (hfind : (foldExtendTower base layers).find? (fun f => f.1 == name) = some (name, x)) :
    collapseProjection (.get (termExtendTower base layers) name) = x := by
  simp [collapseProjection, collapseExtendTerm_termExtendTower, hfind]

/-- Projecting a field from a settled record value costs 1 extra tick compared to evaluating
the resolved field directly. -/
theorem cv_get_record_step {fs : List (String × Term)} {name : String} {x v : Term} {k : Nat}
    (hrec : CValue (.record fs))
    (hfind : fs.find? (fun f => f.1 == name) = some (name, x))
    (hx : CV x v k) :
    CV (.get (.record fs) name) v (k + 1) := by
  have hget := Run.get (r := .eval) (Run.value hrec) hfind hx
  simpa using hget

/-- Inversion of `CV (.get (.record fs) name) v k` for a settled record `CValue (.record fs)`:
every derivation has positive cost `0 < k` and comes from a derivation `CV x v (k - 1)` of
the statically resolved field `x`. -/
theorem cv_get_record_inv {fs : List (String × Term)} {name : String} {x v : Term} {k : Nat}
    (hrec : CValue (.record fs))
    (hfind : fs.find? (fun f => f.1 == name) = some (name, x))
    (h : CV (.get (.record fs) name) v k) :
    0 < k ∧ CV x v (k - 1) := by
  cases h with
  | value h0 => cases h0
  | get h1 hit h2 =>
    obtain ⟨heq, rfl⟩ := cv_of_value hrec h1
    injection heq with hfs
    subst hfs
    rw [hfind] at hit
    injection hit with hpair
    injection hpair with _ hx_eq
    subst hx_eq
    exact ⟨by omega, by simpa using h2⟩

/-- **`collapse_reduces_ticks`**: Collapsing a statically known record projection
`.get (.record fs) name` to `collapseProjection (.get (.record fs) name)` strictly reduces
evaluation tick cost by 1 (`k` vs `k + 1`), establishing both `StrictEvalImproves 1` and
Sands' `EvalImproves`. -/
theorem collapse_reduces_ticks {fs : List (String × Term)} {name : String} {x v : Term} {k : Nat}
    (hrec : CValue (.record fs))
    (hfind : fs.find? (fun f => f.1 == name) = some (name, x))
    (hx : CV x v k) :
    collapseProjection (.get (.record fs) name) = x ∧
      CV (collapseProjection (.get (.record fs) name)) v k ∧
      CV (.get (.record fs) name) v (k + 1) ∧
      k < k + 1 ∧
      StrictEvalImproves 1 (.get (.record fs) name) (collapseProjection (.get (.record fs) name)) ∧
      EvalImproves (.get (.record fs) name) (collapseProjection (.get (.record fs) name)) := by
  have hcol := collapseProjection_record_eq hfind
  refine ⟨hcol, ?_, cv_get_record_step hrec hfind hx, Nat.lt_succ_self k, ?_, ?_⟩
  · rwa [hcol]
  · intro w j hw
    rw [hcol] at hw
    exact cv_get_record_step hrec hfind hw
  · intro w j hw
    rw [hcol]
    obtain ⟨hpos, hbody⟩ := cv_get_record_inv hrec hfind hw
    exact ⟨j - 1, hbody, by omega⟩

theorem run_fields_settled : ∀ (fs : List (String × Term)),
    (∀ f ∈ fs, Settled f.2) → Run .fields (.record fs) (.record fs) fs.length
  | [], _ => .nil
  | (n, t) :: rest, h => by
    have ht : Settled t := h (n, t) List.mem_cons_self
    have hrest := run_fields_settled rest (fun f hf => h f (List.mem_cons_of_mem _ hf))
    have hcons := Run.cons (n := n) (Run.keep ht) hrest
    simpa using hcons

/-- Collapsing a statically known extension projection `.get (.extend (.record inh) fs) name`
saves `fs.length + 2` ticks compared to evaluating the extension and field lookup at runtime. -/
theorem collapse_extend_reduces_ticks {inh fs : List (String × Term)} {name : String}
    {x v : Term} {k : Nat}
    (hinh : CValue (.record inh))
    (hfs : ∀ f ∈ fs, Settled f.2)
    (hfind : (extendFields inh fs).find? (fun f => f.1 == name) = some (name, x))
    (hx : CV x v k) :
    collapseProjection (.get (.extend (.record inh) fs) name) = x ∧
      CV (collapseProjection (.get (.extend (.record inh) fs) name)) v k ∧
      CV (.get (.extend (.record inh) fs) name) v (fs.length + k + 2) ∧
      k < fs.length + k + 2 := by
  have hcol := collapseProjection_extend_eq hfind
  have hext : CV (.extend (.record inh) fs) (.record (extendFields inh fs)) (fs.length + 1) := by
    have := Run.extend (Run.value hinh) (run_fields_settled fs hfs)
    simpa using this
  have hget : CV (.get (.extend (.record inh) fs) name) v (fs.length + k + 2) := by
    have := Run.get (r := .eval) hext hfind hx
    have heq : (fs.length + 1) + k + 1 = fs.length + k + 2 := by omega
    rwa [heq] at this
  refine ⟨hcol, ?_, hget, by omega⟩
  rwa [hcol]

/-! ## 9. Horizon-Compressed 256-Bit Salted Blinded Multiproofs (`collapseSaltedTraceRoot256`)

Welds `Obend.Fold.Collapse` consensus horizon rollups to `Obend.Receipt.Merkle` 256-bit
domain-separated salted blinded multiproofs (`BlindedMultiproof256`). Empty/timeout blocks prune
away bit-identically while unqueried vault cells remain strictly redacted behind salted 32-byte
commitments, with `Type`-valued `PSum` collision extraction (`0 Classical.choice`). -/

/-- Full-width 256-bit salted cell valuation mapping each schema key in a `VaultStore` to its
salted byte-framed leaf (`SaltedLeaf256`). -/
abbrev SaltedCellValuation256 := VaultStore → String → SaltedLeaf256

/-- Materialize the canonical list of 256-bit salted leaves over `schema` for store `s`. -/
def collapseSaltedEntries256 (schema : List String) (val256 : SaltedCellValuation256)
    (s : VaultStore) : List SaltedLeaf256 :=
  schema.map (val256 s)

/-- Compute the 256-bit salted Merkle commitment over a folded `VaultStore`. -/
def collapseSaltedRoot256 (H : Hash) (schema : List String) (val256 : SaltedCellValuation256)
    (s : VaultStore) : Digest256 :=
  saltedTreeRoot256 H (collapseSaltedEntries256 schema val256 s)

/-- Roll up consensus trace `trace` from `s₀` into a canonical 256-bit salted Merkle root. -/
@[expose] def collapseSaltedTraceRoot256 (H : Hash) (schema : List String)
    (val256 : SaltedCellValuation256) (s₀ : VaultStore) (trace : Trace) : Digest256 :=
  collapseSaltedRoot256 H schema val256 (foldTrace s₀ trace)

theorem collapseSaltedRoot256_congr {H : Hash} {schema : List String}
    {val256 : SaltedCellValuation256} {s₁ s₂ : VaultStore}
    (h_agree : ∀ k ∈ schema, val256 s₁ k = val256 s₂ k) :
    collapseSaltedRoot256 H schema val256 s₁ = collapseSaltedRoot256 H schema val256 s₂ := by
  unfold collapseSaltedRoot256 collapseSaltedEntries256
  rw [List.map_congr_left h_agree]

/-- **256-Bit Horizon Compression Invariance (`collapseSaltedTraceRoot256_prune_empty`)**:
Pruning empty/timeout consensus blocks (`filterActive trace`) leaves the 256-bit salted horizon
root commitment bit-for-bit identical. -/
theorem collapseSaltedTraceRoot256_prune_empty (H : Hash) (schema : List String)
    (val256 : SaltedCellValuation256) (s₀ : VaultStore) (trace : Trace) :
    collapseSaltedTraceRoot256 H schema val256 s₀ trace =
      collapseSaltedTraceRoot256 H schema val256 s₀ (filterActive trace) := by
  unfold collapseSaltedTraceRoot256
  rw [foldTrace_filter_empty]

/-- Build a salted blinded 256-bit multiproof opening `queriedIndices` over the horizon-collapsed
consensus trace `foldTrace s₀ trace`, redacting all unqueried sibling subtrees into 32-byte
commitments. -/
def buildCollapsedHorizonMultiproof256 (H : Hash) (schema : List String)
    (val256 : SaltedCellValuation256) (s₀ : VaultStore) (trace : Trace)
    (queriedIndices : List Nat) : BlindedMultiproof256 :=
  buildBlindedMultiproof256 H
    (collapseSaltedEntries256 schema val256 (foldTrace s₀ trace))
    queriedIndices

/-- Verify a salted blinded 256-bit multiproof against a collapsed horizon root `horizonRoot` and
expected schema cardinality `schemaLen`. -/
@[expose] def verifyCollapsedHorizonMultiproof256 (H : Hash) (schemaLen : Nat)
    (proof : BlindedMultiproof256) (horizonRoot : Digest256) : Bool :=
  (proof.treeSize == schemaLen) && verifyBlindedMultiproof256 H proof horizonRoot

/-- Inhabitedness witness for `verifyCollapsedHorizonMultiproof256` over `emptyStore` and an empty
timeout block trace `[⟨0, 0, none, 0⟩]`, valid for every `H : Hash` (including `cshakeMultiproofHash`). -/
theorem verifyCollapsedHorizonMultiproof256_inhabited (H : Hash) :
    let schema := ["vault/root"]
    let val256 : SaltedCellValuation256 := fun _ _ => ⟨0#256, [0x01]⟩
    let trace : Trace := [⟨0, 0, none, 0⟩]
    verifyCollapsedHorizonMultiproof256 H schema.length
      (buildCollapsedHorizonMultiproof256 H schema val256 emptyStore trace [0])
      (collapseSaltedTraceRoot256 H schema val256 emptyStore trace) = true := by
  have hComp := verifyBlindedMultiproof256_complete H [⟨0#256, [0x01]⟩] [0] (by decide)
  simpa [verifyCollapsedHorizonMultiproof256, buildCollapsedHorizonMultiproof256,
    collapseSaltedTraceRoot256, collapseSaltedRoot256, collapseSaltedEntries256,
    foldTrace, stepBlock, buildBlindedMultiproof256] using hComp

/-- **Completeness under Horizon Compression (`verifyCollapsedHorizonMultiproof256_complete`)**:
A multiproof built on the pruned active trace `filterActive trace` verifies directly against the
unpruned consensus trace root `collapseSaltedTraceRoot256 H schema val256 s₀ trace`. -/
theorem verifyCollapsedHorizonMultiproof256_complete (H : Hash) (schema : List String)
    (val256 : SaltedCellValuation256) (s₀ : VaultStore) (trace : Trace)
    (queriedIndices : List Nat)
    (hValid : strictlyAscendingInBounds schema.length queriedIndices = true) :
    verifyCollapsedHorizonMultiproof256 H schema.length
      (buildCollapsedHorizonMultiproof256 H schema val256 s₀ (filterActive trace) queriedIndices)
      (collapseSaltedTraceRoot256 H schema val256 s₀ trace) = true := by
  rw [collapseSaltedTraceRoot256_prune_empty]
  unfold verifyCollapsedHorizonMultiproof256 buildCollapsedHorizonMultiproof256
    collapseSaltedTraceRoot256 collapseSaltedRoot256
  have hLen : (collapseSaltedEntries256 schema val256 (foldTrace s₀ (filterActive trace))).length =
      schema.length := by simp [collapseSaltedEntries256]
  have hTreeSz : (buildBlindedMultiproof256 H
      (collapseSaltedEntries256 schema val256 (foldTrace s₀ (filterActive trace)))
      queriedIndices).treeSize == schema.length := by
    simp [buildBlindedMultiproof256, hLen]
  rw [hTreeSz, Bool.true_and]
  have hValidEntries :
      strictlyAscendingInBounds
        (collapseSaltedEntries256 schema val256 (foldTrace s₀ (filterActive trace))).length
        queriedIndices = true := by
    rw [hLen]
    exact hValid
  exact verifyBlindedMultiproof256_complete H _ queriedIndices hValidEntries

/-- **Constructive `Type`-Valued Horizon Collision Extractor (`extractCollapsedHorizonCollision`)**:
With **`0 Classical.choice`**, any accepted horizon multiproof constructively yields either exact
cell agreement `val256 (foldTrace s₀ trace) k = leaf` on every opened schema cell `(idx, k)`, or an
explicit `ScopedCollision256` pair of distinct preimages under `H`. -/
def extractCollapsedHorizonCollision (H : Hash) (schema : List String)
    (val256 : SaltedCellValuation256) (s₀ : VaultStore) (trace : Trace)
    (proof : BlindedMultiproof256)
    (hVer : verifyCollapsedHorizonMultiproof256 H schema.length proof
      (collapseSaltedTraceRoot256 H schema val256 s₀ trace) = true) :
    let entries := collapseSaltedEntries256 schema val256 (foldTrace s₀ trace)
    PSum
      (∃ opened,
        evalBlindedNode256 H proof.tree schema.length 0 =
          some (collapseSaltedTraceRoot256 H schema val256 s₀ trace, opened) ∧
        opened.map Prod.fst = proof.queriedIndices ∧
        ∀ idx leaf k, (idx, leaf) ∈ opened → schema[idx]? = some k →
          val256 (foldTrace s₀ trace) k = leaf)
      (ScopedCollision256 H (multiproofScopePreimages H entries proof)) :=
  let entries := collapseSaltedEntries256 schema val256 (foldTrace s₀ trace)
  have hConj : proof.treeSize = schema.length ∧
      verifyBlindedMultiproof256 H proof (saltedTreeRoot256 H entries) = true := by
    unfold verifyCollapsedHorizonMultiproof256 collapseSaltedTraceRoot256 collapseSaltedRoot256 at hVer
    have hBoth := (Bool.and_eq_true _ _).mp hVer
    exact ⟨beq_iff_eq.mp hBoth.1, hBoth.2⟩
  have hLen : entries.length = schema.length := List.length_map _
  have hSize : proof.treeSize = entries.length := hConj.1.trans hLen.symm
  match extractMultiproofCollision H entries proof hSize hConj.2 with
  | .inl ok =>
    PSum.inl (by
      obtain ⟨opened, hEv, hIdxs, hAgree⟩ := ok
      rw [hLen] at hEv
      refine ⟨opened, hEv, hIdxs, fun idx leaf k hm hk => ?_⟩
      have hEnt := hAgree idx leaf hm
      dsimp only [entries, collapseSaltedEntries256] at hEnt
      rw [List.getElem?_map, hk] at hEnt
      exact Option.some.inj hEnt)
  | .inr col => PSum.inr col

/-- **Horizon Redaction Non-Leakage (`collapsedHorizon_redaction_nonleakage`)**:
Across a folded consensus trace `foldTrace s₀ trace`, unqueried schema cells are completely absent
from `.openedLeaf` nodes and simulated bit-for-bit identically using **only** 32-byte salted
subtree commitments. -/
theorem collapsedHorizon_redaction_nonleakage (H : Hash) (schema : List String)
    (val256 : SaltedCellValuation256) (s₀ : VaultStore) (trace : Trace)
    (queriedIndices : List Nat)
    (hValid : strictlyAscendingInBounds schema.length queriedIndices = true) :
    let entries := collapseSaltedEntries256 schema val256 (foldTrace s₀ trace)
    (buildCollapsedHorizonMultiproof256 H schema val256 s₀ trace queriedIndices).tree =
      simulateBlindedNode256
        (fun i => if i ∈ queriedIndices then entries.getD i defaultSaltedLeaf256 else defaultSaltedLeaf256)
        (fun st sz => saltedSubtreeRoot256 H st ((entries.drop st).take sz))
        0 schema.length queriedIndices := by
  have hLen : (collapseSaltedEntries256 schema val256 (foldTrace s₀ trace)).length = schema.length := by
    simp [collapseSaltedEntries256]
  have hSim := blindedMultiproof_redaction_nonleakage H
    (collapseSaltedEntries256 schema val256 (foldTrace s₀ trace))
    queriedIndices (by rwa [hLen])
  simpa [buildCollapsedHorizonMultiproof256, hLen] using hSim

/-- **Full 32-Byte `cSHAKE256` Collision Binding (`cshakeCollapsedHorizon_collision_binds`)**:
Discharges the 32-byte digest-width invariant for `cshakeMultiproofHash`, proving that any
`ScopedCollision256` extracted from a forged horizon multiproof is a genuine `CollisionAmong`
`cshakeMultiproofHash` over the finite preimage scope. -/
theorem cshakeCollapsedHorizon_collision_binds (schema : List String)
    (val256 : SaltedCellValuation256) (s₀ : VaultStore) (trace : Trace)
    (proof : BlindedMultiproof256)
    (col : ScopedCollision256 cshakeMultiproofHash
      (multiproofScopePreimages cshakeMultiproofHash
        (collapseSaltedEntries256 schema val256 (foldTrace s₀ trace)) proof)) :
    CollisionAmong cshakeMultiproofHash
      (fun x => x ∈ multiproofScopePreimages cshakeMultiproofHash
        (collapseSaltedEntries256 schema val256 (foldTrace s₀ trace)) proof) :=
  col.toCollisionAmong (fun m _ => cshakeMultiproofHash_length_32 m)

/-- **Two-Table Redaction Indistinguishability (`blindedMultiproof_two_table_indistinguishable`)**:
Any two salted leaf tables `entries₁` and `entries₂` of equal length that agree on `queriedIndices`
and induce equal 32-byte salted commitments on redacted spans produce bit-for-bit **identical**
`BlindedMultiproof256` values — proving redacted leaf payloads/salts cannot influence the proof
beyond their 32-byte `.blinded` subtree commitments. -/
theorem blindedMultiproof_two_table_indistinguishable (H : Hash)
    (entries₁ entries₂ : List SaltedLeaf256) (queriedIndices : List Nat)
    (hLen : entries₁.length = entries₂.length)
    (hValid : strictlyAscendingInBounds entries₁.length queriedIndices = true)
    (hAgreeQueried : ∀ i ∈ queriedIndices,
      entries₁.getD i defaultSaltedLeaf256 = entries₂.getD i defaultSaltedLeaf256)
    (hAgreeRedacted : ∀ st sz,
      saltedSubtreeRoot256 H st ((entries₁.drop st).take sz) =
      saltedSubtreeRoot256 H st ((entries₂.drop st).take sz)) :
    buildBlindedMultiproof256 H entries₁ queriedIndices =
      buildBlindedMultiproof256 H entries₂ queriedIndices := by
  have hValid₂ : strictlyAscendingInBounds entries₂.length queriedIndices = true := by
    rwa [← hLen]
  have hTree₁ := blindedMultiproof_redaction_nonleakage H entries₁ queriedIndices hValid
  have hTree₂ := blindedMultiproof_redaction_nonleakage H entries₂ queriedIndices hValid₂
  have hOracle₁ :
      (fun i => if i ∈ queriedIndices then entries₁.getD i defaultSaltedLeaf256 else defaultSaltedLeaf256) =
      (fun i => if i ∈ queriedIndices then entries₂.getD i defaultSaltedLeaf256 else defaultSaltedLeaf256) := by
    funext i
    by_cases hi : i ∈ queriedIndices
    · simp only [hi, ↓reduceIte]
      exact hAgreeQueried i hi
    · simp only [hi, ↓reduceIte]
  have hOracle₂ :
      (fun st sz => saltedSubtreeRoot256 H st ((entries₁.drop st).take sz)) =
      (fun st sz => saltedSubtreeRoot256 H st ((entries₂.drop st).take sz)) := by
    funext st sz
    exact hAgreeRedacted st sz
  have hTreeEq :
      (buildBlindedMultiproof256 H entries₁ queriedIndices).tree =
      (buildBlindedMultiproof256 H entries₂ queriedIndices).tree := by
    rw [hTree₁, hTree₂, hOracle₁, hOracle₂, hLen]
  cases hmk₁ : buildBlindedMultiproof256 H entries₁ queriedIndices with
  | mk sz₁ q₁ t₁ =>
    cases hmk₂ : buildBlindedMultiproof256 H entries₂ queriedIndices with
    | mk sz₂ q₂ t₂ =>
      have hsz₁ : sz₁ = entries₁.length := by
        simpa [buildBlindedMultiproof256] using congrArg BlindedMultiproof256.treeSize hmk₁.symm
      have hsz₂ : sz₂ = entries₂.length := by
        simpa [buildBlindedMultiproof256] using congrArg BlindedMultiproof256.treeSize hmk₂.symm
      have hq₁ : q₁ = queriedIndices := by
        simpa [buildBlindedMultiproof256] using congrArg BlindedMultiproof256.queriedIndices hmk₁.symm
      have hq₂ : q₂ = queriedIndices := by
        simpa [buildBlindedMultiproof256] using congrArg BlindedMultiproof256.queriedIndices hmk₂.symm
      rw [hmk₁, hmk₂] at hTreeEq
      dsimp only at hTreeEq
      subst hsz₁ hsz₂ hq₁ hq₂ hTreeEq
      rw [hLen]

end Obend.Fold.Collapse
end
