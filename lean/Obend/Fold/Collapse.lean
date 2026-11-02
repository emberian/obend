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
public import Obend.Equiv.Improvement

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

/-! ## 8. Connecting Static Record/Extension Collapse to Sands Improvement (`collapse_reduces_ticks`) -/

open Obend.Core.Term (Term extendFields)
open Obend.Equiv (CValue Settled Run CV EvalImproves StrictEvalImproves cv_of_value)

/-- Fold a tower of static record extension layers over a base field list. -/
def foldExtendTower (base : List (String × Term)) (layers : List (List (String × Term))) :
    List (String × Term) :=
  layers.foldl extendFields base

theorem foldExtendTower_append (base : List (String × Term))
    (l₁ l₂ : List (List (String × Term))) :
    foldExtendTower base (l₁ ++ l₂) = foldExtendTower (foldExtendTower base l₁) l₂ := by
  simp [foldExtendTower, List.foldl_append]

/-- Construct the uncollapsed syntax tree `.extend (... (.extend (.record base) l₁) ...) lₙ`
for a tower of static extension layers. -/
def termExtendTower (base : List (String × Term)) (layers : List (List (String × Term))) : Term :=
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
def collapseProjection : Term → Term
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

end Obend.Fold.Collapse
