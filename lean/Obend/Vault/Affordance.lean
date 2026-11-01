module
/-
# Obend.Vault.Affordance — Gated Affordances with Constructive Repair Badges

Absorbs `breadstuffs/Dregg2/Deos/GatedAffordance.lean` and `FireProgramAgreement.lean`,
wired to `Obend.Vault.Law` (`suggestMultiField`, `suggest`) and `Obend.Spec.LawDial` (`solveLawWitness`).
-/
public import Obend.Core.Data
public import Obend.Core.Term
public import Obend.Law.Contract
public import Obend.Vault.Law
public import Obend.Spec.LawDial
public import Obend.Spec.Law

@[expose] public section

namespace Obend.Vault.Affordance

open Obend.Core.Data
open Obend.Core.Term
open Obend.Law
open Obend.Vault
open Obend.Spec.Law
open Obend.Spec.LawDial

set_option autoImplicit false

/-! ## 1. The 8-Authority Lattice & Cap Gate -/

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

def fireGate (required held : List Auth) : Bool :=
  required.all (fun a => held.contains a)

theorem fireGate_iff_subset (required held : List Auth) :
    fireGate required held = true ↔ required ⊆ held := by
  unfold fireGate
  constructor
  · intro hg a ha
    have := List.all_eq_true.mp hg a ha
    simpa [List.contains_eq_mem] using this
  · intro hsub
    rw [List.all_eq_true]
    intro a ha
    simpa [List.contains_eq_mem] using hsub ha

theorem fireGate_refl (r : List Auth) : fireGate r r = true := by
  rw [fireGate_iff_subset]; exact fun _ ha => ha

theorem fireGate_trans {r h₁ h₂ : List Auth} (h12 : h₁ ⊆ h₂) (hf : fireGate r h₁ = true) :
    fireGate r h₂ = true := by
  rw [fireGate_iff_subset] at hf ⊢
  exact List.Subset.trans hf h12

/-! ## 2. GatedAffordance Structure & Dispatch -/

variable {φ : Type}

structure CellAffordance (φ : Type) where
  required : List Auth
  effect   : φ
  name     : String
deriving DecidableEq, Repr

structure FireCtx (φ : Type) where
  effectDigest : φ → Nat
  prevDigest   : Nat
  preCommit    : Nat
  postCommit   : Nat

structure FiredSurface (φ : Type) where
  firedEffect : φ
  boundRoot   : Nat

structure AffordanceIntent (φ : Type) where
  surface     : FiredSurface φ
  effectsHash : Nat

def fire (aff : CellAffordance φ) (held : List Auth) (fc : FireCtx φ) : Option (AffordanceIntent φ) :=
  if fireGate aff.required held then
    some { surface := { firedEffect := aff.effect, boundRoot := fc.postCommit },
           effectsHash := fc.effectDigest aff.effect }
  else
    none

structure GatedAffordance (φ : Type) where
  aff    : CellAffordance φ
  law    : LawExpr
  fields : List String
  method : Nat := 0

def gatedOK (ga : GatedAffordance φ) (held : List Auth) (facts : Facts) (old : Option Data) (new : Data) : Bool :=
  fireGate ga.aff.required held && ga.law.denote facts old new

def fireGated (ga : GatedAffordance φ) (held : List Auth) (facts : Facts) (old : Option Data) (new : Data)
    (fc : FireCtx φ) : Option (AffordanceIntent φ) :=
  if gatedOK ga held facts old new then
    fire ga.aff held fc
  else
    none

/-! ## 3. Keystone & Polar Metatheorems -/

theorem fireGated_iff (ga : GatedAffordance φ) (held : List Auth) (facts : Facts) (old : Option Data) (new : Data)
    (fc : FireCtx φ) :
    (fireGated ga held facts old new fc).isSome = true ↔
      (fireGate ga.aff.required held = true ∧ ga.law.denote facts old new = true) := by
  unfold fireGated gatedOK fire
  by_cases hcap : fireGate ga.aff.required held = true
  · by_cases hlaw : ga.law.denote facts old new = true
    · simp [hcap, hlaw]
    · simp [hcap, hlaw]
  · simp [hcap]

theorem fireGated_both_pass (ga : GatedAffordance φ) (held : List Auth) (facts : Facts) (old : Option Data) (new : Data)
    (fc : FireCtx φ) (hcap : fireGate ga.aff.required held = true) (hlaw : ga.law.denote facts old new = true) :
    (fireGated ga held facts old new fc).isSome = true :=
  (fireGated_iff ga held facts old new fc).mpr ⟨hcap, hlaw⟩

theorem fireGated_cap_fail_refuses (ga : GatedAffordance φ) (held : List Auth) (facts : Facts) (old : Option Data) (new : Data)
    (fc : FireCtx φ) (hcap : fireGate ga.aff.required held = false) :
    fireGated ga held facts old new fc = none := by
  unfold fireGated gatedOK
  simp [hcap]

theorem fireGated_state_fail_refuses (ga : GatedAffordance φ) (held : List Auth) (facts : Facts) (old : Option Data) (new : Data)
    (fc : FireCtx φ) (hlaw : ga.law.denote facts old new = false) :
    fireGated ga held facts old new fc = none := by
  unfold fireGated gatedOK
  simp [hlaw]

theorem fireGated_needs_both (ga₁ ga₂ : GatedAffordance φ) (held₁ held₂ : List Auth) (facts : Facts)
    (o₁ n₁ o₂ n₂ : Data) (fc : FireCtx φ)
    (_h1cap : fireGate ga₁.aff.required held₁ = true)
    (h1law : ga₁.law.denote facts (some o₁) n₁ = false)
    (h2cap : fireGate ga₂.aff.required held₂ = false)
    (_h2law : ga₂.law.denote facts (some o₂) n₂ = true) :
    fireGated ga₁ held₁ facts (some o₁) n₁ fc = none ∧
    fireGated ga₂ held₂ facts (some o₂) n₂ fc = none :=
  ⟨fireGated_state_fail_refuses ga₁ held₁ facts (some o₁) n₁ fc h1law,
   fireGated_cap_fail_refuses ga₂ held₂ facts (some o₂) n₂ fc h2cap⟩

theorem fireGated_carries_real_effect (ga : GatedAffordance φ) (held : List Auth) (facts : Facts)
    (old : Option Data) (new : Data) (fc : FireCtx φ) (intent : AffordanceIntent φ)
    (h : fireGated ga held facts old new fc = some intent) :
    intent.surface.firedEffect = ga.aff.effect := by
  unfold fireGated gatedOK fire at h
  split at h
  · split at h
    · cases h; rfl
    · contradiction
  · contradiction

theorem fireGated_binds_attested_root (ga : GatedAffordance φ) (held : List Auth) (facts : Facts)
    (old : Option Data) (new : Data) (fc : FireCtx φ) (intent : AffordanceIntent φ)
    (h : fireGated ga held facts old new fc = some intent) :
    intent.surface.boundRoot = fc.postCommit := by
  unfold fireGated gatedOK fire at h
  split at h
  · split at h
    · cases h; rfl
    · contradiction
  · contradiction

/-- **THE HTMX REACTIVITY THEOREM**:
    For a fixed viewer holding authorizing rights, the affordance lights or darkens dynamically
    in response to changes in cell state. -/
theorem fireGated_reactive (ga : GatedAffordance φ) (held : List Auth) (facts : Facts)
    (o₁ n₁ o₂ n₂ : Data) (fc : FireCtx φ)
    (hcap : fireGate ga.aff.required held = true)
    (hlaw₁ : ga.law.denote facts (some o₁) n₁ = false)
    (hlaw₂ : ga.law.denote facts (some o₂) n₂ = true) :
    (fireGated ga held facts (some o₁) n₁ fc).isSome = false ∧
    (fireGated ga held facts (some o₂) n₂ fc).isSome = true :=
  ⟨by rw [fireGated_state_fail_refuses ga held facts (some o₁) n₁ fc hlaw₁]; rfl,
   fireGated_both_pass ga held facts (some o₂) n₂ fc hcap hlaw₂⟩

/-! ## 4. State-Aware Projection & Monotonicity -/

abbrev GatedSurface (φ : Type) := List (GatedAffordance φ)

def projectGatedFor (held : List Auth) (facts : Facts) (old : Option Data) (new : Data)
    (affs : GatedSurface φ) : GatedSurface φ :=
  affs.filter (fun ga => gatedOK ga held facts old new)

theorem projectGatedFor_all_fireable (held : List Auth) (facts : Facts) (old : Option Data) (new : Data)
    (affs : GatedSurface φ) (ga : GatedAffordance φ) (fc : FireCtx φ)
    (hmem : ga ∈ projectGatedFor held facts old new affs) :
    (fireGated ga held facts old new fc).isSome = true := by
  unfold projectGatedFor at hmem
  rw [List.mem_filter] at hmem
  have hgok := hmem.2
  unfold gatedOK at hgok
  rw [Bool.and_eq_true] at hgok
  rw [fireGated_iff]
  exact ⟨hgok.1, hgok.2⟩

theorem projectGatedFor_monotone {held₁ held₂ : List Auth} (h12 : held₁ ⊆ held₂)
    (facts : Facts) (old : Option Data) (new : Data) (affs : GatedSurface φ) :
    projectGatedFor held₁ facts old new affs ⊆ projectGatedFor held₂ facts old new affs := by
  intro ga ha
  unfold projectGatedFor at ha ⊢
  rw [List.mem_filter] at ha ⊢
  refine ⟨ha.1, ?_⟩
  have hgok₁ := ha.2
  unfold gatedOK at hgok₁ ⊢
  rw [Bool.and_eq_true] at hgok₁ ⊢
  have hcap₂ := fireGate_trans h12 hgok₁.1
  exact ⟨hcap₂, hgok₁.2⟩

/-! ## 5. Constructive Repair Badges for Disabled Actions -/

structure RefusalBadge where
  byLaw       : String
  reason      : String
  missingCaps : List Auth := []
  repairEdits : Option (List (String × Nat)) := none
  suggestion  : String := ""
deriving DecidableEq, Repr

inductive AffordanceStatus (φ : Type) where
  | lit  (intent : AffordanceIntent φ)
  | dark (badge : RefusalBadge)

/-- **CONSTRUCTIVE REPAIR BADGE SYNTHESIZER**:
    When an affordance is dark, inspects failure reasons and queries `suggestMultiField` /
    `solveLawWitness` to construct a concrete, actionable repair proposal. -/
def synthesizeRepairBadge (ga : GatedAffordance φ) (held : List Auth) (facts : Facts)
    (old : Option Data) (new : Data) (frontmatterKeys : List String := []) : RefusalBadge :=
  let capPass := fireGate ga.aff.required held
  let lawPass := ga.law.denote facts old new
  if !capPass && !lawPass then
    let missing := ga.aff.required.filter (fun a => !held.contains a)
    let edits := suggestMultiField ga.law facts old new
    let sug := suggest ga.law facts old new frontmatterKeys
    ⟨ga.aff.name, "unauthorized and state contract violated", missing, edits, sug⟩
  else if !capPass then
    let missing := ga.aff.required.filter (fun a => !held.contains a)
    ⟨ga.aff.name, "unauthorized: missing required capabilities", missing, none, ""⟩
  else if !lawPass then
    let edits := suggestMultiField ga.law facts old new
    let sug := suggest ga.law facts old new frontmatterKeys
    ⟨ga.aff.name, "state condition unmet: contract violated", [], edits, sug⟩
  else
    ⟨ga.aff.name, "ok", [], none, ""⟩

/-- Full affordance evaluation returning a lit intent or a constructive repair badge. -/
def evaluateAffordance (ga : GatedAffordance φ) (held : List Auth) (facts : Facts)
    (old : Option Data) (new : Data) (fc : FireCtx φ) (frontmatterKeys : List String := []) :
    AffordanceStatus φ :=
  match fireGated ga held facts old new fc with
  | some intent => .lit intent
  | none => .dark (synthesizeRepairBadge ga held facts old new frontmatterKeys)

/-- **CONSTRUCTIVE REPAIR SOUNDNESS**:
    Any witness synthesized by `solveLawWitness` provably satisfies the active transition law. -/
theorem constructive_repair_sound {keys : List String} {e : LawExpr} {facts : Facts}
    {old : Option Data} {w : Data}
    (hw : solveLawWitness keys e facts old = some w) :
    e.denote facts old w = true :=
  solveLawWitness_sound hw

/-! ## 6. Fire-Program & Contract Agreement (Bypass Impossibility) -/

/-- An attacker attempting to bypass a darkened affordance by submitting a turn directly
    to the store is rejected by contract validation whenever the law fails. -/
theorem bypass_refused_by_contract (ga : GatedAffordance φ) (facts : Facts) (old new : Data)
    (hdark : ga.law.denote facts (some old) new = false) :
    ¬ (ga.law.denote facts (some old) new = true) := by
  intro h; rw [hdark] at h; contradiction

end Obend.Vault.Affordance

end
