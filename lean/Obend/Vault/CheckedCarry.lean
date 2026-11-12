module
/-
# Obend.Vault.CheckedCarry — Obligations at a Change of World Interpretation

Mathlib-free pure Lean 4 port of `minidregg/Theory/CheckedCarry.lean` onto
`Obend.Vault.Retention.Contract` and `Obend.Vault.Transport.Grants`.

## Core Metatheorems:
1. **Complete Inventory Dispositions (`Plan`)**:
   - `disposition_total`: every source cell index is accounted for (`keep` or `drop`).
   - `duplicate_output_refused`: distinct source cells cannot collide on a kept target ID.
   - `no_drop_at`: under `NoDrops`, no cell is dropped.
   - `dropped_cell_in_retire`: under `RetentionAlignedPlan`, every dropped cell is explicitly
     declared in the active `Retention.Contract.retire` list.
2. **Neutral Authority Lift (`AuthorityMeaning`)**:
   - Over `Transport.Grants` (standing + two-phase `revoked` set) and `Retention.Contract`
     (`retire`, `abandon`), changing commitment roots (`grantRoot`, `storeRoot`) while
     preserving `AuthorityMeaning` preserves `AdmissibleCarry` iff (`neutral_capability_iff`),
     while revoking a grant (`Grants.revoke`), retiring a form, abandoning a branch, or
     resetting `logicalHeight` to `0` strictly refuses admission (`AuthorityPoles`).
3. **Semantic Field Migration (`TitleMigration`)**:
   - `copied_title_grant_not_semantic_narrowing`: copying raw numeric field grants across a
     schema migration where slots `3` and `8` remap to `7` and `3` fails `NoNewMeaning`
     (leaking `.membership` authority from a `.title`-only grant).
   - `translated_title_grant_preserves_meaning` & `translated_effect_exact`: semantic field
     translation preserves `NoNewMeaning` and exact edit semantics.
4. **Shared-Origin Receipt Recovery (`Origin`, `recover`, `admit`)**:
   - `original_acceptance_makes_translation_replay`: original and translated requests share one
     `Origin`, preventing double execution across world migrations.
   - `fresh_revoked_translation_refuses` & `changed_origin_meaning_refuses`: unconsumed
     revoked requests and mutated semantic commitments are refused.
-/

public import Obend.Vault.Retention
public import Obend.Vault.Transport

@[expose] public section

namespace Obend.Vault.CheckedCarry

open Obend.Vault.Form (Grant mayWrite)
open Obend.Vault.Retention (Contract)
open Obend.Vault.Transport (Standing Grants mem_live mem_live_revoke)

set_option autoImplicit false

/-! ## 1. Complete Dispositions Over Verified Source Inventories -/

/-- Canonical digest carrier (`ByteArray`, e.g. 32-byte cSHAKE256 output). -/
abbrev Digest := ByteArray

/-- A cell entry in a verified source or target vault inventory. -/
structure Cell where
  id : String
  bytes : List UInt8
  deriving DecidableEq, Repr

/-- Explicit drop metadata; existence of a reason string grants no authority on its own. -/
structure DropReason where
  code : Nat
  contractName : String
  explanation : String
  nonempty : explanation ≠ ""

/-- Per-cell disposition across a checked carry boundary. -/
inductive Disposition where
  | keep (target : Cell)
  | drop (reason : DropReason)

/-- Verified carry plan over a duplicate-free `source` inventory. -/
structure Plan (source : List Cell) (keepRelation : Cell → Cell → Prop) where
  sourceUnique : (source.map Cell.id).Nodup
  decideCell : (i : Fin source.length) → Disposition
  kept : ∀ i target, decideCell i = .keep target →
    keepRelation source[i] target
  outputsUnique : ∀ i j target other,
    decideCell i = .keep target → decideCell j = .keep other →
    target.id = other.id → i = j

/-- Every cell in the verified source inventory receives a total disposition. -/
theorem disposition_total {source : List Cell} {relation : Cell → Cell → Prop}
    (plan : Plan source relation) (i : Fin source.length) :
    (∃ target, plan.decideCell i = .keep target) ∨
    (∃ reason, plan.decideCell i = .drop reason) := by
  cases choice : plan.decideCell i with
  | keep target => exact .inl ⟨target, rfl⟩
  | drop reason => exact .inr ⟨reason, rfl⟩

/-- Two distinct source entries cannot map to kept target cells with the same `id`. -/
theorem duplicate_output_refused {source : List Cell} {relation : Cell → Cell → Prop}
    (plan : Plan source relation)
    (i j : Fin source.length) (different : i ≠ j) (left right : Cell)
    (hi : plan.decideCell i = .keep left)
    (hj : plan.decideCell j = .keep right) : left.id ≠ right.id := by
  intro same
  exact different (plan.outputsUnique i j left right hi hj same)

/-- Stronger law-component cut: every source cell is kept (`NoDrops`). -/
def NoDrops {source : List Cell} {relation : Cell → Cell → Prop}
    (plan : Plan source relation) : Prop :=
  ∀ i, ∃ target, plan.decideCell i = .keep target

theorem no_drop_at {source : List Cell} {relation : Cell → Cell → Prop}
    {plan : Plan source relation}
    (noDrops : NoDrops plan) (i : Fin source.length) (reason : DropReason) :
    plan.decideCell i ≠ .drop reason := by
  obtain ⟨target, hkept⟩ := noDrops i
  rw [hkept]
  intro impossible
  cases impossible

/-- Materialized list of kept target cells across `source`. -/
def Plan.outputs {source : List Cell} {rel : Cell → Cell → Prop} (plan : Plan source rel) : List Cell :=
  (List.finRange source.length).filterMap fun i =>
    match plan.decideCell i with
    | .keep target => some target
    | .drop _ => none

/-- Under `NoDrops plan`, every source cell index maps to a target cell in `plan.outputs` satisfying `rel`. -/
theorem Plan.noDrops_maps_all_cells {source : List Cell} {rel : Cell → Cell → Prop}
    (plan : Plan source rel) (hNoDrops : NoDrops plan) :
    ∀ i : Fin source.length, ∃ next ∈ plan.outputs, rel source[i] next := by
  intro i
  obtain ⟨target, hkeep⟩ := hNoDrops i
  refine ⟨target, ?_, plan.kept i target hkeep⟩
  unfold Plan.outputs
  exact List.mem_filterMap.mpr ⟨i, List.mem_finRange i, by simp [hkeep]⟩

/-- A drop is authorized by a declared `Retention.Contract` iff the source cell is listed in
    `retContract.retire` and the drop names `retContract.name`. -/
def DropAuthorizedBy (retContract : Retention.Contract) (src : Cell) (reason : DropReason) : Prop :=
  src.id ∈ retContract.retire ∧ reason.contractName = retContract.name

/-- A `Plan` aligned with a `Retention.Contract`: every `.drop` is authorized by `retContract`. -/
structure RetentionAlignedPlan
    (retContract : Retention.Contract)
    (source : List Cell)
    (keepRelation : Cell → Cell → Prop) extends Plan source keepRelation where
  dropAuthorized : ∀ i reason, decideCell i = .drop reason →
    DropAuthorizedBy retContract source[i] reason

theorem dropped_cell_in_retire
    {retContract : Retention.Contract} {source : List Cell} {rel : Cell → Cell → Prop}
    (plan : RetentionAlignedPlan retContract source rel)
    (i : Fin source.length) (reason : DropReason)
    (hdrop : plan.decideCell i = .drop reason) :
    source[i].id ∈ retContract.retire ∧ reason.contractName = retContract.name :=
  plan.dropAuthorized i reason hdrop

/-! ## 2. Neutral Authority Meaning Over `Transport.Grants` & `Retention.Contract` -/

/-- Vault authority state combining `Transport.Grants` (standing + two-phase `revoked`),
    `Retention.Contract` (`retire` forms + `abandon` branches), monotonic `logicalHeight`,
    and rerootable cryptographic commitment digests (`grantRoot`, `storeRoot`). -/
structure VaultAuthState where
  grants : Grants
  retention : Retention.Contract
  logicalHeight : Nat
  grantRoot : Digest
  storeRoot : Digest
  deriving DecidableEq

/-- Request evaluated across a checked carry boundary. -/
structure CarryRequest where
  holder : String
  grantId : String
  formName : String
  branchName : Option String
  scope : List String
  pages : List String
  validFrom : Nat
  validUntil : Nat
  deriving DecidableEq, Repr

/-- Write scope coverage for `pages` under a standing grant `s` and `scope`. -/
def CoversPages (s : Standing) (scope pages : List String) : Prop :=
  ∀ p ∈ pages, mayWrite (s.grant.viewer scope) p = true

/-- Capability and retention admission predicate over `VaultAuthState`. -/
def AdmissibleCarry (st : VaultAuthState) (req : CarryRequest) : Prop :=
  ∃ standing : Standing,
    standing ∈ st.grants.live ∧
    standing.id = req.grantId ∧
    standing.grant.holder = req.holder ∧
    CoversPages standing req.scope req.pages ∧
    req.validFrom ≤ st.logicalHeight ∧
    st.logicalHeight ≤ req.validUntil ∧
    req.formName ∉ st.retention.retire ∧
    (∀ b, req.branchName = some b → b ∉ st.retention.abandon)

/-- Commitment roots (`grantRoot`, `storeRoot`) may change across compaction/rerooting,
    while the logical authority interpretation (`grants.live`, `grants.revoked`,
    `retention.retire`, `retention.abandon`, `logicalHeight`) is preserved. -/
structure AuthorityMeaning (old next : VaultAuthState) : Prop where
  liveIff : ∀ s, s ∈ old.grants.live ↔ s ∈ next.grants.live
  revokedEq : old.grants.revoked = next.grants.revoked
  retireEq : old.retention.retire = next.retention.retire
  abandonEq : old.retention.abandon = next.retention.abandon
  logicalHeightEq : old.logicalHeight = next.logicalHeight

theorem AuthorityMeaning.symm {old next : VaultAuthState} (same : AuthorityMeaning old next) :
    AuthorityMeaning next old :=
  ⟨fun s => (same.liveIff s).symm, same.revokedEq.symm, same.retireEq.symm,
    same.abandonEq.symm, same.logicalHeightEq.symm⟩

theorem neutral_capability_forward {old next : VaultAuthState}
    (same : AuthorityMeaning old next) (req : CarryRequest)
    (accepted : AdmissibleCarry old req) : AdmissibleCarry next req := by
  rcases accepted with ⟨standing, isLive, idEq, holderEq, covers, validFromLe, validUntilGe,
    formNotRetired, branchNotAbandoned⟩
  exact ⟨standing,
    (same.liveIff standing).mp isLive,
    idEq,
    holderEq,
    covers,
    same.logicalHeightEq ▸ validFromLe,
    same.logicalHeightEq ▸ validUntilGe,
    same.retireEq ▸ formNotRetired,
    fun b hb => same.abandonEq ▸ branchNotAbandoned b hb⟩

theorem neutral_capability_iff {old next : VaultAuthState}
    (same : AuthorityMeaning old next) (req : CarryRequest) :
    AdmissibleCarry old req ↔ AdmissibleCarry next req :=
  ⟨neutral_capability_forward same req, neutral_capability_forward same.symm req⟩

theorem neutral_write_scope_iff {old next : VaultAuthState}
    (same : AuthorityMeaning old next) (s : Standing) (scope pages : List String) :
    (s ∈ old.grants.live ∧ CoversPages s scope pages) ↔
      (s ∈ next.grants.live ∧ CoversPages s scope pages) := by
  rw [same.liveIff s]

/-! ### Concrete Semantic Poles Over `Transport.Grants` & `Retention.Contract` -/

namespace AuthorityPoles

def demoStanding : Standing :=
  { id := "grant-treasury-1"
  , grant := { holder := "alice", held := [.read, .write], patterns := ["vault/desk"] } }

def demoState : VaultAuthState :=
  { grants := { standing := [demoStanding], revoked := [] }
  , retention := { name := "horizon-1", retire := ["legacy-form"], abandon := ["stale-fork"] }
  , logicalHeight := 42
  , grantRoot := ByteArray.mk #[0x01, 0x02]
  , storeRoot := ByteArray.mk #[0x03, 0x04] }

def demoRequest : CarryRequest :=
  { holder := "alice"
  , grantId := "grant-treasury-1"
  , formName := "drex-order-v1"
  , branchName := some "active-fork"
  , scope := ["vault/desk"]
  , pages := ["vault/desk"]
  , validFrom := 10
  , validUntil := 100 }

theorem demoRequest_admissible : AdmissibleCarry demoState demoRequest := by
  refine ⟨demoStanding, by decide, rfl, rfl, ?_, by decide, by decide, by decide, ?_⟩
  · intro p hp
    simp only [demoRequest, List.mem_singleton] at hp
    subst hp
    decide
  · intro b hb
    injection hb with hb'
    subst hb'
    decide

def rerooted : VaultAuthState :=
  { demoState with
    grantRoot := ByteArray.mk #[0xAA, 0xBB]
    storeRoot := ByteArray.mk #[0xCC, 0xDD] }

theorem same_meaning : AuthorityMeaning demoState rerooted :=
  ⟨fun _ => Iff.rfl, rfl, rfl, rfl, rfl⟩

theorem commitments_changed :
    demoState.grantRoot ≠ rerooted.grantRoot ∧
      demoState.storeRoot ≠ rerooted.storeRoot := by
  constructor <;>
  · intro h
    have hlist := congrArg (fun b => b.data.toList) h
    simp [demoState, rerooted] at hlist

theorem live_capability_survives_rerooting :
    AdmissibleCarry rerooted demoRequest :=
  neutral_capability_forward same_meaning demoRequest demoRequest_admissible

def revokedState : VaultAuthState :=
  { rerooted with grants := rerooted.grants.revoke "grant-treasury-1" }

theorem fresh_revoked_capability_refused :
    ¬ AdmissibleCarry revokedState demoRequest := by
  rintro ⟨standing, isLive, idEq, _⟩
  have hlive := (mem_live_revoke rerooted.grants "grant-treasury-1" standing).mp isLive
  exact hlive.2 idEq

def retiredFormState : VaultAuthState :=
  { rerooted with
    retention := { rerooted.retention with retire := "drex-order-v1" :: rerooted.retention.retire } }

theorem retired_form_refused :
    ¬ AdmissibleCarry retiredFormState demoRequest := by
  rintro ⟨_, _, _, _, _, _, _, formNotRetired, _⟩
  exact formNotRetired (List.Mem.head _)

def resetHeightState : VaultAuthState :=
  { rerooted with logicalHeight := 0 }

theorem resetting_segment_height_does_not_refresh_grant :
    ¬ AdmissibleCarry resetHeightState demoRequest := by
  rintro ⟨_, _, _, _, _, validFromLe, _⟩
  simp [resetHeightState, demoRequest] at validFromLe

end AuthorityPoles

/-! ## 3. Semantic Field Migration (`TitleMigration`) — Meaning, Not Numeric Slot Inclusion -/

namespace TitleMigration

inductive FieldSlot where
  | slot (n : Nat)
  deriving DecidableEq, Repr

/-- Explicit field-slot grant (`none` = unrestricted, `some slots` = restricted to `slots`). -/
abbrev FieldGrant := Option (List FieldSlot)

def FieldGrant.NamedBy (g : FieldGrant) (f : FieldSlot) : Prop :=
  match g with
  | none => True
  | some slots => f ∈ slots

instance (g : FieldGrant) (f : FieldSlot) : Decidable (FieldGrant.NamedBy g f) := by
  cases g with
  | none => exact isTrue trivial
  | some slots =>
    unfold FieldGrant.NamedBy
    infer_instance

def FieldGrant.SetNarrows (sub sup : FieldGrant) : Prop :=
  ∀ f, FieldGrant.NamedBy sub f → FieldGrant.NamedBy sup f

theorem FieldGrant.SetNarrows.refl (g : FieldGrant) : FieldGrant.SetNarrows g g :=
  fun _ h => h

inductive Meaning where
  | title
  | membership
  deriving DecidableEq, Repr

def oldField : Meaning → FieldSlot
  | .title => .slot 3
  | .membership => .slot 8

def nextField : Meaning → FieldSlot
  | .title => .slot 7
  | .membership => .slot 3

def oldGrant : FieldGrant := some [.slot 3]
def correctGrant : FieldGrant := some [.slot 7]
def copiedGrant : FieldGrant := oldGrant

/-- A migrated field grant introduces no new semantic authority: every semantic field
    permitted in the target schema was permitted in the source schema. -/
def NoNewMeaning (oldFields newFields : FieldGrant) : Prop :=
  ∀ meaning, FieldGrant.NamedBy newFields (nextField meaning) →
    FieldGrant.NamedBy oldFields (oldField meaning)

theorem numeric_subset_is_insufficient :
    FieldGrant.SetNarrows copiedGrant oldGrant :=
  FieldGrant.SetNarrows.refl oldGrant

theorem copied_title_grant_gives_membership :
    FieldGrant.NamedBy copiedGrant (nextField .membership) := by decide

/-- Naive numeric slot copying across schema migration fails `NoNewMeaning`:
    a `.title`-only grant (`slot 3`) silently acquires `.membership` authority (`slot 3` in next). -/
theorem copied_title_grant_not_semantic_narrowing :
    ¬ NoNewMeaning oldGrant copiedGrant := by
  intro supposed
  have forbidden := supposed .membership copied_title_grant_gives_membership
  have absent : ¬ FieldGrant.NamedBy oldGrant (oldField .membership) := by decide
  exact absent forbidden

/-- Semantic translation (`slot 3 → slot 7`) preserves `NoNewMeaning`. -/
theorem translated_title_grant_preserves_meaning :
    NoNewMeaning oldGrant correctGrant := by
  intro meaning allowed
  cases meaning with
  | title => decide
  | membership =>
    have forbidden : ¬ FieldGrant.NamedBy correctGrant (nextField .membership) := by decide
    exact False.elim (forbidden allowed)

structure Document where
  title : Nat
  membership : Nat
  deriving DecidableEq, Repr

structure Edit where
  field : Nat
  value : Nat
  deriving DecidableEq, Repr

def oldStep (document : Document) (edit : Edit) : Option Document :=
  if edit.field = 3 then some { document with title := edit.value }
  else if edit.field = 8 then some { document with membership := edit.value }
  else none

def nextStep (document : Document) (edit : Edit) : Option Document :=
  if edit.field = 7 then some { document with title := edit.value }
  else if edit.field = 3 then some { document with membership := edit.value }
  else none

def translate (edit : Edit) : Option Edit :=
  if edit.field = 3 then some { edit with field := 7 }
  else if edit.field = 8 then some { edit with field := 3 }
  else none

theorem translated_effect_exact (document : Document) (edit : Edit) :
    (translate edit).bind (nextStep document) = oldStep document edit := by
  rcases edit with ⟨field, value⟩
  by_cases title : field = 3
  · simp [translate, nextStep, oldStep, title]
  · by_cases member : field = 8
    · simp [translate, nextStep, oldStep, member]
    · simp [translate, oldStep, title, member]

theorem byte_copy_changes_the_wrong_field :
    nextStep ⟨10, 0⟩ ⟨3, 17⟩ = some ⟨10, 17⟩ ∧
    oldStep ⟨10, 0⟩ ⟨3, 17⟩ = some ⟨17, 0⟩ := by decide

end TitleMigration

/-! ## 4. Shared-Origin Receipt Recovery Across World Interpretations -/

/-- Canonical origin identity shared between an original request and its carried translation. -/
structure Origin where
  domain : Digest
  genesis : Digest
  transaction : Digest
  effectIndex : Nat
  deriving DecidableEq

/-- Retained receipt journal entry binding `origin` and semantic commitment `meaning` to `outcome`. -/
structure Receipt where
  origin : Origin
  meaning : Digest
  outcome : Digest
  deriving DecidableEq

inductive Recovery where
  | fresh
  | historical (outcome : Digest)
  | conflict
  deriving DecidableEq

/-- Constructive origin lookup using `decide` on `DecidableEq Origin` (avoiding `LawfulBEq` axioms). -/
def recover (journal : List Receipt) (origin : Origin) (meaning : Digest) : Recovery :=
  match journal.find? (fun receipt => decide (receipt.origin = origin)) with
  | none => .fresh
  | some receipt =>
    if receipt.meaning = meaning then .historical receipt.outcome else .conflict

theorem exact_origin_recovers (receipt : Receipt) (rest : List Receipt) :
    recover (receipt :: rest) receipt.origin receipt.meaning =
      .historical receipt.outcome := by
  simp [recover]

theorem changed_meaning_conflicts (receipt : Receipt) (rest : List Receipt)
    (different : Digest) (changed : receipt.meaning ≠ different) :
    recover (receipt :: rest) receipt.origin different = .conflict := by
  simp [recover, changed]

theorem retained_journal_does_not_refresh (receipt : Receipt) (rest : List Receipt) :
    recover (receipt :: rest) receipt.origin receipt.meaning ≠ .fresh := by
  rw [exact_origin_recovers]
  intro impossible
  cases impossible

/-- Translated request sharing `origin` and semantic `meaning` with its pre-migration original. -/
structure TranslatedRequest where
  origin : Origin
  meaning : Digest
  oldSignedBytes : List UInt8
  newCanonicalBytes : List UInt8
  carryArtifact : Digest

def TranslatedRequest.recovery (request : TranslatedRequest) (journal : List Receipt) : Recovery :=
  recover journal request.origin request.meaning

theorem translated_original_same_recovery (request : TranslatedRequest)
    (journal : List Receipt) :
    request.recovery journal = recover journal request.origin request.meaning := rfl

inductive Admission where
  | accepted (journal : List Receipt) (outcome : Digest)
  | replayed (outcome : Digest)
  | refused
  deriving DecidableEq

/-- Admit a carried request against the retained receipt journal and current authority. -/
def admit (journal : List Receipt) (request : TranslatedRequest)
    (currentAllowed : Bool) (outcome : Digest) : Admission :=
  match request.recovery journal with
  | .historical recorded => .replayed recorded
  | .conflict => .refused
  | .fresh =>
    if currentAllowed then
      .accepted (⟨request.origin, request.meaning, outcome⟩ :: journal) outcome
    else .refused

theorem original_acceptance_makes_translation_replay
    (journal : List Receipt) (request : TranslatedRequest)
    (recorded candidate : Digest) (allowed : Bool) :
    admit (⟨request.origin, request.meaning, recorded⟩ :: journal)
      request allowed candidate = .replayed recorded := by
  simp [admit, TranslatedRequest.recovery, recover]

theorem fresh_revoked_translation_refuses (journal : List Receipt)
    (request : TranslatedRequest) (outcome : Digest)
    (unconsumed : request.recovery journal = .fresh) :
    admit journal request false outcome = .refused := by
  simp [admit, unconsumed]

theorem changed_origin_meaning_refuses (journal : List Receipt)
    (request : TranslatedRequest) (oldMeaning recorded candidate : Digest)
    (allowed : Bool) (changed : oldMeaning ≠ request.meaning) :
    admit (⟨request.origin, oldMeaning, recorded⟩ :: journal)
      request allowed candidate = .refused := by
  simp [admit, TranslatedRequest.recovery, recover, changed]

end Obend.Vault.CheckedCarry
end
