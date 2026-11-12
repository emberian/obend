module
/-
# Obend.Trailblaze.Obligations — Composable Wave-4 Obligation Metadata & Executable Silver Workflows

Provides the shared Trailblazer spine (`AMBITION.md`, `PROCESS.md`) across all 7 `Obend` organs:
1. **`OrganId`, `ObligationMeta`, `ObligationManifest`**: Machine-readable provenance for every
   deferred Wave-4 Golden proof loop (`organ`, `theoremId`, `waveOwner`, `externalOracle`, `summary`),
   enabling `obb apex` / `obb pipeline` to audit remaining `[...Obligations]` hypotheses until
   every organ retires by promotion (`0` open obligations).
2. **`SilverWorkflow` & `SilverSound`**: Pairs an executable end-to-end workflow runner
   (`runValid : W → Bool`), a constructive named refusal (`refuseInvalid : W → Option String`),
   an independent declarative specification (`Spec : W → Prop`), an explicit completeness domain
   (`CompleteOn : W → Prop`), bidirectional refusal consistency (`runValid w = true ↔ refuseInvalid w = none`),
   soundness (`SilverSound`), and decision completeness (`silverComplete`).
3. **Compositional Combinators (`SilverWorkflow.prod`, `SilverWorkflow.toJudge`)**: Composes
   organ-level `SilverWorkflow` instances across pairs `(W₁ × W₂)` and lifts any `SilverWorkflow`
   into a genuinely refuting `Obend.Judge W Unit` (`refutes := fun _ => true`, non-empty
   `Fragment := fun w => wf.CompleteOn w ∧ wf.Spec w`) with zero `sorry` and zero custom `axiom`s.
-/
public import Obend.Judge.Class

public section
namespace Obend.Trailblaze
set_option autoImplicit false

/-! ## 1. Organ Registry & Wave-4 Obligation Metadata -/

/-- Canonical identifier for each of the 7 `Obend` organs. -/
inductive OrganId where
  | o1VaultLedger
  | o2RepairSpine
  | o3PolisDeos
  | o4DualCrypto
  | o5ZkStripe
  | o6ClusterGov
  | o7LeanFpga
  deriving @[expose] DecidableEq, Repr

/-- Stable machine-readable tag for an `OrganId`. -/
def OrganId.tag : OrganId → String
  | .o1VaultLedger => "O1:VaultLedger"
  | .o2RepairSpine => "O2:RepairSpine"
  | .o3PolisDeos   => "O3:PolisDeos"
  | .o4DualCrypto  => "O4:DualCrypto"
  | .o5ZkStripe    => "O5:ZkStripe"
  | .o6ClusterGov  => "O6:ClusterGov"
  | .o7LeanFpga    => "O7:LeanFpga"

/-- Metadata descriptor for a single Wave-4 proof obligation field in `class <Organ>Obligations : Prop`. -/
structure ObligationMeta where
  organ          : OrganId
  theoremId      : String
  waveOwner      : String
  externalOracle : String
  summary        : String
  deriving DecidableEq, Repr

/-- Complete manifest of deferred Golden proof obligations for a Trailblazer organ. -/
structure ObligationManifest where
  organ   : OrganId
  entries : List ObligationMeta
  deriving DecidableEq, Repr

/-- Single-entry well-formedness check: belongs to `targetOrgan` and has non-empty identifiers. -/
@[expose] def checkEntryForOrgan (targetOrgan : OrganId) (m : ObligationMeta) : Bool :=
  (m.organ == targetOrgan) &&
  !m.theoremId.isEmpty &&
  !m.waveOwner.isEmpty &&
  !m.externalOracle.isEmpty

/-- Manifest audit check: non-empty list of entries all belonging to `manifest.organ` with non-empty IDs. -/
@[expose] def checkManifestWellFormed (manifest : ObligationManifest) : Bool :=
  !manifest.entries.isEmpty &&
  manifest.entries.all (checkEntryForOrgan manifest.organ)

/-- Count obligations assigned to a specific Wave-4 swarm lane/owner. -/
def ObligationManifest.countByOwner (manifest : ObligationManifest) (owner : String) : Nat :=
  (manifest.entries.filter (fun e => e.waveOwner == owner)).length

/-- Soundness of `checkManifestWellFormed`: every entry in an audited manifest matches `manifest.organ`
    and carries a non-empty `theoremId`, `waveOwner`, and `externalOracle`. -/
theorem checkManifestWellFormed_sound
    (manifest : ObligationManifest)
    (m : ObligationMeta)
    (hWf : checkManifestWellFormed manifest = true)
    (hMem : m ∈ manifest.entries) :
    m.organ = manifest.organ ∧
    m.theoremId.isEmpty = false ∧
    m.waveOwner.isEmpty = false ∧
    m.externalOracle.isEmpty = false := by
  unfold checkManifestWellFormed at hWf
  simp only [Bool.and_eq_true, List.all_eq_true] at hWf
  have hEntry := hWf.2 m hMem
  unfold checkEntryForOrgan at hEntry
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hEntry
  exact ⟨hEntry.1.1.1, hEntry.1.1.2, hEntry.1.2, hEntry.2⟩

/-- Witness confirming `checkManifestWellFormed` is inhabited on concrete metadata. -/
example :
    checkManifestWellFormed
      { organ := .o3PolisDeos
      , entries :=
          [ { organ := .o3PolisDeos
            , theoremId := "sel4PhysicalDmaBusNonInterference"
            , waveOwner := "wave4-firmament-sel4"
            , externalOracle := "verify_foc_hil.sh"
            , summary := "seL4 SMMU physical DMA bus non-interference on FocHil watchdog MMIO" } ] } = true := rfl

/-! ## 2. Executable Silver Workflows & `SilverSound` -/

/-- Executable Trailblazer workflow class pairing a live runner `runValid`, constructive named
    refusal `refuseInvalid`, declarative domain invariant `Spec`, and completeness domain `CompleteOn`. -/
class SilverWorkflow (W : Type) where
  /-- Independent declarative domain specification established by accepted runs. -/
  Spec : W → Prop
  /-- Admissible workflow domain on which `runValid` decides `Spec` completely. -/
  CompleteOn : W → Prop
  /-- Live executable Silver check (`true` iff the workflow succeeds end-to-end). -/
  runValid : W → Bool
  /-- Constructive named refusal (`none` when admitted, `some clauseName` when refused). -/
  refuseInvalid : W → Option String
  /-- Exact alignment between boolean acceptance and absence of named refusal. -/
  refuse_iff : ∀ w : W, runValid w = true ↔ refuseInvalid w = none
  /-- `SilverSound` law: every accepted Silver run satisfies `Spec`. -/
  silverSound : ∀ w : W, runValid w = true → Spec w
  /-- Every accepted Silver run belongs to the completeness domain `CompleteOn`. -/
  silverCompleteDomain : ∀ w : W, runValid w = true → CompleteOn w
  /-- Completeness law: every `CompleteOn` workflow input satisfying `Spec` is accepted by `runValid`. -/
  silverComplete : ∀ w : W, CompleteOn w → Spec w → runValid w = true

/-- Standalone propositional statement of the `SilverSound` law for workflow carrier `W`. -/
def SilverSound (W : Type) [wf : SilverWorkflow W] : Prop :=
  ∀ w : W, wf.runValid w = true → wf.Spec w

/-- Every `SilverWorkflow` instance constructively inhabits `SilverSound`. -/
theorem silverWorkflow_satisfies_silverSound
    (W : Type) [wf : SilverWorkflow W] (w : W)
    (hRun : wf.runValid w = true) :
    wf.Spec w :=
  wf.silverSound w hRun

/-- Every admitted `SilverWorkflow` input produces `none` from `refuseInvalid`. -/
theorem SilverWorkflow.admitted_no_refusal
    {W : Type} [wf : SilverWorkflow W] (w : W)
    (hRun : wf.runValid w = true) :
    wf.refuseInvalid w = none :=
  (wf.refuse_iff w).mp hRun

/-- Every rejected `SilverWorkflow` input (`runValid w = false`) produces an explicit named refusal string. -/
theorem SilverWorkflow.rejected_names_clause
    {W : Type} [wf : SilverWorkflow W] (w : W)
    (hRej : wf.runValid w = false) :
    ∃ reason : String, wf.refuseInvalid w = some reason := by
  cases hOpt : wf.refuseInvalid w with
  | none =>
    have hValid : wf.runValid w = true := (wf.refuse_iff w).mpr hOpt
    rw [hValid] at hRej
    cases hRej
  | some reason =>
    exact ⟨reason, rfl⟩

/-- Product composition of two `SilverWorkflow`s: runs both checks, preserves completeness domains,
    and reports the first named refusal. -/
@[expose, instance_reducible] def SilverWorkflow.prod (W₁ W₂ : Type)
    [wf₁ : SilverWorkflow W₁] [wf₂ : SilverWorkflow W₂] :
    SilverWorkflow (W₁ × W₂) where
  Spec := fun p => wf₁.Spec p.1 ∧ wf₂.Spec p.2
  CompleteOn := fun p => wf₁.CompleteOn p.1 ∧ wf₂.CompleteOn p.2
  runValid := fun p => wf₁.runValid p.1 && wf₂.runValid p.2
  refuseInvalid := fun p =>
    match wf₁.refuseInvalid p.1 with
    | some r => some r
    | none => wf₂.refuseInvalid p.2
  refuse_iff := by
    intro ⟨w₁, w₂⟩
    simp only [Bool.and_eq_true]
    constructor
    · rintro ⟨h₁, h₂⟩
      rw [(wf₁.refuse_iff w₁).mp h₁]
      exact (wf₂.refuse_iff w₂).mp h₂
    · intro hNone
      cases hOpt₁ : wf₁.refuseInvalid w₁ with
      | some r =>
        rw [hOpt₁] at hNone
        cases hNone
      | none =>
        rw [hOpt₁] at hNone
        exact ⟨(wf₁.refuse_iff w₁).mpr hOpt₁, (wf₂.refuse_iff w₂).mpr hNone⟩
  silverSound := by
    intro ⟨w₁, w₂⟩ hBoth
    simp only [Bool.and_eq_true] at hBoth
    exact ⟨wf₁.silverSound w₁ hBoth.1, wf₂.silverSound w₂ hBoth.2⟩
  silverCompleteDomain := by
    intro ⟨w₁, w₂⟩ hBoth
    simp only [Bool.and_eq_true] at hBoth
    exact ⟨wf₁.silverCompleteDomain w₁ hBoth.1, wf₂.silverCompleteDomain w₂ hBoth.2⟩
  silverComplete := by
    intro ⟨w₁, w₂⟩ ⟨hDom₁, hDom₂⟩ ⟨hSpec₁, hSpec₂⟩
    simp only [Bool.and_eq_true]
    exact ⟨wf₁.silverComplete w₁ hDom₁ hSpec₁, wf₂.silverComplete w₂ hDom₂ hSpec₂⟩

/-- Lift any `SilverWorkflow W` into a grade-monotone, genuinely refuting `Obend.Judge W Unit`
    whose `Fragment` is inhabited by every admitted workflow turn. -/
@[instance_reducible] def SilverWorkflow.toJudge (W : Type) [wf : SilverWorkflow W] : Obend.Judge W Unit where
  Clause := String
  Meaning := fun w _cert => wf.CompleteOn w ∧ wf.Spec w
  check := fun _grade w _cert =>
    match wf.refuseInvalid w with
    | none => .ok
    | some clause => .refused clause []
  sound := by
    intro _r w _c hOk
    cases hOpt : wf.refuseInvalid w with
    | none =>
      have hRun : wf.runValid w = true := (wf.refuse_iff w).mpr hOpt
      exact ⟨wf.silverCompleteDomain w hRun, wf.silverSound w hRun⟩
    | some clause =>
      rw [hOpt] at hOk
      cases hOk
  refutes := fun _clause => true
  refuted := by
    intro _r w _c clause _p hCheck _hRef _c' ⟨hDom, hSpec⟩
    have hRun : wf.runValid w = true := wf.silverComplete w hDom hSpec
    have hNone : wf.refuseInvalid w = none := (wf.refuse_iff w).mp hRun
    rw [hNone] at hCheck
    cases hCheck
  Fragment := fun w => wf.CompleteOn w ∧ wf.Spec w
  complete := by
    intro w ⟨hDom, hSpec⟩ _hEx
    have hRun : wf.runValid w = true := wf.silverComplete w hDom hSpec
    have hNone : wf.refuseInvalid w = none := (wf.refuse_iff w).mp hRun
    refine ⟨(), 0, ?_⟩
    rw [hNone]
  mono := by
    intro _r _r' _o _c _hle _hDec
    rfl

/-- Every admitted `SilverWorkflow` input inhabits `(SilverWorkflow.toJudge W).Fragment`. -/
theorem SilverWorkflow.admitted_in_judge_fragment
    {W : Type} [wf : SilverWorkflow W] (w : W)
    (hRun : wf.runValid w = true) :
    (SilverWorkflow.toJudge W).Fragment w :=
  ⟨wf.silverCompleteDomain w hRun, wf.silverSound w hRun⟩

/-- Every rejected `SilverWorkflow` input inside `CompleteOn` refutes `Spec`. -/
theorem SilverWorkflow.rejected_refutes_spec
    {W : Type} [wf : SilverWorkflow W] (w : W)
    (hRej : wf.runValid w = false)
    (hDom : wf.CompleteOn w) :
    ¬ wf.Spec w := by
  intro hSpec
  have hRun : wf.runValid w = true := wf.silverComplete w hDom hSpec
  rw [hRun] at hRej
  cases hRej

end Obend.Trailblaze
end
