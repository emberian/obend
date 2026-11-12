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
   an independent declarative specification (`Spec : W → Prop`), bidirectional refusal consistency
   (`runValid w = true ↔ refuseInvalid w = none`), and soundness (`SilverSound`: every accepted
   Silver run establishes `Spec w`).
3. **Compositional Combinators (`SilverWorkflow.prod`, `SilverWorkflow.toJudge`)**: Composes
   organ-level `SilverWorkflow` instances across pairs `(W₁ × W₂)` and lifts any `SilverWorkflow`
   into an `Obend.Judge W Unit` instance with zero `sorry` and zero custom `axiom`s.
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
@[expose] def OrganId.tag : OrganId → String
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
  deriving @[expose] DecidableEq, Repr

/-- Complete manifest of deferred Golden proof obligations for a Trailblazer organ. -/
structure ObligationManifest where
  organ   : OrganId
  entries : List ObligationMeta
  deriving @[expose] DecidableEq, Repr

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
@[expose] def ObligationManifest.countByOwner (manifest : ObligationManifest) (owner : String) : Nat :=
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
            , theoremId := "regularCoveragePullbackStable"
            , waveOwner := "wave4-polis"
            , externalOracle := "lean-kernel"
            , summary := "Asm(P) regular epimorphism pullback stability" } ] } = true := rfl

/-! ## 2. Executable Silver Workflows & `SilverSound` -/

/-- Executable Trailblazer workflow class pairing a live runner `runValid`, constructive named
    refusal `refuseInvalid`, and declarative domain invariant `Spec`. -/
class SilverWorkflow (W : Type) where
  /-- Independent declarative domain specification established by accepted runs. -/
  Spec : W → Prop
  /-- Live executable Silver check (`true` iff the workflow succeeds end-to-end). -/
  runValid : W → Bool
  /-- Constructive named refusal (`none` when admitted, `some clauseName` when refused). -/
  refuseInvalid : W → Option String
  /-- Exact alignment between boolean acceptance and absence of named refusal. -/
  refuse_iff : ∀ w : W, runValid w = true ↔ refuseInvalid w = none
  /-- `SilverSound` law: every accepted Silver run satisfies `Spec`. -/
  silverSound : ∀ w : W, runValid w = true → Spec w

/-- Standalone propositional statement of the `SilverSound` law for workflow carrier `W`. -/
@[expose] def SilverSound (W : Type) [wf : SilverWorkflow W] : Prop :=
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

/-- Product composition of two `SilverWorkflow`s: runs both checks and reports the first named refusal. -/
@[expose, instance_reducible] def SilverWorkflow.prod (W₁ W₂ : Type)
    [wf₁ : SilverWorkflow W₁] [wf₂ : SilverWorkflow W₂] :
    SilverWorkflow (W₁ × W₂) where
  Spec := fun p => wf₁.Spec p.1 ∧ wf₂.Spec p.2
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

/-- Lift any `SilverWorkflow W` into a grade-monotone `Obend.Judge W Unit`. -/
@[instance_reducible] def SilverWorkflow.toJudge (W : Type) [wf : SilverWorkflow W] : Obend.Judge W Unit where
  Clause := String
  Meaning := fun w _cert => wf.Spec w
  check := fun _grade w _cert =>
    match wf.refuseInvalid w with
    | none => .ok
    | some clause => .refused clause []
  sound := by
    intro _r w _c hOk
    cases hOpt : wf.refuseInvalid w with
    | none =>
      exact wf.silverSound w ((wf.refuse_iff w).mpr hOpt)
    | some clause =>
      rw [hOpt] at hOk
      cases hOk
  refutes := fun _clause => false
  refuted := by
    intro _r _o _c _k _p _hCheck hRef
    cases hRef
  Fragment := fun _w => False
  complete := by
    intro _w hFrag
    cases hFrag
  mono := by
    intro _r _r' _o _c _hle _hDec
    rfl

end Obend.Trailblaze
end
