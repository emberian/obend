module
/-
# Obend.Vault.SwarmLedgerSeams — Typed Link Roles, `Reasons`-Routed Telemetry, `_kind` Succession & Complete `LawDial` Repair

Closes Chasms 9 & 10 (`VAULT.md:95-109` & `THESIS.md:56-57`):

1. **Typed Link Roles (`FINDINGS 6, 8`)**:
   Separates `LinkRole` (`box`, `brief`, `parent`, `listed`, `custom`) on forward (`linkedInRole`)
   and backward (`linkedByInRole`) page link views so modifying a `brief` link never perturbs laws
   quantified over `linked[box]`, while `DEV`'s `linked_by[merged_lane]` catches unlisted merged lanes.
2. **`Reasons`-Routed Floor Breaches (`FINDINGS 14, 20`)**:
   Routes environmental telemetry (`box_unreachable`, tally floor breaches) into `Obend.Reasons.State`
   as observations (`ingestTelemetryObservation`) instead of refusing reality at the Vault gate,
   immediately flipping `dispatch_to(B)` from `.supported` to `.unsupported` with `whyNot` naming
   `box_unreachable(B)`.
3. **Vault `_kind` Law Succession as a `Genealogy.Habitat` (`FINDINGS 19`, `PROCESS.md` `Reground` `G4`)**:
   Instantiates `vaultDoctrineHabitat : Genealogy.Habitat` over monotone doctrine floors (`FloorSpec`),
   admitting tightening/new floors in `Reground` while refusing any succession that drops or loosens
   an existing floor.
4. **Complete Multi-Field Constructive Repair via `LawDial` (`THESIS.md:56-57`)**:
   Bridges `Obend.Spec.LawDial.solveLawWitness` (`solveLawWitness_sound`) with Kleene least-fixpoint
   difference-constraint relaxation (`synthesizePassingDelta`), proving both **soundness** (admitted by
   `Vault.Law.judge` and `Obend.Law.Admits`) and **completeness** (every satisfiable bounded
   difference-constraint system yields `.some delta`, and `.none` certifies unsatisfiability).
-/
public import Obend.Vault.Law
public import Obend.Reasons
public import Obend.Judge.Genealogy
public import Obend.Spec.LawDial
public import Obend.Tactic.Tooth

public section

namespace Obend.Vault.SwarmLedgerSeams

set_option autoImplicit false

open Obend.Core.Term (Term Value Step Steps Evaluates)
open Obend.Core.Ty (Ty)
open Obend.Core.Data (Data)
open Obend.Spec.Law (LawRef LawExpr Facts scalarOf firstScalarField fieldOf firstField fieldLabel)
open Obend.Judge

/-! ## 1. Typed Link Roles (`FINDINGS 6, 8`) -/

/-- Typed link edge roles separating orthogonal swarm graph seams (`linked[role]` / `linked_by[role]`). -/
inductive LinkRole where
  | box
  | brief
  | parent
  | listed
  | custom (tag : String)
  deriving @[expose] DecidableEq, Repr

/-- Standard custom role for merged lanes pointing back to `DEV`. -/
abbrev LinkRole.mergedLane : LinkRole := .custom "merged_lane"

/-- A directed link from a Vault page annotated with its `LinkRole`. -/
structure TypedLink where
  role : LinkRole
  target : String
  deriving @[expose] DecidableEq, Repr

/-- A Vault page carrying scalar/label state `Data` and role-typed outgoing links. -/
structure RolePage where
  name : String
  state : Data
  links : List TypedLink
  deriving Repr

/-- Target page names of outgoing links matching `role`. -/
@[expose] def targetsInRole (role : LinkRole) (links : List TypedLink) : List String :=
  (links.filter (·.role == role)).map (·.target)

/-- Lookup a `RolePage` by name in a store snapshot. -/
@[expose] def findRolePage (pages : List RolePage) (name : String) : Option RolePage :=
  pages.find? (·.name == name)

/-- Forward role-filtered link view (`linked[role]`): states of resolved target pages in `role`. -/
@[expose] def linkedInRole (pages : List RolePage) (page : RolePage) (role : LinkRole) : List Data :=
  (targetsInRole role page.links).filterMap fun tgt => (findRolePage pages tgt).map (·.state)

/-- Backward role-filtered link view (`linked_by[role]`): pages in `pages` linking to `hubName` in `role`. -/
@[expose] def linkedByInRole (pages : List RolePage) (hubName : String) (role : LinkRole) : List RolePage :=
  pages.filter fun src => (targetsInRole role src.links).contains hubName

/-- Replace all outgoing links of `page` in `editRole` with `newTargets`, leaving all other roles intact. -/
@[expose] def editRoleLinks (page : RolePage) (editRole : LinkRole) (newTargets : List String) : RolePage :=
  { page with links := page.links.filter (·.role != editRole) ++ newTargets.map (TypedLink.mk editRole) }

/-- Evaluate a Vault `LawExpr` over every page state in `linked[role]`. -/
@[expose] def evalRoleLinkLaw (facts : Facts) (law : LawExpr) (pages : List RolePage)
    (page : RolePage) (role : LinkRole) : Bool :=
  (linkedInRole pages page role).all fun st => law.denote facts (some st) st

theorem filter_edit_disjoint_links {lawRole editRole : LinkRole} (hne : editRole ≠ lawRole) :
    ∀ (links : List TypedLink),
      (links.filter (·.role != editRole)).filter (·.role == lawRole) = links.filter (·.role == lawRole)
  | [] => rfl
  | l :: ls => by
    by_cases hl : l.role = lawRole
    · have hne' : (l.role != editRole) = true := by
        rw [hl]; exact bne_iff_ne.2 (Ne.symm hne)
      have heq : (l.role == lawRole) = true := beq_iff_eq.2 hl
      simp [hne', heq, filter_edit_disjoint_links hne ls]
    · have heq : (l.role == lawRole) = false := beq_false_of_ne hl
      by_cases he : (l.role != editRole) = true <;>
        simp [he, heq, filter_edit_disjoint_links hne ls]

theorem filter_mapped_disjoint_links {lawRole editRole : LinkRole} (hne : editRole ≠ lawRole) :
    ∀ (targets : List String),
      ((targets.map (TypedLink.mk editRole)).filter (·.role == lawRole)) = []
  | [] => rfl
  | t :: ts => by
    have heq : (editRole == lawRole) = false := beq_false_of_ne hne
    simp [heq, filter_mapped_disjoint_links hne ts]

/-- Editing links in `editRole` leaves `targetsInRole lawRole` identically unchanged whenever `editRole ≠ lawRole`. -/
theorem targetsInRole_edit_disjoint (page : RolePage) {editRole lawRole : LinkRole}
    (hne : editRole ≠ lawRole) (newTargets : List String) :
    targetsInRole lawRole (editRoleLinks page editRole newTargets).links =
      targetsInRole lawRole page.links := by
  simp only [targetsInRole, editRoleLinks, List.filter_append,
    filter_edit_disjoint_links hne, filter_mapped_disjoint_links hne, List.append_nil]

/-- **Role Isolation (`FINDINGS 6, 8`)**: Adding or modifying links in `editRole` (such as `.brief`)
    never alters `linkedInRole` or any law quantified solely over `linked[lawRole]` (such as `.box`)
    whenever `editRole ≠ lawRole`. -/
theorem write_in_disjoint_role_preserves_role_law
    (facts : Facts) (law : LawExpr) (pages : List RolePage) (page : RolePage)
    {editRole lawRole : LinkRole} (hne : editRole ≠ lawRole) (newTargets : List String) :
    linkedInRole pages (editRoleLinks page editRole newTargets) lawRole =
      linkedInRole pages page lawRole ∧
    evalRoleLinkLaw facts law pages (editRoleLinks page editRole newTargets) lawRole =
      evalRoleLinkLaw facts law pages page lawRole := by
  have hlink : linkedInRole pages (editRoleLinks page editRole newTargets) lawRole =
      linkedInRole pages page lawRole := by
    simp only [linkedInRole, targetsInRole_edit_disjoint page hne newTargets]
  exact ⟨hlink, by simp only [evalRoleLinkLaw, hlink]⟩

/-- Specialized corollary for `FINDINGS 6`: editing `brief` links never alters `linked[box]` laws. -/
theorem brief_write_preserves_linked_box_law
    (facts : Facts) (law : LawExpr) (pages : List RolePage) (page : RolePage) (newBriefs : List String) :
    evalRoleLinkLaw facts law pages (editRoleLinks page .brief newBriefs) .box =
      evalRoleLinkLaw facts law pages page .box :=
  (write_in_disjoint_role_preserves_role_law facts law pages page (by decide) newBriefs).2

/-- Project a referring page's state with an explicit `listed : 0 | 1` backlink indicator. -/
@[expose] def stateWithListedFlag (listed : Bool) : Data → Data
  | .record fs =>
    .record (("listed", .natural (if listed then 1 else 0)) :: fs.filter (·.1 != "listed"))
  | other => other

/-- `DEV`'s backlink audit law over `linked_by[merged_lane]`: every merged lane (`new.merged == 1`)
    must be listed back by `DEV` (`new.listed == 1`). -/
@[expose] def devMergedLaneBacklinkLaw : LawExpr :=
  .implies (.eqC (.field "merged") 1) (.eqC (.field "listed") 1)

/-- Evaluate a backlink law on `hub` across all pages in `linked_by[inRole]`, binding `listed`
    according to whether `hub` links back to the referrer in `listRole`. -/
@[expose] def checkBacklinkRoleLaw (facts : Facts) (law : LawExpr) (pages : List RolePage)
    (hub : RolePage) (inRole listRole : LinkRole) : Bool :=
  (linkedByInRole pages hub.name inRole).all fun refPage =>
    let st := stateWithListedFlag ((targetsInRole listRole hub.links).contains refPage.name) refPage.state
    law.denote facts (some st) st

theorem firstScalarField_filter_not_listed {f : String} (hne : f ≠ "listed") :
    ∀ (fs : List (String × Data)),
      firstScalarField f (fs.filter (·.1 != "listed")) = firstScalarField f fs
  | [] => rfl
  | (k, v) :: rest => by
    by_cases hk : k = "listed"
    · subst hk
      have hne' : ("listed" = f) ↔ False := ⟨fun h => hne h.symm, False.elim⟩
      simp [firstScalarField, hne', firstScalarField_filter_not_listed hne rest]
    · have hkb : (k != "listed") = true := bne_iff_ne.2 hk
      simp only [List.filter_cons, hkb, ite_true, firstScalarField]
      rw [firstScalarField_filter_not_listed hne rest]

theorem fieldOf_stateWithListedFlag_other {f : String} (hne : f ≠ "listed") (b : Bool)
    {fs : List (String × Data)} :
    fieldOf f (stateWithListedFlag b (.record fs)) = fieldOf f (.record fs) := by
  have h1 : ("listed" = f) ↔ False := ⟨fun h => hne h.symm, False.elim⟩
  simp [stateWithListedFlag, fieldOf, firstScalarField, h1, firstScalarField_filter_not_listed hne fs]

/-- **Backlink Detection (`FINDINGS 8`)**: If any page `lane ∈ pages` links to `dev` in
    `LinkRole.mergedLane` with `merged = 1` on its record state, and `dev` fails to list `lane.name`
    in `LinkRole.listed`, `checkBacklinkRoleLaw` on `devMergedLaneBacklinkLaw` returns `false`. -/
theorem dev_backlink_detects_unlisted_merged_lane
    (facts : Facts) (pages : List RolePage) (dev lane : RolePage) (fs : List (String × Data))
    (hlane : lane ∈ pages)
    (hstate : lane.state = .record fs)
    (hmerged : fieldOf "merged" lane.state = some 1)
    (href : dev.name ∈ targetsInRole .mergedLane lane.links)
    (hunlisted : lane.name ∉ targetsInRole .listed dev.links) :
    checkBacklinkRoleLaw facts devMergedLaneBacklinkLaw pages dev .mergedLane .listed = false := by
  unfold checkBacklinkRoleLaw
  rw [Bool.eq_false_iff]
  intro hall
  have hmemBack : lane ∈ linkedByInRole pages dev.name .mergedLane := by
    simp [linkedByInRole, hlane, href]
  have hden := List.all_eq_true.1 hall lane hmemBack
  have hcont : (targetsInRole .listed dev.links).contains lane.name = false := by
    cases hc : (targetsInRole .listed dev.links).contains lane.name
    · rfl
    · exact absurd (List.contains_iff_mem.1 hc) hunlisted
  have hmField :
      fieldOf "merged" (stateWithListedFlag false lane.state) = some 1 := by
    rw [hstate] at hmerged ⊢
    rw [fieldOf_stateWithListedFlag_other (by decide) false]
    exact hmerged
  have hlField :
      fieldOf "listed" (stateWithListedFlag false lane.state) = some 0 := by
    rw [hstate]
    rfl
  simp only [hcont] at hden
  simp [devMergedLaneBacklinkLaw, LawExpr.denote, LawRef.read, hmField, hlField] at hden

/-! ## 2. `Reasons`-Routed Floor Breaches (`FINDINGS 14, 20`) -/

/-- Telemetry events emitted by remote build boxes or historical swarm audits. -/
inductive TelemetryEvent where
  | boxUnreachable (box : String) (detail : String) (source : String)
  | tallyBreach (metric : String) (observed : Nat) (floor : Nat) (source : String)
  deriving @[expose] DecidableEq, Repr

/-- Atom naming that `box` is registered in the build fleet. -/
@[expose] def boxRegisteredAtom (box : String) : String := "box_registered(" ++ box ++ ")"

/-- Defeater atom naming that `box` is currently unreachable. -/
@[expose] def boxUnreachableAtom (box : String) : String := "box_unreachable(" ++ box ++ ")"

/-- Derived conclusion that `box` is usable. -/
@[expose] def boxUsableAtom (box : String) : String := "box_usable(" ++ box ++ ")"

/-- Derived action-justification conclusion that lanes may dispatch to `box`. -/
@[expose] def dispatchToAtom (box : String) : String := "dispatch_to(" ++ box ++ ")"

/-- Atom naming an observed floor/tally breach on `metric`. -/
@[expose] def tallyBreachAtom (metric : String) : String := "tally_breach(" ++ metric ++ ")"

/-- Convert a `TelemetryEvent` into a non-refusable `Reasons.Observation`. -/
@[expose] def TelemetryEvent.toObservation : TelemetryEvent → Reasons.Observation
  | .boxUnreachable box detail src =>
    { name := boxUnreachableAtom box, text := detail, source := src }
  | .tallyBreach metric obs flr src =>
    { name := tallyBreachAtom metric, text := toString obs ++ " > " ++ toString flr, source := src }

/-- Defeasible explanation `box_usable(B) ← box_registered(B), not box_unreachable(B)`. -/
@[expose] def boxUsableRule (box : String) : Reasons.Rule :=
  { name := "usable_" ++ box
    concl := boxUsableAtom box
    pos := [boxRegisteredAtom box]
    neg := [boxUnreachableAtom box] }

/-- Defeasible dispatch rule `dispatch_to(B) ← box_registered(B), not box_unreachable(B)`. -/
@[expose] def boxDispatchRule (box : String) : Reasons.Rule :=
  { name := "dispatch_" ++ box
    concl := dispatchToAtom box
    pos := [boxRegisteredAtom box]
    neg := [boxUnreachableAtom box] }

/-- Initial `Reasons.Base` for a registered build box `box` with proposed dispatch action. -/
@[expose] def mkBoxDispatchBase (box : String) : Reasons.Base :=
  { observations := [{ name := boxRegisteredAtom box, text := "registered", source := "fleet" }]
    assumptions := []
    withdrawn := []
    explanations := [boxUsableRule box, boxDispatchRule box]
    defeaters := []
    actions := [{ name := "run_lane_" ++ box, because := dispatchToAtom box }] }

/-- Initial `Reasons.State` for `box` with consistent kept well-founded judgment. -/
@[expose] def mkBoxDispatchState (box : String) : Reasons.State :=
  { base := mkBoxDispatchBase box, kept := Reasons.judge (mkBoxDispatchBase box) }

/-- Ingest a `TelemetryEvent` into `Reasons.State` as an observation (idempotent if already recorded). -/
@[expose] def ingestTelemetryObservation (s : Reasons.State) (ev : TelemetryEvent) :
    Except String Reasons.State :=
  if s.base.observations.any (·.name == ev.toObservation.name) then .ok s
  else s.step (.observe ev.toObservation)

theorem boxRegistered_ne_unreachable (box : String) :
    boxRegisteredAtom box ≠ boxUnreachableAtom box := by
  intro h
  have hl := congrArg String.toList h
  simp [boxRegisteredAtom, boxUnreachableAtom] at hl

theorem boxRegistered_ne_dispatch (box : String) :
    boxRegisteredAtom box ≠ dispatchToAtom box := by
  intro h
  have hl := congrArg String.toList h
  simp [boxRegisteredAtom, dispatchToAtom] at hl

theorem boxUnreachable_ne_dispatch (box : String) :
    boxUnreachableAtom box ≠ dispatchToAtom box := by
  intro h
  have hl := congrArg String.toList h
  simp [boxUnreachableAtom, dispatchToAtom] at hl

theorem boxRegistered_ne_usable (box : String) :
    boxRegisteredAtom box ≠ boxUsableAtom box := by
  intro h
  have hl := congrArg String.toList h
  simp [boxRegisteredAtom, boxUsableAtom] at hl

theorem boxUnreachable_ne_usable (box : String) :
    boxUnreachableAtom box ≠ boxUsableAtom box := by
  intro h
  have hl := congrArg String.toList h
  simp [boxUnreachableAtom, boxUsableAtom] at hl

theorem boxUsable_ne_dispatch (box : String) :
    boxUsableAtom box ≠ dispatchToAtom box := by
  intro h
  have hl := congrArg String.toList h
  simp [boxUsableAtom, dispatchToAtom] at hl

theorem mkBoxDispatchState_consistent (box : String) : (mkBoxDispatchState box).Consistent :=
  ⟨Reasons.Same.refl _, Reasons.Same.refl _⟩

theorem mkBoxDispatchState_initial_supported (box : String) :
    (mkBoxDispatchState box).status (dispatchToAtom box) = .supported ∧
    (mkBoxDispatchState box).status (boxUsableAtom box) = .supported := by
  have hcons := mkBoxDispatchState_consistent box
  rw [Reasons.State.status_eq hcons, Reasons.State.status_eq hcons]
  have hreg : Reasons.status (mkBoxDispatchBase box) (boxRegisteredAtom box) = .supported := by
    rw [Reasons.supported_iff]
    exact Or.inl (by simp [Reasons.Base.program, mkBoxDispatchBase])
  have hunr : Reasons.status (mkBoxDispatchBase box) (boxUnreachableAtom box) = .unsupported := by
    rw [Reasons.status_unsupported_iff, Reasons.judge]
    intro hmem
    rcases Reasons.mem_gamma.1 hmem with hfact | ⟨r, hr, hconcl, _, _⟩
    · simp [Reasons.Base.program, mkBoxDispatchBase, Reasons.Base.held] at hfact
      exact boxRegistered_ne_unreachable box hfact.symm
    · simp [Reasons.Base.program, mkBoxDispatchBase, Reasons.Base.rule, boxUsableRule, boxDispatchRule] at hr
      rcases hr with rfl | rfl
      · exact boxUnreachable_ne_usable box hconcl.symm
      · exact boxUnreachable_ne_dispatch box hconcl.symm
  refine ⟨?_, ?_⟩
  · rw [Reasons.supported_iff]
    refine Or.inr ⟨boxDispatchRule box, ?_, rfl, ?_, ?_⟩
    · simp [Reasons.Base.program, mkBoxDispatchState, mkBoxDispatchBase, Reasons.Base.rule, boxDispatchRule]
    · intro p hp
      simp [boxDispatchRule] at hp
      subst hp; exact hreg
    · intro d hd
      simp [boxDispatchRule] at hd
      subst hd; exact hunr
  · rw [Reasons.supported_iff]
    refine Or.inr ⟨boxUsableRule box, ?_, rfl, ?_, ?_⟩
    · simp [Reasons.Base.program, mkBoxDispatchState, mkBoxDispatchBase, Reasons.Base.rule, boxUsableRule]
    · intro p hp
      simp [boxUsableRule] at hp
      subst hp; exact hreg
    · intro d hd
      simp [boxUsableRule] at hd
      subst hd; exact hunr

/-- **`Reasons`-Routed Floor Breaches (`FINDINGS 14, 20`)**:
    For every box `box`, prior to failure `dispatch_to(box)` is `.supported`; recording
    `TelemetryEvent.boxUnreachable box detail source` via `ingestTelemetryObservation` succeeds
    unconditionally (never refusing the telemetry fact!), immediately flips both `box_usable(box)`
    and `dispatch_to(box)` to `.unsupported`, and `Reasons.whyNot` explicitly names
    `box_unreachable(box)` as the supported defeater. -/
theorem telemetry_defeats_lane_dispatch_without_refusing_fact
    (box detail source : String) :
    (mkBoxDispatchState box).status (dispatchToAtom box) = .supported ∧
    ∃ s₁,
      ingestTelemetryObservation (mkBoxDispatchState box) (.boxUnreachable box detail source) = .ok s₁ ∧
      s₁.status (boxUsableAtom box) = .unsupported ∧
      s₁.status (dispatchToAtom box) = .unsupported ∧
      Reasons.whyNot s₁ (dispatchToAtom box) =
        ["dispatch_" ++ box ++ " is defeated by " ++ boxUnreachableAtom box ++ " (supported)"] := by
  refine ⟨(mkBoxDispatchState_initial_supported box).1, ?_⟩
  let obs : Reasons.Observation := { name := boxUnreachableAtom box, text := detail, source := source }
  have hneReg : (boxRegisteredAtom box == boxUnreachableAtom box) = false :=
    beq_false_of_ne (boxRegistered_ne_unreachable box)
  let b₁ : Reasons.Base :=
    { mkBoxDispatchBase box with observations := (mkBoxDispatchBase box).observations ++ [obs] }
  have hbstep : (mkBoxDispatchBase box).step (.observe obs) = .ok b₁ := by
    simp [Reasons.Base.step, mkBoxDispatchBase, obs, hneReg, b₁]
  let s₁ : Reasons.State :=
    { base := b₁, kept := (mkBoxDispatchState box).update (.observe obs) b₁ }
  have hsstep : (mkBoxDispatchState box).step (.observe obs) = .ok s₁ := by
    have hbase : (mkBoxDispatchState box).base = mkBoxDispatchBase box := rfl
    unfold Reasons.State.step
    rw [hbase, hbstep]
  have hingest :
      ingestTelemetryObservation (mkBoxDispatchState box) (.boxUnreachable box detail source) = .ok s₁ := by
    unfold ingestTelemetryObservation
    have hto : (TelemetryEvent.boxUnreachable box detail source).toObservation = obs := rfl
    have hany : ((mkBoxDispatchState box).base.observations.any (·.name == obs.name)) = false := by
      simp [mkBoxDispatchState, mkBoxDispatchBase, obs, hneReg]
    rw [hto, hany]
    exact hsstep
  have hcons₁ : s₁.Consistent :=
    Reasons.step_consistent (mkBoxDispatchState_consistent box) hsstep
  have hstEq : ∀ x, s₁.status x = Reasons.status b₁ x := Reasons.State.status_eq hcons₁
  have hreg₁ : Reasons.status b₁ (boxRegisteredAtom box) = .supported := by
    rw [Reasons.supported_iff]
    exact Or.inl (by simp [Reasons.Base.program, b₁, mkBoxDispatchBase])
  have hunr₁ : Reasons.status b₁ (boxUnreachableAtom box) = .supported := by
    rw [Reasons.supported_iff]
    exact Or.inl (by simp [Reasons.Base.program, b₁, mkBoxDispatchBase, obs])
  have hunrMem : boxUnreachableAtom box ∈ (Reasons.judge b₁).1 :=
    (Reasons.status_supported_iff b₁ _).1 hunr₁
  have husable₁ : Reasons.status b₁ (boxUsableAtom box) = .unsupported := by
    rw [Reasons.status_unsupported_iff, Reasons.judge]
    intro hmem
    rcases Reasons.mem_gamma.1 hmem with hfact | ⟨r, hr, hconcl, _, hneg⟩
    · simp [Reasons.Base.program, b₁, mkBoxDispatchBase, Reasons.Base.held, obs] at hfact
      rcases hfact with h1 | h2
      · exact boxRegistered_ne_usable box h1.symm
      · exact boxUnreachable_ne_usable box h2.symm
    · simp [Reasons.Base.program, b₁, mkBoxDispatchBase, Reasons.Base.rule,
        boxUsableRule, boxDispatchRule] at hr
      rcases hr with rfl | rfl
      · exact hneg (boxUnreachableAtom box) (by simp) hunrMem
      · dsimp only at hconcl
        exact boxUsable_ne_dispatch box hconcl.symm
  have hdisp₁ : Reasons.status b₁ (dispatchToAtom box) = .unsupported := by
    rw [Reasons.status_unsupported_iff, Reasons.judge]
    intro hmem
    rcases Reasons.mem_gamma.1 hmem with hfact | ⟨r, hr, hconcl, _, hneg⟩
    · simp [Reasons.Base.program, b₁, mkBoxDispatchBase, Reasons.Base.held, obs] at hfact
      rcases hfact with h1 | h2
      · exact boxRegistered_ne_dispatch box h1.symm
      · exact boxUnreachable_ne_dispatch box h2.symm
    · simp [Reasons.Base.program, b₁, mkBoxDispatchBase, Reasons.Base.rule,
        boxUsableRule, boxDispatchRule] at hr
      rcases hr with rfl | rfl
      · dsimp only at hconcl
        exact boxUsable_ne_dispatch box hconcl
      · exact hneg (boxUnreachableAtom box) (by simp) hunrMem
  have hs1Reg : s₁.status (boxRegisteredAtom box) = .supported := by rw [hstEq]; exact hreg₁
  have hs1Unr : s₁.status (boxUnreachableAtom box) = .supported := by rw [hstEq]; exact hunr₁
  have hs1Use : s₁.status (boxUsableAtom box) = .unsupported := by rw [hstEq]; exact husable₁
  have hs1Disp : s₁.status (dispatchToAtom box) = .unsupported := by rw [hstEq]; exact hdisp₁
  have hrulesFor : b₁.rulesFor (dispatchToAtom box) = [boxDispatchRule box] := by
    have hneUD : (boxUsableAtom box == dispatchToAtom box) = false :=
      beq_false_of_ne (boxUsable_ne_dispatch box)
    simp [Reasons.Base.rulesFor, Reasons.Base.program, b₁, mkBoxDispatchBase,
      Reasons.Base.rule, boxUsableRule, boxDispatchRule, hneUD]
  have hwhy :
      Reasons.whyNot s₁ (dispatchToAtom box) =
        ["dispatch_" ++ box ++ " is defeated by " ++ boxUnreachableAtom box ++ " (supported)"] := by
    unfold Reasons.whyNot
    have hw : (b₁.withdrawn.contains (dispatchToAtom box) && !b₁.held.contains (dispatchToAtom box)) = false := by
      simp [b₁, mkBoxDispatchBase]
    change (if b₁.withdrawn.contains (dispatchToAtom box) && !b₁.held.contains (dispatchToAtom box) then _
      else if (b₁.rulesFor (dispatchToAtom box)).isEmpty then _
      else _) = _
    rw [hw, hrulesFor]
    simp [boxDispatchRule, hs1Reg, hs1Unr, Reasons.Status.text, String.append_assoc]
  exact ⟨s₁, hingest, hs1Use, hs1Disp, hwhy⟩

/-! ## 3. Vault `_kind` Law Succession as a `Genealogy.Habitat` (`FINDINGS 19`, `Reground` `G4`) -/

/-- Monotone Vault `_kind` doctrine floors (`PROCESS.md` `Reground` `G4`). -/
inductive FloorSpec where
  /-- Corrigibility bedrock: operator can always revert within `maxSteps` of home. -/
  | corrigibilityHome (maxSteps : Nat)
  /-- Upper bound on a counter metric (e.g., `laptop_builds <= 0`, `git_add_all <= 0`). -/
  | maxCounter (metric : String) (cap : Nat)
  /-- Mandatory frontmatter/gate field line on `_kind.md` (e.g., `"gate"`). -/
  | mandatoryLine (field : String)
  deriving @[expose] DecidableEq, Repr

/-- Snapshot of a Vault `_kind` doctrine page's counters, present gate lines, and distance from home. -/
structure DoctrineSnapshot where
  counters : List (String × Nat)
  presentLines : List String
  stepsFromHome : Nat
  deriving @[expose] DecidableEq, Repr

/-- State governed by `vaultDoctrineHabitat`. -/
structure DoctrineState where
  current : DoctrineSnapshot
  auditLog : List String
  deriving @[expose] DecidableEq, Repr

/-- Actions proposed in `vaultDoctrineHabitat`. -/
inductive DoctrineAct where
  | revert
  | writeKind (next : DoctrineSnapshot)
  | recordAudit (note : String)
  deriving @[expose] DecidableEq, Repr

/-- Read a counter metric from a `DoctrineSnapshot` (defaulting to `0`). -/
@[expose] def DoctrineSnapshot.counterAt (snap : DoctrineSnapshot) (metric : String) : Nat :=
  (snap.counters.lookup metric).getD 0

/-- Decidable meaning of a `FloorSpec` on `DoctrineState`. -/
@[expose] def floorHoldsB (φ : FloorSpec) (s : DoctrineState) : Bool :=
  match φ with
  | .corrigibilityHome maxSteps => decide (s.current.stepsFromHome ≤ maxSteps)
  | .maxCounter metric cap => decide (s.current.counterAt metric ≤ cap)
  | .mandatoryLine field => s.current.presentLines.contains field

/-- Declarative `Prop` meaning of a `FloorSpec` on `DoctrineState`. -/
@[expose] def DoctrineFloorHolds (φ : FloorSpec) (s : DoctrineState) : Prop :=
  match φ with
  | .corrigibilityHome maxSteps => s.current.stepsFromHome ≤ maxSteps
  | .maxCounter metric cap => s.current.counterAt metric ≤ cap
  | .mandatoryLine field => field ∈ s.current.presentLines

instance doctrineFloorDecidable (φ : FloorSpec) (s : DoctrineState) :
    Decidable (DoctrineFloorHolds φ s) := by
  unfold DoctrineFloorHolds
  cases φ <;> infer_instance

/-- Step function for `vaultDoctrineHabitat`. -/
@[expose] def stepDoctrine (a : DoctrineAct) (s : DoctrineState) : DoctrineState :=
  match a with
  | .revert => { s with current := { s.current with stepsFromHome := 0 } }
  | .writeKind next => { s with current := next }
  | .recordAudit note => { s with auditLog := s.auditLog ++ [note] }

/-- Action format tag for `vaultDoctrineHabitat`. -/
@[expose] def doctrineFormat : DoctrineAct → String
  | .revert => "revert"
  | .writeKind _ => "vault-kind-write"
  | .recordAudit _ => "audit-note"

/-- Habitat-proved format preservation table (`revert` and `audit-note` preserve every `FloorSpec`). -/
@[expose] def doctrineProved (fmt : String) (_φ : FloorSpec) : Bool :=
  fmt == "revert" || fmt == "audit-note"

theorem doctrineProved_sound {fmt : String} {φ : FloorSpec} (hp : doctrineProved fmt φ = true) :
    ∀ a s, doctrineFormat a = fmt → DoctrineFloorHolds φ s → DoctrineFloorHolds φ (stepDoctrine a s) := by
  intro a s hfmt hφ
  cases a with
  | revert =>
    cases φ with
    | corrigibilityHome maxSteps => exact Nat.zero_le maxSteps
    | maxCounter metric cap => exact hφ
    | mandatoryLine field => exact hφ
  | recordAudit note =>
    cases φ <;> exact hφ
  | writeKind next =>
    subst hfmt
    simp [doctrineProved, doctrineFormat] at hp

/-- **`vaultDoctrineHabitat`**: concrete `Genealogy.Habitat` governing Vault `_kind` doctrine succession. -/
@[expose] def vaultDoctrineHabitat : Genealogy.Habitat where
  State := DoctrineState
  Act := DoctrineAct
  Floor := FloorSpec
  holds := DoctrineFloorHolds
  step := stepDoctrine
  format := doctrineFormat
  proved := doctrineProved
  proved_sound := doctrineProved_sound
  revert := .revert
  revert_proved _ := rfl
  bedrock
    | .corrigibilityHome _ => true
    | _ => false

/-- Build a canonical kernel-backed `Genealogy.Gate` for `vaultDoctrineHabitat` over `floors`. -/
@[expose] def mkDoctrineGate (name : String) (floors : List FloorSpec) :
    Genealogy.Gate vaultDoctrineHabitat :=
  { name := name
    formats := ["revert", "vault-kind-write", "audit-note"]
    floors := floors
    methods :=
      (floors.map fun φ => ("revert", φ, Genealogy.Method.lemma)) ++
      (floors.map fun φ => ("audit-note", φ, Genealogy.Method.lemma)) ++
      (floors.map fun φ => ("vault-kind-write", φ, Genealogy.Method.eval .kernel))
    basis := [.kernel] }

/-- Genesis `Reground` `G4` gate: corrigibility home `<= 8`, `laptop_builds <= 0`,
    `git_add_all <= 0`, and mandatory `"gate"` line. -/
@[expose] def genesisDoctrineGate : Genealogy.Gate vaultDoctrineHabitat :=
  mkDoctrineGate "genesis-doctrine"
    [.corrigibilityHome 8, .maxCounter "laptop_builds" 0, .maxCounter "git_add_all" 0, .mandatoryLine "gate"]

/-- Boolean succession check for label-free (`[]`) kernel `Reground` transitions. -/
@[expose] def checkDoctrineSuccession
    (cur : Genealogy.Gate vaultDoctrineHabitat)
    (s : DoctrineState)
    (next : Genealogy.Gate vaultDoctrineHabitat) : Bool :=
  match Genealogy.succeed cur s next [] with
  | .ok () => true
  | .error _ => false

/-- Soundness of `checkDoctrineSuccession`: `true` implies declarative `Genealogy.Succeeds`. -/
theorem checkDoctrineSuccession_sound
    {cur next : Genealogy.Gate vaultDoctrineHabitat} {s : DoctrineState}
    (h : checkDoctrineSuccession cur s next = true) :
    Genealogy.Succeeds cur s next [] := by
  unfold checkDoctrineSuccession at h
  split at h
  · next hok => exact Genealogy.succession_sound_meaning hok
  · cases h

theorem mkDoctrineGate_method_find {fmt : String} {φ : FloorSpec} {m : Genealogy.Method} :
    ∀ (floors : List FloorSpec),
      φ ∈ floors →
      ((floors.map fun ψ => (fmt, ψ, m)).find? fun entry =>
        entry.1 == fmt && decide (entry.2.1 = φ)) = some (fmt, φ, m)
  | [], h => nomatch h
  | ψ :: rest, h => by
    by_cases heq : ψ = φ
    · subst heq
      simp
    · rcases List.mem_cons.1 h with rfl | hrest
      · exact absurd rfl heq
      · have hne : decide (ψ = φ) = false := decide_eq_false heq
        simp [hne, mkDoctrineGate_method_find rest hrest]

theorem find_skip_diff_fmt {fmt₁ fmt₂ : String} (hne : (fmt₁ == fmt₂) = false) (φ : FloorSpec)
    (m : Genealogy.Method) :
    ∀ (floors : List FloorSpec) (tail : List (String × FloorSpec × Genealogy.Method)),
      (((floors.map fun ψ => (fmt₁, ψ, m)) ++ tail).find? fun entry =>
        entry.1 == fmt₂ && decide (entry.2.1 = φ)) =
      (tail.find? fun entry => entry.1 == fmt₂ && decide (entry.2.1 = φ))
  | [], tail => rfl
  | _ :: rest, tail => by
    simp [hne, find_skip_diff_fmt hne φ m rest tail]

theorem mkDoctrineGate_method_revert (name : String) {floors : List FloorSpec} {φ : FloorSpec}
    (hφ : φ ∈ floors) :
    (mkDoctrineGate name floors).method "revert" φ = some .lemma := by
  change (((floors.map fun ψ => ("revert", ψ, Genealogy.Method.lemma)) ++
      (floors.map fun ψ => ("audit-note", ψ, Genealogy.Method.lemma)) ++
      (floors.map fun ψ => ("vault-kind-write", ψ, Genealogy.Method.eval .kernel))).find?
      fun m => m.1 == "revert" && decide (m.2.1 = φ)).map (·.2.2) = some .lemma
  rw [List.find?_append, List.find?_append, mkDoctrineGate_method_find floors hφ]
  rfl

theorem mkDoctrineGate_method_write (name : String) {floors : List FloorSpec} {φ : FloorSpec}
    (hφ : φ ∈ floors) :
    (mkDoctrineGate name floors).method "vault-kind-write" φ = some (.eval .kernel) := by
  change (((floors.map fun ψ => ("revert", ψ, Genealogy.Method.lemma)) ++
      (floors.map fun ψ => ("audit-note", ψ, Genealogy.Method.lemma)) ++
      (floors.map fun ψ => ("vault-kind-write", ψ, Genealogy.Method.eval .kernel))).find?
      fun m => m.1 == "vault-kind-write" && decide (m.2.1 = φ)).map (·.2.2) = some (.eval .kernel)
  rw [List.append_assoc,
      find_skip_diff_fmt (fmt₁ := "revert") (fmt₂ := "vault-kind-write") rfl φ .lemma floors,
      find_skip_diff_fmt (fmt₁ := "audit-note") (fmt₂ := "vault-kind-write") rfl φ .lemma floors,
      mkDoctrineGate_method_find floors hφ]
  rfl

theorem mkDoctrineGate_method_audit (name : String) {floors : List FloorSpec} {φ : FloorSpec}
    (hφ : φ ∈ floors) :
    (mkDoctrineGate name floors).method "audit-note" φ = some .lemma := by
  change (((floors.map fun ψ => ("revert", ψ, Genealogy.Method.lemma)) ++
      (floors.map fun ψ => ("audit-note", ψ, Genealogy.Method.lemma)) ++
      (floors.map fun ψ => ("vault-kind-write", ψ, Genealogy.Method.eval .kernel))).find?
      fun m => m.1 == "audit-note" && decide (m.2.1 = φ)).map (·.2.2) = some .lemma
  rw [List.append_assoc,
      find_skip_diff_fmt (fmt₁ := "revert") (fmt₂ := "audit-note") rfl φ .lemma floors,
      List.find?_append, mkDoctrineGate_method_find floors hφ]
  rfl

theorem mkDoctrineGate_wellFormed (name : String) (floors : List FloorSpec)
    (hbed : ∃ k, FloorSpec.corrigibilityHome k ∈ floors) :
    Genealogy.wellFormed (mkDoctrineGate name floors) = .ok () := by
  unfold Genealogy.wellFormed
  rw [Genealogy.both_ok]
  refine ⟨?_, ?_⟩
  · rw [Genealogy.need_ok, List.any_eq_true]
    obtain ⟨k, hk⟩ := hbed
    exact ⟨.corrigibilityHome k, hk, rfl⟩
  · rw [Genealogy.both_ok]
    refine ⟨by simp [mkDoctrineGate, vaultDoctrineHabitat, doctrineFormat, Genealogy.need], ?_⟩
    rw [Genealogy.allE_ok]
    intro f hf
    rw [Genealogy.allE_ok]
    intro φ hφ
    have hφ' : φ ∈ floors := hφ
    simp only [mkDoctrineGate, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl
    · unfold Genealogy.methodCheck
      rw [mkDoctrineGate_method_revert name hφ']
      rfl
    · unfold Genealogy.methodCheck
      rw [mkDoctrineGate_method_write name hφ']
      rfl
    · unfold Genealogy.methodCheck
      rw [mkDoctrineGate_method_audit name hφ']
      rfl

/-- **`Reground` Tightening Admitted (`FINDINGS 19`, `G4`)**:
    Adding new or tighter doctrine floors (`extraFloors`) onto a `mkDoctrineGate` succeeds in every
    state `s` where the combined floors hold, and the resulting gate is immediately `GateSound`. -/
theorem vaultDoctrine_admits_tightening
    (curName nextName : String) (baseFloors extraFloors : List FloorSpec) (s : DoctrineState)
    (hbed : ∃ k, FloorSpec.corrigibilityHome k ∈ baseFloors)
    (hholds : ∀ φ ∈ baseFloors ++ extraFloors, DoctrineFloorHolds φ s) :
    checkDoctrineSuccession
      (mkDoctrineGate curName baseFloors) s
      (mkDoctrineGate nextName (baseFloors ++ extraFloors)) = true ∧
    Genealogy.GateSound Genealogy.Exec.faithful
      (mkDoctrineGate nextName (baseFloors ++ extraFloors)) := by
  have hbed' : ∃ k, FloorSpec.corrigibilityHome k ∈ baseFloors ++ extraFloors := by
    obtain ⟨k, hk⟩ := hbed
    exact ⟨k, List.mem_append_left _ hk⟩
  have hwf := mkDoctrineGate_wellFormed nextName (baseFloors ++ extraFloors) hbed'
  have hsuc : Genealogy.succeed
      (mkDoctrineGate curName baseFloors) s
      (mkDoctrineGate nextName (baseFloors ++ extraFloors)) [] = .ok () := by
    unfold Genealogy.succeed
    rw [Genealogy.both_ok]
    refine ⟨?_, ?_⟩
    · unfold Genealogy.nonRegression
      rw [Genealogy.allE_ok]
      intro φ hφ
      rw [Genealogy.need_ok, List.contains_iff_mem]
      exact List.mem_append_left _ hφ
    · rw [Genealogy.both_ok]
      refine ⟨hwf, ?_⟩
      rw [Genealogy.both_ok]
      refine ⟨?_, ?_⟩
      · rw [Genealogy.allE_ok]
        intro φ hφ
        rw [Genealogy.need_ok]
        have hd : @decide (vaultDoctrineHabitat.holds φ s) (vaultDoctrineHabitat.decHolds φ s) = true :=
          @decide_eq_true (DoctrineFloorHolds φ s) (doctrineFloorDecidable φ s) (hholds φ hφ)
        exact hd
      · simp [mkDoctrineGate, Genealogy.both, Genealogy.allE, Genealogy.need]
  have hchk : checkDoctrineSuccession
      (mkDoctrineGate curName baseFloors) s
      (mkDoctrineGate nextName (baseFloors ++ extraFloors)) = true := by
    simp [checkDoctrineSuccession, hsuc]
  exact ⟨hchk, (checkDoctrineSuccession_sound hchk).sound
    Genealogy.Exec.faithful (fun t _ => Genealogy.Exec.faithful_holds t) (fun _ h => nomatch h)⟩

/-- **`Reground` Refuses Loosening or Dropping Any Floor (`FINDINGS 19`, `G4`)**:
    Any proposed successor gate `next` that replaces `.maxCounter metric cap` with a looser cap
    (or drops it without keeping `.maxCounter metric cap ∈ next.floors`) is refused by both
    `Genealogy.succeed` and `checkDoctrineSuccession`. -/
theorem vaultDoctrine_refuses_loosening
    (cur next : Genealogy.Gate vaultDoctrineHabitat) (s : DoctrineState)
    (metric : String) (cap looserCap : Nat)
    (hcur : FloorSpec.maxCounter metric cap ∈ cur.floors)
    (hlt : cap < looserCap)
    (honlyLooser : ∀ c, FloorSpec.maxCounter metric c ∈ next.floors → looserCap ≤ c) :
    checkDoctrineSuccession cur s next = false ∧
    ∀ L, Genealogy.succeed cur s next L ≠ .ok () := by
  have hdrop : FloorSpec.maxCounter metric cap ∉ next.floors := by
    intro hmem
    have hle := honlyLooser cap hmem
    omega
  have hno : ∀ L, Genealogy.succeed cur s next L ≠ .ok () :=
    fun L => Genealogy.succeed_refuses_drop hcur hdrop
  refine ⟨?_, hno⟩
  unfold checkDoctrineSuccession
  split
  · next hok => exact absurd hok (hno [])
  · rfl

/-! ## 4. Complete Multi-Field Constructive Repair via `LawDial` (`THESIS.md:56-57`) -/

/-- True when `r` is a numeric request/ledger fact (`subject`, `caller`, `height`, `turn`). -/
@[expose] def isNumericFactRef : LawRef → Bool
  | .subject | .caller | .height | .turn => true
  | .field _ | .labelConst _ => false

/-- Read a numeric request/ledger fact directly from `facts` (state-independent). -/
@[expose] def readFactRef (facts : Facts) : LawRef → Option Int
  | .subject => facts.subject.map Int.ofNat
  | .caller => facts.caller.map Int.ofNat
  | .height => some (Int.ofNat facts.height)
  | .turn => some (Int.ofNat facts.turn)
  | .field _ | .labelConst _ => none

/-- Decidable recognizer for the conjunctive `LawDial` difference-constraint fragment:
    arbitrary `.and` combinations of `new.a == c`, `new.a <= c`, `new.a == new.b`,
    `new.a <= new.b`, `new.a <= new.b + k` (for any `k : Int`), `monotone(a)`, `writeOnce(a)`,
    and numeric fact comparisons (`request.subject`, `request.caller`, `ledger.height`, `request.turn`). -/
@[expose] def isDiffConstraintLaw : LawExpr → Bool
  | .eqC (.field _) _ | .leC (.field _) _ => true
  | .eqC r _ | .leC r _ | .inC r _ => isNumericFactRef r
  | .eqR (.field _) (.field _) | .leR (.field _) (.field _) | .leROff (.field _) (.field _) _ => true
  | .eqR (.field _) r | .leR (.field _) r | .leROff (.field _) r _ => isNumericFactRef r
  | .eqR l (.field _) | .leR l (.field _) | .leROff l (.field _) _ => isNumericFactRef l
  | .eqR l r | .leR l r | .leROff l r _ => isNumericFactRef l && isNumericFactRef r
  | .monotone _ | .writeOnce _ => true
  | .and l r => isDiffConstraintLaw l && isDiffConstraintLaw r
  | .or _ _ | .not _ | .implies _ _ => false

/-- Canonical natural-field `Data.record` over `keys` from an environment `env : String → Nat`. -/
@[expose] def stateFromEnv (keys : List String) (env : String → Nat) : Data :=
  .record (keys.map fun k => (k, .natural (env k)))

/-- Conjoin a precedence list of `(name, LawExpr)` laws into a single `LawExpr`. -/
@[expose] def conjLaws : List (String × LawExpr) → LawExpr
  | [] => LawExpr.eqR .turn .turn
  | [(_, e)] => e
  | (_, e) :: rest => .and e (conjLaws rest)

/-- Check whether `cand` satisfies every law on `lin` at occasion `occ` from prior state `o`. -/
@[expose] def allLawsHold (lin : List (String × LawExpr)) (facts : Facts) (o cand : Data)
    (occ : Vault.Occ) : Bool :=
  lin.all fun p => p.2.denote facts (occ.old o cand) cand

/-- Effective old state seen by `monotone`/`writeOnce` on natural states (`adopt` acts like `none`). -/
@[expose] def effectiveOldForOcc (occ : Vault.Occ) (o : Data) : Option Data :=
  match occ with
  | .write => some o
  | .birth | .adopt => none

/-- Upward lower-bound contribution of `e` on field `h` under `env` (Kleene/Pratt operator). -/
def atomBound (facts : Facts) (old : Option Data) (env : String → Nat) (e : LawExpr) (h : String) : Nat :=
  match e with
  | .eqC (.field f) c => if h == f && 0 ≤ c then c.toNat else 0
  | .eqR (.field f) (.field g) =>
    max (if h == f then env g else 0) (if h == g then env f else 0)
  | .eqR (.field f) r =>
    match readFactRef facts r with
    | some c => if h == f && 0 ≤ c then c.toNat else 0
    | none => 0
  | .eqR l (.field g) =>
    match readFactRef facts l with
    | some c => if h == g && 0 ≤ c then c.toNat else 0
    | none => 0
  | .leR (.field f) (.field g) => if h == g then env f else 0
  | .leR l (.field g) =>
    match readFactRef facts l with
    | some c => if h == g && 0 ≤ c then c.toNat else 0
    | none => 0
  | .leROff (.field f) (.field g) k =>
    let lb := Int.ofNat (env f) - k
    if h == g && 0 ≤ lb then lb.toNat else 0
  | .leROff l (.field g) k =>
    match readFactRef facts l with
    | some c => if h == g && 0 ≤ c - k then (c - k).toNat else 0
    | none => 0
  | .monotone f => if h == f then Obend.Spec.LawDial.oldNatAt old f else 0
  | .writeOnce f =>
    match old.bind (fieldOf f) with
    | some b => if h == f && b != 0 then b.toNat else 0
    | none => 0
  | .and l r => max (atomBound facts old env l h) (atomBound facts old env r h)
  | _ => 0

/-- One parallel upward relaxation pass across all laws in `lin`. -/
@[expose] def raiseLinEnv (facts : Facts) (old : Option Data) (lin : List (String × LawExpr))
    (env : String → Nat) (h : String) : Nat :=
  lin.foldl (fun acc p => max acc (atomBound facts old env p.2 h)) (env h)

/-- Early-stopping Kleene least-fixpoint iteration up to `fuel` rounds. -/
@[expose] def kleeneLoop (keys : List String) (facts : Facts) (old : Option Data)
    (lin : List (String × LawExpr)) : Nat → (String → Nat) → (String → Nat)
  | 0, env => env
  | fuel + 1, env =>
    let next := raiseLinEnv facts old lin env
    if keys.all (fun k => next k == env k) then env
    else kleeneLoop keys facts old lin fuel next

/-- Constructive multi-field repair witness returned by `synthesizePassingDelta`. -/
structure PassingDelta where
  targetState : Data
  edits : List (String × Nat)
  deriving Repr

/-- Build a `PassingDelta` recording the natural-field assignments on `keys` that differ from `cur`. -/
@[expose] def mkPassingDelta (keys : List String) (cur : Data) (env : String → Nat) : PassingDelta :=
  { targetState := stateFromEnv keys env
    edits := keys.filterMap fun k =>
      let v := env k
      if v != Vault.natAt cur k then some (k, v) else none }

/-- **`synthesizePassingDelta`**: Complete multi-field constructive repair over `keys` and `lin`.
    1. First invokes `Obend.Spec.LawDial.solveLawWitness` (preserving minimal edits near `old`),
       canonicalized onto `keys`.
    2. Falls back to the monotone Kleene least-fixpoint solver `kleeneLoop` with bound `cap`
       (`keys.length * cap + 1` rounds, early-exiting on stabilization), which avoids upper/lower
       oscillation and is **complete** for all satisfiable difference-constraint systems bounded by `cap`. -/
@[expose] def synthesizePassingDelta (keys : List String) (lin : List (String × LawExpr))
    (facts : Facts) (o cur : Data) (occ : Vault.Occ) (cap : Nat) : Option PassingDelta :=
  let old := effectiveOldForOcc occ o
  let dialEnv : String → Nat :=
    match Obend.Spec.LawDial.solveLawWitness keys (conjLaws lin) facts old with
    | some w => Vault.natAt w
    | none => fun _ => 0
  let dialCand := stateFromEnv keys dialEnv
  if allLawsHold lin facts o dialCand occ then
    some (mkPassingDelta keys cur dialEnv)
  else
    let kleeneEnv := kleeneLoop keys facts old lin (keys.length * cap + 1) (fun _ => 0)
    let kleeneCand := stateFromEnv keys kleeneEnv
    if allLawsHold lin facts o kleeneCand occ then
      some (mkPassingDelta keys cur kleeneEnv)
    else
      none

/-- Graded counterpart to `Vault.judge` parameterized by step budget `fuel` (`Vault.judge` is
    `judgeAtFuel Vault.lawFuel`). -/
@[expose] def judgeAtFuel (fuel : Nat) (S : Ty) (pkg : String) (lin : List (String × LawExpr))
    (o n rq : Data) : Vault.Verdict :=
  if lin.all (fun p => Obend.Spec.LawCompile.Fits S p.2 o && Obend.Spec.LawCompile.Fits S p.2 n) then
    if (Vault.compiled S pkg lin).all (fun p => Obend.Law.closedB p.2) then
      Vault.readVerdict (Obend.Law.run fuel (Obend.Law.applyLaw (Obend.Law.effective (Vault.compiled S pkg lin)) o n rq))
    else .undecided "a compiled law is not closed"
  else .undecided "the page state does not fit a law"

theorem judgeAtFuel_lawFuel_eq (S : Ty) (pkg : String) (lin : List (String × LawExpr)) (o n rq : Data) :
    judgeAtFuel Vault.lawFuel S pkg lin o n rq = Vault.judge S pkg lin o n rq := rfl

/-! ### 4.1 Core4 Closedness, `Fits` on `stateFromEnv`, and `run` Completeness -/

theorem cond_scopedB (S : Ty) (src : Obend.Spec.LawCompile.OldSrc) :
    ∀ (e : LawExpr) (a : Obend.Law.At) (n : Nat),
      a.depth + 3 ≤ n →
      Obend.Law.scopedB n (Obend.Core.TermTraverse.encode (Obend.Spec.LawCompile.cond S src a e)) = true := by
  have hbnd : ∀ (i n : Nat), i < n →
      Obend.Law.scopedB n (Obend.Core.TermTraverse.encode (.bound i)) = true := by
    intro i n hi
    simp [Obend.Core.TermTraverse.encode, Obend.Law.scopedB, hi]
  have href : ∀ (r : LawRef) (a : Obend.Law.At) (n : Nat), a.depth + 3 ≤ n →
      Obend.Law.scopedB n (Obend.Core.TermTraverse.encode (Obend.Spec.LawCompile.refRead S a r).present) = true ∧
      Obend.Law.scopedB n (Obend.Core.TermTraverse.encode (Obend.Spec.LawCompile.refRead S a r).value) = true := by
    intro r a n hn
    cases r with
    | field f =>
      simp only [Obend.Spec.LawCompile.refRead, Obend.Spec.LawCompile.fieldRead]
      cases Obend.Spec.LawCompile.fieldKind S f with
      | none => simp [Obend.Law.falseT, Obend.Law.natT, Obend.Core.TermTraverse.encode, Obend.Law.scopedB, Obend.Law.scopedsB]
      | some k =>
        cases k <;>
          simp [Obend.Law.trueT, Obend.Law.natT, Obend.Spec.LawCompile.scalarRead,
            Obend.Law.At.newF, Obend.Law.At.new, Obend.Core.TermTraverse.encode,
            Obend.Law.scopedB, Obend.Law.scopedsB] <;> omega
    | subject | caller =>
      simp [Obend.Spec.LawCompile.refRead, Obend.Spec.LawCompile.optRead,
        Obend.Spec.LawCompile.isSomeT, Obend.Spec.LawCompile.payloadT,
        Obend.Law.falseT, Obend.Law.trueT, Obend.Law.natT,
        Obend.Law.At.reqF, Obend.Law.At.req, Obend.Core.TermTraverse.encode,
        Obend.Law.scopedB, Obend.Law.scopedsB]
      omega
    | height | turn =>
      simp [Obend.Spec.LawCompile.refRead, Obend.Law.trueT,
        Obend.Law.At.reqF, Obend.Law.At.req, Obend.Core.TermTraverse.encode,
        Obend.Law.scopedB, Obend.Law.scopedsB]
      omega
    | labelConst _ =>
      simp [Obend.Spec.LawCompile.refRead, Obend.Law.falseT, Obend.Law.natT,
        Obend.Core.TermTraverse.encode, Obend.Law.scopedB, Obend.Law.scopedsB]
  have hlbl : ∀ (r : LawRef) (a : Obend.Law.At) (n : Nat) (t : Term),
      a.depth + 3 ≤ n →
      Obend.Spec.LawCompile.labelRead S a r = some t →
      Obend.Law.scopedB n (Obend.Core.TermTraverse.encode t) = true := by
    intro r a n t hn hl
    cases r <;> simp [Obend.Spec.LawCompile.labelRead] at hl
    · rcases hl with ⟨_, rfl⟩
      simp [Obend.Law.At.new, Obend.Core.TermTraverse.encode,
        Obend.Law.scopedB, Obend.Law.scopedsB]
      omega
    · subst hl
      simp [Obend.Core.TermTraverse.encode, Obend.Law.scopedB, Obend.Law.scopedsB]
  have hold : ∀ (a : Obend.Law.At) (f : String) (n : Nat), a.depth + 3 ≤ n →
      Obend.Law.scopedB n (Obend.Core.TermTraverse.encode (Obend.Spec.LawCompile.oldRead src a f)) = true := by
    intro a f n hn
    cases src <;>
      simp [Obend.Spec.LawCompile.oldRead, Obend.Law.At.oldF, Obend.Law.At.old,
        Obend.Law.At.newF, Obend.Law.At.new, Obend.Core.TermTraverse.encode,
        Obend.Law.scopedB, Obend.Law.scopedsB] <;> omega
  have hany : ∀ (ts : List Term) (n : Nat),
      (∀ t ∈ ts, Obend.Law.scopedB n (Obend.Core.TermTraverse.encode t) = true) →
      Obend.Law.scopedB n (Obend.Core.TermTraverse.encode (Obend.Law.anyOf ts)) = true := by
    intro ts n hts
    induction ts with
    | nil => simp [Obend.Law.anyOf, Obend.Law.falseT, Obend.Core.TermTraverse.encode, Obend.Law.scopedB, Obend.Law.scopedsB]
    | cons t rest ih =>
      have ht := hts t List.mem_cons_self
      have hr := ih (fun u hu => hts u (List.mem_cons_of_mem _ hu))
      simp [Obend.Law.anyOf, Obend.Law.trueT, Obend.Core.TermTraverse.encode,
        Obend.Law.scopedB, Obend.Law.scopedsB, ht, hr]
  intro e
  induction e with
  | eqC r c =>
    intro a n hn
    obtain ⟨hp, hv⟩ := href r a n hn
    simp only [Obend.Spec.LawCompile.cond]
    split <;> simp [Obend.Law.andT, Obend.Law.eqNat, Obend.Law.natT, Obend.Law.falseT,
      Obend.Core.TermTraverse.encode, Obend.Law.scopedB, Obend.Law.scopedsB, hp, hv]
  | leC r c =>
    intro a n hn
    obtain ⟨hp, hv⟩ := href r a n hn
    simp only [Obend.Spec.LawCompile.cond]
    split <;> simp [Obend.Law.andT, Obend.Law.leNat, Obend.Law.natT, Obend.Law.falseT,
      Obend.Core.TermTraverse.encode, Obend.Law.scopedB, Obend.Law.scopedsB, hp, hv]
  | inC r cs =>
    intro a n hn
    obtain ⟨hp, hv⟩ := href r a n hn
    have hcs : Obend.Law.scopedB n (Obend.Core.TermTraverse.encode
        (Obend.Law.anyOf ((cs.filter (0 ≤ ·)).map fun c =>
          Obend.Law.eqNat (Obend.Spec.LawCompile.refRead S a r).value (Obend.Law.natT c.toNat)))) = true := by
      apply hany
      intro t ht
      obtain ⟨c, _, rfl⟩ := List.mem_map.1 ht
      simp [Obend.Law.eqNat, Obend.Law.natT, Obend.Core.TermTraverse.encode,
        Obend.Law.scopedB, Obend.Law.scopedsB, hv]
    simp [Obend.Spec.LawCompile.cond, Obend.Law.andT, Obend.Law.falseT,
      Obend.Core.TermTraverse.encode, Obend.Law.scopedB, Obend.Law.scopedsB, hp, hcs]
  | eqR l r =>
    intro a n hn
    obtain ⟨hpl, hvl⟩ := href l a n hn
    obtain ⟨hpr, hvr⟩ := href r a n hn
    simp only [Obend.Spec.LawCompile.cond]
    cases hll : Obend.Spec.LawCompile.labelRead S a l with
    | none =>
      simp [Obend.Spec.LawCompile.both, Obend.Law.andT, Obend.Law.eqNat, Obend.Law.falseT,
        Obend.Core.TermTraverse.encode, Obend.Law.scopedB, Obend.Law.scopedsB, hpl, hvl, hpr, hvr]
    | some tl =>
      cases hlr : Obend.Spec.LawCompile.labelRead S a r with
      | none =>
        simp [Obend.Spec.LawCompile.both, Obend.Law.andT, Obend.Law.eqNat, Obend.Law.falseT,
          Obend.Core.TermTraverse.encode, Obend.Law.scopedB, Obend.Law.scopedsB, hpl, hvl, hpr, hvr]
      | some tr =>
        have h1 := hlbl l a n tl hn hll
        have h2 := hlbl r a n tr hn hlr
        simp [Obend.Law.eqLabel, Obend.Core.TermTraverse.encode,
          Obend.Law.scopedB, Obend.Law.scopedsB, h1, h2]
  | leR l r =>
    intro a n hn
    obtain ⟨hpl, hvl⟩ := href l a n hn
    obtain ⟨hpr, hvr⟩ := href r a n hn
    simp [Obend.Spec.LawCompile.cond, Obend.Spec.LawCompile.both, Obend.Law.andT,
      Obend.Law.leNat, Obend.Law.falseT, Obend.Core.TermTraverse.encode,
      Obend.Law.scopedB, Obend.Law.scopedsB, hpl, hvl, hpr, hvr]
  | leROff l r k =>
    intro a n hn
    obtain ⟨hpl, hvl⟩ := href l a n hn
    obtain ⟨hpr, hvr⟩ := href r a n hn
    simp only [Obend.Spec.LawCompile.cond]
    split <;> simp [Obend.Spec.LawCompile.both, Obend.Law.andT, Obend.Law.leNat,
      Obend.Law.addNat, Obend.Law.natT, Obend.Law.falseT, Obend.Core.TermTraverse.encode,
      Obend.Law.scopedB, Obend.Law.scopedsB, hpl, hvl, hpr, hvr]
  | monotone f =>
    intro a n hn
    have ho := hold a f n hn
    simp only [Obend.Spec.LawCompile.cond]
    split
    · simp [Obend.Law.trueT, Obend.Core.TermTraverse.encode, Obend.Law.scopedB, Obend.Law.scopedsB]
    · cases Obend.Spec.LawCompile.fieldKind S f with
      | none => simp [Obend.Law.falseT, Obend.Core.TermTraverse.encode, Obend.Law.scopedB, Obend.Law.scopedsB]
      | some k =>
        cases k <;>
          simp [Obend.Law.leNat, Obend.Spec.LawCompile.scalarRead, Obend.Law.natT,
            Obend.Law.At.newF, Obend.Law.At.new, Obend.Core.TermTraverse.encode,
            Obend.Law.scopedB, Obend.Law.scopedsB, ho] <;> omega
  | writeOnce f =>
    intro a n hn
    have ho := hold a f n hn
    simp only [Obend.Spec.LawCompile.cond]
    split
    · simp [Obend.Law.trueT, Obend.Core.TermTraverse.encode, Obend.Law.scopedB, Obend.Law.scopedsB]
    · cases Obend.Spec.LawCompile.fieldKind S f with
      | some k =>
        cases k <;>
          simp [Obend.Law.eqNat, Obend.Spec.LawCompile.scalarRead, Obend.Law.trueT, Obend.Law.natT,
            Obend.Law.At.newF, Obend.Law.At.new, Obend.Core.TermTraverse.encode,
            Obend.Law.scopedB, Obend.Law.scopedsB, ho] <;> omega
      | none =>
        by_cases hl : Obend.Spec.LawCompile.labelField S f = true
        · simp [hl, Obend.Law.eqLabel, Obend.Law.trueT, Obend.Law.At.newF, Obend.Law.At.new,
            Obend.Core.TermTraverse.encode, Obend.Law.scopedB, Obend.Law.scopedsB, ho]
          omega
        · simp [hl, Obend.Law.trueT, Obend.Core.TermTraverse.encode, Obend.Law.scopedB, Obend.Law.scopedsB]
  | not body ih =>
    intro a n hn
    simp [Obend.Spec.LawCompile.cond, Obend.Law.notT, Obend.Law.falseT, Obend.Law.trueT,
      Obend.Core.TermTraverse.encode, Obend.Law.scopedB, Obend.Law.scopedsB, ih a n hn]
  | and l r ihl ihr =>
    intro a n hn
    simp [Obend.Spec.LawCompile.cond, Obend.Law.andT, Obend.Law.falseT,
      Obend.Core.TermTraverse.encode, Obend.Law.scopedB, Obend.Law.scopedsB, ihl a n hn, ihr a n hn]
  | or l r ihl ihr =>
    intro a n hn
    simp [Obend.Spec.LawCompile.cond, Obend.Spec.LawCompile.orT, Obend.Law.trueT,
      Obend.Core.TermTraverse.encode, Obend.Law.scopedB, Obend.Law.scopedsB, ihl a n hn, ihr a n hn]
  | implies l r ihl ihr =>
    intro a n hn
    simp [Obend.Spec.LawCompile.cond, Obend.Spec.LawCompile.impliesT, Obend.Law.trueT,
      Obend.Core.TermTraverse.encode, Obend.Law.scopedB, Obend.Law.scopedsB, ihl a n hn, ihr a n hn]

/-- Every compiled `.obend` `LawExpr` is syntactically closed (`closedB = true`). -/
theorem compile_closed (S : Ty) (pkg name : String) (e : LawExpr) :
    Obend.Law.closedB (Obend.Spec.LawCompile.compile S pkg name e) = true := by
  have hcNone := cond_scopedB S .none e ⟨1⟩ 4 (by decide)
  have hcSame := cond_scopedB S .same e ⟨1⟩ 4 (by decide)
  have hcPrior := cond_scopedB S .prior e ⟨1⟩ 4 (by decide)
  simp [Obend.Law.closedB, Obend.Spec.LawCompile.compile, Obend.Law.lawOf6,
    Obend.Law.law3, Obend.Law.lawCase6, Obend.Spec.LawCompile.clause,
    Obend.Law.guard, Obend.Law.okT, Obend.Law.refusedT,
    Obend.Core.TermTraverse.encode, Obend.Law.scopedB, Obend.Law.scopedsB,
    hcNone, hcSame, hcPrior]

theorem rowMember_stateTy (f : String) :
    ∀ (keys : List String),
      Obend.Core.Bidirectional.rowMember (Vault.stateTy keys) f =
        if f ∈ keys then some .natural else none
  | [] => by simp [Vault.stateTy, Obend.Core.Bidirectional.rowMember]
  | k :: ks => by
    simp only [Vault.stateTy, List.foldr_cons, Obend.Core.Bidirectional.rowMember, List.mem_cons]
    by_cases hk : k = f
    · subst hk; simp
    · have hfk : f = k ↔ False := ⟨fun h => hk h.symm, False.elim⟩
      have ih := rowMember_stateTy f ks
      simp only [Vault.stateTy] at ih
      simp [hk, hfk, ih]

theorem fieldsLookup_stateFromEnv (f : String) (env : String → Nat) :
    ∀ (keys : List String),
      Obend.Law.fieldsLookup f (keys.map fun k => (k, Data.natural (env k))) =
        if f ∈ keys then some (.natural (env f)) else none
  | [] => by simp [Obend.Law.fieldsLookup]
  | k :: ks => by
    simp only [List.map_cons, Obend.Law.fieldsLookup, List.mem_cons]
    by_cases hk : k = f
    · subst hk; simp
    · have hkb : (k == f) = false := beq_false_of_ne hk
      have hfk : f = k ↔ False := ⟨fun h => hk h.symm, False.elim⟩
      simp [hkb, hfk, fieldsLookup_stateFromEnv f env ks]

theorem firstScalarField_stateFromEnv (f : String) (env : String → Nat) :
    ∀ (keys : List String),
      firstScalarField f (keys.map fun k => (k, Data.natural (env k))) =
        if f ∈ keys then some (Int.ofNat (env f)) else none
  | [] => by simp [firstScalarField]
  | k :: ks => by
    simp only [List.map_cons, firstScalarField, List.mem_cons]
    by_cases hk : k = f
    · subst hk; simp [scalarOf]
    · have hfk : f = k ↔ False := ⟨fun h => hk h.symm, False.elim⟩
      simp [hk, hfk, firstScalarField_stateFromEnv f env ks]

theorem fieldOf_stateFromEnv_mem {keys : List String} {f : String} (hf : f ∈ keys) (env : String → Nat) :
    fieldOf f (stateFromEnv keys env) = some (Int.ofNat (env f)) := by
  simp [stateFromEnv, fieldOf, firstScalarField_stateFromEnv, hf]

theorem firstField_stateFromEnv_not_label (f : String) (env : String → Nat) :
    ∀ (keys : List String),
      fieldLabel f (.record (keys.map fun k => (k, Data.natural (env k)))) = none
  | [] => rfl
  | k :: ks => by
    simp only [List.map_cons, fieldLabel, firstField]
    by_cases hk : k = f
    · subst hk; simp
    · simp only [hk, ite_false]
      exact firstField_stateFromEnv_not_label f env ks

/-- Every `stateFromEnv keys env` unconditionally fits `Vault.stateTy keys` for every `e : LawExpr`. -/
theorem fits_stateFromEnv (keys : List String) (env : String → Nat) (e : LawExpr) :
    Obend.Spec.LawCompile.Fits (Vault.stateTy keys) e (stateFromEnv keys env) = true := by
  simp only [Obend.Spec.LawCompile.Fits, stateFromEnv, List.all_eq_true]
  intro f _
  unfold Obend.Spec.LawCompile.fitsField Obend.Spec.LawCompile.fieldKind Obend.Spec.LawCompile.labelField
  rw [rowMember_stateTy f keys, fieldsLookup_stateFromEnv f env keys,
      firstScalarField_stateFromEnv f env keys, firstField_stateFromEnv_not_label f env keys]
  by_cases hf : f ∈ keys <;> simp [hf]

theorem term_value_isValueB {t : Term} (hv : Value t) : Obend.Law.isValueB t = true := by
  cases hv <;> rfl

theorem term_isValueB_value {t : Term} (hb : Obend.Law.isValueB t = true) : Value t := by
  cases t <;> simp [Obend.Law.isValueB] at hb <;> constructor

/-- Completeness of `Obend.Law.run`: every terminating `Evaluates t v` finishes within some finite `fuel₀`
    and stays `some v` for all `fuel ≥ fuel₀`. -/
theorem run_complete_of_evaluates {t v : Term} (hev : Evaluates t v) :
    ∃ fuel₀, ∀ fuel, fuel₀ ≤ fuel → Obend.Law.run fuel t = some v := by
  obtain ⟨hsteps, hv⟩ := hev
  induction hsteps with
  | refl =>
    refine ⟨0, fun fuel _ => ?_⟩
    cases fuel <;> simp [Obend.Law.run, term_value_isValueB hv]
  | @next init mid _ s _ ih =>
    obtain ⟨fuel₀, hfuel⟩ := ih hv
    have hnotVal : Obend.Law.isValueB init = false := by
      cases hb : Obend.Law.isValueB init
      · rfl
      · exact False.elim (Obend.Law.value_no_step (term_isValueB_value hb) s)
    have hstep : Obend.Law.step? init = some mid := Obend.Law.step?_complete s
    refine ⟨fuel₀ + 1, fun fuel hge => ?_⟩
    obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
    simp only [Obend.Law.run, hnotVal, Bool.false_eq_true, ite_false, hstep]
    exact hfuel k (by omega)

theorem run_deterministic_some {f₁ f₂ : Nat} {t v₁ v₂ : Term}
    (h₁ : Obend.Law.run f₁ t = some v₁) (h₂ : Obend.Law.run f₂ t = some v₂) : v₁ = v₂ :=
  Obend.Law.evaluates_unique (Obend.Law.run_sound f₁ h₁) (Obend.Law.run_sound f₂ h₂)

/-! ### 4.2 Soundness of `synthesizePassingDelta` -/

/-- **Soundness of `synthesizePassingDelta`**:
    Whenever `synthesizePassingDelta` returns `some delta` (assuming `Fits (Vault.stateTy keys) p.2 o`
    for prior state `o`, which always holds when `o = Vault.stateOf keys _` or `stateFromEnv keys _`):
    1. Every `(nm, e) ∈ lin` holds by `LawExpr.denote` on `delta.targetState` at `occ`.
    2. Package-level `Obend.Law.effective` admits `o → delta.targetState` under `Obend.Law.Admits`.
    3. `judgeAtFuel` admits for all sufficiently large `fuel ≥ fuel₀`.
    4. `Vault.judge` never refuses, and equals `.admitted` whenever its step budget `Vault.lawFuel` finishes. -/
theorem synthesizePassingDelta_sound
    {keys : List String} {lin : List (String × LawExpr)}
    {facts : Facts} {o cur : Data} {occ : Vault.Occ} {cap : Nat} {delta : PassingDelta}
    (pkg who pr : String)
    (hfitO : ∀ p ∈ lin, Obend.Spec.LawCompile.Fits (Vault.stateTy keys) p.2 o = true)
    (hsyn : synthesizePassingDelta keys lin facts o cur occ cap = some delta) :
    (∀ p ∈ lin, p.2.denote facts (occ.old o delta.targetState) delta.targetState = true) ∧
    Obend.Law.Admits
      (Obend.Law.effective (Vault.compiled (Vault.stateTy keys) pkg lin))
      o delta.targetState (Vault.requestBy who pr occ facts) ∧
    (∃ fuel₀, ∀ fuel, fuel₀ ≤ fuel →
      judgeAtFuel fuel (Vault.stateTy keys) pkg lin o delta.targetState
        (Vault.requestBy who pr occ facts) = .admitted) ∧
    (∀ v, Obend.Law.run Vault.lawFuel
        (Obend.Law.applyLaw (Obend.Law.effective (Vault.compiled (Vault.stateTy keys) pkg lin))
          o delta.targetState (Vault.requestBy who pr occ facts)) = some v →
      Vault.judge (Vault.stateTy keys) pkg lin o delta.targetState
        (Vault.requestBy who pr occ facts) = .admitted) := by
  have hextract : ∃ env, delta = mkPassingDelta keys cur env ∧
      allLawsHold lin facts o (stateFromEnv keys env) occ = true := by
    unfold synthesizePassingDelta at hsyn
    let old := effectiveOldForOcc occ o
    let dialEnv : String → Nat :=
      match Obend.Spec.LawDial.solveLawWitness keys (conjLaws lin) facts old with
      | some w => Vault.natAt w
      | none => fun _ => 0
    let kleeneEnv := kleeneLoop keys facts old lin (keys.length * cap + 1) (fun _ => 0)
    change (if allLawsHold lin facts o (stateFromEnv keys dialEnv) occ then
        some (mkPassingDelta keys cur dialEnv)
      else if allLawsHold lin facts o (stateFromEnv keys kleeneEnv) occ then
        some (mkPassingDelta keys cur kleeneEnv)
      else none) = some delta at hsyn
    by_cases h1 : allLawsHold lin facts o (stateFromEnv keys dialEnv) occ = true
    · simp only [h1, ite_true] at hsyn
      exact ⟨dialEnv, (Option.some.inj hsyn).symm, h1⟩
    · simp only [h1] at hsyn
      by_cases h2 : allLawsHold lin facts o (stateFromEnv keys kleeneEnv) occ = true
      · simp only [h2, ite_true] at hsyn
        exact ⟨kleeneEnv, (Option.some.inj hsyn).symm, h2⟩
      · simp only [h2] at hsyn
        cases hsyn
  obtain ⟨env, rfl, hall⟩ := hextract
  have htarget : (mkPassingDelta keys cur env).targetState = stateFromEnv keys env := rfl
  rw [htarget]
  have hden : ∀ p ∈ lin, p.2.denote facts (occ.old o (stateFromEnv keys env)) (stateFromEnv keys env) = true :=
    fun p hp => List.all_eq_true.1 hall p hp
  have hclosed : ∀ q ∈ Vault.compiled (Vault.stateTy keys) pkg lin, Obend.Law.closedB q.2 = true := by
    intro q hq
    obtain ⟨e, _, heq⟩ := Vault.mem_compiled hq
    rw [heq]
    exact compile_closed (Vault.stateTy keys) pkg q.1 e
  have hadmits : Obend.Law.Admits
      (Obend.Law.effective (Vault.compiled (Vault.stateTy keys) pkg lin))
      o (stateFromEnv keys env) (Vault.requestBy who pr occ facts) := by
    rw [Obend.Law.effective_law_eval hclosed]
    intro q hq
    obtain ⟨e, hmem, heq⟩ := Vault.mem_compiled hq
    rw [heq]
    have hfo := hfitO (q.1, e) hmem
    have hfn := fits_stateFromEnv keys env e
    have hev := Vault.compile_occ (S := Vault.stateTy keys) (pkg := pkg) (name := q.1)
      (e := e) (o := o) (n := stateFromEnv keys env) (facts := facts) (who := who) (pr := pr) occ hfo hfn
    rw [hden (q.1, e) hmem] at hev
    exact ⟨.record [], hev⟩
  obtain ⟨w, hevOk⟩ := hadmits
  obtain ⟨fuel₀, hfuel⟩ := run_complete_of_evaluates hevOk
  have hfitAll : (lin.all fun p =>
      Obend.Spec.LawCompile.Fits (Vault.stateTy keys) p.2 o &&
      Obend.Spec.LawCompile.Fits (Vault.stateTy keys) p.2 (stateFromEnv keys env)) = true := by
    rw [List.all_eq_true]
    intro p hp
    simp [hfitO p hp, fits_stateFromEnv keys env p.2]
  have hclAll : ((Vault.compiled (Vault.stateTy keys) pkg lin).all fun p => Obend.Law.closedB p.2) = true :=
    List.all_eq_true.2 hclosed
  refine ⟨hden, ⟨w, hevOk⟩, ⟨fuel₀, fun fuel hge => ?_⟩, fun v hrun => ?_⟩
  · simp [judgeAtFuel, hfitAll, hclAll, hfuel fuel hge, Vault.readVerdict]
  · have hv : v = .inject "ok" w :=
      run_deterministic_some hrun (hfuel (max fuel₀ Vault.lawFuel) (Nat.le_max_left _ _))
    subst hv
    simp [Vault.judge, hfitAll, hclAll, hrun, Vault.readVerdict]

/-! ### 4.3 Completeness of `synthesizePassingDelta` on the Bounded `LawDial` Fragment -/

theorem read_numericFactRef {r : LawRef} (hr : isNumericFactRef r = true)
    (facts : Facts) (d : Data) :
    r.read facts d = readFactRef facts r := by
  cases r <;> simp [isNumericFactRef, LawRef.read, readFactRef] at hr ⊢

theorem readLabel_numericFactRef {r : LawRef} (hr : isNumericFactRef r = true) (d : Data) :
    r.readLabel d = none := by
  cases r <;> simp [isNumericFactRef, LawRef.readLabel] at hr ⊢

theorem denote_adopt_eq_none_stateFromEnv (keys : List String) (facts : Facts) (env : String → Nat) :
    ∀ (e : LawExpr),
      (∀ f ∈ e.fields, f ∈ keys) →
      e.denote facts (some (stateFromEnv keys env)) (stateFromEnv keys env) =
        e.denote facts none (stateFromEnv keys env)
  | .eqC _ _, _ | .leC _ _, _ | .inC _ _, _ | .eqR _ _, _ | .leR _ _, _ | .leROff _ _ _, _ => rfl
  | .monotone f, hfields => by
    have hf : f ∈ keys := hfields f (by simp [LawExpr.fields])
    simp [LawExpr.denote, fieldOf_stateFromEnv_mem hf env]
  | .writeOnce f, hfields => by
    have hf : f ∈ keys := hfields f (by simp [LawExpr.fields])
    simp [LawExpr.denote, fieldOf_stateFromEnv_mem hf env]
  | .not b, hfields => by
    simp [LawExpr.denote, denote_adopt_eq_none_stateFromEnv keys facts env b hfields]
  | .and l r, hfields => by
    have hl : ∀ f ∈ l.fields, f ∈ keys := fun f hf => hfields f (by simp [LawExpr.fields, hf])
    have hr : ∀ f ∈ r.fields, f ∈ keys := fun f hf => hfields f (by simp [LawExpr.fields, hf])
    simp [LawExpr.denote, denote_adopt_eq_none_stateFromEnv keys facts env l hl,
      denote_adopt_eq_none_stateFromEnv keys facts env r hr]
  | .or l r, hfields => by
    have hl : ∀ f ∈ l.fields, f ∈ keys := fun f hf => hfields f (by simp [LawExpr.fields, hf])
    have hr : ∀ f ∈ r.fields, f ∈ keys := fun f hf => hfields f (by simp [LawExpr.fields, hf])
    simp [LawExpr.denote, denote_adopt_eq_none_stateFromEnv keys facts env l hl,
      denote_adopt_eq_none_stateFromEnv keys facts env r hr]
  | .implies l r, hfields => by
    have hl : ∀ f ∈ l.fields, f ∈ keys := fun f hf => hfields f (by simp [LawExpr.fields, hf])
    have hr : ∀ f ∈ r.fields, f ∈ keys := fun f hf => hfields f (by simp [LawExpr.fields, hf])
    simp [LawExpr.denote, denote_adopt_eq_none_stateFromEnv keys facts env l hl,
      denote_adopt_eq_none_stateFromEnv keys facts env r hr]

theorem denote_occ_eq_effectiveOld (keys : List String) (facts : Facts) (o : Data)
    (occ : Vault.Occ) (env : String → Nat) {e : LawExpr} (hfields : ∀ f ∈ e.fields, f ∈ keys) :
    e.denote facts (occ.old o (stateFromEnv keys env)) (stateFromEnv keys env) =
      e.denote facts (effectiveOldForOcc occ o) (stateFromEnv keys env) := by
  cases occ with
  | write => rfl
  | birth => rfl
  | adopt => exact denote_adopt_eq_none_stateFromEnv keys facts env e hfields

theorem fieldOf_nonneg {f : String} {d : Data} {b : Int} (h : fieldOf f d = some b) : 0 ≤ b := by
  cases d <;> simp [fieldOf] at h
  exact Obend.Spec.LawDial.firstScalarField_nonneg h

theorem lawRef_cases (r : LawRef) : (∃ f, r = .field f) ∨ (∀ f, r ≠ .field f) := by
  cases r with
  | field f => exact .inl ⟨f, rfl⟩
  | _ => exact .inr fun _ h => by cases h

theorem isDiff_eqC_nonfield {r : LawRef} {c : Int} (hn : ∀ f, r ≠ .field f)
    (h : isDiffConstraintLaw (.eqC r c) = true) : isNumericFactRef r = true := by
  cases r with
  | field f => exact absurd rfl (hn f)
  | _ => exact h

theorem isDiff_leC_nonfield {r : LawRef} {c : Int} (hn : ∀ f, r ≠ .field f)
    (h : isDiffConstraintLaw (.leC r c) = true) : isNumericFactRef r = true := by
  cases r with
  | field f => exact absurd rfl (hn f)
  | _ => exact h

theorem isDiff_inC_nonfield {r : LawRef} {vs : List Int} (hn : ∀ f, r ≠ .field f)
    (h : isDiffConstraintLaw (.inC r vs) = true) : isNumericFactRef r = true := by
  cases r with
  | field f => exact absurd rfl (hn f)
  | _ => exact h

theorem isDiff_eqR_right {f : String} {r : LawRef} (hn : ∀ g, r ≠ .field g)
    (h : isDiffConstraintLaw (.eqR (.field f) r) = true) : isNumericFactRef r = true := by
  cases r with
  | field g => exact absurd rfl (hn g)
  | _ => exact h

theorem isDiff_eqR_left {l : LawRef} {g : String} (hn : ∀ f, l ≠ .field f)
    (h : isDiffConstraintLaw (.eqR l (.field g)) = true) : isNumericFactRef l = true := by
  cases l with
  | field f => exact absurd rfl (hn f)
  | _ => exact h

theorem int_ofNat_nonneg (n : Nat) : 0 ≤ Int.ofNat n := by rw [Int.ofNat_eq_natCast]; omega
theorem int_ofNat_toNat (n : Nat) : (Int.ofNat n).toNat = n := rfl

theorem read_field_stateFromEnv {keys : List String} {f : String} (hf : f ∈ keys)
    (facts : Facts) (env : String → Nat) :
    (LawRef.field f).read facts (stateFromEnv keys env) = some (Int.ofNat (env f)) :=
  fieldOf_stateFromEnv_mem hf env

theorem isDiff_eqR_both {l r : LawRef} (hnl : ∀ f, l ≠ .field f) (hnr : ∀ g, r ≠ .field g)
    (h : isDiffConstraintLaw (.eqR l r) = true) :
    isNumericFactRef l = true ∧ isNumericFactRef r = true := by
  cases l with
  | field f => exact absurd rfl (hnl f)
  | _ =>
    cases r with
    | field g => exact absurd rfl (hnr g)
    | _ => simpa [isDiffConstraintLaw] using h

theorem isDiff_leR_right {f : String} {r : LawRef} (hn : ∀ g, r ≠ .field g)
    (h : isDiffConstraintLaw (.leR (.field f) r) = true) : isNumericFactRef r = true := by
  cases r with
  | field g => exact absurd rfl (hn g)
  | _ => exact h

theorem isDiff_leR_left {l : LawRef} {g : String} (hn : ∀ f, l ≠ .field f)
    (h : isDiffConstraintLaw (.leR l (.field g)) = true) : isNumericFactRef l = true := by
  cases l with
  | field f => exact absurd rfl (hn f)
  | _ => exact h

theorem isDiff_leR_both {l r : LawRef} (hnl : ∀ f, l ≠ .field f) (hnr : ∀ g, r ≠ .field g)
    (h : isDiffConstraintLaw (.leR l r) = true) :
    isNumericFactRef l = true ∧ isNumericFactRef r = true := by
  cases l with
  | field f => exact absurd rfl (hnl f)
  | _ =>
    cases r with
    | field g => exact absurd rfl (hnr g)
    | _ => simpa [isDiffConstraintLaw] using h

theorem isDiff_leROff_right {f : String} {r : LawRef} {k : Int} (hn : ∀ g, r ≠ .field g)
    (h : isDiffConstraintLaw (.leROff (.field f) r k) = true) : isNumericFactRef r = true := by
  cases r with
  | field g => exact absurd rfl (hn g)
  | _ => exact h

theorem isDiff_leROff_left {l : LawRef} {g : String} {k : Int} (hn : ∀ f, l ≠ .field f)
    (h : isDiffConstraintLaw (.leROff l (.field g) k) = true) : isNumericFactRef l = true := by
  cases l with
  | field f => exact absurd rfl (hn f)
  | _ => exact h

theorem isDiff_leROff_both {l r : LawRef} {k : Int} (hnl : ∀ f, l ≠ .field f) (hnr : ∀ g, r ≠ .field g)
    (h : isDiffConstraintLaw (.leROff l r k) = true) :
    isNumericFactRef l = true ∧ isNumericFactRef r = true := by
  cases l with
  | field f => exact absurd rfl (hnl f)
  | _ =>
    cases r with
    | field g => exact absurd rfl (hnr g)
    | _ => simpa [isDiffConstraintLaw] using h

theorem atomBound_eqC_nonfield (facts : Facts) (old : Option Data) (env : String → Nat)
    {r : LawRef} (hn : ∀ f, r ≠ .field f) (c : Int) (h : String) :
    atomBound facts old env (.eqC r c) h = 0 := by
  cases r with
  | field f => exact absurd rfl (hn f)
  | _ => rfl

theorem atomBound_eqR_right (facts : Facts) (old : Option Data) (env : String → Nat)
    (f : String) {r : LawRef} (hn : ∀ g, r ≠ .field g) (h : String) :
    atomBound facts old env (.eqR (.field f) r) h =
      match readFactRef facts r with
      | some c => if h == f && 0 ≤ c then c.toNat else 0
      | none => 0 := by
  cases r with
  | field g => exact absurd rfl (hn g)
  | _ => rfl

theorem atomBound_eqR_left (facts : Facts) (old : Option Data) (env : String → Nat)
    {l : LawRef} (hn : ∀ f, l ≠ .field f) (g : String) (h : String) :
    atomBound facts old env (.eqR l (.field g)) h =
      match readFactRef facts l with
      | some c => if h == g && 0 ≤ c then c.toNat else 0
      | none => 0 := by
  cases l with
  | field f => exact absurd rfl (hn f)
  | _ => rfl

theorem atomBound_eqR_both (facts : Facts) (old : Option Data) (env : String → Nat)
    {l r : LawRef} (hnl : ∀ f, l ≠ .field f) (hnr : ∀ g, r ≠ .field g) (h : String) :
    atomBound facts old env (.eqR l r) h = 0 := by
  cases l with
  | field f => exact absurd rfl (hnl f)
  | _ =>
    cases r with
    | field g => exact absurd rfl (hnr g)
    | _ => rfl

theorem atomBound_leR_right (facts : Facts) (old : Option Data) (env : String → Nat)
    (f : String) {r : LawRef} (hn : ∀ g, r ≠ .field g) (h : String) :
    atomBound facts old env (.leR (.field f) r) h = 0 := by
  cases r with
  | field g => exact absurd rfl (hn g)
  | _ => rfl

theorem atomBound_leR_left (facts : Facts) (old : Option Data) (env : String → Nat)
    {l : LawRef} (hn : ∀ f, l ≠ .field f) (g : String) (h : String) :
    atomBound facts old env (.leR l (.field g)) h =
      match readFactRef facts l with
      | some c => if h == g && 0 ≤ c then c.toNat else 0
      | none => 0 := by
  cases l with
  | field f => exact absurd rfl (hn f)
  | _ => rfl

theorem atomBound_leR_both (facts : Facts) (old : Option Data) (env : String → Nat)
    {l r : LawRef} (hnl : ∀ f, l ≠ .field f) (hnr : ∀ g, r ≠ .field g) (h : String) :
    atomBound facts old env (.leR l r) h = 0 := by
  cases l with
  | field f => exact absurd rfl (hnl f)
  | _ =>
    cases r with
    | field g => exact absurd rfl (hnr g)
    | _ => rfl

theorem atomBound_leROff_right (facts : Facts) (old : Option Data) (env : String → Nat)
    (f : String) {r : LawRef} (hn : ∀ g, r ≠ .field g) (k : Int) (h : String) :
    atomBound facts old env (.leROff (.field f) r k) h = 0 := by
  cases r with
  | field g => exact absurd rfl (hn g)
  | _ => rfl

theorem atomBound_leROff_left (facts : Facts) (old : Option Data) (env : String → Nat)
    {l : LawRef} (hn : ∀ f, l ≠ .field f) (g : String) (k : Int) (h : String) :
    atomBound facts old env (.leROff l (.field g) k) h =
      match readFactRef facts l with
      | some c => if h == g && 0 ≤ c - k then (c - k).toNat else 0
      | none => 0 := by
  cases l with
  | field f => exact absurd rfl (hn f)
  | _ => rfl

theorem atomBound_leROff_both (facts : Facts) (old : Option Data) (env : String → Nat)
    {l r : LawRef} (hnl : ∀ f, l ≠ .field f) (hnr : ∀ g, r ≠ .field g) (k : Int) (h : String) :
    atomBound facts old env (.leROff l r k) h = 0 := by
  cases l with
  | field f => exact absurd rfl (hnl f)
  | _ =>
    cases r with
    | field g => exact absurd rfl (hnr g)
    | _ => rfl

/-- Every upward `atomBound` stays below any satisfying assignment `σ` on `keys`. -/
theorem atomBound_le_of_denote {keys : List String} {facts : Facts} {old : Option Data}
    {env σ : String → Nat} (hle : ∀ k ∈ keys, env k ≤ σ k) :
    ∀ {e : LawExpr},
      isDiffConstraintLaw e = true →
      (∀ f ∈ e.fields, f ∈ keys) →
      e.denote facts old (stateFromEnv keys σ) = true →
      ∀ h ∈ keys, atomBound facts old env e h ≤ σ h := by
  intro e hdiff hfields hden h hh
  induction e with
  | eqC ref c =>
    rcases lawRef_cases ref with ⟨f, rfl⟩ | hn
    · have hf : f ∈ keys := hfields f (by simp [LawExpr.fields, LawRef.fields])
      simp only [LawExpr.denote, read_field_stateFromEnv hf facts σ,
        decide_eq_true_eq, Option.some.injEq] at hden
      subst hden
      simp only [atomBound]
      by_cases hhf : h == f
      · have heq := beq_iff_eq.1 hhf; subst heq; simp
      · simp [hhf]
    · simp [atomBound_eqC_nonfield facts old env hn]
  | leC _ _ | inC _ _ => simp [atomBound]
  | eqR l r =>
    rcases lawRef_cases l with ⟨f, rfl⟩ | hnl
    · have hf : f ∈ keys := hfields f (by simp [LawExpr.fields, LawRef.fields])
      rcases lawRef_cases r with ⟨g, rfl⟩ | hnr
      · have hg : g ∈ keys := hfields g (by simp [LawExpr.fields, LawRef.fields])
        simp only [LawExpr.denote, read_field_stateFromEnv hf facts σ,
          read_field_stateFromEnv hg facts σ, decide_eq_true_eq, Int.ofNat_eq_natCast] at hden
        have hef := hle f hf
        have heg := hle g hg
        simp only [atomBound, Nat.max_le]
        constructor
        · by_cases hhf : h == f
          · have := beq_iff_eq.1 hhf; subst this; simp; omega
          · simp [hhf]
        · by_cases hhg : h == g
          · have := beq_iff_eq.1 hhg; subst this; simp; omega
          · simp [hhg]
      · have hr := isDiff_eqR_right hnr hdiff
        rw [atomBound_eqR_right facts old env f hnr h]
        simp only [LawExpr.denote, read_field_stateFromEnv hf facts σ,
          read_numericFactRef hr, readLabel_numericFactRef hr] at hden
        cases hrf : readFactRef facts r with
        | none =>
          rw [hrf] at hden
          cases fieldLabel f (stateFromEnv keys σ) <;> simp [LawRef.readLabel] at hden
        | some c =>
          rw [hrf] at hden
          simp only [decide_eq_true_eq] at hden
          subst hden
          simp only
          by_cases hhf : h == f
          · have := beq_iff_eq.1 hhf; subst this; simp
          · simp [hhf]
    · rcases lawRef_cases r with ⟨g, rfl⟩ | hnr
      · have hg : g ∈ keys := hfields g (by simp [LawExpr.fields, LawRef.fields])
        have hl := isDiff_eqR_left hnl hdiff
        rw [atomBound_eqR_left facts old env hnl g h]
        simp only [LawExpr.denote, read_field_stateFromEnv hg facts σ,
          read_numericFactRef hl, readLabel_numericFactRef hl] at hden
        cases hlf : readFactRef facts l with
        | none => rw [hlf] at hden; simp at hden
        | some c =>
          rw [hlf] at hden
          simp only [decide_eq_true_eq] at hden
          subst hden
          simp only
          by_cases hhg : h == g
          · have := beq_iff_eq.1 hhg; subst this; simp
          · simp [hhg]
      · simp [atomBound_eqR_both facts old env hnl hnr h]
  | leR l r =>
    rcases lawRef_cases l with ⟨f, rfl⟩ | hnl
    · have hf : f ∈ keys := hfields f (by simp [LawExpr.fields, LawRef.fields])
      rcases lawRef_cases r with ⟨g, rfl⟩ | hnr
      · have hg : g ∈ keys := hfields g (by simp [LawExpr.fields, LawRef.fields])
        simp only [LawExpr.denote, read_field_stateFromEnv hf facts σ,
          read_field_stateFromEnv hg facts σ, decide_eq_true_eq, Int.ofNat_eq_natCast] at hden
        have hef := hle f hf
        simp only [atomBound]
        by_cases hhg : h == g
        · have := beq_iff_eq.1 hhg; subst this; simp; omega
        · simp [hhg]
      · simp [atomBound_leR_right facts old env f hnr h]
    · rcases lawRef_cases r with ⟨g, rfl⟩ | hnr
      · have hg : g ∈ keys := hfields g (by simp [LawExpr.fields, LawRef.fields])
        have hl := isDiff_leR_left hnl hdiff
        rw [atomBound_leR_left facts old env hnl g h]
        simp only [LawExpr.denote, read_field_stateFromEnv hg facts σ,
          read_numericFactRef hl] at hden
        cases hlf : readFactRef facts l with
        | none => rw [hlf] at hden; simp at hden
        | some c =>
          rw [hlf] at hden
          simp only [decide_eq_true_eq, Int.ofNat_eq_natCast] at hden
          simp only
          by_cases hhg : h == g
          · have := beq_iff_eq.1 hhg; subst this
            simp only [beq_self_eq_true, Bool.true_and]
            split <;> omega
          · simp [hhg]
      · simp [atomBound_leR_both facts old env hnl hnr h]
  | leROff l r k =>
    rcases lawRef_cases l with ⟨f, rfl⟩ | hnl
    · have hf : f ∈ keys := hfields f (by simp [LawExpr.fields, LawRef.fields])
      rcases lawRef_cases r with ⟨g, rfl⟩ | hnr
      · have hg : g ∈ keys := hfields g (by simp [LawExpr.fields, LawRef.fields])
        simp only [LawExpr.denote, read_field_stateFromEnv hf facts σ,
          read_field_stateFromEnv hg facts σ, decide_eq_true_eq, Int.ofNat_eq_natCast] at hden
        have hef := hle f hf
        simp only [atomBound, Int.ofNat_eq_natCast]
        by_cases hhg : h == g
        · have := beq_iff_eq.1 hhg; subst this
          simp only [beq_self_eq_true, Bool.true_and]
          split <;> omega
        · simp [hhg]
      · simp [atomBound_leROff_right facts old env f hnr k h]
    · rcases lawRef_cases r with ⟨g, rfl⟩ | hnr
      · have hg : g ∈ keys := hfields g (by simp [LawExpr.fields, LawRef.fields])
        have hl := isDiff_leROff_left hnl hdiff
        rw [atomBound_leROff_left facts old env hnl g k h]
        simp only [LawExpr.denote, read_field_stateFromEnv hg facts σ,
          read_numericFactRef hl] at hden
        cases hlf : readFactRef facts l with
        | none => rw [hlf] at hden; simp at hden
        | some c =>
          rw [hlf] at hden
          simp only [decide_eq_true_eq, Int.ofNat_eq_natCast] at hden
          simp only
          by_cases hhg : h == g
          · have := beq_iff_eq.1 hhg; subst this
            simp only [beq_self_eq_true, Bool.true_and]
            split <;> omega
          · simp [hhg]
      · simp [atomBound_leROff_both facts old env hnl hnr k h]
  | monotone f =>
    have hf : f ∈ keys := hfields f (by simp [LawExpr.fields])
    simp only [atomBound]
    by_cases hhf : h == f
    · have := beq_iff_eq.1 hhf; subst this
      cases old with
      | none => simp [Obend.Spec.LawDial.oldNatAt]
      | some o =>
        simp only [LawExpr.denote, fieldOf_stateFromEnv_mem hf σ] at hden
        cases ho : fieldOf h o with
        | none => simp [ho] at hden
        | some b =>
          rw [ho] at hden
          simp only [decide_eq_true_eq, Int.ofNat_eq_natCast] at hden
          simp only [beq_self_eq_true, ite_true, Obend.Spec.LawDial.oldNatAt, Option.bind_some, ho]
          omega
    · simp [hhf]
  | writeOnce f =>
    have hf : f ∈ keys := hfields f (by simp [LawExpr.fields])
    simp only [atomBound]
    cases hob : old.bind (fieldOf f) with
    | none => simp
    | some b =>
      simp only [LawExpr.denote, hob, fieldOf_stateFromEnv_mem hf σ] at hden
      by_cases hhf : h == f
      · have := beq_iff_eq.1 hhf; subst this
        by_cases hb0 : (b == 0) = true
        · have hbEq : b = 0 := beq_iff_eq.1 hb0
          subst hbEq
          simp
        · have hbF : (b == 0) = false := Bool.eq_false_iff.2 hb0
          simp only [hbF, Bool.false_or, decide_eq_true_eq, Option.some.injEq] at hden
          subst hden
          simp only [beq_self_eq_true, Bool.true_and, int_ofNat_toNat]
          split <;> omega
      · simp [hhf]
  | and l r ihl ihr =>
    simp only [isDiffConstraintLaw, Bool.and_eq_true] at hdiff
    simp only [LawExpr.denote, Bool.and_eq_true] at hden
    have hfl : ∀ f ∈ l.fields, f ∈ keys := fun f hf => hfields f (by simp [LawExpr.fields, hf])
    have hfr : ∀ f ∈ r.fields, f ∈ keys := fun f hf => hfields f (by simp [LawExpr.fields, hf])
    exact Nat.max_le.2 ⟨ihl hdiff.1 hfl hden.1, ihr hdiff.2 hfr hden.2⟩
  | or _ _ | not _ | implies _ _ => simp [isDiffConstraintLaw] at hdiff

/-- Any fixpoint `res` of `atomBound` (`atomBound ... res e ≤ res` on `keys`) that lies below a
    satisfying assignment `σ` (`res ≤ σ` on `keys`) itself satisfies `e.denote`! -/
theorem denote_of_atomBound_fix {keys : List String} {facts : Facts} {old : Option Data}
    {res σ : String → Nat}
    (hle : ∀ k ∈ keys, res k ≤ σ k) :
    ∀ {e : LawExpr},
      isDiffConstraintLaw e = true →
      (∀ f ∈ e.fields, f ∈ keys) →
      (∀ h ∈ keys, atomBound facts old res e h ≤ res h) →
      e.denote facts old (stateFromEnv keys σ) = true →
      e.denote facts old (stateFromEnv keys res) = true := by
  intro e hdiff hfields hfix hden
  induction e with
  | eqC ref c =>
    rcases lawRef_cases ref with ⟨f, rfl⟩ | hn
    · have hf : f ∈ keys := hfields f (by simp [LawExpr.fields, LawRef.fields])
      simp only [LawExpr.denote, read_field_stateFromEnv hf facts σ,
        read_field_stateFromEnv hf facts res, decide_eq_true_eq, Option.some.injEq] at hden ⊢
      have hfx := hfix f hf
      have hleF := hle f hf
      subst hden
      simp only [atomBound, beq_self_eq_true, Bool.true_and, int_ofNat_nonneg, decide_true,
        ite_true, int_ofNat_toNat] at hfx
      have heq : res f = σ f := by omega
      rw [heq]
    · have hr := isDiff_eqC_nonfield hn hdiff
      simpa [LawExpr.denote, read_numericFactRef hr] using hden
  | leC ref c =>
    rcases lawRef_cases ref with ⟨f, rfl⟩ | hn
    · have hf : f ∈ keys := hfields f (by simp [LawExpr.fields, LawRef.fields])
      have hleF := hle f hf
      simp only [LawExpr.denote, read_field_stateFromEnv hf facts σ,
        read_field_stateFromEnv hf facts res, decide_eq_true_eq, Int.ofNat_eq_natCast] at hden ⊢
      omega
    · have hr := isDiff_leC_nonfield hn hdiff
      simpa [LawExpr.denote, read_numericFactRef hr] using hden
  | inC ref vs =>
    rcases lawRef_cases ref with ⟨f, rfl⟩ | hn
    · simp [isDiffConstraintLaw, isNumericFactRef] at hdiff
    · have hr := isDiff_inC_nonfield hn hdiff
      simpa [LawExpr.denote, read_numericFactRef hr] using hden
  | eqR l r =>
    rcases lawRef_cases l with ⟨f, rfl⟩ | hnl
    · have hf : f ∈ keys := hfields f (by simp [LawExpr.fields, LawRef.fields])
      rcases lawRef_cases r with ⟨g, rfl⟩ | hnr
      · have hg : g ∈ keys := hfields g (by simp [LawExpr.fields, LawRef.fields])
        have hfxF := hfix f hf
        have hfxG := hfix g hg
        simp only [atomBound, Nat.max_le] at hfxF hfxG
        have hgf : res g ≤ res f := by simpa using hfxF.1
        have hfg : res f ≤ res g := by simpa using hfxG.2
        simp only [LawExpr.denote, read_field_stateFromEnv hf facts res,
          read_field_stateFromEnv hg facts res, decide_eq_true_eq, Int.ofNat_eq_natCast]
        omega
      · have hr := isDiff_eqR_right hnr hdiff
        have hfxF := hfix f hf
        have hleF := hle f hf
        rw [atomBound_eqR_right facts old res f hnr f] at hfxF
        simp only [LawExpr.denote, read_field_stateFromEnv hf facts σ,
          read_field_stateFromEnv hf facts res, read_numericFactRef hr,
          readLabel_numericFactRef hr] at hden ⊢
        cases hrf : readFactRef facts r with
        | none =>
          rw [hrf] at hden
          cases fieldLabel f (stateFromEnv keys σ) <;> simp [LawRef.readLabel] at hden
        | some c =>
          rw [hrf] at hden hfxF
          simp only [decide_eq_true_eq] at hden ⊢
          subst hden
          simp only [beq_self_eq_true, Bool.true_and, int_ofNat_nonneg, decide_true, ite_true,
            int_ofNat_toNat] at hfxF
          have heq : res f = σ f := by omega
          rw [heq]
    · rcases lawRef_cases r with ⟨g, rfl⟩ | hnr
      · have hg : g ∈ keys := hfields g (by simp [LawExpr.fields, LawRef.fields])
        have hl := isDiff_eqR_left hnl hdiff
        have hfxG := hfix g hg
        have hleG := hle g hg
        rw [atomBound_eqR_left facts old res hnl g g] at hfxG
        simp only [LawExpr.denote, read_field_stateFromEnv hg facts σ,
          read_field_stateFromEnv hg facts res, read_numericFactRef hl,
          readLabel_numericFactRef hl] at hden ⊢
        cases hlf : readFactRef facts l with
        | none => rw [hlf] at hden; simp at hden
        | some c =>
          rw [hlf] at hden hfxG
          simp only [decide_eq_true_eq] at hden ⊢
          subst hden
          simp only [beq_self_eq_true, Bool.true_and, int_ofNat_nonneg, decide_true, ite_true,
            int_ofNat_toNat] at hfxG
          have heq : res g = σ g := by omega
          rw [heq]
      · obtain ⟨hl, hr⟩ := isDiff_eqR_both hnl hnr hdiff
        simpa [LawExpr.denote, read_numericFactRef hl, read_numericFactRef hr,
          readLabel_numericFactRef hl, readLabel_numericFactRef hr] using hden
  | leR l r =>
    rcases lawRef_cases l with ⟨f, rfl⟩ | hnl
    · have hf : f ∈ keys := hfields f (by simp [LawExpr.fields, LawRef.fields])
      rcases lawRef_cases r with ⟨g, rfl⟩ | hnr
      · have hg : g ∈ keys := hfields g (by simp [LawExpr.fields, LawRef.fields])
        have hfxG := hfix g hg
        simp only [atomBound, beq_self_eq_true, ite_true] at hfxG
        simp only [LawExpr.denote, read_field_stateFromEnv hf facts res,
          read_field_stateFromEnv hg facts res, decide_eq_true_eq, Int.ofNat_eq_natCast]
        omega
      · have hr := isDiff_leR_right hnr hdiff
        have hleF := hle f hf
        simp only [LawExpr.denote, read_field_stateFromEnv hf facts σ,
          read_field_stateFromEnv hf facts res, read_numericFactRef hr] at hden ⊢
        cases hrf : readFactRef facts r with
        | none => rw [hrf] at hden; simp at hden
        | some c =>
          rw [hrf] at hden
          simp only [decide_eq_true_eq, Int.ofNat_eq_natCast] at hden ⊢
          omega
    · rcases lawRef_cases r with ⟨g, rfl⟩ | hnr
      · have hg : g ∈ keys := hfields g (by simp [LawExpr.fields, LawRef.fields])
        have hl := isDiff_leR_left hnl hdiff
        have hfxG := hfix g hg
        rw [atomBound_leR_left facts old res hnl g g] at hfxG
        simp only [LawExpr.denote, read_field_stateFromEnv hg facts σ,
          read_field_stateFromEnv hg facts res, read_numericFactRef hl] at hden ⊢
        cases hlf : readFactRef facts l with
        | none => rw [hlf] at hden; simp at hden
        | some c =>
          rw [hlf] at hden hfxG
          simp only [decide_eq_true_eq, Int.ofNat_eq_natCast] at hden ⊢
          simp only [beq_self_eq_true, Bool.true_and] at hfxG
          by_cases hc : 0 ≤ c
          · simp only [hc, decide_true, ite_true] at hfxG; omega
          · omega
      · obtain ⟨hl, hr⟩ := isDiff_leR_both hnl hnr hdiff
        simpa [LawExpr.denote, read_numericFactRef hl, read_numericFactRef hr] using hden
  | leROff l r k =>
    rcases lawRef_cases l with ⟨f, rfl⟩ | hnl
    · have hf : f ∈ keys := hfields f (by simp [LawExpr.fields, LawRef.fields])
      rcases lawRef_cases r with ⟨g, rfl⟩ | hnr
      · have hg : g ∈ keys := hfields g (by simp [LawExpr.fields, LawRef.fields])
        have hfxG := hfix g hg
        simp only [atomBound, beq_self_eq_true, Bool.true_and, Int.ofNat_eq_natCast] at hfxG
        simp only [LawExpr.denote, read_field_stateFromEnv hf facts res,
          read_field_stateFromEnv hg facts res, decide_eq_true_eq, Int.ofNat_eq_natCast]
        by_cases hlb : 0 ≤ (res f : Int) - k
        · simp only [hlb, decide_true, ite_true] at hfxG; omega
        · omega
      · have hr := isDiff_leROff_right hnr hdiff
        have hleF := hle f hf
        simp only [LawExpr.denote, read_field_stateFromEnv hf facts σ,
          read_field_stateFromEnv hf facts res, read_numericFactRef hr] at hden ⊢
        cases hrf : readFactRef facts r with
        | none => rw [hrf] at hden; simp at hden
        | some c =>
          rw [hrf] at hden
          simp only [decide_eq_true_eq, Int.ofNat_eq_natCast] at hden ⊢
          omega
    · rcases lawRef_cases r with ⟨g, rfl⟩ | hnr
      · have hg : g ∈ keys := hfields g (by simp [LawExpr.fields, LawRef.fields])
        have hl := isDiff_leROff_left hnl hdiff
        have hfxG := hfix g hg
        rw [atomBound_leROff_left facts old res hnl g k g] at hfxG
        simp only [LawExpr.denote, read_field_stateFromEnv hg facts σ,
          read_field_stateFromEnv hg facts res, read_numericFactRef hl] at hden ⊢
        cases hlf : readFactRef facts l with
        | none => rw [hlf] at hden; simp at hden
        | some c =>
          rw [hlf] at hden hfxG
          simp only [decide_eq_true_eq, Int.ofNat_eq_natCast] at hden ⊢
          simp only [beq_self_eq_true, Bool.true_and] at hfxG
          by_cases hc : 0 ≤ c - k
          · simp only [hc, decide_true, ite_true] at hfxG; omega
          · omega
      · obtain ⟨hl, hr⟩ := isDiff_leROff_both hnl hnr hdiff
        simpa [LawExpr.denote, read_numericFactRef hl, read_numericFactRef hr] using hden
  | monotone f =>
    have hf : f ∈ keys := hfields f (by simp [LawExpr.fields])
    cases old with
    | none => rfl
    | some o =>
      have hfxF := hfix f hf
      simp only [LawExpr.denote, fieldOf_stateFromEnv_mem hf σ,
        fieldOf_stateFromEnv_mem hf res] at hden ⊢
      cases ho : fieldOf f o with
      | none => rw [ho] at hden; simp at hden
      | some b =>
        have hb0 : 0 ≤ b := fieldOf_nonneg ho
        rw [ho] at hden
        simp only [atomBound, beq_self_eq_true, ite_true, Obend.Spec.LawDial.oldNatAt,
          Option.bind_some, ho] at hfxF
        simp only [decide_eq_true_eq, Int.ofNat_eq_natCast] at hden ⊢
        omega
  | writeOnce f =>
    have hf : f ∈ keys := hfields f (by simp [LawExpr.fields])
    have hfxF := hfix f hf
    have hleF := hle f hf
    simp only [LawExpr.denote] at hden ⊢
    cases hob : old.bind (fieldOf f) with
    | some b =>
      rw [hob] at hden
      rw [fieldOf_stateFromEnv_mem hf σ] at hden
      rw [fieldOf_stateFromEnv_mem hf res]
      by_cases hb0 : (b == 0) = true
      · simp [hb0]
      · have hbF : (b == 0) = false := Bool.eq_false_iff.2 hb0
        simp only [hbF, Bool.false_or, decide_eq_true_eq, Option.some.injEq] at hden ⊢
        subst hden
        have hbne : (Int.ofNat (σ f) != 0) = true := by
          rw [bne_iff_ne]
          intro heq
          exact hb0 (beq_iff_eq.2 heq)
        simp only [atomBound, hob, beq_self_eq_true, hbne, Bool.true_and, ite_true,
          int_ofNat_toNat] at hfxF
        have heq : res f = σ f := by omega
        rw [heq]
    | none =>
      rw [hob] at hden
      have hlσ : fieldLabel f (stateFromEnv keys σ) = none :=
        firstField_stateFromEnv_not_label f σ keys
      have hlr : fieldLabel f (stateFromEnv keys res) = none :=
        firstField_stateFromEnv_not_label f res keys
      cases hobL : old.bind (fieldLabel f) with
      | none => rfl
      | some s =>
        rw [hobL] at hden
        simpa [hlσ, hlr] using hden
  | and l r ihl ihr =>
    simp only [isDiffConstraintLaw, Bool.and_eq_true] at hdiff
    simp only [LawExpr.denote, Bool.and_eq_true] at hden ⊢
    have hfl : ∀ f ∈ l.fields, f ∈ keys := fun f hf => hfields f (by simp [LawExpr.fields, hf])
    have hfr : ∀ f ∈ r.fields, f ∈ keys := fun f hf => hfields f (by simp [LawExpr.fields, hf])
    have hfxL : ∀ h ∈ keys, atomBound facts old res l h ≤ res h :=
      fun h hh => (Nat.max_le.1 (hfix h hh)).1
    have hfxR : ∀ h ∈ keys, atomBound facts old res r h ≤ res h :=
      fun h hh => (Nat.max_le.1 (hfix h hh)).2
    exact ⟨ihl hdiff.1 hfl hfxL hden.1, ihr hdiff.2 hfr hfxR hden.2⟩
  | or _ _ | not _ | implies _ _ => simp [isDiffConstraintLaw] at hdiff

theorem foldl_max_ge_init (g : String × LawExpr → Nat) :
    ∀ (ps : List (String × LawExpr)) (acc : Nat),
      acc ≤ ps.foldl (fun a p => max a (g p)) acc
  | [], acc => Nat.le_refl acc
  | p :: ps, acc => Nat.le_trans (Nat.le_max_left _ _) (foldl_max_ge_init g ps (max acc (g p)))

theorem foldl_max_ge_mem (g : String × LawExpr → Nat) :
    ∀ (ps : List (String × LawExpr)) (acc : Nat) {p : String × LawExpr},
      p ∈ ps → g p ≤ ps.foldl (fun a q => max a (g q)) acc
  | [], _, _, h => nomatch h
  | q :: ps, acc, p, h => by
    rcases List.mem_cons.1 h with rfl | hrest
    · exact Nat.le_trans (Nat.le_max_right _ _) (foldl_max_ge_init g ps _)
    · exact foldl_max_ge_mem g ps (max acc (g q)) hrest

theorem foldl_max_le (g : String × LawExpr → Nat) {ub : Nat} :
    ∀ (ps : List (String × LawExpr)) {acc : Nat},
      acc ≤ ub → (∀ p ∈ ps, g p ≤ ub) →
      ps.foldl (fun a p => max a (g p)) acc ≤ ub
  | [], _, hacc, _ => hacc
  | p :: ps, _, hacc, hall =>
    foldl_max_le g ps (Nat.max_le.2 ⟨hacc, hall p List.mem_cons_self⟩)
      (fun q hq => hall q (List.mem_cons_of_mem _ hq))

theorem raiseLinEnv_ge (facts : Facts) (old : Option Data) (lin : List (String × LawExpr))
    (env : String → Nat) (h : String) :
    env h ≤ raiseLinEnv facts old lin env h :=
  foldl_max_ge_init (fun p => atomBound facts old env p.2 h) lin (env h)

theorem raiseLinEnv_le_of_denote {keys : List String} {facts : Facts} {old : Option Data}
    {lin : List (String × LawExpr)} {env σ : String → Nat}
    (hfrag : ∀ p ∈ lin, isDiffConstraintLaw p.2 = true ∧ ∀ f ∈ p.2.fields, f ∈ keys)
    (hden : ∀ p ∈ lin, p.2.denote facts old (stateFromEnv keys σ) = true)
    (hle : ∀ k ∈ keys, env k ≤ σ k) :
    ∀ h ∈ keys, raiseLinEnv facts old lin env h ≤ σ h := by
  intro h hh
  apply foldl_max_le (fun p => atomBound facts old env p.2 h) lin (hle h hh)
  intro p hp
  exact atomBound_le_of_denote hle (hfrag p hp).1 (hfrag p hp).2 (hden p hp) h hh

theorem map_sum_le_of_le {f g : String → Nat} :
    ∀ (ks : List String), (∀ k ∈ ks, f k ≤ g k) → (ks.map f).sum ≤ (ks.map g).sum
  | [], _ => Nat.le_refl 0
  | k :: ks, h => by
    have hk := h k List.mem_cons_self
    have hks := map_sum_le_of_le ks (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp only [List.map_cons, List.sum_cons]
    omega

theorem map_sum_lt_of_lt {f g : String → Nat} :
    ∀ (ks : List String),
      (∀ k ∈ ks, f k ≤ g k) →
      (∃ k₀ ∈ ks, f k₀ < g k₀) →
      (ks.map f).sum < (ks.map g).sum
  | [], _, ⟨_, hm, _⟩ => nomatch hm
  | k :: ks, hle, ⟨k₀, hm, hlt⟩ => by
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.1 hm with rfl | hrest
    · have hks := map_sum_le_of_le ks (fun x hx => hle x (List.mem_cons_of_mem _ hx))
      omega
    · have hk := hle k List.mem_cons_self
      have hks := map_sum_lt_of_lt ks (fun x hx => hle x (List.mem_cons_of_mem _ hx)) ⟨k₀, hrest, hlt⟩
      omega

theorem map_sum_le_cap {σ : String → Nat} {cap : Nat} :
    ∀ (ks : List String), (∀ k ∈ ks, σ k ≤ cap) → (ks.map σ).sum ≤ ks.length * cap
  | [], _ => by simp
  | k :: ks, h => by
    have hk := h k List.mem_cons_self
    have hks := map_sum_le_cap ks (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
    omega

theorem map_zero_sum : ∀ (ks : List String), (ks.map fun _ => 0).sum = 0
  | [] => rfl
  | _ :: ks => by simp [map_zero_sum ks]

theorem kleeneLoop_reaches_fixpoint
    {keys : List String} {facts : Facts} {old : Option Data}
    {lin : List (String × LawExpr)} {σ : String → Nat} {cap : Nat}
    (hfrag : ∀ p ∈ lin, isDiffConstraintLaw p.2 = true ∧ ∀ f ∈ p.2.fields, f ∈ keys)
    (hden : ∀ p ∈ lin, p.2.denote facts old (stateFromEnv keys σ) = true)
    (hcap : ∀ k ∈ keys, σ k ≤ cap) :
    ∀ (fuel : Nat) (env : String → Nat),
      (∀ k ∈ keys, env k ≤ σ k) →
      keys.length * cap < (keys.map env).sum + fuel →
      let res := kleeneLoop keys facts old lin fuel env
      (∀ k ∈ keys, res k ≤ σ k) ∧
      (∀ k ∈ keys, raiseLinEnv facts old lin res k = res k) := by
  intro fuel
  induction fuel with
  | zero =>
    intro env hle hpot
    have hsumLe : (keys.map env).sum ≤ keys.length * cap :=
      Nat.le_trans (map_sum_le_of_le keys hle) (map_sum_le_cap keys hcap)
    omega
  | succ fuel ih =>
    intro env hle hpot
    simp only [kleeneLoop]
    split
    · next hall =>
      refine ⟨hle, fun k hk => ?_⟩
      exact beq_iff_eq.1 (List.all_eq_true.1 hall k hk)
    · next hnotAll =>
      let next := raiseLinEnv facts old lin env
      have hnextLe : ∀ k ∈ keys, next k ≤ σ k :=
        raiseLinEnv_le_of_denote hfrag hden hle
      have hexDiff : ∃ k₀ ∈ keys, env k₀ < next k₀ := by
        have hfalse : keys.all (fun k => next k == env k) = false :=
          Bool.eq_false_iff.2 hnotAll
        obtain ⟨k₀, hk₀, hneqB⟩ := List.all_eq_false.1 hfalse
        have hneq : next k₀ ≠ env k₀ := by
          intro heq; simp [heq] at hneqB
        have hge : env k₀ ≤ next k₀ := raiseLinEnv_ge facts old lin env k₀
        exact ⟨k₀, hk₀, by omega⟩
      have hsumLt : (keys.map env).sum < (keys.map next).sum :=
        map_sum_lt_of_lt keys (fun k _ => raiseLinEnv_ge facts old lin env k) hexDiff
      exact ih next hnextLe (by omega)

/-- **Completeness of `synthesizePassingDelta` on the Bounded `LawDial` Fragment**:
    Whenever every law in `lin` belongs to `isDiffConstraintLaw` with fields in `keys`, if **any**
    natural-field assignment `σ : String → Nat` bounded by `cap` (`∀ k ∈ keys, σ k ≤ cap`) satisfies
    `lin` at `occ`, `synthesizePassingDelta` is guaranteed to return `some delta`! -/
theorem synthesizePassingDelta_complete
    {keys : List String} {lin : List (String × LawExpr)}
    {facts : Facts} {o cur : Data} {occ : Vault.Occ} {cap : Nat}
    (hfrag : ∀ p ∈ lin, isDiffConstraintLaw p.2 = true ∧ ∀ f ∈ p.2.fields, f ∈ keys)
    {σ : String → Nat}
    (hcap : ∀ k ∈ keys, σ k ≤ cap)
    (hsat : ∀ p ∈ lin, p.2.denote facts (occ.old o (stateFromEnv keys σ)) (stateFromEnv keys σ) = true) :
    ∃ delta, synthesizePassingDelta keys lin facts o cur occ cap = some delta := by
  have hdenOld : ∀ p ∈ lin, p.2.denote facts (effectiveOldForOcc occ o) (stateFromEnv keys σ) = true := by
    intro p hp
    rw [← denote_occ_eq_effectiveOld keys facts o occ σ (hfrag p hp).2]
    exact hsat p hp
  have hzeroSum : (keys.map (fun _ : String => 0)).sum = 0 := map_zero_sum keys
  obtain ⟨hresLe, hresFix⟩ :=
    kleeneLoop_reaches_fixpoint hfrag hdenOld hcap (keys.length * cap + 1) (fun _ => 0)
      (fun _ _ => Nat.zero_le _) (by omega)
  let kleeneEnv := kleeneLoop keys facts (effectiveOldForOcc occ o) lin (keys.length * cap + 1) (fun _ => 0)
  have hallHold : allLawsHold lin facts o (stateFromEnv keys kleeneEnv) occ = true := by
    rw [allLawsHold, List.all_eq_true]
    intro p hp
    rw [denote_occ_eq_effectiveOld keys facts o occ kleeneEnv (hfrag p hp).2]
    refine denote_of_atomBound_fix hresLe (hfrag p hp).1 (hfrag p hp).2 ?_ (hdenOld p hp)
    intro h hh
    have hge := foldl_max_ge_mem (fun q => atomBound facts (effectiveOldForOcc occ o) kleeneEnv q.2 h) lin (kleeneEnv h) hp
    exact Nat.le_trans hge (Nat.le_of_eq (hresFix h hh))
  unfold synthesizePassingDelta
  let dialEnv : String → Nat :=
    match Obend.Spec.LawDial.solveLawWitness keys (conjLaws lin) facts (effectiveOldForOcc occ o) with
    | some w => Vault.natAt w
    | none => fun _ => 0
  change ∃ delta,
    (if allLawsHold lin facts o (stateFromEnv keys dialEnv) occ then
      some (mkPassingDelta keys cur dialEnv)
    else if allLawsHold lin facts o (stateFromEnv keys kleeneEnv) occ then
      some (mkPassingDelta keys cur kleeneEnv)
    else none) = some delta
  by_cases h1 : allLawsHold lin facts o (stateFromEnv keys dialEnv) occ = true
  · exact ⟨mkPassingDelta keys cur dialEnv, by simp [h1]⟩
  · exact ⟨mkPassingDelta keys cur kleeneEnv, by simp [h1, hallHold]⟩

/-- **Unsatisfiability Certificate (`THESIS.md:56-57`)**:
    When `synthesizePassingDelta` returns `none` on the `isDiffConstraintLaw` fragment, **no**
    natural-field assignment bounded by `cap` satisfies `lin`! -/
theorem synthesizePassingDelta_none_unsat
    {keys : List String} {lin : List (String × LawExpr)}
    {facts : Facts} {o cur : Data} {occ : Vault.Occ} {cap : Nat}
    (hfrag : ∀ p ∈ lin, isDiffConstraintLaw p.2 = true ∧ ∀ f ∈ p.2.fields, f ∈ keys)
    (hnone : synthesizePassingDelta keys lin facts o cur occ cap = none)
    (σ : String → Nat) (hcap : ∀ k ∈ keys, σ k ≤ cap) :
    ¬ (∀ p ∈ lin, p.2.denote facts (occ.old o (stateFromEnv keys σ)) (stateFromEnv keys σ) = true) := by
  intro hsat
  obtain ⟨delta, hsome⟩ := synthesizePassingDelta_complete hfrag hcap hsat
  rw [hnone] at hsome
  cases hsome

-- Concrete sanity checks ensuring every hypothesis ledger premise is positively inhabited:
example :
    (synthesizePassingDelta ["a", "b"]
      [("coupled", .and (.and (.monotone "a") (.leR (.field "a") (.field "b"))) (.leC (.field "b") 10))]
      { subject := some 0, caller := none, height := 0, turn := 0 }
      (Vault.stateOf ["a", "b"] [("a", 4), ("b", 1)])
      (Vault.stateOf ["a", "b"] [("a", 2), ("b", 1)])
      .write 10).isSome = true := rfl

example :
    synthesizePassingDelta ["a"]
      [("contradiction", .and (.eqC (.field "a") 5) (.leC (.field "a") 3))]
      { subject := some 0, caller := none, height := 0, turn := 0 }
      (Vault.stateOf ["a"] [("a", 0)])
      (Vault.stateOf ["a"] [("a", 0)])
      .write 10 = none := rfl

end Obend.Vault.SwarmLedgerSeams
end
