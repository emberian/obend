module
/-
# BookLinkAndSuperRefinesTest — End-to-End Verification of Chasm C2

Integrates and verifies all four Chasm-C2 modules together:
1. **`Obend.Paco.GPaco`**: Parameterized (`paco`) and Generalized Parameterized Coinduction
   (`gpaco`, `gpaco_clo`, `companion`) over `MonoRel α` without Mathlib or custom axioms.
2. **`Obend.Leaf.LinkSpecialize`**: Whole-book `link` specialization equivalence
   (`specializeBook_link_sound : WellPinnedBook B pins → (specializeBook B pins).link ≈b B.link`),
   multi-argument method-call equivalence across the `fix` knot, canonical self-pinning, and
   lying-pin refutations.
3. **`Obend.Logic.SuperRefines`**: Vertical `super.m` unfolding (`superSymUnfold`,
   `superClaimResolver`), `superClaim_sound`, receiver-qualified `T3_super_claim_frame`, and
   universal separation from inert-`super` `claimCheck`.
4. **`Obend.Slot.SupportSheaf`**: Unified `SupportSheaf` + Clarke coalgebraic Delta-Lens
   `RepairableSheaf` across `Obend.Slot`, `Obend.Intention` (`RegPin`), and `SuperClaimCert`,
   proving $O(1)$ certificate pushforward without re-running `superClaimCheck`.
5. **Capstone 4-Module Pipeline**: Vertical `super.m` spec proof → $O(1)$ `SupportSheaf` overlay
   pushforward → `Leaf.emit` book emission → `LinkSpecialize` + `GPaco` whole-book specialization
   equivalence `(specializeBook (emit C) pins).link ≈b (emit C).link` and method-call agreement
   with `C.object`.
-/

public import Obend.Paco.GPaco
public import Obend.Leaf.LinkSpecialize
public import Obend.Logic.Obligation
public import Obend.Slot.SupportSheaf
public import Obend.Tactic.Tooth
import all Obend.Paco.GPaco
import all Obend.Leaf.LinkSpecialize
import all Obend.Logic.Obligation
import all Obend.Logic.Frame
import all Obend.Slot.SupportSheaf

public section

namespace Obend.Tests.Metasystem.BookLinkAndSuperRefinesTest

open Obend.Core.Term
open Obend.Core.Data (Data)
open Obend.Equiv
open Obend.Logic
open Obend.Leaf
open Obend.Leaf.Static
open Obend.Leaf.LinkSpecialize
open Obend.Paco
open Obend.Slot.SupportSheaf

set_option autoImplicit false

/-! ## 1. `Obend.Paco.GPaco` — Coinduction, Up-To Closures & Companion -/

theorem test_gpaco_laws {α : Type} (F : MonoRel α) (r g : Rel α) :
    gpaco F ⊥ ⊥ = F.gfp ∧
    paco F r = F (upaco F r) ∧
    gpaco F r g ≤ F (gupaco F r g) ⊔ r ∧
    gpaco F r g = F (gupaco F r g) ⊔ r ∧
    gupaco_clo F (companion F) r = companion F r ∧
    gpaco_clo F (companion F) ⊥ ⊥ = F.gfp :=
  ⟨gpaco_init F, paco_fixed F r, gpaco_unfold F r g, gpaco_step F r g,
    companion_gupaco_eq F r,
    gpaco_clo_init F (companion F) (companion_mono F) (companion_compat F)⟩

example :
    orbitBisimF.gfp 0 2 ∧ ¬ orbitBisimF.gfp 0 1 :=
  ⟨orbit_zero_two_bisim_witness, orbit_zero_one_not_bisim⟩

/-! ## 2. `Obend.Leaf.LinkSpecialize` — Whole-Book `.link ≈b` & Lying-Pin Refutation -/

theorem test_whole_book_link_equivalence {B : Book} {pins : List LeafPin}
    (hw : WellPinnedBook B pins) (m : String) (args : List Term) (obs : Observation) :
    (specializeBook B pins).link ≈b B.link ∧
    apps (.get (specializeBook B pins).link m) args ≈b apps (.get B.link m) args ∧
    (Halts (apps (.get (specializeBook B pins).link m) args) obs ↔
      Halts (apps (.get B.link m) args) obs) :=
  ⟨specializeBook_link_sound hw,
   specializeBook_call_bequiv hw m args,
   specializeBook_call_halts_iff hw m args obs⟩

example :
    (specializeBook mutualCountdownBook honestMutualPins).link ≈b mutualCountdownBook.link ∧
    Evaluates (.app (.get (specializeBook mutualCountdownBook honestMutualPins).link "evenAcc") (.nat 4))
      (.nat 14) ∧
    ¬ ((specializeBook mutualCountdownBook lyingMutualPins).link ≈b mutualCountdownBook.link) ∧
    ¬ WellPinnedBook mutualCountdownBook lyingMutualPins :=
  ⟨mutualCountdown_specialized_witness.1,
   mutualCountdown_specialized_witness.2.2.2,
   lyingMutualPins_breaks_link_bequiv,
   lyingMutualPins_not_wellPinned.2⟩

/-! ## 3. `Obend.Logic.SuperRefines` — Vertical `super.m` Refinement & `T3_super_claim_frame` -/

theorem test_superRefines_and_separation (k : Nat) (steps : List RStep) :
    claimCheck k verticalLimitClaimObj steps ≠ .ok ∧
    superClaimCheck 10 verticalLimitClaimObj verticalLimitSteps = .ok ∧
    Holds (instantiateClaim verticalLimitClaimObj.claim verticalComp 0) [] ∧
    superClaimCheck 15 { verticalOpenRecClaimObj with comp := wrappedVerticalComp, layer := 1 }
      verticalOpenRecSteps = .ok :=
  ⟨verticalLimit_impossible_claimCheck k steps,
   verticalLimit_superClaim_accepted.1,
   verticalLimit_superClaim_accepted.2,
   verticalOpenRec_frame_transport_accepted.2.2⟩

example :
    superClaimCheck 10 verticalLimitClaimObj wrongSuperProviderSteps =
      .refused (.rewrite .stepMismatch) [0] :=
  wrongSuperProvider_refused

/-! ## 4. `Obend.Slot.SupportSheaf` — Unified Sheaf & Coalgebraic Delta-Lens Fast-Path -/

theorem test_repairable_sheaf_fastpath {W Δ Fact Obj : Type}
    [S : RepairableSheaf W Δ Fact Obj] {w : W} {δ₂ δ₁ : Δ} {x : Obj}
    (hu : S.usable w x = true)
    (hd₁ : disjoint (S := S) (S.changed δ₁) (S.supports x) = true)
    (hd₂ : disjoint (S := S) (S.changed δ₂) (S.supports x) = true) :
    S.transport S.idDelta x = .ok x ∧
    S.transport (S.compDelta δ₂ δ₁) x = .ok x ∧
    S.usable (S.applyDelta (S.compDelta δ₂ δ₁) w) x = true := by
  obtain ⟨_, htr, hus⟩ := disjoint_comp_transport_sound hu hd₁ hd₂
  exact ⟨transport_id x, htr, hus⟩

example :
    RepairableSheaf.transport (W := KeyedWorld String Nat) conflictingKeyedDelta
      (⟨8080⟩ : SlotFill portSlot) = .error "port" ∧
    transportRegPin compatibleMinorDelta codecPinV10 = .ok ⟨"codec", 1, ⟨1, 1, 222⟩⟩ ∧
    transportRegPin breakingMajorDelta codecPinV10 = .error (.majorBroken "codec" 1 2) ∧
    transportSuperCert auditOverlayDelta verticalOpenRecCert = .ok verticalOpenRecCert ∧
    transportSuperCert conflictingScaleOverlayDelta verticalOpenRecCert =
      .error (.overriddenSelf "ScaleOverride" "scale") :=
  ⟨slotConflict_refused,
   regPin_active_rebind_witness.2.1,
   regPin_majorBreak_refused,
   superCert_overlay_fastpath_witness.2.2.1,
   superCert_selfOverride_refused⟩

/-! ## 5. Capstone 4-Module Pipeline: `SuperRefines` → `SupportSheaf` → `Emit` → `LinkSpecialize` + `GPaco` -/

/-- **Universal End-to-End Composition-to-Specialized-Book Theorem**:
For any closed `Composition` `C` (`C.closedB = true`) and any `WellPinnedBook (emit C) pins`,
1. `(specializeBook (emit C) pins).link ≈b C.flatten` (`emit_sound` + `specializeBook_link_sound`), and
2. every multi-argument method call on `(specializeBook (emit C) pins).link` is reflectively
   contextually equivalent (`≈b`) to the method call on `C.object`! -/
theorem specializedEmit_call_bequiv_object {C : Composition}
    (hc : C.closedB = true) {pins : List LeafPin}
    (hw : WellPinnedBook (emit C) pins) (m : String) (args : List Term) :
    (specializeBook (emit C) pins).link ≈b C.flatten ∧
    apps (.get (specializeBook (emit C) pins).link m) args ≈b
      apps (.get C.object m) args := by
  have hlink : (specializeBook (emit C) pins).link ≈b (emit C).link :=
    specializeBook_link_sound hw
  have hflat : (specializeBook (emit C) pins).link ≈b C.flatten :=
    hlink.trans (emit_sound C)
  have hmem : .get (specializeBook (emit C) pins).link m ≈b .get C.object m :=
    (bequiv_get hlink m).trans (book_sound C hc m)
  exact ⟨hflat, bequiv_apps_fn hmem args⟩

/-- Non-flat telemetry overlay layer adding `"telemetryTag"` without overriding `"scale"` or `"apply"`. -/
def telemetryLayer : Layer where
  name := "Telemetry"
  metadata := .inject "declared" (.record [("name", .label "Telemetry")])
  fields := [("telemetryTag", .nat 7)]

def telemetryOverlay : OverlayDelta where
  steps := [⟨telemetryLayer, rfl⟩]

/-- 3-layer pointed composition obtained by pushing `verticalPointedOrigin` across `telemetryOverlay`. -/
def telemetryPointedComp : PointedComp :=
  applyOverlay telemetryOverlay verticalPointedOrigin

/-- Emitted `Book` of the 3-layer vertical-refinement stack `telemetryPointedComp.toComp`. -/
def telemetryBook : Book :=
  emit telemetryPointedComp.toComp

/-- Served pin specializing `"scale"` (`3`) inside `telemetryBook`. -/
def telemetryPins : List LeafPin :=
  [⟨.layer "scale", .nat 3⟩]

/-- **Full 4-Module Integration Witness**:
1. `verticalOpenRecCert` transports in $O(1)$ across `telemetryOverlay` via `SupportSheaf`
   (`transportSuperCert` returns `.ok verticalOpenRecCert`), establishing `claimMeaning` on the
   3-layer `telemetryPointedComp` without re-running `superClaimCheck`.
2. `telemetryBook = emit telemetryPointedComp.toComp` with `telemetryPins` satisfies `WellPinnedBook`
   (via `LinkSpecialize` + `GPaco`).
3. `(specializeBook telemetryBook telemetryPins).link ≈b telemetryBook.link` AND calling `"apply"` at `5`
   on the specialized book's `.link` is `≈b` calling `"apply"` at `5` on `telemetryPointedComp.toComp.object`
   and evaluates to `.nat 16` (`3 * 5 + 1`). -/
theorem capstone_pipeline_witness :
    transportSuperCert telemetryOverlay verticalOpenRecCert = .ok verticalOpenRecCert ∧
    claimMeaning (telemetryPointedComp.claimObj
      verticalOpenRecClaimObj.claim verticalOpenRecClaimObj.arity) ∧
    (specializeBook telemetryBook telemetryPins).link ≈b telemetryBook.link ∧
    apps (.get (specializeBook telemetryBook telemetryPins).link "apply") [.nat 5] ≈b
      apps (.get telemetryPointedComp.toComp.object "apply") [.nat 5] ∧
    Evaluates (.app (.get (specializeBook telemetryBook telemetryPins).link "apply") (.nat 5))
      (.nat 16) := by
  have hOrigin : superClaimCheck 15
      (verticalPointedOrigin.claimObj verticalOpenRecClaimObj.claim verticalOpenRecClaimObj.arity)
      verticalOpenRecSteps = .ok :=
    verticalOpenRec_frame_transport_accepted.1
  have htr : transportSuperCert telemetryOverlay verticalOpenRecCert = .ok verticalOpenRecCert := by
    rw [transportSuperCert_verticalOpenRecCert]
    rfl
  have hwf : (telemetryPointedComp.claimObj
      verticalOpenRecClaimObj.claim verticalOpenRecClaimObj.arity).wellFormed = true := by
    decide +kernel
  have hmeaning : claimMeaning (telemetryPointedComp.claimObj
      verticalOpenRecClaimObj.claim verticalOpenRecClaimObj.arity) :=
    (superCert_transport_sound hOrigin htr hwf).2.2
  have hclosed : telemetryPointedComp.toComp.closedB = true := by
    decide +kernel
  have hwp : WellPinnedBook telemetryBook telemetryPins :=
    wellPinnedBook_of_bool (fuel := 300) (by decide +kernel)
  obtain ⟨_, hcallEq⟩ := specializedEmit_call_bequiv_object hclosed hwp "apply" [.nat 5]
  have hrun16 : Obend.Law.run 400
      (.app (.get telemetryBook.link "apply") (.nat 5)) = some (.nat 16) :=
    optTermEq_sound (by decide +kernel)
  have heval16 : Evaluates
      (.app (.get (specializeBook telemetryBook telemetryPins).link "apply") (.nat 5))
      (.nat 16) :=
    (specializeBook_call_evaluates_obs_iff hwp "apply" [.nat 5] (.natural 16)).2
      (Obend.Law.run_sound 400 hrun16)
  exact ⟨htr, hmeaning, specializeBook_link_sound hwp, hcallEq, heval16⟩

/-! ## 6. Mutation Barriers (`#tooth`) & Axiom Audit (`0 sorryAx`, `0 custom axioms`) -/

#tooth wellPinnedBook_of_bool by
  mutation wellPinnedBookB := fun _ _ _ => true

#tooth T3_super_claim_frame by
  mutation SuperSupport.holds := fun _ _ _ _ => true

#tooth superCert_transport_sound by
  mutation transportSuperCert := fun _ cert => .ok cert

#tooth regPin_transport_sound by
  mutation stepRegPin := fun _ p => .ok p

#print axioms paco_fixed
#print axioms paco_final
#print axioms gpaco_init
#print axioms gpaco_unfold
#print axioms gpaco_coind
#print axioms gpaco_clo_sound
#print axioms companion_compat
#print axioms companion_gupaco_eq
#print axioms gpaco_upToStep_sound
#print axioms closed_bindBookPins_link
#print axioms specializeBook_link_sound
#print axioms specializeBook_call_bequiv
#print axioms specializeBook_call_evaluates_obs_iff
#print axioms bookCanonicalPins_wellPinned
#print axioms lyingMutualPins_breaks_link_bequiv
#print axioms superClaimResolver_sound
#print axioms superClaim_sound
#print axioms T3_super_claim_frame
#print axioms verticalLimit_impossible_claimCheck
#print axioms disjoint_transport_sound
#print axioms regPin_transport_sound
#print axioms superCert_transport_sound
#print axioms specializedEmit_call_bequiv_object
#print axioms capstone_pipeline_witness

end Obend.Tests.Metasystem.BookLinkAndSuperRefinesTest

end

open Obend.Logic in
#tooth superClaim_sound by
  mutation superClaimCheck := fun _ _ _ => .ok

open Obend.Logic in
#tooth claimCheck_illFormed by
  mutation claimCheck := fun _ _ _ => .refused .illFormed []

open Obend.Logic in
#tooth obligationCheck_refuses_false_external_claim by
  mutation externalClaimBound := fun _ _ _ => true

open Obend.Logic in
#tooth checkWorldCarrySpec_iff by
  mutation checkWorldCarrySpec := fun _ _ => .ok

namespace GroundClaimAudit
open Obend.Logic

def falseGroundClaim : ClaimObj :=
  { reflexiveClaimObj with claim := .lam (.lam (.binary .equal (.nat 7) (.nat 8))) }

theorem closed_ground_refused : claimCheck 0 falseGroundClaim [] = .refused .groundMismatch [] := by
  decide +kernel

example : claimJudge.Fragment falseGroundClaim := by
  exact ⟨by decide +kernel, .nat, .nat 7, .nat 8, rfl,
    .inr ⟨rfl, .natural 7, .natural 8, rfl, rfl⟩⟩

example : ¬ claimMeaning falseGroundClaim := claimCheck_groundMismatch closed_ground_refused
example : claimJudge.refutes .groundMismatch = true := rfl
example : claimCheck 0 reflexiveClaimObj [] = .ok := by decide +kernel

#tooth closed_ground_refused by mutation
  Obend.Logic.groundMismatch := fun _ _ _ => false

end GroundClaimAudit
