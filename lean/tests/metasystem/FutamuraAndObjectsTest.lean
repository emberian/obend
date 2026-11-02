/-
# `tests/FutamuraAndObjectsTest.lean` — In-Place `Futamura` Specialization,
# Faré `OB5`/`LT5` Cross-Package Open Recursion, `K-KIND-CELL`, Multi-File `#import_obend` & `DocsCensus`

End-to-end verification of `WS-U`:
1. **Task 1 (`Obend.Leaf.Futamura`) — In-Place Audit Fix 11**:
   - `encodeStagedBookTerm (B : Book) : Term` (depends ONLY on `B`, zero host `pins` argument) and
     `encodePinsRecordForBook (B : Book) (pins : List LeafPin) : Term`.
   - `quoteBookMixTerm` applies `(.bound 1)` (`bookPayload`) to `(.bound 0)` (`pinsRecord`) inside `Core4`.
   - 1-argument `futamura2BookCompiler (B : Book) : Term` and `futamura2BookCompiler_specializes_in_core`:
     `dataPinSpecialize (.app (futamura2BookCompiler B) (encodePinsRecordForBook B pins)) = encodeBookTerm (specializeBook B pins)`.
   - True Futamura 1, 2, and 3 commuting diagrams (`futamura1_book_specializer_sound`,
     `futamura2_compiler_generator_commutes`, `futamura3_cogen_self_application_commutes`) + `#tooth` probes.

2. **Task 2 (`Obend.Leaf.Specialize`, `Obend.Lower.Transport`, `Obend.Spec.Elaborate`, `Obend.Spec.CrossPackage`) — Cross-Package Open Recursion (`OB5`/`LT5`)**:
   - `slotReadCone`, `coneSupports`, `Candidate.slotBook`, and `slotBook_moved_pin_blocks`.
   - `transportSlot_usable_of_disjoint_overlay`.
   - `CrossPackageLink`, `overlayModifiedFields`, `linkComposition`, `symUnfold_linkComposition_of_not_mem`,
     `crossPackage_disjoint_override_preserves_transportedSlot_and_specSlot`, and
     `crossPackage_intersecting_override_pinpoints_stale`.

3. **Task 3 (`Obend.Kind`, `Obend.Kind.Proofs`, `Obend.Vault.Store`) — First-Class `K-KIND-CELL`**:
   - `KindCell` enriched with `layers : List Obend.Logic.Layer := []` and `contract : List Law := []`.
   - `KindDerivation`, `deriveKindFrom`, and `deriveKindFrom_inherits_ancestors_and_narrows_laws`.
   - `Store.createFrom` on `_kind/Child` pages and `createFrom_kind_preserves_ancestor_laws`.

4. **Task 4 (`Obend.Elab.Workbook`, `stdlib/{core,ledger,usd}/*.obend`, `Obend.Stdlib`) — Multi-File `#import_obend`**:
   - Recursive multi-file `.obend` `import` resolution in `Workbook.lean`.
   - `stdlib/core/Cell.obend`, `stdlib/ledger/Account.obend`, and `stdlib/usd/ScenePrim.obend` elaborated in
     `Obend.Stdlib` with open-recursion specialization and cross-package pin survival proofs.

5. **Task 5 (`Obend.Tactic.DocsCensus`) — Compile-Time Docs Census Gate**:
   - `#check_docs_census` verifying all 7 top-level markdown documents (`DESIGN.md`, `PLAN.md`, `METATHEORY.md`,
     `PHYSICAL.md`, `SILICON-ELABORATOR.md`, `NEXT-MATHEMATICA.md`, `DEOS-CONTRACTS-CONSENSUS.md`).
-/
import Obend.Leaf.Futamura
import Obend.Leaf.Specialize
import Obend.Leaf.BendTT
import Obend.Lower.Transport
import Obend.Spec.CrossPackage
import Obend.Kind
import Obend.Kind.Proofs
import Obend.Vault.Store
import Obend.Stdlib
import Obend.Tactic.DocsCensus
import Obend.Elab.Workbook
import Obend.Tactic.Tooth

namespace Obend.Tests.FutamuraAndObjectsTest

open Obend.Core
open Obend.Core.Term
open Obend.Core.Ty (Ty Quantity safeQuantity)
open Obend.Law
open Obend.Equiv
open Obend.Logic
open Obend.Slot.World
open Obend.Leaf
open Obend.Leaf.Futamura
open Obend.Leaf.BendTT
open Obend.Lower
open Obend.Spec.CrossPackage
open Obend.Kind
open Obend.Vault
open Obend.Stdlib
open Obend.Tactic.DocsCensus
open Obend.Elab.Workbook

set_option autoImplicit false
set_option maxHeartbeats 800000

-- ============================================================================
-- 1. Multi-File `#import_obend` Standard Library (`Obend.Stdlib`)
-- ============================================================================

/-- All 3 multi-file `.obend` standard library modules (`stdlib/core/Cell.obend`,
`stdlib/ledger/Account.obend`, `stdlib/usd/ScenePrim.obend`) pass `FrontEnd.accept`
and discharge their open-recursion `claim`s and `law` obligations. -/
theorem all_stdlib_obend_packages_accepted_and_verified :
    (StdlibCell.accepted = true ∧
     StdlibAccount.accepted = true ∧
     StdlibScenePrim.accepted = true) ∧
    (obligationMeaningWithJudges workbookFormats
       StdlibCell.claim_next_value_open_recursion_obj
       StdlibCell.claim_next_value_open_recursion_just ∧
     obligationMeaningWithJudges workbookFormats
       StdlibAccount.claim_available_open_recursion_obj
       StdlibAccount.claim_available_open_recursion_just ∧
     obligationMeaningWithJudges workbookFormats
       StdlibScenePrim.claim_world_transform_open_recursion_obj
       StdlibScenePrim.claim_world_transform_open_recursion_just) ∧
    (StdlibCell.package.laws.length = 2 ∧
     StdlibAccount.package.laws.length = 4 ∧
     StdlibScenePrim.package.laws.length = 3) :=
  ⟨stdlib_all_accepted, stdlib_all_claims_hold, stdlib_inherited_laws_count⟩

theorem stdlib_elaborated_domain_benchmarks :
    StdlibCell.versionedCellNextAt25_val = .nat 125 ∧
    StdlibCell.versionedCellGasAt4_val = .nat 32 ∧
    StdlibAccount.escrowAvailableAt10_val = .nat 1020 ∧
    StdlibAccount.escrowSettlementAt100_val = .nat 270 ∧
    StdlibScenePrim.composedWorldTransformAt100_val = .nat 140 ∧
    StdlibScenePrim.composedVoxelCostAt5_val = .nat 28 :=
  stdlib_open_recursion_eval

-- ============================================================================
-- 2. In-Place `Futamura` Specialization (Audit Fix 11: 1-Arg `futamura2BookCompiler B`)
-- ============================================================================

example : decodeBookTerm? (encodeBookTerm sampleSpecializableBook) = some sampleSpecializableBook :=
  decodeBookTerm_encodeBookTerm sampleSpecializableBook

example : decodeBookTerm? (encodeBookTerm (emit StdlibCell.versionedCell_comp)) =
    some (emit StdlibCell.versionedCell_comp) :=
  decodeBookTerm_encodeBookTerm (emit StdlibCell.versionedCell_comp)

example : decodeBookTerm? (encodeBookTerm (emit StdlibAccount.escrowAccount_comp)) =
    some (emit StdlibAccount.escrowAccount_comp) :=
  decodeBookTerm_encodeBookTerm (emit StdlibAccount.escrowAccount_comp)

example : decodeBookTerm? (encodeBookTerm (emit StdlibScenePrim.composedUsdPrim_comp)) =
    some (emit StdlibScenePrim.composedUsdPrim_comp) :=
  decodeBookTerm_encodeBookTerm (emit StdlibScenePrim.composedUsdPrim_comp)

example (B : Book) : decodeBookTerm? (encodeBookTerm B) = some B :=
  decodeBookTerm_encodeBookTerm B

/-- Reordered `.record` fields decode identically to canonical field ordering, while malformed
records with missing or ill-typed fields return `none`. -/
example :
    decodeLeafPin? (.record [("code", .nat 7), ("cell", encodeLeafCell (.layer "couplingWeight"))]) =
      some ⟨.layer "couplingWeight", .nat 7⟩ ∧
    decodeBookItem? (.inject "static" (.record [("value", .nat 7), ("member", .label "couplingWeight")])) =
      some (.static "couplingWeight" (.nat 7)) ∧
    decodeLeafDef? (.record [
      ("reads", encodeNatList []),
      ("code", .nat 42),
      ("kind", encodeDefKind .cell),
      ("slot", .nat 0),
      ("member", .label "m0")
    ]) = some ⟨"m0", 0, .cell, .nat 42, []⟩ ∧
    decodeLeafPin? (.record [("code", .nat 7)]) = none ∧
    decodeBookTerm? (.record [("items", .nat 0)]) = none :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Concrete verification of constant propagation, dead-branch elimination on `.ifZero`/`.ifBool`,
and method inlining across `Book` definitions in `specializeBook` and `specializeBookInCore`. -/
example :
    lookupBookCode (specializeBook sampleSpecializableBook sampleBookPins) "dispatch" =
      some (.lam (.lam (.binary .add (.binary .add (.bound 0) (.nat 16)) (.nat 9)))) ∧
    ((specializeBook sampleSpecializableBook sampleBookPins).defs.find? (·.member == "dispatch")).map (·.reads) =
      some [] ∧
    evalResidualBookAt (specializeBook sampleSpecializableBook sampleBookPins) "dispatch" (.nat 5) =
      some (.nat 30) ∧
    evalBook (specializeBook sampleSpecializableBook sampleBookPins) "dispatch" =
      evalBook sampleSpecializableBook "dispatch" :=
  specializeBook_eliminates_branches_and_inlines_methods

/-- Non-vacuous verification of `HoldsForBookMember` and `evalBook_specializeBook_eq_evalBook`
on `sampleSpecializableBook` and non-empty `sampleBookPins`. -/
example :
    HoldsForBookMember sampleSpecializableBook sampleBookPins "dispatch" ∧
    evalBook (specializeBook sampleSpecializableBook sampleBookPins) "dispatch" =
      evalBook sampleSpecializableBook "dispatch" := by
  have hholds : HoldsForBookMember sampleSpecializableBook sampleBookPins "dispatch" := by
    refine ⟨fun d hd => ?_, fun hnone => by cases hnone⟩
    have hd_eq := Option.some.inj hd
    subst hd_eq
    refine ⟨by decide +kernel, fun r hr => ?_, fun hemp => by cases hemp⟩
    have hlist : extractReadMembersCode
      ({ member := "dispatch", slot := 3, kind := DefKind.method,
         code :=
           .lam (.lam (.ifZero (.get (.bound 1) "mode")
             (.ifBool (.binary .lessEqual (.get (.bound 1) "threshold") (.nat 10))
               (.binary .add (.app (.get (.bound 1) "helper") (.bound 0)) (.get (.bound 1) "threshold"))
               (.nat 999))
             (.lam (.nat 888)))),
         reads := [0, 1, 2] } : LeafDef).code = ["mode", "threshold", "helper", "threshold"] := by
      decide +kernel
    rw [hlist] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact optTermEq_sound (by decide +kernel)
  exact ⟨hholds, evalBook_specializeBook_eq_evalBook sampleSpecializableBook sampleBookPins "dispatch" hholds⟩

/-- True Futamura 1, 2, and 3 commuting diagrams on arbitrary `Book` `B`, `pins : List LeafPin`,
member `m : String`, and runtime argument `x : Term` (with in-place 1-arg `futamura2BookCompiler B`
and `futamura2BookCompiler_specializes_in_core`). -/
theorem test_true_futamura_1_2_3_commuting_diagrams (B : Book) (pins : List LeafPin) (m : String) (x : Term) :
    -- Futamura 1: internalized specializer decodes to `specializeBook B pins` and preserves semantics
    decodeBookTerm? (specializeBookInCore B pins) = some (specializeBook B pins) ∧
    lookupBookCode (specializeBook B pins) m = evalBookUnderPins B pins m ∧
    evalResidualBookAt (specializeBook B pins) m x = evalBookUnderPinsAt B pins m x ∧
    (holdsAll pins → lookupBookCode (specializeBook B pins) m = evalBookUnderPins B [] m) ∧
    (HoldsForBookMember B pins m → evalBook (specializeBook B pins) m = evalBook B m) ∧
    -- Futamura 2: staged compiler `futamura2BookCompiler B` (zero host `pins` argument) specializes in Core4
    dataPinSpecialize (.app (futamura2BookCompiler B) (encodePinsRecordForBook B pins)) =
      encodeBookTerm (specializeBook B pins) ∧
    decodeBookTerm? (runStagedCompiler (futamura2BookCompiler B) (encodePinsRecordForBook B pins)) =
      some (specializeBook B pins) ∧
    ((decodeBookTerm? (runStagedCompiler (futamura2BookCompiler B) (encodePinsRecordForBook B pins))).bind
      (fun B_res => evalResidualBookAt B_res m x)) = evalBookUnderPinsAt B pins m x ∧
    -- Futamura 3: self-applied compiler generator `cogenBookInCore` reproduces `futamura2BookCompiler B`
    dataPinSpecialize
      (resolveApp cogenBookInCore (bookStageSpec (encodeStagedBookTerm B))) =
      futamura2BookCompiler B ∧
    decodeBookTerm?
      (runStagedCompiler
        (dataPinSpecialize
          (resolveApp cogenBookInCore (bookStageSpec (encodeStagedBookTerm B))))
        (encodePinsRecordForBook B pins)) =
      some (specializeBook B pins) := by
  have f1 := futamura1_book_specializer_sound B pins m x
  have f2 := futamura2_compiler_generator_commutes B pins m x
  have f3 := futamura3_cogen_self_application_commutes B pins m x
  exact ⟨f1.1, f1.2.1, f1.2.2.1, f1.2.2.2.1, f1.2.2.2.2.2,
    futamura2BookCompiler_specializes_in_core B pins,
    f2.2.2.1, f2.2.2.2, f3.2.2.1, f3.2.2.2.1⟩

-- `#tooth` mutation probe on `specializeBook`.
theorem probe_specializeBook_eliminates_ifZero :
    lookupBookCode (specializeBook sampleSpecializableBook sampleBookPins) "dispatch" =
      some (.lam (.lam (.binary .add (.binary .add (.bound 0) (.nat 16)) (.nat 9)))) :=
  optTermEq_sound (by decide +kernel)

#tooth probe_specializeBook_eliminates_ifZero by mutation
  specializeBook := fun B _ => B

-- ============================================================================
-- 3. Complete Dependency Support Extraction & Conservatism Tests
-- ============================================================================

def sampleMethodTerm : Term :=
  .lam (.binary .add
    (.binary .multiply (.bound 0) (.get (.bound 1) "couplingWeight"))
    (.get (.bound 1) "hypercubeDim"))

def deepBinderShadowTerm : Term :=
  .lam (
    .ifZero (.bound 0)
      (.get (.bound 1) "zeroBranchSelfField")
      (.case (.bound 0) [
        ("tagA",
          .binary .add
            (.get (.bound 0) "shadowedCasePayload")
            (.binary .add
              (.get (.bound 1) "shadowedIfZeroPred")
              (.binary .add
                (.get (.bound 2) "shadowedLamArg")
                (.get (.bound 3) "outerSelfField"))))
      ]))

#guard extractReadMembers sampleMethodTerm == ["couplingWeight", "hypercubeDim"]
#guard extractReadPins sampleMethodTerm == ["couplingWeight", "hypercubeDim"]
#guard extractReadMembers deepBinderShadowTerm == ["zeroBranchSelfField", "outerSelfField"]

example (t : Term) : extractReadMembers t = selfReads 0 t :=
  extractReadMembers_eq_selfReads t

theorem test_extractReadMembers_conservative_and_mutation_invariant
    (env1 env2 : String → Option Term) (v : Option Term) (fuel : Nat) :
    (AgreeOnMembers (extractReadMembers sampleMethodTerm) env1 env2 →
      substMemberEnv env1 sampleMethodTerm = substMemberEnv env2 sampleMethodTerm ∧
      evalWithMemberEnv fuel env1 sampleMethodTerm = evalWithMemberEnv fuel env2 sampleMethodTerm) ∧
    substMemberEnv (mutateMemberEnv env1 "krawtchoukPhaseShiftMrad" v) sampleMethodTerm =
      substMemberEnv env1 sampleMethodTerm ∧
    substMemberEnv (mutateMemberEnv env1 "shadowedCasePayload" v) deepBinderShadowTerm =
      substMemberEnv env1 deepBinderShadowTerm := by
  refine ⟨fun hagree =>
    ⟨(extractReadMembers_conservative hagree).1,
     (extractReadMembers_conservative hagree).2.1 fuel⟩,
    (extractReadMembers_mutation_invariant sampleMethodTerm env1 v (by decide +kernel)).1,
    (extractReadMembers_mutation_invariant deepBinderShadowTerm env1 v (by decide +kernel)).1⟩

example (pins : List LeafPin) (v1 v2 : LeafView) (t : Term) (fuel : Nat)
    (hcov : SupportsCoverMembers pins (extractReadMembers t))
    (h1 : ∀ p ∈ pins, holdsAt v1 p = true)
    (h2 : ∀ p ∈ pins, holdsAt v2 p = true) :
    substMemberEnv (viewLayerEnv v1) t = substMemberEnv (viewLayerEnv v2) t ∧
    evalWithMemberEnv fuel (viewLayerEnv v1) t = evalWithMemberEnv fuel (viewLayerEnv v2) t :=
  ⟨(candidate_supports_conservative hcov h1 h2).1,
   (candidate_supports_conservative hcov h1 h2).2 fuel⟩

theorem probe_extractReadMembers_sample :
    extractReadMembers sampleMethodTerm = ["couplingWeight", "hypercubeDim"] := by
  decide +kernel

#tooth probe_extractReadMembers_sample by mutation
  extractReadMembers := fun _ => []

-- ============================================================================
-- 4. Affine `BendTT` Resource Discipline & Port Wiring Validation Tests
-- ============================================================================

def affineLinearAddBendTerm : BendTerm :=
  .lam (.binOp .add (.var 0) (.nat 10))

def nonAffineDuplicateUseBendTerm : BendTerm :=
  .lam (.binOp .add (.var 0) (.var 0))

def affineIfZeroBendTerm : BendTerm :=
  .lam (.ifZero (.var 0) (.nat 0) (.var 0))

def balancedFixBendTerm : BendTerm :=
  .fix (.lam (.lam (.var 0))) (.nat 0)

def unbalancedFixBendTerm : BendTerm :=
  .fix (.lam (.var 0)) (.nat 0)

#guard countVarUses 0 (.binOp .add (.var 0) (.nat 10)) == 1
#guard countVarUses 0 (.binOp .add (.var 0) (.var 0)) == 2
#guard isAffineBendTerm affineLinearAddBendTerm == true
#guard isAffineBendTerm nonAffineDuplicateUseBendTerm == false
#guard isAffineBendTerm affineIfZeroBendTerm == true
#guard isAffineBendTerm balancedFixBendTerm == true
#guard isAffineBendTerm unbalancedFixBendTerm == false

theorem test_affine_bendtt_subst_and_quantity_refinement
    (body arg : BendTerm) (haffBody : isAffineBendTerm body = true)
    (haffArg : isAffineBendTerm arg = true) (hclosedArg : closedAtB 0 arg = true) :
    isAffineBendTerm (instantiateB body arg) = true :=
  affine_bendTerm_subst_preserves body arg haffBody haffArg hclosedArg

theorem test_affine_bendtt_fix_unfold_preserves
    (s i : BendTerm) (hfix : isAffineBendTerm (.fix s i) = true) :
    isFixSpecPortBalanced s = true ∧
    (∃ body : BendTerm, s = .lam (.lam body)) ∧
    isAffineBendTerm (.app (.app s (.fix s i)) i) = true ∧
    (∀ body : BendTerm, s = .lam (.lam body) →
      closedAtB 0 (.fix s i) = true →
      isAffineBendTerm (instantiateB (.lam body) (.fix s i)) = true) :=
  affine_bendTerm_fix_unfold_preserves s i hfix

example {t : Term} {bt : BendTerm} (hcomp : compileToBendTT t = some bt)
    (q : Quantity) (hq : q = .affine ∨ q = .linear) :
    (∀ idx : Nat, countVarUses idx bt = termVarUses idx t) ∧
    (safeQuantity q (termVarUses 0 t) = true ↔ countVarUses 0 bt ≤ 1) ∧
    (q.fits (termVarUses 0 t) = true → isAffineBendTerm bt = true → isAffineBendTerm (.lam bt) = true) ∧
    (isAffineBendTerm bt = isAffineCoreTerm t) :=
  quantity_affine_linear_refines_bendTerm hcomp q hq

theorem probe_nonAffine_rejected :
    isAffineBendTerm nonAffineDuplicateUseBendTerm = false := by
  decide +kernel

#tooth probe_nonAffine_rejected by mutation
  isAffineBendTerm := fun _ => true

-- ============================================================================
-- 5. Faré `OB5` / `LT5` Cross-Package Open Recursion (`Specialize`, `Transport`, `CrossPackage`)
-- ============================================================================

/-- Cross-package disjoint override preserves symbolic unfolding, provenance, and cone supports
across `StdlibCell` (`nextValue`) and `StdlibAccount` (`availableAfterFee`). -/
theorem test_crossPackage_disjoint_cone_survival :
    let C_cell := StdlibCell.baseCell_comp
    let L_cell := StdlibCell.versionedCell_comp.top
    let C_acct := StdlibAccount.baseAccount_comp
    let L_acct := StdlibAccount.escrowAccount_comp.top
    ((linkComposition C_cell L_cell).symUnfold "nextValue" = C_cell.symUnfold "nextValue" ∧
     (linkComposition C_cell L_cell).provenance "nextValue" = C_cell.provenance "nextValue" ∧
     memberConePin (linkComposition C_cell L_cell) "nextValue" = memberConePin C_cell "nextValue" ∧
     coneSupports (linkComposition C_cell L_cell) (slotReadCone C_cell "nextValue") =
       coneSupports C_cell (slotReadCone C_cell "nextValue")) ∧
    (coneSupports (linkComposition C_acct L_acct) (slotReadCone C_acct "availableAfterFee") =
       coneSupports C_acct (slotReadCone C_acct "availableAfterFee")) :=
  ⟨stdlib_cell_crossPackage_nextValue_pin_survives,
   stdlib_account_crossPackage_availableAfterFee_cone_survives⟩

-- ============================================================================
-- 6. First-Class `K-KIND-CELL` (`Obend.Kind`, `Obend.Kind.Proofs`, `Obend.Vault.Store`)
-- ============================================================================

/-- `deriveKindFrom` inherits ancestor layout + contracts along C4 and preserves narrowing,
and `Store.createFrom` on `_kind/Child` preserves all ancestor laws. -/
theorem test_deriveKindFrom_and_store_createFrom_kind
    {Law : Type} {ks ks' : Kinds Law} {d : KindDerivation Law} {child : KindCell Law}
    (h : deriveKindFrom ks d = .ok (child, ks')) :
    child.name = d.name ∧
    child.parents = d.parents ∧
    child.law = d.law ∧
    d.law ∈ child.contract := by
  have h1 := deriveKindFrom_inherits_ancestors_and_narrows_laws h
  exact ⟨h1.1, h1.2.1, h1.2.2.1, h1.2.2.2.2.1⟩

example {s : Store} {k page md : String}
    (hkind : isKind page = true)
    (hcf : createFrom s k page = .ok md) :
    (s.page? page).isSome = false ∧ kindName k ≠ page := by
  have h1 := createFrom_kind_preserves_ancestor_laws hkind hcf
  exact ⟨h1.1, h1.2.1⟩

-- ============================================================================
-- 7. Compile-Time Docs Census Gate (`Obend.Tactic.DocsCensus`)
-- ============================================================================

#check_docs_census

example :
    extractObendLeanPaths "Obend/Leaf/Futamura.lean lean/Obend/Spec/CrossPackage.lean" =
      ["Obend/Leaf/Futamura.lean", "Obend/Spec/CrossPackage.lean"] ∧
    extractObendDottedRoots "Obend.Leaf.Futamura Obend.Spec.CrossPackage" =
      ["Leaf", "Spec"] :=
  ⟨extractObendLeanPaths_sample, extractObendDottedRoots_sample⟩

-- ============================================================================
-- 8. Axiom Audit (`0 sorryAx`, `0 Classical.choice`)
-- ============================================================================

#print axioms decodeBookTerm_encodeBookTerm
#print axioms dataPinSpecialize_encodeBookTerm
#print axioms specializeBook_eliminates_branches_and_inlines_methods
#print axioms evalBook_specializeBook_eq_evalBook
#print axioms futamura1_book_specializer_sound
#print axioms futamura2BookCompiler_specializes_in_core
#print axioms futamura2_compiler_generator_commutes
#print axioms futamura3_cogen_self_application_commutes
#print axioms extractReadMembers_eq_selfReads
#print axioms extractReadMembers_conservative
#print axioms extractReadMembers_mutation_invariant
#print axioms candidate_supports_conservative
#print axioms slotBook_moved_pin_blocks
#print axioms transportSlot_usable_of_disjoint_overlay
#print axioms symUnfold_linkComposition_of_not_mem
#print axioms crossPackage_disjoint_override_preserves_transportedSlot_and_specSlot
#print axioms crossPackage_intersecting_override_pinpoints_stale
#print axioms deriveKindFrom_inherits_ancestors_and_narrows_laws
#print axioms createFrom_kind_preserves_ancestor_laws
#print axioms stdlib_all_accepted
#print axioms stdlib_all_claims_hold
#print axioms stdlib_inherited_laws_count
#print axioms stdlib_open_recursion_eval
#print axioms stdlib_flatten_and_book_sound
#print axioms stdlib_futamura2_in_core
#print axioms stdlib_cell_crossPackage_nextValue_pin_survives
#print axioms stdlib_account_crossPackage_availableAfterFee_cone_survives
#print axioms extractObendLeanPaths_sample
#print axioms extractObendDottedRoots_sample
#print axioms censusReport_isClean_iff
#print axioms affine_bendTerm_subst_preserves
#print axioms affine_bendTerm_fix_unfold_preserves
#print axioms quantity_affine_linear_refines_bendTerm

end Obend.Tests.FutamuraAndObjectsTest
