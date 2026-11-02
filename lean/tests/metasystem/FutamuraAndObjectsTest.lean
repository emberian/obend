/-
# `tests/metasystem/FutamuraAndObjectsTest.lean` — Literal Self-Application (`Futamura 1, 2 & 3`),
# Conservative Support Extraction, Affine `BendTT`, and Domain Objects Inside `.obend`

End-to-end verification of `WS-B`:
1. **`Obend.Leaf.Futamura` — Literal Self-Application of `dataPinSpecialize` & Commuting Semantic Decoding Diagrams**:
   - Program-as-Data (`Core.Term`) representation of `Leaf.Book`: `encodeBookTerm` and `decodeBookTerm?`
     with proved roundtrip `decodeBookTerm_encodeBookTerm : ∀ b, decodeBookTerm? (encodeBookTerm b) = some b`.
   - Internalized specializer `specializeBook`, `specializeBookInCore`, `futamura2BookCompiler`, and
     `cogenBookInCore` operating directly on encoded `Book`s and `LeafPin` environments, performing
     constant propagation, dead-branch elimination on `.ifZero`/`.ifBool` over pinned fields, and
     method inlining across `Book` definitions (`specializeBook_eliminates_branches_and_inlines_methods`).
   - True Futamura 1, 2, and 3 commuting diagrams (`futamura1_book_specializer_sound`,
     `futamura2_compiler_generator_commutes`, `futamura3_cogen_self_application_commutes`).
   - `#tooth` mutation probes on `specializeBook` and `futamura2_compiler_generator_commutes`.

2. **`Obend.Leaf.Specialize` — Complete Dependency Support Extraction & Conservatism Theorem**:
   - `extractReadMembers : Term → List String` (and `extractReadPins`), `AgreeOnMembers`.
   - `extractReadMembers_conservative`, `extractReadMembers_mutation_invariant`, and
     `candidate_supports_conservative`.
   - `#tooth` mutation probe on `extractReadMembersAt`.

3. **`Obend.Leaf.BendTT` — Affine Resource Discipline & Interaction-Net Port Wiring Validation**:
   - `countVarUses : Nat → BendTerm → Nat`, `isFixSpecPortBalanced`, and `isAffineBendTerm : BendTerm → Bool`.
   - `affine_bendTerm_subst_preserves` and `quantity_affine_linear_refines_bendTerm`.
   - `#tooth` mutation probe on `isAffineBendTerm`.

4. **`Obend.Hardware.UserspacePhysical` & `#import_obend` / `#obend_decl` — Domain Objects Inside `.obend`**:
   - 3 multi-layer open-recursive `Core4` prototype hierarchies (`Term.fix (Term.mix baseSpec overrideSpec) (.record seed)`)
     reasoned about directly via `fix_mix_flatten_sound` (`Leaf.flatten_sound` / `BEquiv`),
     `extractReadMembers_conservative`, and `futamura2_compiler_generator_commutes`:
     * **Domain Object 1**: Multi-layer LC Drives In-Slot Stator (`statorInSlotCore4Object`, `#import_obend` from
       `lean/tests/obend-source/world/physical/LcDrivesStatorUsd.obend`),
      * **Domain Object 2**: `MS350` SiC Half-Bridge Phase Leg (`ms350PhaseLegCore4Object`, plus `#obend_decl`),
      * **Domain Object 3**: $Q_3$ Photonic Coupler Array (`q3PhotonicCore4Object`, plus `#obend_decl`),
      * Plus `cnc5AxisMillComp` (`Cnc5AxisMill.obend` open-recursive composition in `UserspacePhysical.lean`).
   - Compile-time axiom audit (`0 sorryAx`, `0 Classical.choice`).
-/
import Obend.Leaf.Futamura
import Obend.Leaf.Specialize
import Obend.Leaf.BendTT
import Obend.Hardware.UserspacePhysical
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
open Obend.Hardware.UserspacePhysical
open Obend.Elab.Workbook

set_option autoImplicit false
set_option maxHeartbeats 800000

-- ============================================================================
-- 1. `#import_obend` & `#obend_decl` Integration with `.obend` Physical Models
-- ============================================================================

#import_obend "lean/tests/obend-source/world/physical/LcDrivesStatorUsd.obend" as LcDrivesStator

#obend_decl Ms350SicPhaseLeg "
record Ms350PhaseLeg:
  deadtimeNs() -> Nat
  slewRateLimitVPerNs() -> Nat
  switchingLossUj(currentA: Nat) -> Nat
  effectiveGateDelayNs(marginNs: Nat) -> Nat

spec SicBaseSwitch for Ms350PhaseLeg:
  requires deadtimeNs() -> Nat
  def deadtimeNs() -> Nat:
    40n
  def slewRateLimitVPerNs() -> Nat:
    50n
  def switchingLossUj(currentA: Nat) -> Nat:
    currentA * 3n + self.deadtimeNs
  def effectiveGateDelayNs(marginNs: Nat) -> Nat:
    marginNs + 12n

spec DeadtimeProtectionOverride for Ms350PhaseLeg:
  requires effectiveGateDelayNs(marginNs: Nat) -> Nat
  def deadtimeNs() -> Nat:
    120n
  def slewRateLimitVPerNs() -> Nat:
    80n
  def effectiveGateDelayNs(marginNs: Nat) -> Nat:
    super.effectiveGateDelayNs(marginNs) + 25n

def seedSicSwitch() -> Ms350PhaseLeg:
  {deadtimeNs: 0n, slewRateLimitVPerNs: 0n, switchingLossUj: fn(i: Nat) -> Nat: 0n, effectiveGateDelayNs: fn(m: Nat) -> Nat: 0n}

def ms350ProtectedPhaseLeg() -> Ms350PhaseLeg:
  fix(compose(SicBaseSwitch, DeadtimeProtectionOverride), seedSicSwitch())

def ms350LossAt100A() -> Nat:
  ms350ProtectedPhaseLeg().switchingLossUj(100n)

def ms350GateDelayAt10Ns() -> Nat:
  ms350ProtectedPhaseLeg().effectiveGateDelayNs(10n)
"

#obend_decl Q3PhotonicArray "
record Q3PhotonicCouplerArray:
  couplingWeight() -> Nat
  hypercubeDim() -> Nat
  transferredPowerMw(pInMw: Nat) -> Nat
  krawtchoukPhaseShiftMrad(modeIdx: Nat) -> Nat

spec PlanarWaveguideBase for Q3PhotonicCouplerArray:
  requires couplingWeight() -> Nat
  requires hypercubeDim() -> Nat
  def couplingWeight() -> Nat:
    2n
  def hypercubeDim() -> Nat:
    3n
  def transferredPowerMw(pInMw: Nat) -> Nat:
    pInMw * self.couplingWeight + self.hypercubeDim
  def krawtchoukPhaseShiftMrad(modeIdx: Nat) -> Nat:
    modeIdx * 15n

spec KrawtchoukCouplingOverride for Q3PhotonicCouplerArray:
  requires krawtchoukPhaseShiftMrad(modeIdx: Nat) -> Nat
  def couplingWeight() -> Nat:
    7n
  def krawtchoukPhaseShiftMrad(modeIdx: Nat) -> Nat:
    super.krawtchoukPhaseShiftMrad(modeIdx) + 45n

def seedPhotonic() -> Q3PhotonicCouplerArray:
  {couplingWeight: 0n, hypercubeDim: 0n, transferredPowerMw: fn(p: Nat) -> Nat: 0n, krawtchoukPhaseShiftMrad: fn(m: Nat) -> Nat: 0n}

def q3KrawtchoukArray() -> Q3PhotonicCouplerArray:
  fix(compose(PlanarWaveguideBase, KrawtchoukCouplingOverride), seedPhotonic())

def q3PowerAt20Mw() -> Nat:
  q3KrawtchoukArray().transferredPowerMw(20n)

def q3PhaseAtMode3() -> Nat:
  q3KrawtchoukArray().krawtchoukPhaseShiftMrad(3n)
"

/-- All 3 `.obend` physical domain packages (`LcDrivesStatorUsd.obend`, `Ms350SicPhaseLeg`,
`Q3PhotonicArray`) pass `FrontEnd.accept` and discharge the open-recursion obligation! -/
theorem all_physical_obend_packages_accepted_and_verified :
    LcDrivesStator.accepted = true ∧
    Ms350SicPhaseLeg.accepted = true ∧
    Q3PhotonicArray.accepted = true ∧
    obligationMeaningWithJudges workbookFormats
      LcDrivesStator.claim_peak_temp_open_recursion_obj
      LcDrivesStator.claim_peak_temp_open_recursion_just :=
  ⟨LcDrivesStator.accepted_eq,
   Ms350SicPhaseLeg.accepted_eq,
   Q3PhotonicArray.accepted_eq,
   LcDrivesStator.claim_peak_temp_open_recursion_holds⟩

theorem obend_elaborated_domain_benchmarks :
    LcDrivesStator.lcDrivesInSlotPeakTemp8kW_val = .nat 122 ∧
    Ms350SicPhaseLeg.ms350LossAt100A_val = .nat 420 ∧
    Ms350SicPhaseLeg.ms350GateDelayAt10Ns_val = .nat 47 ∧
    Q3PhotonicArray.q3PowerAt20Mw_val = .nat 143 ∧
    Q3PhotonicArray.q3PhaseAtMode3_val = .nat 90 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- 2. Literal Self-Application of `dataPinSpecialize` & Futamura 1, 2, 3 Tests
-- ============================================================================

example : decodeBookTerm? (encodeBookTerm sampleSpecializableBook) = some sampleSpecializableBook :=
  decodeBookTerm_encodeBookTerm sampleSpecializableBook

example : decodeBookTerm? (encodeBookTerm (emit statorInSlotComp)) = some (emit statorInSlotComp) :=
  decodeBookTerm_encodeBookTerm (emit statorInSlotComp)

example : decodeBookTerm? (encodeBookTerm (emit cnc5AxisMillComp)) = some (emit cnc5AxisMillComp) :=
  decodeBookTerm_encodeBookTerm (emit cnc5AxisMillComp)

example : decodeBookTerm? (encodeBookTerm (emit ms350PhaseLegComp)) = some (emit ms350PhaseLegComp) :=
  decodeBookTerm_encodeBookTerm (emit ms350PhaseLegComp)

example : decodeBookTerm? (encodeBookTerm (emit q3PhotonicComp)) = some (emit q3PhotonicComp) :=
  decodeBookTerm_encodeBookTerm (emit q3PhotonicComp)

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
member `m : String`, and runtime argument `x : Term`. -/
theorem test_true_futamura_1_2_3_commuting_diagrams (B : Book) (pins : List LeafPin) (m : String) (x : Term) :
    -- Futamura 1: internalized specializer decodes to `specializeBook B pins` and preserves semantics
    decodeBookTerm? (specializeBookInCore B pins) = some (specializeBook B pins) ∧
    lookupBookCode (specializeBook B pins) m = evalBookUnderPins B pins m ∧
    evalResidualBookAt (specializeBook B pins) m x = evalBookUnderPinsAt B pins m x ∧
    (holdsAll pins → lookupBookCode (specializeBook B pins) m = evalBookUnderPins B [] m) ∧
    (HoldsForBookMember B pins m → evalBook (specializeBook B pins) m = evalBook B m) ∧
    -- Futamura 2: staged compiler `futamura2BookCompiler B pins` commutes with `specializeBook B pins`
    decodeBookTerm? (runStagedCompiler (futamura2BookCompiler B pins) (encodePinsRecord pins)) =
      some (specializeBook B pins) ∧
    ((decodeBookTerm? (runStagedCompiler (futamura2BookCompiler B pins) (encodePinsRecord pins))).bind
      (fun B_res => evalResidualBookAt B_res m x)) = evalBookUnderPinsAt B pins m x ∧
    -- Futamura 3: self-applied compiler generator `cogenBookInCore` reproduces `futamura2BookCompiler B pins`
    dataPinSpecialize
      (runStagedCompiler cogenBookInCore (bookStageSpec (encodeBookTerm (bindBookPins B pins)))) =
      futamura2BookCompiler B pins ∧
    decodeBookTerm?
      (runStagedCompiler
        (dataPinSpecialize
          (runStagedCompiler cogenBookInCore (bookStageSpec (encodeBookTerm (bindBookPins B pins)))))
        (encodePinsRecord pins)) =
      some (specializeBook B pins) := by
  have f1 := futamura1_book_specializer_sound B pins m x
  have f2 := futamura2_compiler_generator_commutes B pins m x
  have f3 := futamura3_cogen_self_application_commutes B pins m x
  exact ⟨f1.1, f1.2.1, f1.2.2.1, f1.2.2.2.1, f1.2.2.2.2.2, f2.2.2.1, f2.2.2.2, f3.2.2.1, f3.2.2.2.1⟩

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

/-- Deep multi-binder term nesting `.lam` (depth 1), `.ifZero` successor arm (depth 2),
and `.case` arm payload (depth 3): inner `.get (.bound 0) "shadowedCasePayload"`,
`.get (.bound 1) "shadowedIfZeroPred"`, and `.get (.bound 2) "shadowedLamArg"` must NOT be
reported as reads of `self` (`(.bound 3)` at depth 3), while `.get (.bound 3) "outerSelfField"`
is extracted at depth 0! -/
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

/-- Support Extraction Conservatism & Mutation Invariance:
Any store mutation outside `extractReadMembers sampleMethodTerm` (and `deepBinderShadowTerm`)
leaves `substMemberEnv` and `evalWithMemberEnv` identical. -/
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

/-- Candidate support conservatism: a `Candidate` whose `pins` cover `extractReadMembers t`
evaluates identically under `viewLayerEnv v1` and `viewLayerEnv v2` whenever all `pins` hold at `v1` and `v2`. -/
example (pins : List LeafPin) (v1 v2 : LeafView) (t : Term) (fuel : Nat)
    (hcov : SupportsCoverMembers pins (extractReadMembers t))
    (h1 : ∀ p ∈ pins, holdsAt v1 p = true)
    (h2 : ∀ p ∈ pins, holdsAt v2 p = true) :
    substMemberEnv (viewLayerEnv v1) t = substMemberEnv (viewLayerEnv v2) t ∧
    evalWithMemberEnv fuel (viewLayerEnv v1) t = evalWithMemberEnv fuel (viewLayerEnv v2) t :=
  ⟨(candidate_supports_conservative hcov h1 h2).1,
   (candidate_supports_conservative hcov h1 h2).2 fuel⟩

-- `#tooth` mutation probe on `extractReadMembers`.
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

/-- `affine_bendTerm_subst_preserves`, `affine_bendTerm_fix_unfold_preserves`, &
`quantity_affine_linear_refines_bendTerm`. -/
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

-- `#tooth` mutation probe on `isAffineBendTerm`.
theorem probe_nonAffine_rejected :
    isAffineBendTerm nonAffineDuplicateUseBendTerm = false := by
  decide +kernel

#tooth probe_nonAffine_rejected by mutation
  isAffineBendTerm := fun _ => true

-- ============================================================================
-- 5. Open-Recursive `Core4` Domain Objects (`Term.fix (Term.mix base override) seed`)
-- ============================================================================

/-- Universal parametric verification across all 3 multi-layer open-recursive `Core4` domain objects:
1. `statorInSlotCore4Object = .fix (.mix statorBaseSpec inSlotCoolingOverrideSpec) (.record seedStatorFields)`
2. `ms350PhaseLegCore4Object = .fix (.mix sicBaseSwitchSpec deadtimeProtectionOverrideSpec) (.record seedSicSwitchFields)`
3. `q3PhotonicCore4Object = .fix (.mix planarWaveguideBaseSpec krawtchoukCouplingOverrideSpec) (.record seedPhotonicFields)` -/
theorem test_three_core4_domain_objects_universal
    (loss r currentA diDt margin pIn modeIdx : Nat) :
    -- Domain Object 1: LC Drives In-Slot Stator
    Evaluates (.app (.get statorInSlotCore4Object "peakWindingTemp") (.nat loss)) (.nat (50 + loss * 9)) ∧
    Evaluates (.app (.get statorInSlotCore4Object "sdfMargin") (.nat r)) (.nat ((r + 10) + 6)) ∧
    -- Domain Object 2: MS350 SiC Half-Bridge Phase Leg
    Evaluates (.app (.get ms350PhaseLegCore4Object "switchingLossUj") (.nat currentA)) (.nat (currentA * 3 + 120)) ∧
    Evaluates (.app (.get ms350PhaseLegCore4Object "shootThroughSafe") (.nat diDt)) (.boolean (decide (diDt ≤ 80))) ∧
    Evaluates (.app (.get ms350PhaseLegCore4Object "effectiveGateDelayNs") (.nat margin)) (.nat ((margin + 12) + 25)) ∧
    -- Domain Object 3: Q3 Photonic Coupler Array
    Evaluates (.app (.get q3PhotonicCore4Object "transferredPowerMw") (.nat pIn)) (.nat (pIn * 7 + 3)) ∧
    Evaluates (.app (.get q3PhotonicCore4Object "krawtchoukPhaseShiftMrad") (.nat modeIdx)) (.nat (modeIdx * 15 + 45)) :=
  ⟨stator_in_slot_peak_temp_forall loss,
   stator_in_slot_sdf_margin_forall r,
   ms350_switching_loss_forall currentA,
   ms350_shoot_through_safe_forall diDt,
   ms350_gate_delay_forall margin,
   q3_photonic_transferred_power_forall pIn,
   q3_photonic_phase_shift_forall modeIdx⟩

-- `#tooth` mutation probes on the 3 `Core4` domain objects.
theorem probe_stator_inSlot_override_active :
    Obend.Law.run 40 (.app (.get statorInSlotComp.flatten "peakWindingTemp") (.nat 8)) =
      some (.nat 122) :=
  optTermEq_sound (by decide +kernel)

#tooth probe_stator_inSlot_override_active by mutation
  lcDrivesInSlotUpgradeLayer := outerJacketStatorLayer

theorem probe_ms350_deadtime_override_active :
    Obend.Law.run 40 (.app (.get ms350PhaseLegComp.flatten "switchingLossUj") (.nat 100)) =
      some (.nat 420) :=
  optTermEq_sound (by decide +kernel)

#tooth probe_ms350_deadtime_override_active by mutation
  deadtimeProtectionOverrideLayer := sicBaseSwitchLayer

theorem probe_q3_krawtchouk_override_active :
    Obend.Law.run 40 (.app (.get q3PhotonicComp.flatten "transferredPowerMw") (.nat 20)) =
      some (.nat 143) :=
  optTermEq_sound (by decide +kernel)

#tooth probe_q3_krawtchouk_override_active by mutation
  krawtchoukCouplingOverrideLayer := planarWaveguideBaseLayer

-- ============================================================================
-- 6. Axiom Audit (`0 sorryAx`, `0 Classical.choice`)
-- ============================================================================

#print axioms decodeBookTerm_encodeBookTerm
#print axioms dataPinSpecialize_encodeBookTerm
#print axioms specializeBook_eliminates_branches_and_inlines_methods
#print axioms evalBook_specializeBook_eq_evalBook
#print axioms futamura1_book_specializer_sound
#print axioms futamura2_compiler_generator_commutes
#print axioms futamura3_cogen_self_application_commutes
#print axioms extractReadMembers_eq_selfReads
#print axioms extractReadMembers_conservative
#print axioms extractReadMembers_mutation_invariant
#print axioms candidate_supports_conservative
#print axioms affine_bendTerm_subst_preserves
#print axioms affine_bendTerm_fix_unfold_preserves
#print axioms quantity_affine_linear_refines_bendTerm
#print axioms fix_mix_flatten_sound
#print axioms statorInSlot_flatten_sound
#print axioms stator_in_slot_peak_temp_forall
#print axioms stator_in_slot_sdf_margin_forall
#print axioms stator_in_slot_support_and_futamura2
#print axioms ms350PhaseLeg_flatten_sound
#print axioms ms350_switching_loss_forall
#print axioms ms350_shoot_through_safe_forall
#print axioms ms350_gate_delay_forall
#print axioms ms350_support_and_futamura2
#print axioms q3Photonic_flatten_sound
#print axioms q3_photonic_transferred_power_forall
#print axioms q3_photonic_phase_shift_forall
#print axioms q3_photonic_support_and_futamura2
#print axioms test_three_core4_domain_objects_universal

end Obend.Tests.FutamuraAndObjectsTest
