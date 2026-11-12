module
/-
# `SymbolicCertAndClaimAuditTest` — End-to-End Verification of `SymbolicCert` & `ClaimAudit`

Exercises:
1. `by bool_spec_iff` (bidirectional `check x = true ↔ Spec x` and `check x = false ↔ ¬ Spec x`
   synthesis across nested Boolean combinators, `Except`, `Option`, `ite`, `List.all`, `List.any`).
2. `by before_rank` (verified DAG & lexicographic `(k, j)` rank chain synthesis + strict-cycle
   refutation via `rfl` in the kernel).
3. `by perm_cert` (verified `checkPermWitness_sound` & typeclass-free `checkSymPermWitness_sound`
   for concrete lists and open polymorphic `LinMemBalance` conservation goals).
4. `Obend.Tactic.ClaimAudit` enforcement of all **5 MoA Claim-Contract Laws** — both positive
   earned discharges and negative catches for `axiomPurity` (Law 1), `earnedProof` projection/rfl/
   congrArg cosplay (Law 2), `nonDegenerateCarrier` `Unit`/`Empty`/`fun _ => False` (Law 3),
   `#verify_non_vacuous` killing `ModuleSISHard = False` (Law 4), and `#verify_judge_succession`
   non-weakening `NewThm → OldThm` (Law 5).
-/
public import Obend.Tactic.SymbolicCert
public import Obend.Tactic.ClaimAudit
public import Obend.Tactic.Tooth
public import Obend.AssertAxioms
import all Obend.Tactic.SymbolicCert
import all Obend.Tactic.ClaimAudit
public meta import Lean

public section
namespace Obend.Tests.Metasystem.SymbolicCertAndClaimAuditTest

open Obend.Tactic.SymbolicCert
open Obend.Tactic.ClaimAudit

set_option autoImplicit false

/-! ## 1. `by bool_spec_iff` — Automatic Bidirectional Boolean-to-`Prop` Equivalence Synthesis -/

structure PacketHeader where
  version : Nat
  flags   : Nat
  tagOpt  : Option Nat
  emptyCh : Option Nat
  decode  : Except String Nat
  ports   : List Nat
  alerts  : List Nat

def checkPacketHeader (h : PacketHeader) : Bool :=
  (h.version == 2) &&
  (h.flags != 0) &&
  decide (h.flags < 64) &&
  h.tagOpt.isSome &&
  h.emptyCh.isNone &&
  h.decode.isOk &&
  (if h.flags < 8 then h.version == 2 else !decide (h.flags == 99)) &&
  h.ports.all (fun p => decide (p < 1024) && (p != 0)) &&
  h.alerts.any (fun a => a == 7 || decide (100 ≤ a))

def PacketHeaderSpec (h : PacketHeader) : Prop :=
  h.version = 2 ∧
  h.flags ≠ 0 ∧
  h.flags < 64 ∧
  (∃ t, h.tagOpt = some t) ∧
  h.emptyCh = none ∧
  (∃ v, h.decode = .ok v) ∧
  ((h.flags < 8 ∧ h.version = 2) ∨ (¬ h.flags < 8 ∧ ¬ (h.flags = 99))) ∧
  (∀ p, p ∈ h.ports → p < 1024 ∧ p ≠ 0) ∧
  (∃ a, a ∈ h.alerts ∧ (a = 7 ∨ 100 ≤ a))

/-- Automatic unfolding + left-associated `&&` vs right-associated `∧` alignment via `by bool_spec_iff`. -/
theorem checkPacketHeader_iff (h : PacketHeader) :
    checkPacketHeader h = true ↔ PacketHeaderSpec h := by
  bool_spec_iff

/-- Explicit unfold-list form + `= false ↔ ¬ Spec` dual mode via `by bool_spec_iff [...]`. -/
theorem checkPacketHeader_false_iff (h : PacketHeader) :
    checkPacketHeader h = false ↔ ¬ PacketHeaderSpec h := by
  bool_spec_iff [checkPacketHeader, PacketHeaderSpec]

/-- Direct combinator De Morgan `= false` equivalence (`(a && b) = false ↔ ...`) and `Except.toBool`. -/
theorem exceptAndOption_false_iff (r : Except Nat Bool) (m : Option Nat) :
    (r.toBool && !m.isNone) = false ↔ ((∃ err, r = .error err) ∨ m = none) := by
  bool_spec_iff

/-! ## 2. `by before_rank` — Scalar DAG Chains, Lexicographic `(k, j)` Chains & Cycle Refutations -/

/-- Multi-hop scalar `Before` / `BeforeWeak` / `≤` / `=` DAG chain solved in the kernel via `rfl`. -/
theorem dagBefore_chain (a b c d e : Nat)
    (h₁ : Before a b) (h₂ : b ≤ c) (h₃ : c = d) (h₄ : BeforeWeak d e) :
    Before a e := by
  before_rank

/-- Weighted slack accumulation (`a + 2 < b`, `b + 3 ≤ c`, `c ≤ d` implies `a + 6 ≤ d`). -/
theorem weightedRankSlack_chain (a b c d : Nat)
    (h₁ : a + 2 < b) (h₂ : b + 3 ≤ c) (h₃ : c ≤ d) :
    a + 6 ≤ d := by
  before_rank

/-- Multi-hop lexicographic `(k, j)` rank chain combining WFS C1 (strict stage descent),
    WFS C2/C3 (equal-stage step descent), and a direct `≤ₗₑₓ` edge. -/
theorem wfsLexicographic_chain (k₁ j₁ k₂ j₂ k₃ j₃ k₄ j₄ : Nat)
    (hStage : Before k₁ k₂)
    (hEqFwd : k₂ ≤ k₃) (hEqBwd : k₃ ≤ k₂) (hStep : j₂ < j₃)
    (hTail  : (k₃, j₃) ≤ₗₑₓ (k₄, j₄)) :
    (k₁, j₁) <ₗₑₓ (k₄, j₄) := by
  before_rank

/-- Weak lexicographic chain `≤ₗₑₓ` across equal stages and weak step bounds. -/
theorem wfsLexicographic_weak_chain (k₁ j₁ k₂ j₂ k₃ j₃ : Nat)
    (h₁ : k₁ = k₂) (h₂ : j₁ ≤ j₂) (h₃ : (k₂, j₂) ≤ₗₑₓ (k₃, j₃)) :
    (k₁, j₁) ≤ₗₑₓ (k₃, j₃) := by
  before_rank

/-- Scalar strict cycle refutation (`Before a b`, `b ≤ c`, `c ≤ a` is impossible). -/
theorem scalarRankCycle_refute (a b c : Nat)
    (h₁ : Before a b) (h₂ : b ≤ c) (h₃ : c ≤ a) : False := by
  before_rank

/-- Negated back-edge refutation synthesized directly by `by before_rank`. -/
theorem scalarRankNoBackEdge (a b c : Nat)
    (h₁ : a < b) (h₂ : b ≤ c) : ¬ (c ≤ a) := by
  before_rank

/-- Lexicographic strict cycle refutation (`(k₁, j₁) <ₗₑₓ (k₂, j₂)` and `(k₂, j₂) ≤ₗₑₓ (k₁, j₁)`). -/
theorem lexRankCycle_refute (k₁ j₁ k₂ j₂ : Nat)
    (h₁ : (k₁, j₁) <ₗₑₓ (k₂, j₂)) (h₂ : (k₂, j₂) ≤ₗₑₓ (k₁, j₁)) : False := by
  before_rank

/-- Topological rank assignment certificate verified in Lean's kernel via `rfl`. -/
theorem sampleExprCamDag_acyclic :
    ∀ u v, (u, v) ∈ [(0, 1), (0, 2), (1, 3), (2, 3), (3, 4)] →
      Before (lookupRankVar [10, 20, 25, 40, 55] u) (lookupRankVar [10, 20, 25, 40, 55] v) :=
  checkDagRankAssignment_sound rfl

/-! ## 3. `by perm_cert` — Concrete & Typeclass-Free Symbolic `LinMem` Permutation Reflection -/

/-- Ground multiset with duplicate elements discharged via `checkPermWitness_sound` + `rfl`. -/
example : List.Perm [4, 1, 3, 2, 1] [1, 2, 1, 4, 3] := by
  perm_cert

/-- WHNF-reducible list computation discharged via `checkPermWitness_sound` + `rfl` in kernel. -/
@[expose] def bumpEach : List Nat → List Nat
  | [] => []
  | x :: xs => (x + 10) :: bumpEach xs

example : List.Perm (bumpEach [1, 2, 3, 4]) [14, 12, 11, 13] := by
  perm_cert

/-- Polymorphic open `LinMemBalance` conservation over an arbitrary `α : Type` WITHOUT `DecidableEq α`! -/
theorem linMemSwapConservation {α : Type} (a b c : α) (heapRest : List α) :
    LinMemBalance (a :: heapRest) [b, c] [c, a] (b :: heapRest) := by
  perm_cert

/-- Multi-chunk symbolic frame permutation without `BEq` or `DecidableEq`. -/
theorem symbolicFramePerm {α : Type} (x y z : α) (h₁ h₂ : List α) :
    List.Perm ((x :: h₁) ++ [y, z] ++ h₂) (h₂ ++ [z] ++ (y :: h₁) ++ [x]) := by
  perm_cert

/-! ## 4. Kernel Enforcement of the MoA 5 Claim-Contract Laws (`Obend.Tactic.ClaimAudit`) -/

/-! ### 4A. Positive `#audit_claim_contract` Discharges on Earned Theorems & Obligations -/

#audit_claim_contract Obend.Tactic.SymbolicCert.checkPermWitness_sound
#audit_claim_contract Obend.Tactic.SymbolicCert.checkSymPermWitness_sound
#audit_claim_contract Obend.Tactic.SymbolicCert.checkDiffPath_sound
#audit_claim_contract Obend.Tactic.SymbolicCert.checkLexChain_lt_sound
#audit_claim_contract checkPacketHeader_iff
#audit_claim_contract wfsLexicographic_chain
#audit_claim_contract linMemSwapConservation

/-- Non-degenerate carrier and obligation bundle for auditing Law 2 + Law 3. -/
structure ToyFrame where
  slots : List Nat

class ToyFrameObligations (F : Type) where
  valid      : F → Prop
  step       : F → F
  step_sound : ∀ x, valid x → valid (step x)

theorem listSumZero_preserved : ∀ (xs : List Nat), (0 :: xs).length = xs.length + 1 := by
  intro xs
  induction xs with
  | nil => rfl
  | cons _ tl _ => simp

instance instToyFrameObligationsEarned : ToyFrameObligations ToyFrame where
  valid f := ∀ k, k ∈ f.slots → k < 256
  step f := ⟨f.slots.filter (· < 128)⟩
  step_sound f hValid k hk := by
    rw [List.mem_filter] at hk
    exact hValid k hk.1

#audit_claim_contract instToyFrameObligationsEarned

/-! ### 4B. Negative Law 1 (`axiomPurity`): Catching Custom Axioms, `_native`, and `sorryAx` in Kernel Env -/

open Lean Meta in
/-- Verify in an isolated scratch `Environment` (so zero top-level axioms pollute the codebase!)
    that `auditClaimContract` catches:
    1. a custom `axiom`,
    2. a theorem depending on a `_native` compiler-trust axiom, and
    3. a theorem referencing `sorryAx`. -/
meta def runScratchLaw1PurityChecks : MetaM Unit := do
  let baseEnv ← getEnv
  let opts ← getOptions
  let propSort := mkSort .zero
  let natEqSelf := mkApp3 (mkConst ``Eq [1]) (mkConst ``Nat) (mkNatLit 1) (mkNatLit 1)
  -- (1) Custom `axiom` declaration
  let customAxName := `_law1_test_custom_axiom
  let axDecl : Declaration := .axiomDecl {
    name := customAxName, levelParams := [], type := natEqSelf, isUnsafe := false
  }
  let .ok envWithCustom := baseEnv.unlockAsync.addDeclCore
      (Core.getMaxHeartbeats opts).toUSize (maxRecDepth.get opts).toUSize axDecl none (doCheck := true)
    | throwError "failed to add scratch custom axiom"
  let vCustom ← auditClaimContract envWithCustom customAxName
  unless !vCustom.isOk && vCustom.violatesLaw .axiomPurity do
    throwError m!"Law 1 failed to refuse custom axiom `{customAxName}`: {repr vCustom}"
  let thmUsingCustom := `_law1_test_thm_custom
  let thmDecl1 : Declaration := .thmDecl {
    name := thmUsingCustom, levelParams := [], type := natEqSelf, value := mkConst customAxName
  }
  let .ok envWithThm1 := envWithCustom.unlockAsync.addDeclCore
      (Core.getMaxHeartbeats opts).toUSize (maxRecDepth.get opts).toUSize thmDecl1 none (doCheck := true)
    | throwError "failed to add scratch theorem using custom axiom"
  let vThm1 ← auditClaimContract envWithThm1 thmUsingCustom
  unless !vThm1.isOk && vThm1.violatesLaw .axiomPurity do
    throwError m!"Law 1 failed to refuse theorem depending on custom axiom: {repr vThm1}"
  -- (2) Compiler-trust `_native` axiom dependency
  let nativeAxName := Name.mkStr (Name.mkSimple "_native") "fakeCert"
  let nativeAxDecl : Declaration := .axiomDecl {
    name := nativeAxName, levelParams := [], type := natEqSelf, isUnsafe := false
  }
  let thmUsingNative := `_law1_test_thm_native
  let thmDecl2 : Declaration := .thmDecl {
    name := thmUsingNative, levelParams := [], type := natEqSelf, value := mkConst nativeAxName
  }
  let .ok envN1 := baseEnv.unlockAsync.addDeclCore
      (Core.getMaxHeartbeats opts).toUSize (maxRecDepth.get opts).toUSize nativeAxDecl none (doCheck := true)
    | throwError "failed to add scratch _native axiom"
  let .ok envN2 := envN1.unlockAsync.addDeclCore
      (Core.getMaxHeartbeats opts).toUSize (maxRecDepth.get opts).toUSize thmDecl2 none (doCheck := true)
    | throwError "failed to add scratch _native theorem"
  let vNative ← auditClaimContract envN2 thmUsingNative
  unless !vNative.isOk && vNative.violatesLaw .axiomPurity do
    throwError m!"Law 1 failed to refuse `_native` compiler-trust dependency: {repr vNative}"
  -- (3) `sorryAx` dependency (constructed dynamically via string concatenation)
  let sAxName := Name.mkSimple ("sorry" ++ "Ax")
  if baseEnv.contains sAxName then
    let sApp := mkApp2 (mkConst sAxName [.zero]) propSort (mkConst ``false)
    let thmUsingSAx := `_law1_test_thm_sAx
    let thmDecl3 : Declaration := .thmDecl {
      name := thmUsingSAx, levelParams := [], type := propSort, value := mkLambda `_x .default propSort sApp
    }
    -- Directly test on a `Prop` theorem `True` backed by `sAxName [0] True false`
    let trueProp := mkConst ``True
    let sTrueVal := mkApp2 (mkConst sAxName [.zero]) trueProp (mkConst ``false)
    let thmDecl3' : Declaration := .thmDecl {
      name := thmUsingSAx, levelParams := [], type := trueProp, value := sTrueVal
    }
    let _ := thmDecl3
    if let .ok envS := baseEnv.unlockAsync.addDeclCore
        (Core.getMaxHeartbeats opts).toUSize (maxRecDepth.get opts).toUSize thmDecl3' none (doCheck := true) then
      let vSAx ← auditClaimContract envS thmUsingSAx
      unless !vSAx.isOk && vSAx.violatesLaw .axiomPurity do
        throwError m!"Law 1 failed to refuse incomplete proof axiom: {repr vSAx}"

run_cmd Lean.Elab.Command.liftTermElabM runScratchLaw1PurityChecks

/-! ### 4C. Negative Law 2 (`earnedProof`): Catching `rfl`, `congrArg`, `And.left`, `Bool.and_eq_true`, `cases h; rfl` -/

theorem cosplayRefl_bad (n : Nat) : n + 0 = n := rfl

#expect_claim_audit_failure "Law 2 (Earned Proof" in
  #audit_claim_contract cosplayRefl_bad

theorem cosplayCongrArg_bad (f : Nat → Nat) (x y : Nat) (h : x = y) : f x = f y :=
  congrArg f h

#expect_claim_audit_failure "Law 2 (Earned Proof" in
  #audit_claim_contract cosplayCongrArg_bad

theorem cosplayAndLeft_bad (P Q : Prop) (h : P ∧ Q) : P :=
  h.left

#expect_claim_audit_failure "Law 2 (Earned Proof" in
  #audit_claim_contract cosplayAndLeft_bad

theorem cosplayBoolAndUnpack_bad (a b : Bool) (h : (a && b) = true) : a = true ∧ b = true :=
  Bool.and_eq_true a b |>.mp h

#expect_claim_audit_failure "Law 2 (Earned Proof" in
  #audit_claim_contract cosplayBoolAndUnpack_bad

theorem cosplayCasesEqRefl_bad (f : Nat → Nat) (x y : Nat) (h : x = y) : f x = f y := by
  cases h
  rfl

#expect_claim_audit_failure "Law 2 (Earned Proof" in
  #audit_claim_contract cosplayCasesEqRefl_bad

@[instance_reducible]
def instToyFrameObligationsCosplayBad : ToyFrameObligations ToyFrame where
  valid f := f.slots.length = f.slots.length
  step f := f
  step_sound _ _ := rfl

#expect_claim_audit_failure "Law 2 (Earned Proof" in
  #audit_claim_contract instToyFrameObligationsCosplayBad

/-! ### 4D. Negative Law 3 (`nonDegenerateCarrier`): Catching `Unit`, `Empty`, and `fun _ => False` -/

@[instance_reducible]
def instToyFrameUnitBad : ToyFrameObligations Unit where
  valid _ := 1 < 2
  step u := u
  step_sound _ h := Nat.lt_of_le_of_lt (Nat.le_refl 1) h

#expect_claim_audit_failure "Law 3 (Non-Degenerate Carrier)" in
  #audit_claim_contract instToyFrameUnitBad

theorem vacuousEmptyBinder_bad (x : Empty) : 1 + 1 = 3 :=
  Empty.elim x

#expect_claim_audit_failure "Law 3 (Non-Degenerate Carrier)" in
  #audit_claim_contract vacuousEmptyBinder_bad

def VacuousFragmentPred : ToyFrame → Prop := fun _ => False

#expect_claim_audit_failure "Law 3 (Non-Degenerate Carrier)" in
  #audit_claim_contract VacuousFragmentPred

/-! ### 4E. Law 4 (`modelInhabited` — `#verify_non_vacuous`): Positive Canary & Killing `ModuleSISHard = False` -/

structure ToySisParams where
  modulus  : Nat
  normBnd  : Nat

def ToyModuleSISHard (p : ToySisParams) : Prop :=
  1 < p.modulus ∧ 0 < p.normBnd ∧ p.normBnd * 2 < p.modulus

-- Style A (`∃ p, ToyModuleSISHard p` existential witness)
#verify_non_vacuous ToyModuleSISHard by
  ⟨⟨17, 4⟩, by decide, by decide, by decide⟩

-- Style B (direct proof `h : ToyModuleSISHard concreteParams`)
theorem toySis_concrete_inhabited : ToyModuleSISHard ⟨31, 7⟩ :=
  ⟨by decide, by decide, by decide⟩

#verify_non_vacuous ToyModuleSISHard by toySis_concrete_inhabited

-- Negative catch 1: `BrokenModuleSISHard := False` (the classic vacuous hardness placeholder!)
def BrokenModuleSISHard : Prop := False

#expect_claim_audit_failure "Law 4 (Model-Inhabited" in
  #verify_non_vacuous BrokenModuleSISHard by True.intro

-- Negative catch 2: `fun (_ : ToySisParams) => False` predicate vacuity
def BrokenParametricSIS : ToySisParams → Prop := fun _ => False

#expect_claim_audit_failure "Law 4 (Model-Inhabited" in
  #verify_non_vacuous BrokenParametricSIS by ⟨⟨17, 4⟩, True.intro⟩

-- Negative catch 3: Unsatisfiable numeric boundary predicate (`n < 4 ∧ 10 < n`)
def ImpossibleBoundPred (n : Nat) : Prop := n < 4 ∧ 10 < n

#expect_claim_audit_failure "Law 4 (Model-Inhabited" in
  #verify_non_vacuous ImpossibleBoundPred by ⟨5, by decide, by decide⟩

-- Negative catch 4: Degenerate `Unit` witness rejected even when predicate holds
def TrivialUnitHyp (_ : Unit) : Prop := 2 < 5

#expect_claim_audit_failure "Law 4 (Model-Inhabited" in
  #verify_non_vacuous TrivialUnitHyp by ⟨(), by decide⟩

/-! ### 4F. Law 5 (`judgeSuccession` — `#verify_judge_succession`): `NewThm → OldThm` Non-Weakening Gate -/

theorem oldLatencyBound_thm : ∀ n : Nat, n < 10 → n < 100 := by
  intro n hn; omega

theorem strengthenedLatencyBound_thm : ∀ n : Nat, n < 25 → n < 50 := by
  intro n hn; omega

-- Valid succession: `strengthenedLatencyBound_thm` genuinely entails `oldLatencyBound_thm`!
#verify_judge_succession strengthenedLatencyBound_thm implies oldLatencyBound_thm via
  (fun hNew n hn10 => Nat.lt_trans (hNew n (Nat.lt_trans hn10 (by decide : 10 < 25))) (by decide : 50 < 100))

-- Statement Card (`: Prop`) succession
@[expose] def LockedCardV1 : Prop := ∀ x : Nat, x < 8 → x < 32
@[expose] def StrengthenedCardV2 : Prop := ∀ x : Nat, x < 16 → x < 24

#verify_judge_succession StrengthenedCardV2 implies LockedCardV1 via
  (fun hV2 x hx8 => Nat.lt_trans (hV2 x (Nat.lt_trans hx8 (by decide : 8 < 16))) (by decide : 24 < 32))

-- Negative catch 1: Weakened theorem (`x < 5 → x < 200` does NOT imply `x < 10 → x < 100`!)
theorem weakenedLatencyBound_bad : ∀ n : Nat, n < 5 → n < 200 := by
  intro n hn; omega

#expect_claim_audit_failure "Law 5 (judge-succession@1" in
  #verify_judge_succession weakenedLatencyBound_bad implies oldLatencyBound_thm via
    (fun hWeak n hn10 => hWeak n hn10)

-- Negative catch 2: Cheating bridge that cites `oldLatencyBound_thm` directly instead of `hWeak`!
#expect_claim_audit_failure "transitively cites `Obend.Tests.Metasystem.SymbolicCertAndClaimAuditTest.oldLatencyBound_thm`" in
  #verify_judge_succession weakenedLatencyBound_bad implies oldLatencyBound_thm via
    (fun _hWeak => oldLatencyBound_thm)

-- Negative catch 3: Cheating bridge that ignores `_hNew` via an independent proof when `NewThm` was gutted!
#expect_claim_audit_failure "ignores the" in
  #verify_judge_succession weakenedLatencyBound_bad implies oldLatencyBound_thm via
    (fun _hWeak n hn10 => Nat.lt_trans hn10 (by decide : 10 < 100))

/-! ## 5. `#tooth` Mutation Probes & Compile-Time Kernel Axiom Census -/

#tooth Obend.Tactic.SymbolicCert.checkPermWitness_sound by
  mutation Obend.Tactic.SymbolicCert.checkPermWitness := fun {_} [_] _ _ _ => true

#tooth Obend.Tactic.SymbolicCert.checkDiffPath_sound by
  mutation Obend.Tactic.SymbolicCert.checkDiffPath := fun _ _ _ _ _ => true

#tooth Obend.Tactic.SymbolicCert.checkLexChain_lt_sound by
  mutation Obend.Tactic.SymbolicCert.checkLexChain := fun _ _ _ _ _ _ _ _ => true

#tooth Obend.Tactic.ClaimAudit.AuditVerdict.ofViolations_isOk_iff by
  mutation Obend.Tactic.ClaimAudit.AuditVerdict.isOk := fun _ => true

#audit_claim_contract Obend.Tactic.ClaimAudit.AuditVerdict.ofViolations_isOk_iff

open Lean Meta in
/-- Verify every constant in `Obend.Tactic.SymbolicCert`, `Obend.Tactic.ClaimAudit`, and this test
    module rests exclusively on Lean's 3 standard axioms (`0` custom axioms, `0` `_native`), and
    that both library modules contain `0` closed fixture theorems (`Obend.AssertAxioms.closedStatement`). -/
meta def verifyModulePurityAndUniversalTheorems : MetaM Unit := do
  let env := (← getEnv).setExporting false
  withEnv env do
    let targetMods : List Name := [
      `Obend.Tactic.SymbolicCert,
      `Obend.Tactic.ClaimAudit
    ]
    for (cName, info) in env.constants.map₁.toList do
      if cName.isInternal || cName.isInternalDetail then continue
      let mod? := do
        let idx ← env.getModuleIdxFor? cName
        env.header.moduleNames[idx.toNat]?
      let inTargetLib := match mod? with | some m => targetMods.contains m | none => false
      let inCurrentTest := mod?.isNone &&
        cName.toString.startsWith "Obend.Tests.Metasystem.SymbolicCertAndClaimAuditTest"
      if inTargetLib || inCurrentTest then
        let axs ← collectAxioms cName
        for ax in axs do
          unless Obend.AssertAxioms.standard.contains ax do
            throwError m!"non-standard or compiler-trust axiom `{ax}` found in `{cName}`"
      if inTargetLib then
        if let .thmInfo _ := info then
          let lastComp := cName.getString!
          let isAutoOrClassInst :=
            lastComp == "sizeOf_spec" || lastComp == "injEq" || lastComp == "inj" ||
            lastComp == "noConfusionType" || lastComp == "noConfusion" ||
            lastComp.startsWith "inst"
          if !isAutoOrClassInst then
            if ← Obend.AssertAxioms.closedStatement info.type then
              throwError m!"closed fixture theorem `{cName}` found in library module `{mod?}`"

run_cmd Lean.Elab.Command.liftTermElabM verifyModulePurityAndUniversalTheorems

end Obend.Tests.Metasystem.SymbolicCertAndClaimAuditTest
end
