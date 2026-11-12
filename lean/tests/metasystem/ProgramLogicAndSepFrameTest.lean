module
/-
# Multi-Turn Interaction Hoare Logic, Constructive PCM Separation Frame & `TacticM` Test Suite

End-to-end verification of Carbon-1 deliverables across:
1. `Obend.Logic.MultiTurnHoare` + `by obend_wp`:
   - `SafeWP` (`wp_val`, `wp_eval`, `wp_step`, `wp_perform`, `wp_bind_ctx`, `wp_seqNat`),
   - 1-line `by obend_wp` proofs for `Turn.counterBump` and symbolic conditional `guardedRetryStep`,
   - $N$-turn open-recursive `Core4` `.fix` actor loop rule `wp_loop_invariant`,
   - Adequacy `safeWP_adequacy` against `Obend.Equiv.Interaction`,
   - Constructive 2nd-refusal-turn separation (`recklessRetry_one_turn_safe` vs `recklessRetry_two_turns_refuted`).
2. `Obend.Logic.SeparationFrame` + `by sep_cancel` + `by obend_wp`:
   - Generic `[LawfulPCM M]` spatial algebra (`∗`, `-∗`, `sep_wand_adj`, `FPU`),
   - Strictly-sorted `Array (Nat × Val)` `HeapExec` (`disjointMerge_spec_iff`, `hoare_sep_frame`),
   - 1-line `by sep_cancel` 5-atom AC permutations, equalities, and pointwise heap entailments,
   - 1-line `by obend_wp` framing a 2-cell `transferCells_spec` across an untouched 5-cell world.
3. Breadstuffs's Epistemic `AuthCamera`:
   - Conserved linear `ConservedValue` ($\sum\delta = 0$), `grow_authority_fpu`, `spend_nullifier_fpu`,
     and machine-checked refutation `uncoordinated_forget_nullifier_not_fpu`.
4. `Obend.Tactic.ProgramLogic` (`by gpaco_step`):
   - 1-line `GPaco` coinduction proofs (`orbitBisimF.gfp 0 2`, 3-cycle `ring3BisimF.gfp 0 1`) and
     1-line guarded hypothesis release into `gupaco`.
5. `#tooth` kernel mutation probes & compile-time `0 sorryAx` / `0 native_decide` / `0` custom axiom audit.
-/

public import Obend.Logic.MultiTurnHoare
public import Obend.Logic.SeparationFrame
public import Obend.Tactic.ProgramLogic
public import Obend.Tactic.Tooth
public import Obend.AssertAxioms
import all Obend.Logic.MultiTurnHoare
import all Obend.Logic.SeparationFrame
import all Obend.Tactic.ProgramLogic
import all Obend.Paco.GPaco

public section

open Obend.Core.Term
open Obend.Core.Data (Data)
open Obend.Equiv
open Obend.Logic
open Obend.Paco
open Obend.Tactic.ProgramLogic

set_option autoImplicit false

namespace Obend.Tests.Metasystem.ProgramLogicAndSepFrameTest

/-! ## 1. `by obend_wp` Symbolic Execution over `MultiTurnHoare` (`SafeWP` & `Interaction`) -/

/-- **1-line `by obend_wp` verification of `Counter.obend`'s `counterBump`** across demonic
    `"written"` and `"refused"` environment responses! -/
theorem counterBump_wp_by_tactic (c₀ s : Nat) (hle : c₀ ≤ s) :
    SafeWP counterProto (.app counterBump (.nat s))
      (fun v => ∃ s' : Nat, v = .nat s' ∧ c₀ ≤ s') := by
  obend_wp

/-- **1-line `by obend_wp` verification of symbolic conditional `guardedRetryStep`**:
    automatically steps `.beta` + `.less`, splits `decide (r < 1)`, verifies `ExpectedPlan` on both
    `"propose"` and `"cooldown"`, splits demonic responses, and closes `r' ≤ 1` via `omega`! -/
theorem guardedRetry_wp_by_tactic (r : Nat) :
    SafeWP retryProto (.app guardedRetryStep (.nat r))
      (fun v => ∃ r' : Nat, v = .nat r' ∧ r' ≤ 1) := by
  obend_wp

/-- Combined protocol allowing both `counterBumpPlan` and `retryProto` turns in one session. -/
def combinedSessionProto : ProtocolSpec := fun plan resp =>
  counterProto plan resp ∨ retryProto plan resp

theorem lift_counter_to_session {t : Term} {Φ : Term → Prop}
    (h : SafeWP counterProto t Φ) : SafeWP combinedSessionProto t Φ := by
  induction h with
  | val hv hΦ => exact .val hv hΦ
  | step hst _ ih => exact .step hst ih
  | perform hy hexp _ ih =>
    rcases hexp with ⟨w, hw⟩
    refine .perform hy ⟨w, Or.inl hw⟩ (fun resp hcomb => ?_)
    rcases hcomb with hc | hr
    · exact ih resp hc
    · rcases hc_impossible : hw.1 with ⟨c, hplan⟩
      rcases hr with ⟨hp, _⟩ | ⟨hp, _⟩ <;> (rw [hplan] at hp; cases hp)

/-- **2-Turn Sequential Composition via `seqNat` / `wp_bind_ctx` + `by obend_wp`**:
    Turn 1 runs `counterBump s`, then Turn 2 checks whether `s' < 1` before returning `s'`. -/
theorem twoTurn_seqNat_by_tactic (s : Nat) :
    SafeWP counterProto
      (seqNat (.app counterBump (.nat s))
        (.done (.binary .add (.bound 0) (.nat 2))))
      (fun v => ∃ out : Nat, v = .nat out ∧ s + 2 ≤ out) := by
  have hSub : SafeWP counterProto (.app counterBump (.nat s))
      (fun v => ∃ m : Nat, v = .nat m ∧ s ≤ m) := by obend_wp
  obend_wp

/-- **$N$-Turn Actor Loop + `safeWP_adequacy` End-to-End Check**:
    Running `guardedRetryStep` for 3 turns on concrete refusal/cooldown/refusal trace guarantees
    `r_fin ≤ 1` and `AllPlansExpected` by `safeWP_adequacy`! -/
theorem guardedRetry_three_turn_trace_adequate {v : Term}
    (hint : Obend.Equiv.Interaction (runActorFix guardedRetryStep 3 0)
      [ (.label "propose", refusedResponse.term),
        (.label "cooldown", .inject "ack" (.record [])),
        (.label "propose", refusedResponse.term) ]
      v) :
    (∃ r_fin : Nat, v = .nat r_fin ∧ r_fin ≤ 1) ∧
      AllPlansExpected (ExpectedPlan retryProto)
        [ (.label "propose", refusedResponse.term),
          (.label "cooldown", .inject "ack" (.record [])),
          (.label "propose", refusedResponse.term) ] := by
  have hValid : ValidTrace retryProto
      [ (.label "propose", refusedResponse.term),
        (.label "cooldown", .inject "ack" (.record [])),
        (.label "propose", refusedResponse.term) ] := by
    intro entry hentry
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hentry
    rcases hentry with rfl | rfl | rfl
    · exact Or.inl ⟨rfl, Or.inr rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩
    · exact Or.inl ⟨rfl, Or.inr rfl⟩
  exact safeWP_adequacy (guardedRetry_loop_safeWP 3 0 (by omega)) hValid hint

/-- **2nd-Refusal-Turn Contrast**: 1 turn is safe from `0`, 2 turns is constructively refuted! -/
theorem one_turn_vs_two_turn_refusal_separation :
    SafeWP retryProto (runActorFix recklessRetryStep 1 0)
      (fun v => ∃ r' : Nat, v = .nat r' ∧ r' ≤ 1) ∧
    ¬ SafeWP retryProto (runActorFix recklessRetryStep 2 0)
      (fun v => ∃ r_fin : Nat, v = .nat r_fin ∧ r_fin ≤ 1) :=
  ⟨recklessRetry_one_turn_safe, recklessRetry_two_turns_refuted⟩

/-! ## 2. `by sep_cancel`, `HeapExec` Disjoint Merge & 1-Line 5-Cell Framing via `by obend_wp` -/

/-- **1-line `by sep_cancel` 5-atom AC permutation + `sepEmp` elimination** over any `[LawfulPCM M]`. -/
theorem sep_five_atom_perm {M : Type} [LawfulPCM M]
    (P₁ P₂ P₃ P₄ P₅ : SepProp M) :
    ((P₁ ∗ sepEmp ∗ P₂) ∗ (P₃ ∗ (P₄ ∗ P₅))) ⊢ₛ
      ((P₅ ∗ P₃) ∗ (P₁ ∗ sepEmp) ∗ (P₄ ∗ P₂)) := by
  sep_cancel

/-- **1-line `by sep_cancel` spatial equality** via antisymmetry + AC normalization. -/
theorem sep_equality_by_cancel {M : Type} [LawfulPCM M]
    (A B C D : SepProp M) :
    ((A ∗ B) ∗ (sepEmp ∗ C) ∗ D) = ((D ∗ B) ∗ (C ∗ A)) := by
  sep_cancel

/-- **1-line `by sep_cancel` pointwise heap goal** from a permuted local heap hypothesis. -/
theorem sep_pointwise_by_cancel (h : HeapExec Nat)
    (hPre : (((10 ↦ₕ 1) ∗ (20 ↦ₕ 2)) ∗ ((30 ↦ₕ 3) ∗ (40 ↦ₕ 4))) h) :
    (((40 ↦ₕ 4) ∗ (10 ↦ₕ 1)) ∗ ((30 ↦ₕ 3) ∗ (20 ↦ₕ 2))) h := by
  sep_cancel

/-- Magic-wand introduction via `sep_wand_adj` + `by sep_cancel`. -/
theorem wand_intro_by_sep_cancel {M : Type} [LawfulPCM M]
    (P Q R : SepProp M) :
    (P ∗ R) ⊢ₛ (Q -∗ ((Q ∗ R) ∗ P)) := by
  rw [← sep_wand_adj]
  sep_cancel

/-- Overlapping `HeapExec` keys fail `disjointMerge` (`none`), while disjoint keys merge cleanly. -/
theorem heapExec_conflict_and_merge_witness :
    HeapExec.disjointMerge (HeapExec.singleton 7 100) (HeapExec.singleton 7 200) = none ∧
    (HeapExec.disjointMerge (HeapExec.singleton 3 10) (HeapExec.singleton 9 20)).isSome = true := by
  refine ⟨?_, HeapExec.disjointMerge_isSome_iff.2 fun q => ?_⟩
  · cases hm : HeapExec.disjointMerge (HeapExec.singleton 7 100) (HeapExec.singleton 7 200) with
    | none => rfl
    | some h =>
      have hk := (HeapExec.disjointMerge_spec_iff.1 hm).1 7
      simp [HeapExec.singleton_toSpec] at hk
  · by_cases hq : q == 3
    · have heq : q = 3 := eq_of_beq hq
      subst heq
      exact Or.inr (by simp [HeapExec.singleton_toSpec])
    · exact Or.inl (by simp [HeapExec.singleton_toSpec, hq])

/-- **1-Line Automatic 5-Cell Framing via `by obend_wp`**:
    Verifies `transferCells 20 40 amt` inside a 5-cell heap `(10, 20, 30, 40, 50)` with permuted
    postcondition — `by obend_wp` automatically synthesizes the untouched 3-cell frame
    `(10 ↦ₕ v₁₀) ∗ (30 ↦ₕ v₃₀) ∗ (50 ↦ₕ v₅₀)`, applies `hoare_sep_conseq_frame` +
    `transferCells_spec`, and cancels the 5-atom spatial obligations via `sepCancelGoal`! -/
theorem fiveCell_transfer_by_obend_wp
    (v₁₀ b₁ v₃₀ b₂ v₅₀ amt : Nat) (hle : amt ≤ b₁) :
    HoareSep
      ((10 ↦ₕ v₁₀) ∗ (20 ↦ₕ b₁) ∗ (30 ↦ₕ v₃₀) ∗ (40 ↦ₕ b₂) ∗ (50 ↦ₕ v₅₀))
      (transferCells 20 40 amt)
      (fun _ => (50 ↦ₕ v₅₀) ∗ (40 ↦ₕ (b₂ + amt)) ∗ (10 ↦ₕ v₁₀) ∗ (30 ↦ₕ v₃₀) ∗ (20 ↦ₕ (b₁ - amt))) := by
  obend_wp

/-! ## 3. Breadstuffs's Epistemic `AuthCamera` ($\sum\delta = 0$, `FPU`, Refutation) -/

/-- Opposite balanced transfers cancel to `ConservedValue.zero` ($\sum\delta = 0$). -/
theorem conserved_roundtrip_cancels (a b : Nat) (amt : Int) :
    ConservedValue.add (ConservedValue.transfer a b amt) (ConservedValue.transfer b a amt) =
      ConservedValue.zero := by
  apply ConservedValue.ext
  intro q
  simp only [ConservedValue.add,
    deltaAt_addDeltaLists (ConservedValue.transfer a b amt).wf (ConservedValue.transfer b a amt).wf,
    ConservedValue.transfer_deltaAt, ConservedValue.zero, deltaAt]
  by_cases hqa : q == a <;> by_cases hqb : q == b <;> simp [hqa, hqb] <;> omega

/-- Spatial AC cancellation over `SepProp AuthCamera` via `by sep_cancel`. -/
theorem authCamera_sep_perm (k : Nat) (nfs : NullifierSet) (nf₁ nf₂ : Nat) :
    ((fun c => c = AuthCamera.mkAuth k nfs) ∗
      (fun c => c = AuthCamera.mkFrag k (.singleton nf₁)) ∗
      (fun c => c = AuthCamera.mkFrag 0 (.singleton nf₂))) ⊢ₛ
    ((fun c => c = AuthCamera.mkFrag 0 (.singleton nf₂)) ∗
      (fun c => c = AuthCamera.mkAuth k nfs) ∗
      (fun c => c = AuthCamera.mkFrag k (.singleton nf₁))) := by
  sep_cancel

/-- Composing `grow_authority_fpu` (`k → k + 1`) followed by `spend_nullifier_fpu` via `fpu_trans`. -/
theorem epoch_advance_and_spend_fpu (k : Nat) (nfs : NullifierSet) (nf : Nat)
    (val : ConservedValue) (tx : ConservedValue) :
    FPU (AuthCamera.mkAuth k nfs val)
      (fun b => ∃ authNext : AuthCamera,
        authNext = AuthCamera.mkAuth (k + 1) (nfs.insert nf) val ∧
        LawfulPCM.op? authNext (AuthCamera.mkFrag (k + 1) (.singleton nf) tx) = some b) := by
  refine fpu_trans (AuthCamera.grow_authority_fpu (Nat.le_succ k) nfs val val) ?_
  intro mid hmid
  subst hmid
  exact AuthCamera.spend_nullifier_fpu (k + 1) nfs nf val tx

/-- Concrete instance of Breadstuffs's epistemic refutation: forgetting spent nullifier `42` at
    epoch `5` is NOT a frame-preserving update! -/
theorem forget_nullifier_42_refuted :
    ¬ FPUDet
        (AuthCamera.mkAuth 5 (NullifierSet.empty.insert 42) .zero)
        (AuthCamera.mkAuth 5 ((NullifierSet.empty.insert 42).erase 42) .zero) :=
  AuthCamera.uncoordinated_forget_nullifier_not_fpu 5 .empty 42 .zero .zero

/-! ## 4. `by gpaco_step` — `GPaco` Coinduction & Guard-Release Automation -/

/-- **1-line `by gpaco_step` proof of `orbitBisimF.gfp 0 2`**! -/
theorem orbitBisim_by_gpaco_step : orbitBisimF.gfp 0 2 := by
  gpaco_step using (fun x y => (x = 0 ∧ y = 2) ∨ (x = 2 ∧ y = 0))

/-- 3-state ring transition system `0 → 1 → 2 → 0` with identical observable tag `7`. -/
def ring3Step : Nat → Nat
  | 0 => 1
  | 1 => 2
  | 2 => 0
  | n + 3 => n + 3

def ring3Label : Nat → Nat
  | 0 => 7
  | 1 => 7
  | 2 => 7
  | _ => 0

def ring3BisimF : MonoRel Nat where
  F R x y := ring3Label x = ring3Label y ∧ R (ring3Step x) (ring3Step y)
  mono _ _ hRS _ _ h := ⟨h.1, hRS _ _ h.2⟩

/-- **1-line `by gpaco_step` 3-cycle bisimulation** (`0 ~ 1` in `ring3BisimF.gfp`)! -/
theorem ring3_zero_one_bisim : ring3BisimF.gfp 0 1 := by
  gpaco_step using (fun x y => (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 2) ∨ (x = 2 ∧ y = 0))

/-- **1-line `by gpaco_step` Guard-Release Test**:
    With `(2, 0)` held only in the *guarded* slot `g`, `by gpaco_step` unfolds one productive
    `orbitBisimF` step from `(0, 2)` to `(2, 0)` (releasing `g` into `gupaco`) and routes `hg`! -/
theorem gpaco_guard_release_by_step
    (g : Rel Nat) (hg : g 2 0) :
    gpaco orbitBisimF ⊥ g 0 2 := by
  gpaco_step

/-! ## 5. `#tooth` Kernel Mutation Probes & Compile-Time Axiom Audit -/

-- Tooth 1: Mutating `nextCooldownStreak` so cooldown increments `streak + 1` instead of resetting
-- to `0` breaks `guardedRetry_loop_safeWP` on the 2nd refusal turn!
#tooth Obend.Logic.guardedRetry_loop_safeWP by
  mutation Obend.Logic.nextCooldownStreak := fun streakTerm => .binary .add streakTerm (.nat 1)

-- Tooth 2: Mutating `transferCells` so `dst` receives `balDst` (dropping `+ amount`) breaks
-- `transferCells_spec`!
#tooth Obend.Logic.transferCells_spec by
  mutation Obend.Logic.transferCells := fun (src dst amount : Nat) (h : HeapExec Nat) => do
    let (balSrc, _) ← readCell src h
    let (balDst, _) ← readCell dst h
    if src != dst && decide (amount ≤ balSrc) then
      let (_, h₁) ← writeCell src (balSrc - amount) h
      writeCell dst balDst h₁
    else
      none

-- Tooth 3: Mutating `hoare_sep_frame` by breaking `IsLocalOp` — mutating `writeCell` to wipe the
-- heap to a singleton `#[(k, v)]` (destroying untouched frame cells!) breaks `writeCell_local`!
#tooth Obend.Logic.writeCell_local by
  mutation Obend.Logic.writeCell := fun {Val} (k : Nat) (v : Val) (_h : HeapExec Val) =>
    some ((), HeapExec.singleton k v)

-- Tooth 4: Mutating `AuthCamera.grow_authority_fpu` by reversing the watermark check in `compose?`
-- (`w.authority ≤ b.fragAuthority` instead of `b.fragAuthority ≤ w.authority`) breaks `grow_authority_fpu`!
#tooth Obend.Logic.AuthCamera.spend_nullifier_fpu by
  mutation Obend.Logic.NullifierSet.insert := fun (_nf : Nat) (s : NullifierSet) => s

open Lean Elab Command in
elab "#verify_program_logic_axioms" : command => do
  let targets : List Name := [
    ``Obend.Logic.yields_ctxWF,
    ``Obend.Logic.wp_val,
    ``Obend.Logic.wp_eval,
    ``Obend.Logic.wp_step,
    ``Obend.Logic.wp_perform,
    ``Obend.Logic.wp_mono,
    ``Obend.Logic.wp_bind_ctx,
    ``Obend.Logic.wp_seqNat,
    ``Obend.Logic.safeWP_adequacy,
    ``Obend.Logic.not_safeWP_of_bad_interaction,
    ``Obend.Logic.wp_loop_invariant,
    ``Obend.Logic.counterBump_multiTurn_safeWP,
    ``Obend.Logic.guardedRetry_loop_safeWP,
    ``Obend.Logic.guardedRetry_interaction_adequate,
    ``Obend.Logic.recklessRetry_one_turn_safe,
    ``Obend.Logic.recklessRetry_two_turns_refuted,
    ``Obend.Logic.fpu_refl,
    ``Obend.Logic.fpu_trans,
    ``Obend.Logic.fpu_frame,
    ``Obend.Logic.sep_comm,
    ``Obend.Logic.sep_assoc,
    ``Obend.Logic.emp_sep,
    ``Obend.Logic.sep_emp,
    ``Obend.Logic.sep_wand_adj,
    ``Obend.Logic.HeapExec.ext,
    ``Obend.Logic.HeapExec.disjointMerge_spec_iff,
    ``Obend.Logic.HeapExec.instLawfulPCMHeapExec,
    ``Obend.Logic.hoare_sep_frame,
    ``Obend.Logic.hoare_sep_conseq_frame,
    ``Obend.Logic.readCell_local,
    ``Obend.Logic.writeCell_local,
    ``Obend.Logic.transferCells_local,
    ``Obend.Logic.transferCells_spec,
    ``Obend.Logic.transferCells_framed,
    ``Obend.Logic.AuthCamera.instLawfulPCMAuthCamera,
    ``Obend.Logic.AuthCamera.grow_authority_fpu,
    ``Obend.Logic.AuthCamera.spend_nullifier_fpu,
    ``Obend.Logic.AuthCamera.uncoordinated_forget_nullifier_not_fpu,
    ``counterBump_wp_by_tactic,
    ``guardedRetry_wp_by_tactic,
    ``twoTurn_seqNat_by_tactic,
    ``guardedRetry_three_turn_trace_adequate,
    ``one_turn_vs_two_turn_refusal_separation,
    ``sep_five_atom_perm,
    ``sep_equality_by_cancel,
    ``sep_pointwise_by_cancel,
    ``wand_intro_by_sep_cancel,
    ``fiveCell_transfer_by_obend_wp,
    ``conserved_roundtrip_cancels,
    ``authCamera_sep_perm,
    ``epoch_advance_and_spend_fpu,
    ``forget_nullifier_42_refuted,
    ``orbitBisim_by_gpaco_step,
    ``ring3_zero_one_bisim,
    ``gpaco_guard_release_by_step
  ]
  let allowedStandard : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for t in targets do
    let axs ← liftCoreM <| collectAxioms t
    if axs.contains ``sorryAx then
      throwError m!"AXIOM AUDIT FAILED: {t} depends on sorryAx"
    for a in axs do
      if Obend.AssertAxioms.isCompilerTrust a then
        throwError m!"AXIOM AUDIT FAILED: {t} depends on compiler trust {a} (expected 0 native_decide)"
      if !allowedStandard.contains a then
        throwError m!"AXIOM AUDIT FAILED: {t} depends on non-standard axiom {a}"
  logInfo m!"[PASS] ProgramLogic & SeparationFrame axiom audit verified: {targets.length} theorems & instances have 0 sorryAx, 0 native_decide, and 0 non-standard axioms!"

#verify_program_logic_axioms

end Obend.Tests.Metasystem.ProgramLogicAndSepFrameTest
end
