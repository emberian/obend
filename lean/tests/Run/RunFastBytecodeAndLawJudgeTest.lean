module
/-
# RunFastBytecodeAndLawJudgeTest — Verification of `Run` Fast-Path Welds & `LawJudge` / `HyperLaw` Honesty

Exercises and mutation-tests:
1. **`Obend.Run.Core4` ↔ `MachineFast` & `BytecodeRegisterJit` Welds**:
   - `turnFast` & `turnFast_eq_turn` (`@[csimp] theorem turn_eq_turnFast`)
   - `execRunCore4Fast` & `runCore4Fast_eq_spec` (multi-turn activity transcript + residual stop state)
   - `execCore4LoopFast` & `execCore4LoopFast_sound` (`30,000`-iteration dictionary-passing loop on unboxed `Array UInt64` register VM)
2. **`Obend.Run.Runner` `Array`-Backed Handler Driver**:
   - `View.maskArray` & `maskArray_eq_mask`
   - `driveFast` & `driveFast_eq_drive` ($O(1)$ `Array.push` accumulation vs $O(N^2)$ `List` appends)
3. **`Obend.Run.LawJudge` & `Obend.Run.HyperLaw` Honest `Obend.Judge` Instances**:
   - `lawSubmissionJudge` (`Fragment`, `refutes`, `checkLawSubmission_sound`, `checkLawSubmission_refuted`, `lawSubmissionJudge_inhabited`)
   - `glEquilibriumJudge` (`checkGLEquilibrium_refuted`, `self_defeating_modal_refused_on_p`)
-/

public import Obend.Run.Core4
public import Obend.Run.Runner
public import Obend.Run.LawJudge
public import Obend.Run.HyperLaw
public import Obend.Tactic.Tooth
meta import all Obend.Run.Core4
meta import all Obend.Leaf.BytecodeRegisterJit
meta import all Obend.Core.Machine
meta import all Obend.Core.MachineFast
meta import all Obend.Core.RangeSafe
import all Obend.Run.Core4
import all Obend.Run.Runner
import all Obend.Run.LawJudge
import all Obend.Run.HyperLaw

public section

namespace Obend.Tests.Run.RunFastBytecodeAndLawJudgeTest

open Obend.Core.Term (Term)
open Obend.Core.Data (Data Budget)
open Obend.Core.Machine (State Limits initial)
open Obend.Slot Obend.Slot.Protocol
open Obend.Run
open Obend.Run.Core4
open Obend.Run.HyperLaw

set_option autoImplicit false

/-! ## 1. `Run.Core4` Fast-Path Welds (`turnFast`, `execRunCore4Fast`, `execCore4LoopFast`) -/

theorem test_core4_fast_path_theorems
    (L : Limits) (ticks : Nat) (budget : Budget)
    (respondFn : Data → Data) (depth : Nat) (s : State) :
    turnFast L ticks budget s = turn L ticks budget s ∧
    (execRunCore4Fast L ticks budget respondFn depth s).1.size ≤ depth ∧
    Transcript L ticks budget s
      (execRunCore4Fast L ticks budget respondFn depth s).1.toList
      (execRunCore4Fast L ticks budget respondFn depth s).2.1 ∧
    unfold L ticks budget
      (depth - (execRunCore4Fast L ticks budget respondFn depth s).1.size)
      (execRunCore4Fast L ticks budget respondFn depth s).2.1 =
      .ret (execRunCore4Fast L ticks budget respondFn depth s).2.2 := by
  have hSpec := runCore4Fast_eq_spec L ticks budget respondFn depth s
  exact ⟨turnFast_eq_turn L ticks budget s, hSpec.1, hSpec.2.1, hSpec.2.2⟩

#guard execCore4LoopFast 4 30000 450015000
    Obend.Leaf.BytecodeRegisterJit.sumToDictStep 30000 0 == some (.natural 450015000)

#guard
  let prog : Term :=
    .binary .add
      (.perform (.nat 10))
      (.binary .multiply (.perform (.nat 4)) (.nat 5))
  let res := execRunCore4Fast ⟨64, 64⟩ 120 ⟨64, 64, 64⟩
    (fun | .natural k => .natural (k + 2) | d => d) 6 (initial prog)
  res.1.size == 2 &&
  (match res.2.2 with | .ended (.finished (.natural 42) _) => true | _ => false)

/-! ## 2. `Run.Runner` `Array`-Backed `driveFast` & `View.maskArray` -/

theorem test_runner_driveFast_refinement
    {Ix : Type} {S : Sig Ix} {Hole : Ix → Type} {A : Ix → Type}
    {Tok Fact Ob V St : Type}
    [DecidableEq (Σ i, S.Op i)] [DecidableEq Ix] [∀ i, DecidableEq (Hole i)] [DecidableEq Tok]
    (host : Host V Tok Fact) (sp : Spec S Tok Fact Ob)
    (H : Handler S (fun _ => St)) {i : Ix} (n : Nat)
    (c : Cfg S Hole A Tok Fact Ob V i) (s : St) (spent : Array Tok) :
    View.maskArray (host.view c.world) spent = View.mask (host.view c.world) spent.toList ∧
    driveFast host sp H n c s = drive host sp H n c s :=
  ⟨maskArray_eq_mask (host.view c.world) spent, driveFast_eq_drive host sp H n c s⟩

/-! ## 3. `LawJudge` & `HyperLaw` Honest `Obend.Judge` Verification -/

theorem test_lawJudge_and_glEquilibrium_honesty :
    (∃ (q : LawSubmissionProblem) (k : Nat),
      lawSubmissionJudge.Fragment q ∧
      checkLawSubmission k q () = .ok ∧
      LawSubmissionAdmitted q ()) ∧
    (∃ (q : LawSubmissionProblem) (k : Nat) (c : LawJudgeClause) (path : List Nat),
      checkLawSubmission k q () = .refused c path ∧
      lawSubmissionRefutes c = true ∧
      ¬ LawSubmissionAdmitted q ()) ∧
    (checkGLEquilibrium selfDefeatingModalProg ["p"] =
      .refused (.unsatisfiableOddLoop "p") [] ∧
     glRefutes (.unsatisfiableOddLoop "p") = true ∧
     ∀ cand : FactSet, ¬ IsStableEquilibrium selfDefeatingModalProg cand) := by
  have ⟨hFrag, ⟨kOk, hOk⟩, ⟨kBad, hBad⟩, _⟩ := lawSubmissionJudge_inhabited
  refine ⟨⟨_, kOk, hFrag, hOk, checkLawSubmission_sound hOk⟩,
          ⟨_, kBad, _, _, hBad, rfl, checkLawSubmission_refuted hBad rfl⟩,
          ⟨self_defeating_modal_refused_on_p, rfl,
           fun cand hEq => checkGLEquilibrium_refuted self_defeating_modal_refused_on_p rfl cand hEq⟩⟩

/-! ## 4. `#tooth` Mutation Barriers & Axiom Audit -/

#tooth Obend.Run.Core4.turnFast_eq_turn by
  mutation Obend.Run.Core4.turnFast := fun _ _ _ _ => .stop .depth

#tooth Obend.Run.Core4.runCore4Fast_eq_spec by
  mutation Obend.Run.Core4.execRunCore4Fast := fun _ _ _ _ _ s => (#[], s, .depth)

#tooth Obend.Run.maskArray_eq_mask by
  mutation Obend.Run.View.maskArray := fun v _ => v

#tooth Obend.Run.driveFast_eq_drive by
  mutation Obend.Run.driveFast := by
    intros
    exact Drive.halted ‹Cfg _ _ _ _ _ _ _ _› ‹_›

#print axioms turnFast_eq_turn
#print axioms runCore4Fast_eq_spec
#print axioms execCore4LoopFast_sound
#print axioms maskArray_eq_mask
#print axioms driveFast_eq_drive
#print axioms checkLawSubmission_sound
#print axioms checkLawSubmission_refuted
#print axioms lawSubmissionJudge_inhabited
#print axioms oddSelfLoop_no_equilibrium
#print axioms checkGLEquilibrium_refuted
#print axioms test_core4_fast_path_theorems
#print axioms test_runner_driveFast_refinement
#print axioms test_lawJudge_and_glEquilibrium_honesty

end Obend.Tests.Run.RunFastBytecodeAndLawJudgeTest

end
