module
/- The ground teeth of `tests/obend-source/ReviewMember.obend` (transcribed in `FrameTeeth`), the
cohort's `twiceOfThree() == 7` (preview-cohort row `ImportedReview`):

* at `fix(compose(Base, Twice, Augmented), seed)` it runs to `true`: accepted, `Holds`;
* with `Augmented` mutated to `super.review(value) + 2`, it runs to `false`: refused `falseAt`,
  which refutes (`ground_refutes`);
* with `Override` composed last, the claim `repeated` itself runs to `false` at `3` (`3 == 7`):
  refuted of that object, as its rewrite certificate was refused there (`FrameTeeth.frame_refused`). -/
public import Obend.Logic.Ground
public import Obend.Teeth.Logic.FrameTeeth
@[expose] public section
open Obend.Core.Term Obend.Logic
open Obend.Core.Data (Data)

namespace Obend.Teeth.Logic.Review

/-- `twiceOfThree() == 7` at the object of `compose(Base, Twice, Augmented(n))`. -/
def twiceOfThree (n : Nat) : ClaimProblem :=
  ⟨.binary .equal (.app (.get (object n).comp.object "twice") (.nat 3)) (.nat 7), []⟩

theorem ground_seven : groundCheck 160 (twiceOfThree 1) () = .ok := by decide +kernel

theorem ground_mutated_refuted : groundCheck 160 (twiceOfThree 2) () = .refused .falseAt [] := by decide +kernel

theorem twiceOfThree_holds : Holds (twiceOfThree 1).claim [] := ground_sound ground_seven

theorem twiceOfThree_mutated_false : ¬ Holds (twiceOfThree 2).claim [] := ground_refutes ground_mutated_refuted

/-- `repeated` at `3`, at the overridden object. -/
def repeatedOverridden : ClaimProblem :=
  ⟨instantiateClaim repeated overridden.comp overridden.layer, [.natural 3]⟩

theorem repeated_overridden_refuted : groundCheck 160 repeatedOverridden () = .refused .falseAt [] := by
  decide +kernel

/-- And at the composed object it holds at `3`, `0` and `41`. -/
theorem repeated_ground_3 : groundCheck 400 ⟨instantiateClaim repeated (object 1).comp 1, [.natural 3]⟩ () = .ok := by
  decide +kernel
theorem repeated_ground_0 : groundCheck 400 ⟨instantiateClaim repeated (object 1).comp 1, [.natural 0]⟩ () = .ok := by
  decide +kernel
theorem repeated_ground_41 : groundCheck 400 ⟨instantiateClaim repeated (object 1).comp 1, [.natural 41]⟩ () = .ok := by
  decide +kernel

end Obend.Teeth.Logic.Review
end
