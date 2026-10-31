module
/- The teeth of the claim judge and T3 `claim_frame` (`Obend.Logic.Frame`), on a transcription of
`tests/obend-source/ReviewMember.obend` as Elaborate lowers it (the end-to-end run over the
elaborator's own output is `tests/run-logic.py`).

* The derivation `[congr (□ value) self.twice [lateBinding twice Twice], run 1]` is accepted for
  `fix(compose(Base, Twice, Augmented), seed)`; its one support is `twice ↦ Twice`.
* Frame: with `Override` (re-providing `twice`) composed last, the support no longer holds and the
  same derivation is refused at its late-binding step, `[0, 0]`; with a layer that does not provide
  `twice` composed last instead, it is accepted unchanged (`claim_frame`'s positive direction).
* The mutation of `Augmented` to `+ 2` keeps the derivation (the claim is about open recursion and
  never unfolds `review`), which is why the ground judge carries that tooth (`GroundTeeth`). -/
public import Obend.Logic.Obligation
@[expose] public section
open Obend.Core.Term Obend.Logic

namespace Obend.Teeth.Logic.Review

def specMeta (name : String) : Term := .inject "declared" (.record [("name", .label name)])

def layer (name : String) (fields : List (String × Term)) : Layer :=
  { name, metadata := specMeta name, fields }

/-- `def review(value): value + 1`. -/
def base : Layer := layer "ReviewBase.Base" [("review", .lam (.binary .add (.bound 0) (.nat 1)))]
/-- `def twice(value): self.review(self.review(value))`. -/
def twice : Layer := layer "ReviewMember.Twice" [("twice", .lam (.app (.get (.bound 2) "review") (.app (.get (.bound 2) "review") (.bound 0))))]
/-- `def review(value): super.review(value) + n`. -/
def augmented (n : Nat) : Layer := layer "ReviewMember.Augmented" [("review", .lam (.binary .add (.app (.get (.bound 1) "review") (.bound 0)) (.nat n)))]
/-- `def twice(value): value`. -/
def override : Layer := layer "ReviewMember.Override" [("twice", .lam (.bound 0))]
/-- A layer that adds a member nobody reads. -/
def unrelated : Layer := layer "ReviewMember.Unrelated" [("note", .nat 0)]

def seed : List (String × Term) := [("review", .lam (.bound 0)), ("twice", .lam (.bound 0))]

/-- `claim repeated(value: Nat): self.twice(value) == self.review(self.review(value))`. -/
def repeated : Term :=
  .lam (.lam (.lam (.binary .equal (.app (.get (.bound 2) "twice") (.bound 0))
    (.app (.get (.bound 2) "review") (.app (.get (.bound 2) "review") (.bound 0))))))

def object (n : Nat) : ClaimObj := ⟨⟨augmented n, [twice, base], seed⟩, 1, repeated, 1⟩

def derivation : List RStep :=
  [.congr (.app (.bound 0) (.bound 1)) (.get (.bound 2) "twice") [.lateBinding "twice" "ReviewMember.Twice"],
   .run 1]

theorem accepted : claimCheck 4 (object 1) derivation = .ok := by decide +kernel

theorem accepted_mutated : claimCheck 4 (object 2) derivation = .ok := by decide +kernel

def overridden : ClaimObj := ⟨⟨override, [augmented 1, twice, base], seed⟩, 2, repeated, 1⟩

theorem frame_refused : claimCheck 4 overridden derivation = .refused (.rewrite .stepMismatch) [0, 0] := by
  decide +kernel

theorem frame_support_moves :
    (symUnfold overridden.comp 2 "twice").map (·.1) = some "ReviewMember.Override" ∧
      (symUnfold (object 1).comp 2 "twice").map (·.1) = some "ReviewMember.Twice" := by decide +kernel

def extended : ClaimObj := ⟨⟨unrelated, [augmented 1, twice, base], seed⟩, 2, repeated, 1⟩

theorem frame_kept : claimCheck 4 extended derivation = .ok :=
  claim_frame accepted (C' := extended.comp) (j' := 2)
    (by intro m hm; simp [derivation, membersList, RStep.members] at hm; subst hm; rfl) (by decide +kernel)

/-- The members a status names as blocked. -/
def blockedOf : Status → List String
  | .blocked ms => ms
  | _ => []

theorem slot_blocked_twice : blockedOf (readStatus (object 1) 4 overridden.comp (some derivation) none none) = ["twice"] := by
  decide +kernel

theorem slot_checked : (readStatus (object 1) 4 (object 1).comp (some derivation) none none).label = "checked" ∧
    (readStatus (object 1) 4 extended.comp (some derivation) none none).label = "checked" := by
  decide +kernel

end Obend.Teeth.Logic.Review
end
