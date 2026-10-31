module
/- Faré's two laziness tests on Core4's reference semantics, stated with `≈b`.
`keep(7, fix(identity))` is `7`, and stays `7` when the discarded argument diverges;
`{good = 7, bad = self.bad}.good` is `7` while `.bad` diverges. The divergences are proved, so the
tests are not passing because every argument happens to terminate. -/
public import Obend.Equiv.Behaviour
@[expose] public section
namespace Obend.Equiv.FareTests
open Obend.Core.Term
open Obend.Equiv
set_option autoImplicit false

/-- A term whose every reduct stays in a step-closed set with no values never converges. -/
theorem diverges_of_closed (S : Term → Prop) (closed : ∀ x y, S x → Step x y → S y)
    (noValue : ∀ x, S x → ¬ Value x) {t : Term} (ht : S t) : ¬ Converges t := by
  rintro ⟨v, s, val⟩
  revert ht
  induction s with
  | refl => intro ht; exact noValue _ ht val
  | next st _ ih => intro ht; exact ih val (closed _ _ ht st)

/-- `keep x y = x`. -/
def keep : Term := .lam (.lam (.bound 1))

/-- The identity extension `λself. λsuper. super`. -/
def identity : Term := .lam (.lam (.bound 0))

/-- The extension `λself. λsuper. self`: its fixed point demands itself. -/
def selfish : Term := .lam (.lam (.bound 1))

/-- `fix(self ↦ self)`, with any seed. -/
def loop : Term := .fix selfish (.nat 0)

theorem loop_unfold_function : instantiate (.lam (.bound 1)) loop = .lam loop := by
  simp [loop, selfish, instantiate, Term.substitute, liftSubstitution, Term.rename, liftRename]

theorem loop_unfold_body : instantiate loop (.nat 0) = loop := by
  simp [loop, selfish, instantiate, Term.substitute, liftSubstitution, Term.rename]

def loopApplied : Term := .app (.app selfish loop) (.nat 0)
def loopBody : Term := .app (.lam loop) (.nat 0)

theorem loop_diverges : ¬ Converges loop := by
  let A := loopApplied
  let B := loopBody
  have s0 : Step loop A := .fix _ _
  have s1 : Step A B := by
    have := Step.application (.nat 0) (Step.beta (.lam (.bound 1)) loop)
    rwa [loop_unfold_function] at this
  have s2 : Step B loop := by
    have := Step.beta loop (.nat 0); rwa [loop_unfold_body] at this
  refine diverges_of_closed (fun x => x = loop ∨ x = A ∨ x = B) ?_ ?_ (.inl rfl)
  · rintro x y (rfl | rfl | rfl) st
    · exact .inr (.inl (step_deterministic st s0))
    · exact .inr (.inr (step_deterministic st s1))
    · exact .inl (step_deterministic st s2)
  · rintro x (rfl | rfl | rfl) v <;> simp only [A, B, loop, loopApplied, loopBody] at v <;> cases v

/-- `keep(7, y)` is `7` for any `y`, in two steps that never touch `y`. -/
theorem keep_steps (y : Term) : Steps (.app (.app keep (.nat 7)) y) (.nat 7) := by
  have e1 : instantiate (.lam (.bound 1)) (.nat 7) = .lam (.nat 7) := by
    simp [instantiate, Term.substitute, liftSubstitution, Term.rename]
  have e2 : instantiate (.nat 7) y = .nat 7 := by simp [instantiate, Term.substitute]
  have s1 := Step.application y (Step.beta (.lam (.bound 1)) (.nat 7))
  rw [e1] at s1
  have s2 := Step.beta (.nat 7) y
  rw [e2] at s2
  exact .next s1 (.next s2 (.refl _))

/-- **Faré's first test**: `keep(7, fix(identity)) ≈b 7`. -/
theorem keep_fix_identity : .app (.app keep (.nat 7)) (.fix identity (.record [])) ≈b .nat 7 :=
  bequiv_of_steps (keep_steps _)

/-- The test is about laziness, not about `fix(identity)` terminating: a divergent argument is
discarded just as well. -/
theorem keep_loop : .app (.app keep (.nat 7)) loop ≈b .nat 7 ∧ ¬ Converges loop :=
  ⟨bequiv_of_steps (keep_steps _), loop_diverges⟩

/-- `λself. λsuper. {good = 7, bad = self.bad}`. -/
def goodBad : Term :=
  .lam (.lam (.record [("good", .nat 7), ("bad", .get (.bound 1) "bad")]))

/-- The object: `fix` of `goodBad` over an empty seed. -/
def object : Term := .fix goodBad (.record [])

def objectRecord : Term := .record [("good", .nat 7), ("bad", .get object "bad")]

theorem object_unfold_function :
    instantiate (.lam (.record [("good", .nat 7), ("bad", .get (.bound 1) "bad")])) object =
      .lam (.record [("good", .nat 7), ("bad", .get object "bad")]) := by
  simp [object, goodBad, instantiate, Term.substitute, liftSubstitution, Term.rename, liftRename]

theorem object_unfold_body :
    instantiate (.record [("good", .nat 7), ("bad", .get object "bad")]) (.record []) = objectRecord := by
  simp [objectRecord, object, goodBad, instantiate, Term.substitute, liftSubstitution, Term.rename]

/-- `object` reaches its record in three steps, inside any field selection. -/
theorem object_steps (name : String) : Steps (.get object name) (.get objectRecord name) := by
  have s0 : Step (.get object name) (.get (.app (.app goodBad object) (.record [])) name) :=
    .target _ (.fix _ _)
  have s1 := Step.target name (Step.application (.record []) (Step.beta
    (.lam (.record [("good", .nat 7), ("bad", .get (.bound 1) "bad")])) object))
  rw [object_unfold_function] at s1
  have s2 := Step.target name (Step.beta
    (.record [("good", .nat 7), ("bad", .get object "bad")]) (.record []))
  rw [object_unfold_body] at s2
  exact .next s0 (.next s1 (.next s2 (.refl _)))

/-- **Faré's second test**: `{good = 7, bad = self.bad}.good ≈b 7`. -/
theorem good_field : .get object "good" ≈b .nat 7 := by
  apply bequiv_of_steps
  refine steps_trans (object_steps "good") (.next (.field _ _ _ ?_) (.refl _))
  simp

/-- and `.bad` diverges: its run returns to `object.bad` after four steps. -/
theorem bad_field_diverges : ¬ Converges (.get object "bad") := by
  have back : Step (.get objectRecord "bad") (.get object "bad") := .field _ _ _ (by simp)
  let T0 : Term := .get object "bad"
  let T1 : Term := .get (.app (.app goodBad object) (.record [])) "bad"
  let T2 : Term := .get (.app (.lam (.record [("good", .nat 7), ("bad", .get object "bad")]))
    (.record [])) "bad"
  let T3 : Term := .get objectRecord "bad"
  have s0 : Step T0 T1 := .target _ (.fix _ _)
  have s1 : Step T1 T2 := by
    have := Step.target "bad" (Step.application (.record []) (Step.beta
      (.lam (.record [("good", .nat 7), ("bad", .get (.bound 1) "bad")])) object))
    rwa [object_unfold_function] at this
  have s2 : Step T2 T3 := by
    have := Step.target "bad" (Step.beta
      (.record [("good", .nat 7), ("bad", .get object "bad")]) (.record []))
    rwa [object_unfold_body] at this
  refine diverges_of_closed (fun x => x = T0 ∨ x = T1 ∨ x = T2 ∨ x = T3) ?_ ?_ (.inl rfl)
  · rintro x y (rfl | rfl | rfl | rfl) st
    · exact .inr (.inl (step_deterministic st s0))
    · exact .inr (.inr (.inl (step_deterministic st s1)))
    · exact .inr (.inr (.inr (step_deterministic st s2)))
    · exact .inl (step_deterministic st back)
  · rintro x (rfl | rfl | rfl | rfl) v <;> simp only [T0, T1, T2, T3] at v <;> cases v

end Obend.Equiv.FareTests
end
