module
public import Obend.Hardware.Gpu.ArraySourceCore
@[expose] public section

/-! A bounded higher-order Core4 loop. The state may be an array function or a
register environment; it is never encoded by evaluating the source in Lean.
The recursive body and its source step occur once in the syntax. -/
namespace Obend.Hardware.Gpu.BlockCoreLoop
open Obend.Core.Term Obend.Equiv Obend.Core.TermTraverse
open Obend.Hardware.Gpu.ArraySource.Core
set_option autoImplicit false

/-- self, super, step, count, state. The successor branch binds count-1. -/
def loopSpec : Term :=
  .lam (.lam (.lam (.lam (.lam
    (.ifZero (.bound 1) (.bound 0)
      (.app (.app (.bound 3) (.bound 0))
        (.app (.app (.app (.bound 5) (.bound 3)) (.bound 0)) (.bound 1))))))))

def loop : Term := .fix loopSpec (.nat 0)
def call (step count state : Term) : Term := .app (.app (.app loop step) count) state

@[simp] theorem loopSpec_substitute (σ : Nat → Term) : loopSpec.substitute σ = loopSpec := by
  simp [loopSpec, Term.substitute, liftSubstitution, Term.rename]
@[simp] theorem loop_substitute (σ : Nat → Term) : loop.substitute σ = loop := by
  simp [loop, Term.substitute]
@[simp] theorem call_substitute (step count state : Term) (σ : Nat → Term) :
    (call step count state).substitute σ =
      call (step.substitute σ) (count.substitute σ) (state.substitute σ) := by
  simp [call]

theorem unfold_vars :
    Steps (call (.bound 0) (.bound 1) (.bound 2))
      (.ifZero (.bound 1) (.bound 2)
        (.app (.app (.bound 1) (.bound 0))
          (call (.bound 1) (.bound 0) (.bound 3)))) := by
  unfold call loop
  refine .next (.application _ (.application _ (.application _ (.fix _ _)))) ?_
  simp only [loopSpec]
  repeat first
    | exact Steps.refl _
    | (apply Steps.next (Step.application _ (Step.application _ (Step.application _ (Step.application _ (Step.beta _ _))))); simp only [instantiate, Term.substitute, liftSubstitution, Term.rename, liftRename])
    | (apply Steps.next (Step.application _ (Step.application _ (Step.application _ (Step.beta _ _)))); simp only [instantiate, Term.substitute, liftSubstitution, Term.rename])
    | (apply Steps.next (Step.application _ (Step.application _ (Step.beta _ _))); simp only [instantiate, Term.substitute, liftSubstitution, Term.rename])
    | (apply Steps.next (Step.application _ (Step.beta _ _)); simp only [instantiate, Term.substitute, liftSubstitution, Term.rename])
    | (apply Steps.next (Step.beta _ _); simp only [instantiate, Term.substitute, liftSubstitution, Term.rename])

def subst (step count state : Term) : Nat → Term
  | 0 => step | 1 => count | _ => state

theorem zero (step state : Term) : Steps (call step (.nat 0) state) state := by
  have h := steps_substitute (subst step (.nat 0) state) unfold_vars
  simp only [call_substitute, Term.substitute, subst, liftSubstitution, Term.rename] at h
  exact steps_trans h (.next (.zero _ _) (.refl _))

theorem succ_vars (n : Nat) :
    Steps (call (.bound 0) (.nat (n+1)) (.bound 1))
      (.app (.app (.bound 0) (.nat n)) (call (.bound 0) (.nat n) (.bound 1))) := by
  have h := steps_substitute (subst (.bound 0) (.nat (n+1)) (.bound 1)) unfold_vars
  simp only [call_substitute, Term.substitute, subst, liftSubstitution, Term.rename] at h
  apply steps_trans h
  refine .next (.successor n _ _) ?_
  simp only [instantiate, call_substitute, Term.substitute]
  exact .refl _

theorem succ (step state : Term) (n : Nat) :
    Steps (call step (.nat (n+1)) state)
      (.app (.app step (.nat n)) (call step (.nat n) state)) := by
  have h := steps_substitute (subst step state state) (succ_vars n)
  simpa only [call_substitute, Term.substitute, subst] using h

/-- Any observation semantics closed under Core4 steps and the source body
lifts through the bounded loop, for every count and initial state. -/
theorem denotes {α : Type} (D : Term → α → Prop) (step : Term)
    (advance : Nat → α → α)
    (hsteps : ∀ t u value, Steps t u → D u value → D t value)
    (hstep : ∀ i t value, D t value → D (.app (.app step (.nat i)) t) (advance i value))
    (state : Term) (value : α) (hstate : D state value) (n : Nat) :
    D (call step (.nat n) state) ((List.range n).foldl (fun v i => advance i v) value) := by
  induction n with
  | zero => simpa using hsteps _ _ _ (zero step state) hstate
  | succ n ih =>
    rw [List.range_succ, List.foldl_append]
    exact hsteps _ _ _ (succ step state n) (hstep n _ _ ih)

/-- Bounded source admission only needs the body invariant for indices actually
visited by this loop. No condition on unreachable logical lanes is required. -/
theorem denotes_bounded {α : Type} (D : Term → α → Prop) (step : Term)
    (advance : Nat → α → α)
    (hsteps : ∀ t u value, Steps t u → D u value → D t value)
    (n : Nat)
    (hstep : ∀ i < n, ∀ t value, D t value → D (.app (.app step (.nat i)) t) (advance i value))
    (state : Term) (value : α) (hstate : D state value) :
    D (call step (.nat n) state) ((List.range n).foldl (fun v i => advance i v) value) := by
  induction n with
  | zero => simpa using hsteps _ _ _ (zero step state) hstate
  | succ n ih =>
    rw [List.range_succ,List.foldl_append]
    exact hsteps _ _ _ (succ step state n)
      (hstep n (by omega) _ _ (ih (fun i hi => hstep i (by omega))))

end Obend.Hardware.Gpu.BlockCoreLoop
end
