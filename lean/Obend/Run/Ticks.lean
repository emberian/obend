module
/-
# Obend.Run.Ticks — Fuel Monotonicity (`runBounded_mono`), Linear-Time `deepenBounded`, and Cost-Indexed Completeness (`WS 27` `G1`)

Closes Gap `G1` (`PLAN.md` Part III & `METATHEORY.md` §3.1):
1. Re-exports and lifts `runBounded_mono` (`k ≤ k' → runBounded L k s = .finished v s' → runBounded L k' s = .finished v s'`).
2. Provides `deepenBounded L s k : Option (RuntimeValue × State)`, which runs `runBounded L k s` in a
   single linear $O(k)$ pass instead of quadratic `Judge.deepen` $O(k^2)$ replay, and proves that
   `deepenBounded` is both fuel-monotone (`deepenBounded_mono`) and extensionally equal to
   `Judge.deepen (deepenBounded L s) k` (`deepenBounded_eq_deepen`).
3. Re-exports `cost_indexed_completeness` for bounded closures.
-/
public import Obend.Core.Proofs.TickCost
public import Obend.Judge.Class
@[expose] public section

namespace Obend.Run.Ticks
open Obend.Core.Machine (Limits State Outcome RuntimeValue runBounded)
open Obend.Core.Proofs.TickCost (runBounded_mono finishedNat finishedNat_mono InFragment FirstFinish CostIndexedRun cost_indexed_completeness)
open Obend.Equiv (CV)
set_option autoImplicit false

/-- Single-pass $O(k)$ bounded execution extracting a finished `(RuntimeValue × State)`. -/
def deepenBounded (L : Limits) (s : State) (k : Nat) : Option (RuntimeValue × State) :=
  match runBounded L k s with
  | .finished v s' => some (v, s')
  | _ => none

/-- **Theorem (`deepenBounded_mono`)**:
Because `runBounded` is fuel-monotone (`runBounded_mono`), `deepenBounded L s` is already monotone
in `k ≤ k'` without needing `Judge.deepen`'s $O(k^2)$ prefix loop. -/
theorem deepenBounded_mono (L : Limits) (s : State) {k k' : Nat} {res : RuntimeValue × State}
    (h : deepenBounded L s k = some res) (hle : k ≤ k') :
    deepenBounded L s k' = some res := by
  unfold deepenBounded at h ⊢
  revert h
  cases hrun : runBounded L k s with
  | finished v s' =>
    simp only [Option.some.injEq]
    intro heq
    subst heq
    rw [runBounded_mono hrun hle]
  | _ => simp

/-- If `deepenBounded L s k = none`, then for every `j ≤ k`, `deepenBounded L s j = none`. -/
theorem deepenBounded_none_of_le (L : Limits) (s : State) {j k : Nat}
    (hnone : deepenBounded L s k = none) (hle : j ≤ k) :
    deepenBounded L s j = none := by
  cases hj : deepenBounded L s j with
  | none => rfl
  | some res =>
    have hk := deepenBounded_mono L s hj hle
    rw [hnone] at hk
    cases hk

/-- **Theorem (`deepenBounded_eq_deepen`)**:
The single-pass linear $O(k)$ `deepenBounded L s k` produces the exact same result as the
quadratic $O(k^2)$ iterative deepening `Judge.deepen (deepenBounded L s) k` for every `k`. -/
theorem deepenBounded_eq_deepen (L : Limits) (s : State) (k : Nat) :
    Judge.deepen (deepenBounded L s) k = deepenBounded L s k := by
  have hiff : ∀ res, Judge.deepen (deepenBounded L s) k = some res ↔ deepenBounded L s k = some res := by
    intro res
    constructor
    · intro hd
      obtain ⟨i, hle, hi⟩ := Judge.deepen_some (deepenBounded L s) hd
      exact deepenBounded_mono L s hi hle
    · intro hb
      obtain ⟨b, hd⟩ := Judge.deepen_isSome (deepenBounded L s) hb
      obtain ⟨i, hle, hi⟩ := Judge.deepen_some (deepenBounded L s) hd
      have hb' := deepenBounded_mono L s hi hle
      rw [hb] at hb'
      injection hb' with hbe
      subst hbe
      exact hd
  cases hd : Judge.deepen (deepenBounded L s) k with
  | some res => exact ((hiff res).mp hd).symm
  | none =>
    cases hb : deepenBounded L s k with
    | none => rfl
    | some res =>
      have hd' := (hiff res).mpr hb
      rw [hd] at hd'
      cases hd'

end Obend.Run.Ticks
end
