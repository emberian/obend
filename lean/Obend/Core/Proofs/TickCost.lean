module
/- Machine ticks against clairvoyant cost (`review/EQUIV-PLAN-20261031.md` §5, lane 3).

The lane asked for ticks within a constant factor of clairvoyant cost, carried by the existing
machine-to-source relation. For the clairvoyant semantics of `Obend.Equiv.Clairvoyant`, which is
Hackett and Hutton's (Let′ at a recursive binding evaluates its body before `self` is bound), that
bound does not hold in the machine-to-CV direction, for any constants: the machine finishes
`{a = 7, b = self.a}.b` in 25 ticks with `7` (`self_field_machine`), and the clairvoyant semantics
has no derivation of it at all (`Obend.Equiv.CostTests.self_field_no_cv`), so no cost of a derivation
is within any factor of 25 (`ticks_not_within_cv`). The lazy field `b` is forced only after `self`
is updated; a clairvoyant evaluation must evaluate it before (where `self` is not bound) or skip it.

Where the two agree, measured exactly: `{good = 7, bad = self.bad}.good` finishes in 16 ticks and
costs 8 (`good_machine`, `Obend.Equiv.CostTests.good_cost`); `.bad` ends `divergent` (the
blackhole) in 21 ticks and has no derivation (`bad_machine`, `bad_field_no_cv`).

The CV-to-machine direction (a derivation of cost `k` bounds the ticks of a finished run) is not
claimed: it needs source-to-machine completeness, which `Core/Proofs/Adequacy.lean` leaves open. -/
public import Obend.Equiv.CostTests
public import Obend.Core.Machine
@[expose] public section
namespace Obend.Core.Proofs.TickCost
open Obend.Core.Term
open Obend.Core.Machine
open Obend.Equiv
open Obend.Equiv.CostTests
set_option autoImplicit false

/-- The natural number a finished run returns, if it finished with one. -/
def finishedNat : Outcome → Option Nat
  | .finished (.natural n) _ => some n
  | _ => none

/-- A run that ended at the blackhole. -/
def blackholed : Outcome → Bool
  | .divergent _ _ => true
  | _ => false

/-- The machine's limits for these runs. -/
def limits : Limits := ⟨100, 100⟩

/-- `{a = 7, b = self.a}.b` finishes with `7` within 25 ticks, and not within 24. -/
theorem self_field_machine :
    finishedNat (runBounded limits 25 (initial (.get selfField "b"))) = some 7 ∧
      finishedNat (runBounded limits 24 (initial (.get selfField "b"))) = none := by
  constructor <;> simp [finishedNat, limits, runBounded, step, stepRaw, initial, selfObject, allocateFields,
    Array.set!, Array.setIfInBounds, Term.rename, liftRename]

/-- `{good = 7, bad = self.bad}.good` finishes with `7` within 16 ticks, and not within 15. -/
theorem good_machine :
    finishedNat (runBounded limits 16 (initial (.get FareTests.object "good"))) = some 7 ∧
      finishedNat (runBounded limits 15 (initial (.get FareTests.object "good"))) = none := by
  constructor <;> simp [finishedNat, limits, runBounded, step, stepRaw, initial, FareTests.object,
    FareTests.goodBad, allocateFields, Array.set!, Array.setIfInBounds, Term.rename, liftRename]

/-- `.bad` reaches the blackhole within 21 ticks, and not within 20. -/
theorem bad_machine :
    blackholed (runBounded limits 21 (initial (.get FareTests.object "bad"))) = true ∧
      blackholed (runBounded limits 20 (initial (.get FareTests.object "bad"))) = false := by
  constructor <;> simp [blackholed, limits, runBounded, step, stepRaw, initial, FareTests.object,
    FareTests.goodBad, allocateFields, Array.set!, Array.setIfInBounds, Term.rename, liftRename]

/-- **No tick-to-clairvoyant bound**: for no constants `c d` does every finished machine run of `T`
ticks have a clairvoyant derivation of cost at most `c * T + d`. -/
theorem ticks_not_within_cv :
    ¬ ∃ c d : Nat, ∀ (t : Term) (T : Nat) (n : Nat),
      finishedNat (runBounded limits T (initial t)) = some n → ∃ v k, CV t v k ∧ k ≤ c * T + d := by
  rintro ⟨c, d, h⟩
  obtain ⟨v, k, run, _⟩ := h _ 25 7 self_field_machine.1
  exact self_field_no_cv run

/-- Where they agree: `.good` costs 8 and takes 16 ticks; `.bad` has no derivation and blackholes. -/
theorem fare_agreement :
    CV (.get FareTests.object "good") (.nat 7) 8 ∧
      finishedNat (runBounded limits 16 (initial (.get FareTests.object "good"))) = some 7 ∧
      (∀ v k, ¬ CV (.get FareTests.object "bad") v k) ∧
      blackholed (runBounded limits 21 (initial (.get FareTests.object "bad"))) = true :=
  ⟨good_cost, good_machine.1, fun _ _ => bad_field_no_cv, bad_machine.1⟩

end Obend.Core.Proofs.TickCost
end
