module
/- Machine ticks against the two-stage demand cost (`review/EQUIV-PLAN-20261031.md` §5, lane 3;
contract C4).

Under Hackett and Hutton's `Let′` at `fix` the tick bound was false (`ticks_not_within_cv`, retired):
`{a = 7, b = self.a}.b` finishes on the machine and had no clairvoyant derivation. Under the
two-stage rule (`Obend.Equiv.Clairvoyant`: the template settled once, the fields filled in waves)
it has one, and the least cost of each measured program is the demand semantics'
(`Obend.Equiv.Demand.measured_least`). On every measured program the machine's ticks are within a
factor of 4 of the demand cost and above it (`measured_within`): `.good` 5 against 16 ticks, `.b` 7
against 25, `.bad` no derivation against the blackhole at 21.

The general statement (`TicksWithinDemand`) is stated, not proved: it needs a cost-indexed form of
`Core/Proofs/Completeness` (finite completion is proved there by a lexicographic descent on source
cost and a stutter rank, with no count of ticks per source step, and no relation between the heap's
cells and the waves' approximants). That relation is the missing piece, named in
`lean/docs/REPORT-DEMAND-20261101.md`. -/
public import Obend.Equiv.Demand
public import Obend.Core.Machine
@[expose] public section
namespace Obend.Core.Proofs.TickCost
open Obend.Core.Term
open Obend.Core.Machine
open Obend.Equiv
open Obend.Equiv.CostTests
open Obend.Equiv.Demand (measured_least)
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
  constructor <;> simp [finishedNat, limits, runBounded, step, stepRaw, initial, selfObject, selfLam, allocateFields,
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

/-- The tick bound, in its true form: for every program whose demand run exists, the machine's
ticks are within `c` times the least demand cost, plus `d`. -/
def TicksWithinDemand (c d : Nat) : Prop :=
  ∀ (t : Term) (T n : Nat), finishedNat (runBounded limits T (initial t)) = some n →
    (∀ T' < T, finishedNat (runBounded limits T' (initial t)) = none) →
    ∀ k, CV t (.nat n) k → (∀ w j, CV t w j → k ≤ j) → T ≤ c * k + d

/-- **The measured programs are within a factor of 4**: each finishes in at most 4 times its least
demand cost and in no fewer ticks than that cost, and the one without a demand run blackholes. -/
theorem measured_within :
    (CV (.get FareTests.object "good") (.nat 7) 5 ∧ (∀ w k, CV (.get FareTests.object "good") w k → 5 ≤ k) ∧
      finishedNat (runBounded limits 16 (initial (.get FareTests.object "good"))) = some 7 ∧
      finishedNat (runBounded limits 15 (initial (.get FareTests.object "good"))) = none ∧ 5 ≤ 16 ∧ 16 ≤ 4 * 5) ∧
    (CV (.get selfField "b") (.nat 7) 7 ∧ (∀ w k, CV (.get selfField "b") w k → 7 ≤ k) ∧
      finishedNat (runBounded limits 25 (initial (.get selfField "b"))) = some 7 ∧
      finishedNat (runBounded limits 24 (initial (.get selfField "b"))) = none ∧ 7 ≤ 25 ∧ 25 ≤ 4 * 7) ∧
    ((∀ v k, ¬ CV (.get FareTests.object "bad") v k) ∧
      blackholed (runBounded limits 21 (initial (.get FareTests.object "bad"))) = true) := by
  obtain ⟨⟨g1, g2⟩, ⟨b1, b2⟩, bad⟩ := Obend.Equiv.Demand.measured_least
  exact ⟨⟨g1, g2, good_machine.1, good_machine.2, by omega, by omega⟩,
    ⟨b1, b2, self_field_machine.1, self_field_machine.2, by omega, by omega⟩,
    ⟨bad, bad_machine.1⟩⟩

/-- The refutation's witness, now an instance: `{a = 7, b = self.a}.b`, which `ticks_not_within_cv`
used to show no bound holds, is within the factor. -/
theorem self_field_within : ∃ k, CV (.get selfField "b") (.nat 7) k ∧ 25 ≤ 4 * k :=
  ⟨7, self_field_cost, by omega⟩

end Obend.Core.Proofs.TickCost
end
