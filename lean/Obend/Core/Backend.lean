module
/-
# Obend.Core.Backend — the executor interface a world drives, as a typeclass

A backend runs Core4 terms: it starts a state from a term, steps it under limits, reports how a
step ended, and resumes a yielded state with a response. `Outcome σ V` is the demand machine's
`Obend.Core.Machine.Outcome` with the state and value types abstracted; the demand machine is the
one instance here (`Backend Machine.State Machine.RuntimeValue`), with the identity on outcomes, so
nothing is lost between the class and the proved machine. A second instance (a Bend-compiled
state, `Obend.Leaf`) states its own correspondence; the class carries no law, by Ember's rule:
the laws of the demand machine are the theorems in `Obend.Core.Proofs.*` about its own operations,
and a generic driver written against `Backend` inherits them by unfolding the instance.
-/
public import Obend.Core.Term
public import Obend.Core.Machine

@[expose] public section
namespace Obend.Core.Backend

open Obend.Core.Term (Term)

/-- How a bounded run ended, over an abstract state `σ` and value `V`: a value; a suspension with the
exact pre-transition state; a divergence (blackhole) at a heap address; a refusal; a yield whose plan
is at a heap address. -/
inductive Outcome (σ V : Type) where
  | finished (value : V) (state : σ)
  | suspended (reason : Machine.Suspension) (state : σ)
  | divergent (address : Machine.Address) (state : σ)
  | refused (reason : Machine.Refusal) (state : σ)
  | yielded (plan : Machine.Address) (state : σ)

/-- An executor of Core4 terms. -/
class Backend (σ V : Type) where
  /-- the state a term starts in -/
  initial : Term → σ
  /-- one tick under the limits -/
  step : Machine.Limits → σ → Outcome σ V
  /-- at most `ticks` ticks under the limits -/
  runBounded : Machine.Limits → Nat → σ → Outcome σ V
  /-- deliver a response to a yielded state; `none` unless the state is yielded -/
  resume : Term → σ → Option σ

/-- The demand machine's outcome, read into the abstract one. -/
def Outcome.ofMachine : Machine.Outcome → Outcome Machine.State Machine.RuntimeValue
  | .finished v s => .finished v s
  | .suspended r s => .suspended r s
  | .divergent a s => .divergent a s
  | .refused r s => .refused r s
  | .yielded p s => .yielded p s

/-- The abstract outcome, read back into the machine's. -/
def Outcome.toMachine : Outcome Machine.State Machine.RuntimeValue → Machine.Outcome
  | .finished v s => .finished v s
  | .suspended r s => .suspended r s
  | .divergent a s => .divergent a s
  | .refused r s => .refused r s
  | .yielded p s => .yielded p s

theorem Outcome.toMachine_ofMachine (o : Machine.Outcome) : (Outcome.ofMachine o).toMachine = o := by
  cases o <;> rfl

theorem Outcome.ofMachine_toMachine (o : Outcome Machine.State Machine.RuntimeValue) :
    Outcome.ofMachine o.toMachine = o := by
  cases o <;> rfl

/-- The demand machine (`Obend.Core.Machine`), the proved instance. -/
instance demand : Backend Machine.State Machine.RuntimeValue where
  initial := Machine.initial
  step limits state := Outcome.ofMachine (Machine.step limits state)
  runBounded limits ticks state := Outcome.ofMachine (Machine.runBounded limits ticks state)
  resume := Machine.resume

theorem demand_runBounded (limits : Machine.Limits) (ticks : Nat) (state : Machine.State) :
    (Backend.runBounded limits ticks state).toMachine = Machine.runBounded limits ticks state := by
  simp [Backend.runBounded, Outcome.toMachine_ofMachine]

end Obend.Core.Backend
end
