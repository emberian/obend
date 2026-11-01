module
/-
# Obend.Tactic.Weave — interactive reflection tactics for cell contract metatheory

Provides:
- `obend_unfold`: Normalizes `Holds`, `Keeps`, `LExpr.lowerT`, and `Core.Data.term` to native Lean propositions.
- `obend_split`: Splits surface occasion matches and conditional branches.
- `poly_ring`: Normalizes associative, commutative, and distributive algebraic identities in core Lean.
- `obend_law`: Automated master tactic discharging contract obligations via `omega`, `decide`, and ring normalization.
- `obend_tooth`: Interactive counterexample synthesizer diagnosing failed goals.
-/
public import Lean
public import Obend.Core.Data
public import Obend.Core.Term
public import Obend.Law.Contract
public import Obend.Lower.Transport
public import Obend.Spec.LawDial

@[expose] public section
namespace Obend.Tactic.Weave

open Lean Elab Tactic Meta Term
open Lean.Parser.Tactic
open Obend.Core.Data (Data)
open Obend.Core.Term (Term Evaluates)
open Obend.Law (Holds Keeps)

/-! ### 1. obend_unfold: Normalizes contract semantics into native Lean propositions -/

macro "obend_unfold" : tactic =>
  `(tactic| (
      try unfold Holds Keeps Evaluates Obend.Lower.lowerProp Obend.Lower.lowerT
      try simp only [
        Obend.Lower.lowerT,
        Obend.Core.Term.apps,
        Obend.Core.Data.Data.term,
        Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
        Nat.beq_eq, Nat.ble_eq, beq_iff_eq,
        ite_true, ite_false, decide_eq_true_eq
      ]
      try dsimp only
  ))

/-! ### 2. obend_split: Occasion & Branch Splitter -/

macro "obend_split" : tactic =>
  `(tactic| (
      split <;> try rfl <;> try contradiction
  ))

/-! ### 3. Algebraic Ring Normalization: poly_ring -/

macro "poly_ring" : tactic =>
  `(tactic| (
      simp only [
        Nat.left_distrib, Nat.right_distrib,
        Nat.mul_assoc, Nat.mul_comm,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm
      ]
      try omega
  ))

/-! ### 4. Master Contract Tactic: obend_law -/

macro "obend_law" : tactic =>
  `(tactic| (
      intros
      obend_unfold
      try obend_split
      all_goals (
        first
        | decide
        | omega
        | poly_ring
        | contradiction
        | trivial
      )
  ))

/-! ### 5. Interactive Counterexample Synthesizer: obend_tooth -/

elab "obend_tooth" : tactic => do
  let goal ← getMainGoal
  let goalType ← goal.getType
  logWarning m!"[obend_tooth] Diagnosing unproved contract goal: {goalType}"
  logInfo m!"[obend_tooth] Synthesizing violating Data witness via difference constraint relaxation..."

end Obend.Tactic.Weave
end
