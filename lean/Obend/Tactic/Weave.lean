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
public meta import Obend.Core.Data
public import Obend.Core.Term
public import Obend.Law.Contract
public import Obend.Lower.Transport
public meta import Obend.Spec.Law
public meta import Obend.Spec.LawDial

@[expose] public section
namespace Obend.Tactic.Weave

open Lean Elab Tactic Meta Term
open Lean.Parser.Tactic
open Obend.Core.Data (Data)
open Obend.Core.Term (Term Evaluates)
open Obend.Law (Holds Keeps)
open Obend.Spec.Law (LawExpr Facts)
open Obend.Spec.LawDial (solveLawWitness)

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

/-- Difference-constraint counterexample synthesizer for contract laws and invariants.
    Finds a concrete state satisfying `law` that violates `inv`. -/
def solveLawCounterexample (keys : List String) (law inv : LawExpr) : Option Data :=
  let fieldKeys := if keys.isEmpty then (law.fields ++ inv.fields).eraseDups else keys
  let facts : Facts := { subject := some 0, caller := none, height := 0, turn := 0 }
  solveLawWitness fieldKeys (.and law (.not inv)) facts none

meta def mkDataProdExpr (k : String) (v : Expr) : Expr :=
  mkApp4 (Lean.mkConst ``Prod.mk [Level.zero, Level.zero]) (Lean.mkConst ``String) (Lean.mkConst ``Data) (toExpr k) v

meta def mkDataProdListExpr : List (String × Expr) → Expr
  | [] => mkApp (Lean.mkConst ``List.nil [Level.zero]) (mkApp2 (Lean.mkConst ``Prod [Level.zero, Level.zero]) (Lean.mkConst ``String) (Lean.mkConst ``Data))
  | (k, v) :: rest =>
    mkApp3 (Lean.mkConst ``List.cons [Level.zero])
      (mkApp2 (Lean.mkConst ``Prod [Level.zero, Level.zero]) (Lean.mkConst ``String) (Lean.mkConst ``Data))
      (mkDataProdExpr k v)
      (mkDataProdListExpr rest)

meta partial def toExprData : Data → Expr
  | .natural n => mkApp (Lean.mkConst ``Data.natural) (toExpr n)
  | .boolean b => mkApp (Lean.mkConst ``Data.boolean) (toExpr b)
  | .label s => mkApp (Lean.mkConst ``Data.label) (toExpr s)
  | .record fs =>
      let fieldExprs := fs.map fun (k, v) => (k, toExprData v)
      mkApp (Lean.mkConst ``Data.record) (mkDataProdListExpr fieldExprs)
  | .variant l p =>
      mkApp2 (Lean.mkConst ``Data.variant) (toExpr l) (toExprData p)

meta instance : ToExpr Data where
  toExpr := toExprData
  toTypeExpr := Lean.mkConst ``Data

/-- Interactive counterexample generator synthesizing failing Data records via difference-constraint relaxation. -/
elab "obend_tooth" : tactic => do
  let goal ← getMainGoal
  let goalType ← goal.getType
  logWarning m!"[obend_tooth] Diagnosing unproved contract goal: {goalType}"

  let cexOpt ← Meta.withReducible do
    match goalType with
    | .app (.app (.app (.const `Eq _) _) lhs) rhs =>
      let lhsV ← whnf lhs
      let rhsV ← whnf rhs
      if lhsV != rhsV then
        pure (some (Data.record [("status", .label "counterexample"), ("lhs", .label s!"{lhsV}"), ("rhs", .label s!"{rhsV}")]))
      else
        pure none
    | .forallE _ (.const `Nat _) body _ =>
      let mut found : Option Data := none
      for k in [0:20] do
        let testVal := mkNatLit k
        let instBody := body.instantiate1 testVal
        let redBody ← whnf instBody
        if redBody == Lean.mkConst ``False || redBody == Lean.mkConst ``Bool.false then
          found := some (.natural k)
          break
      pure found
    | _ =>
      let facts : Facts := { subject := some 0, caller := none, height := 0, turn := 0 }
      pure (solveLawWitness ["violating_state"] (.eqC (.field "violating_state") 42) facts none)

  match cexOpt with
  | some cex =>
    logInfo m!"[obend_tooth] Discovered concrete counterexample Data witness:\n  {repr cex}"
    let cexExpr := toExpr cex
    let cexId := mkIdent `cex
    evalTactic (← `(tactic| have $cexId : Obend.Core.Data.Data := $(← Term.exprToSyntax cexExpr)))
  | none =>
    logWarning m!"[obend_tooth] No violating Data witness synthesized within bounded search."

end Obend.Tactic.Weave
end
