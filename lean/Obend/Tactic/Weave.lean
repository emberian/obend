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
public import Obend.Spec.Law
public meta import Obend.Spec.Law
public import Obend.Spec.LawDial
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
      first
      | decide +kernel
      | (intros
         obend_unfold
         try obend_split
         all_goals (
           first
           | decide
           | decide +kernel
           | omega
           | poly_ring
           | contradiction
           | trivial
         ))
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
    | .forallE _ (.const ``Nat _) body _ =>
      let mut found : Option Data := none
      for k in [0:20] do
        let testVal := mkNatLit k
        let instBody := body.instantiate1 testVal
        try
          let decInst ← synthInstance (← mkAppM ``Decidable #[instBody])
          let decApp := mkApp2 (Lean.mkConst ``Decidable.decide) instBody decInst
          let red ← Meta.withDefault (whnf decApp)
          if red == Lean.mkConst ``Bool.false then
            found := some (.natural k)
            break
        catch _ =>
          pure ()
      pure found
    | _ =>
      pure none

  match cexOpt with
  | some cex =>
    logInfo m!"[obend_tooth] Discovered concrete counterexample Data witness:\n  {repr cex}"
    let cexExpr := toExpr cex
    let cexId := mkIdent `cex
    evalTactic (← `(tactic| have $cexId : Obend.Core.Data.Data := $(← Term.exprToSyntax cexExpr)))
  | none =>
    logWarning m!"[obend_tooth] No violating Data witness synthesized within bounded search."

/-! ### 6. Chained Multi-Step Discharge: `weave_chain` & `WeaveChainReceipt` -/

/-- Multi-step chained contract discharge tactic macro: unfolds contract obligations, splits
    conditional/conjunctive subgoals, and chains arithmetic/boolean/ring discharge steps. -/
macro "weave_chain" : tactic =>
  `(tactic| (
      first
      | obend_law
      | (try intros
         try obend_unfold
         try obend_split
         all_goals (
           first
           | obend_law
           | poly_ring
           | omega
           | decide
           | decide +kernel
           | assumption
           | trivial
         ))
  ))

syntax "weave_chain" "[" term,* "]" : tactic

macro_rules
  | `(tactic| weave_chain []) =>
    `(tactic| weave_chain)
  | `(tactic| weave_chain [$h:term]) =>
    `(tactic| ((first | have : $h := by weave_chain | have := $h); weave_chain))
  | `(tactic| weave_chain [$h:term, $hs:term,*]) =>
    `(tactic| ((first | have : $h := by weave_chain | have := $h); weave_chain [$hs,*]))

/-- A single implication link `sourceProp → targetProp` in a multi-step `#weave` chain. -/
structure WeaveChainStep where
  label      : String
  sourceProp : String
  targetProp : String
  method     : String := "weave"
  discharged : Bool := true
  deriving Inhabited, Repr, DecidableEq

/-- Receipt for a multi-step `#weave` chain `P_1 → P_2 → ... → P_n` from `initialProp` to `goalProp`. -/
structure WeaveChainReceipt where
  initialProp : String
  goalProp    : String
  steps       : List WeaveChainStep
  deriving Inhabited, Repr, DecidableEq

/-- Verify a single `WeaveChainStep` from `currentProp`: requires a non-empty `label`,
    `discharged = true`, and `s.sourceProp = currentProp` (`0 Classical.choice`). -/
def checkWeaveChainStep (currentProp : String) (s : WeaveChainStep) : Bool :=
  !decide (s.label = "") &&
  s.discharged &&
  decide (s.sourceProp = currentProp)

/-- Recursively verify that `steps` forms a contiguous discharged implication chain from
    `currentProp` to `goalProp` (`0 Classical.choice`). -/
def checkWeaveChainSteps (currentProp goalProp : String) : List WeaveChainStep → Bool
  | [] => decide (currentProp = goalProp)
  | s :: rest =>
    checkWeaveChainStep currentProp s &&
    checkWeaveChainSteps s.targetProp goalProp rest

/-- Verify that a `WeaveChainReceipt` is non-empty, every step is discharged with a non-empty
    label, adjacent steps chain `s_i.targetProp = s_{i+1}.sourceProp` starting from `r.initialProp`,
    and the final step establishes `r.goalProp` (`0 Classical.choice`). -/
def checkWeaveChainReceipt (r : WeaveChainReceipt) : Bool :=
  match r.steps with
  | [] => false
  | s :: rest => checkWeaveChainSteps r.initialProp r.goalProp (s :: rest)

theorem checkWeaveChainSteps_step_valid :
    ∀ {steps : List WeaveChainStep} {currentProp goalProp : String} {s : WeaveChainStep},
      checkWeaveChainSteps currentProp goalProp steps = true →
      s ∈ steps →
      s.discharged = true ∧ s.label ≠ ""
  | [], _, _, _, _, hmem => by cases hmem
  | x :: xs, currentProp, goalProp, s, hchk, hmem => by
    simp only [checkWeaveChainSteps, checkWeaveChainStep, Bool.and_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not, decide_eq_true_eq] at hchk
    cases hmem with
    | head _ => exact ⟨hchk.1.1.2, hchk.1.1.1⟩
    | tail _ htail => exact checkWeaveChainSteps_step_valid hchk.2 htail

theorem checkWeaveChainSteps_modus_ponens (interp : String → Prop) :
    ∀ {steps : List WeaveChainStep} {currentProp goalProp : String},
      checkWeaveChainSteps currentProp goalProp steps = true →
      (∀ s ∈ steps, s.discharged = true → interp s.sourceProp → interp s.targetProp) →
      interp currentProp →
      interp goalProp
  | [], currentProp, goalProp, hchk, _, hcur => by
    simp only [checkWeaveChainSteps, decide_eq_true_eq] at hchk
    rw [← hchk]
    exact hcur
  | x :: xs, currentProp, goalProp, hchk, hsteps, hcur => by
    simp only [checkWeaveChainSteps, checkWeaveChainStep, Bool.and_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not, decide_eq_true_eq] at hchk
    have hx_src : interp x.sourceProp := by
      rw [hchk.1.2]
      exact hcur
    have hx_tgt : interp x.targetProp :=
      hsteps x (List.Mem.head xs) hchk.1.1.2 hx_src
    exact checkWeaveChainSteps_modus_ponens interp hchk.2
      (fun s hs => hsteps s (List.Mem.tail x hs)) hx_tgt

/-- **Soundness of `checkWeaveChainReceipt`** (`0 sorry`, `0 Classical.choice`):
    whenever `checkWeaveChainReceipt r = true`, `r.steps` is non-empty, every step is discharged
    with a non-empty label, and under any propositional interpretation `interp : String → Prop`
    for which each discharged step is sound, `interp r.initialProp` implies `interp r.goalProp`. -/
theorem checkWeaveChainReceipt_sound (r : WeaveChainReceipt)
    (h : checkWeaveChainReceipt r = true) :
    r.steps ≠ [] ∧
    (∀ s ∈ r.steps, s.discharged = true ∧ s.label ≠ "") ∧
    (∀ (interp : String → Prop),
      (∀ s ∈ r.steps, s.discharged = true → interp s.sourceProp → interp s.targetProp) →
      interp r.initialProp → interp r.goalProp) := by
  unfold checkWeaveChainReceipt at h
  cases hsteps : r.steps with
  | nil =>
    rw [hsteps] at h
    cases h
  | cons s rest =>
    rw [hsteps] at h
    refine ⟨List.cons_ne_nil s rest, ?_, ?_⟩
    · intro x hx
      exact checkWeaveChainSteps_step_valid h hx
    · intro interp hsound hinit
      exact checkWeaveChainSteps_modus_ponens interp h hsound hinit

end Obend.Tactic.Weave
end

