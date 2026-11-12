module
/-
# `Obend.Tactic.SymbolicCert` — Verified Reflection & `TacticM` Suite (`bool_spec_iff`, `before_rank`, `perm_cert`)

Provides the custom metaprogramming and verified computational reflection suite for `Obend`'s
3-relation symbolic engine (`Lookup + LinMem + Before`) and Boolean checker equivalences, with
**zero `native_decide`**, **zero `sorry`**, and **zero custom `axiom`s**:

1. **`by bool_spec_iff` (`bool_spec_iff` / `bool_spec_iff [defs, ...]`)**:
   - Goal-directed `TacticM` proof builder discharging bidirectional `check x = true ↔ Spec x` and
     `check x = false ↔ ¬ Spec x` equivalences across nested Boolean combinators (`&&`, `||`, `!`,
     `==`, `!=`, `decide`, `Except.isOk`, `Except.toBool`, `Option.isSome`, `Option.isNone`, `ite`,
     `List.all`, `List.any`), automatically aligning left-associated `&&`/`||` chains against
     right-associated `∧`/`∨` specifications without manual `cases`/`split` boilerplate.
2. **`by before_rank` (`Before`, `BeforeWeak`, `LexLt` `<ₗₑₓ`, `LexLe` `≤ₗₑₓ`)**:
   - Verified topological & lexicographic rank solver using Bellman–Ford / Floyd–Warshall path and
     cycle synthesis in `MetaM`, replayed in Lean's kernel via `@[expose]` structural checkers
     (`checkDiffPath_sound`, `checkDiffCycle_refutes`, `checkLexChain_lt_sound`,
     `checkLexChain_le_sound`, `checkLexCycle_refutes`, and `checkDagRankAssignment_sound`) by `rfl`.
3. **`by perm_cert` (`checkPermWitness_sound`, `LinMemBalance`)**:
   - Constructive `List.Perm` bag-equivalence prover via insertion-extraction witness reflection
     (`checkPermWitness xs ys w = true → List.Perm xs ys`), supporting both `[BEq α] [LawfulBEq α]`
     reducible lists and arbitrary polymorphic `LinMem` multiset conservation goals (`init ++ prod ~
     cons ++ final`) without requiring `DecidableEq α`.
-/
public import Lean
public meta import Lean

public section
namespace Obend.Tactic.SymbolicCert

set_option autoImplicit false

universe u v

/-! ## 1. Compositional Bidirectional Boolean-Spec Lemmas & `by bool_spec_iff` -/

theorem bool_and_iff {a b : Bool} {P Q : Prop} (ha : a = true ↔ P) (hb : b = true ↔ Q) :
    (a && b) = true ↔ (P ∧ Q) := by rw [Bool.and_eq_true, ha, hb]
theorem bool_or_iff {a b : Bool} {P Q : Prop} (ha : a = true ↔ P) (hb : b = true ↔ Q) :
    (a || b) = true ↔ (P ∨ Q) := by rw [Bool.or_eq_true, ha, hb]
theorem bool_not_iff {a : Bool} {P : Prop} (ha : a = true ↔ P) :
    (!a) = true ↔ ¬ P := by cases a <;> simp_all
theorem bool_false_iff_not {a : Bool} {P : Prop} (ha : a = true ↔ P) :
    a = false ↔ ¬ P := by cases a <;> simp_all
theorem bool_not_false_iff {a : Bool} {P : Prop} (ha : a = true ↔ P) :
    (!a) = false ↔ P := by cases a <;> simp_all
theorem bool_and_false_iff {a b : Bool} {P Q : Prop} (ha : a = false ↔ P) (hb : b = false ↔ Q) :
    (a && b) = false ↔ (P ∨ Q) := by cases a <;> cases b <;> simp_all
theorem bool_or_false_iff {a b : Bool} {P Q : Prop} (ha : a = false ↔ P) (hb : b = false ↔ Q) :
    (a || b) = false ↔ (P ∧ Q) := by cases a <;> cases b <;> simp_all
theorem bool_beq_iff {α : Type u} [BEq α] [LawfulBEq α] (x y : α) :
    (x == y) = true ↔ x = y := beq_iff_eq
theorem bool_beq_symm_iff {α : Type u} [BEq α] [LawfulBEq α] (x y : α) :
    (x == y) = true ↔ y = x := by rw [beq_iff_eq, eq_comm]
theorem bool_bne_iff {α : Type u} [BEq α] [LawfulBEq α] (x y : α) :
    (x != y) = true ↔ x ≠ y := bne_iff_ne
theorem bool_beq_false_iff {α : Type u} [BEq α] [LawfulBEq α] (x y : α) :
    (x == y) = false ↔ x ≠ y := beq_eq_false_iff_ne
theorem bool_bne_false_iff {α : Type u} [BEq α] [LawfulBEq α] (x y : α) :
    (x != y) = false ↔ x = y := by unfold bne; cases h : (x == y) <;> simp_all
theorem bool_decide_iff (P : Prop) [Decidable P] : decide P = true ↔ P := decide_eq_true_iff
theorem bool_decide_false_iff (P : Prop) [Decidable P] : decide P = false ↔ ¬ P := decide_eq_false_iff_not
theorem bool_decide_bridge (P : Prop) [Decidable P] {Q : Prop} (hPQ : P ↔ Q) :
    decide P = true ↔ Q := (bool_decide_iff P).trans hPQ
theorem option_isSome_iff {α : Type u} (o : Option α) : o.isSome = true ↔ ∃ v, o = some v := by cases o <;> simp
theorem option_isSome_ne_none_iff {α : Type u} (o : Option α) : o.isSome = true ↔ o ≠ none := by cases o <;> simp
theorem option_isSome_false_iff {α : Type u} (o : Option α) : o.isSome = false ↔ o = none := by cases o <;> simp
theorem option_isNone_iff {α : Type u} (o : Option α) : o.isNone = true ↔ o = none := by cases o <;> simp
theorem option_isNone_false_iff {α : Type u} (o : Option α) : o.isNone = false ↔ ∃ v, o = some v := by cases o <;> simp
theorem option_not_isSome_iff {α : Type u} (o : Option α) : (!o.isSome) = true ↔ o = none := by cases o <;> simp
theorem option_not_isNone_iff {α : Type u} (o : Option α) : (!o.isNone) = true ↔ ∃ v, o = some v := by cases o <;> simp
theorem except_isOk_iff {ε : Type u} {α : Type v} (e : Except ε α) :
    e.isOk = true ↔ ∃ v, e = .ok v := by cases e <;> simp [Except.isOk, Except.toBool]
theorem except_toBool_iff {ε : Type u} {α : Type v} (e : Except ε α) :
    e.toBool = true ↔ ∃ v, e = .ok v := by cases e <;> simp [Except.toBool]
theorem except_isOk_false_iff {ε : Type u} {α : Type v} (e : Except ε α) :
    e.isOk = false ↔ ∃ err, e = .error err := by cases e <;> simp [Except.isOk, Except.toBool]
theorem except_toBool_false_iff {ε : Type u} {α : Type v} (e : Except ε α) :
    e.toBool = false ↔ ∃ err, e = .error err := by cases e <;> simp [Except.toBool]
theorem except_not_isOk_iff {ε : Type u} {α : Type v} (e : Except ε α) :
    (!e.isOk) = true ↔ ∃ err, e = .error err := by cases e <;> simp [Except.isOk, Except.toBool]

theorem bool_ite_iff (C : Prop) [Decidable C] {a b : Bool} {P Q : Prop}
    (ha : a = true ↔ P) (hb : b = true ↔ Q) :
    (if C then a else b) = true ↔ ((C ∧ P) ∨ (¬ C ∧ Q)) := by
  by_cases hC : C <;> simp [hC, ha, hb]

theorem bool_ite_imp_iff (C : Prop) [Decidable C] {a b : Bool} {P Q : Prop}
    (ha : a = true ↔ P) (hb : b = true ↔ Q) :
    (if C then a else b) = true ↔ ((C → P) ∧ (¬ C → Q)) := by
  by_cases hC : C <;> simp [hC, ha, hb]

theorem list_all_spec_iff {α : Type u} {p : α → Bool} {P : α → Prop}
    (xs : List α) (hp : ∀ x, x ∈ xs → (p x = true ↔ P x)) :
    xs.all p = true ↔ ∀ x, x ∈ xs → P x := by
  induction xs with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.all_cons, Bool.and_eq_true, List.mem_cons, forall_eq_or_imp]
    rw [hp hd (.head tl), ih (fun x hx => hp x (.tail hd hx))]

theorem list_any_spec_iff {α : Type u} {p : α → Bool} {P : α → Prop}
    (xs : List α) (hp : ∀ x, x ∈ xs → (p x = true ↔ P x)) :
    xs.any p = true ↔ ∃ x, x ∈ xs ∧ P x := by
  induction xs with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.any_cons, Bool.or_eq_true, List.mem_cons]
    rw [hp hd (.head tl), ih (fun x hx => hp x (.tail hd hx))]
    exact ⟨fun | .inl h => ⟨hd, .inl rfl, h⟩ | .inr ⟨x, hx, hp⟩ => ⟨x, .inr hx, hp⟩,
           fun | ⟨_, .inl rfl, h⟩ => .inl h | ⟨x, .inr hx, hp⟩ => .inr ⟨x, hx, hp⟩⟩

open Lean Meta Elab Tactic

/-- Strip outer `Expr.mdata` wrappers. -/
meta partial def stripMData (e : Expr) : Expr :=
  match e with
  | .mdata _ inner => stripMData inner
  | _ => e

/-- Primitive Boolean combinator head constants NOT unfolded automatically by `bool_spec_iff`. -/
meta def primitiveBoolHeads : List Name :=
  [ ``Bool.and, ``Bool.or, ``Bool.not, ``BEq.beq, ``bne, ``decide
  , ``Option.isSome, ``Option.isNone, ``Except.isOk, ``Except.toBool
  , ``ite, ``cond, ``List.all, ``List.any, ``Nat.ble, ``Nat.blt, ``true, ``false ]

/-- Primitive propositional combinator head constants NOT unfolded automatically by `bool_spec_iff`. -/
meta def primitivePropHeads : List Name :=
  [ ``And, ``Or, ``Not, ``Eq, ``Ne, ``Exists, ``Iff, ``True, ``False
  , ``LT.lt, ``LE.le, ``GT.gt, ``GE.ge, ``List.Mem, ``List.Perm ]

meta def keepUnassigned (gs : List MVarId) : MetaM (List MVarId) :=
  gs.filterM fun g => return !(← g.isAssigned)

/-- Introduce outer universal binders until the target is headed by `Iff`. -/
meta partial def introUntilIff (goal : MVarId) : MetaM MVarId :=
  goal.withContext do
    let tgt := stripMData (← instantiateMVars (← goal.getType))
    if (stripMData tgt.getAppFn).isConstOf ``Iff then return goal
    match tgt with
    | .forallE .. | .letE .. =>
      let (_, nextGoal) ← goal.intro1P
      introUntilIff nextGoal
    | _ => return goal

/-- Try to match the current goal directly against a local hypothesis. -/
meta def tryCloseFromLCtx (goal : MVarId) : MetaM Bool :=
  goal.withContext do
    let tgt ← goal.getType
    for ldecl in ← getLCtx do
      if ldecl.isImplementationDetail then continue
      if ← withoutModifyingState (isDefEq tgt ldecl.type) then
        let _ ← isDefEq tgt ldecl.type
        goal.assign ldecl.toExpr
        return true
    return false

meta def tryApplyConst? (goal : MVarId) (thmName : Name) : MetaM (Option (List MVarId)) :=
  goal.withContext do
    let saved ← saveState
    try
      let thm ← mkConstWithFreshMVarLevels thmName
      return some (← goal.apply thm)
    catch _ =>
      restoreState saved
      return none

meta def normalizeBoolSpecAssoc (goal : MVarId) : TacticM MVarId :=
  goal.withContext do
    let gs ← evalTacticAt
      (← `(tactic| try simp only [Bool.and_assoc, Bool.or_assoc, Bool.not_not, and_assoc, or_assoc]))
      goal
    return match gs with | [g] => g | _ => goal

meta def closeBoolSpecLeaf (goal : MVarId) : TacticM (List MVarId) :=
  goal.withContext do
    if ← tryCloseFromLCtx goal then return []
    let rem ← evalTacticAt
      (← `(tactic| (
        try simp only [
          Nat.ble_eq, Nat.blt_eq, decide_eq_true_eq, decide_eq_false_iff_not,
          beq_iff_eq, bne_iff_ne, beq_eq_false_iff_ne,
          Bool.not_eq_true', Bool.and_eq_true, Bool.or_eq_true
        ]
        try exact Iff.rfl
        try (constructor <;> intro _ <;> first | assumption | rfl | omega)
      )))
      goal
    return (← keepUnassigned rem)

/-- Automatically unfold non-primitive head definitions on the Boolean checker or `Prop` spec side. -/
meta def tryUnfoldUserHead (goal : MVarId) : TacticM (Option MVarId) :=
  goal.withContext do
    let tgt := stripMData (← instantiateMVars (← goal.getType))
    unless (stripMData tgt.getAppFn).isConstOf ``Iff && tgt.getAppArgs.size == 2 do return none
    let lhs := stripMData tgt.getAppArgs[0]!
    let rhs := stripMData tgt.getAppArgs[1]!
    if (stripMData lhs.getAppFn).isConstOf ``Eq && lhs.getAppArgs.size == 3 then
      let bExpr := stripMData lhs.getAppArgs[1]!
      if let some fnName := (stripMData bExpr.getAppFn).constName? then
        if !primitiveBoolHeads.contains fnName then
          let saved ← saveState
          try
            let idStx := mkIdent fnName
            let gs ← evalTacticAt (← `(tactic| unfold $idStx)) goal
            if let [g'] := gs then
              if (← g'.getType) != (← goal.getType) then return some g'
            restoreState saved
          catch _ => restoreState saved
    let propCore :=
      if (stripMData rhs.getAppFn).isConstOf ``Not && rhs.getAppArgs.size == 1 then
        stripMData rhs.getAppArgs[0]!
      else rhs
    if let some pName := (stripMData propCore.getAppFn).constName? then
      if !primitivePropHeads.contains pName then
        let saved ← saveState
        try
          let idStx := mkIdent pName
          let gs ← evalTacticAt (← `(tactic| unfold $idStx)) goal
          if let [g'] := gs then
            if (← g'.getType) != (← goal.getType) then return some g'
          restoreState saved
        catch _ => restoreState saved
    return none

/-- Recursive goal-directed `TacticM` engine for `by bool_spec_iff`. -/
meta partial def boolSpecIffStep (fuel : Nat) (goal : MVarId) : TacticM (List MVarId) :=
  goal.withContext do
    if ← goal.isAssigned then return []
    match fuel with
    | 0 => return [goal]
    | fuel' + 1 =>
      let goal ← introUntilIff goal
      if ← tryCloseFromLCtx goal then return []
      let goal ← normalizeBoolSpecAssoc goal
      let tgt := stripMData (← instantiateMVars (← goal.getType))
      unless (stripMData tgt.getAppFn).isConstOf ``Iff && tgt.getAppArgs.size == 2 do
        return (← closeBoolSpecLeaf goal)
      let lhs := stripMData tgt.getAppArgs[0]!
      let rhs := stripMData tgt.getAppArgs[1]!
      let applyRec := fun (thm : Name) => do
        if let some sgs ← tryApplyConst? goal thm then
          let mut rem := []
          for sg in sgs do rem := rem ++ (← boolSpecIffStep fuel' sg)
          return some (← keepUnassigned rem)
        return none
      let applyLeaf := fun (thm : Name) => do
        if let some sgs ← tryApplyConst? goal thm then
          return some (← keepUnassigned sgs)
        return none
      if (stripMData lhs.getAppFn).isConstOf ``Eq && lhs.getAppArgs.size == 3 then
        let bExpr := stripMData lhs.getAppArgs[1]!
        let boolVal := stripMData lhs.getAppArgs[2]!
        let bHead := (stripMData bExpr.getAppFn).constName?
        let rHead := (stripMData rhs.getAppFn).constName?
        if boolVal.isConstOf ``false then
          if bHead == some ``Bool.not then
            if let some r ← applyRec ``bool_not_false_iff then return r
          if rHead == some ``Not || rHead == some ``Ne then
            if bHead == some ``BEq.beq then
              if let some r ← applyLeaf ``bool_beq_false_iff then return r
            if bHead == some ``decide then
              if let some r ← applyLeaf ``bool_decide_false_iff then return r
            if let some r ← applyRec ``bool_false_iff_not then return r
          if bHead == some ``Bool.and && rHead == some ``Or then
            if let some r ← applyRec ``bool_and_false_iff then return r
          if bHead == some ``Bool.or && rHead == some ``And then
            if let some r ← applyRec ``bool_or_false_iff then return r
          if bHead == some ``bne && rHead == some ``Eq then
            if let some r ← applyLeaf ``bool_bne_false_iff then return r
          if bHead == some ``Option.isSome && rHead == some ``Eq then
            if let some r ← applyLeaf ``option_isSome_false_iff then return r
          if bHead == some ``Option.isNone && rHead == some ``Exists then
            if let some r ← applyLeaf ``option_isNone_false_iff then return r
          if bHead == some ``Except.isOk && rHead == some ``Exists then
            if let some r ← applyLeaf ``except_isOk_false_iff then return r
          if bHead == some ``Except.toBool && rHead == some ``Exists then
            if let some r ← applyLeaf ``except_toBool_false_iff then return r
        if boolVal.isConstOf ``true then
          if bHead == some ``Bool.and && rHead == some ``And then
            if let some r ← applyRec ``bool_and_iff then return r
          if bHead == some ``Bool.or && rHead == some ``Or then
            if let some r ← applyRec ``bool_or_iff then return r
          if bHead == some ``Bool.not then
            let inner := if bExpr.getAppArgs.size >= 1 then stripMData bExpr.getAppArgs[0]! else bExpr
            let innerHead := (stripMData inner.getAppFn).constName?
            if innerHead == some ``Option.isSome && rHead == some ``Eq then
              if let some r ← applyLeaf ``option_not_isSome_iff then return r
            if innerHead == some ``Option.isNone && rHead == some ``Exists then
              if let some r ← applyLeaf ``option_not_isNone_iff then return r
            if innerHead == some ``Except.isOk && rHead == some ``Exists then
              if let some r ← applyLeaf ``except_not_isOk_iff then return r
            if rHead == some ``Not || rHead == some ``Ne then
              if let some r ← applyRec ``bool_not_iff then return r
          if bHead == some ``BEq.beq && rHead == some ``Eq then
            if let some r ← applyLeaf ``bool_beq_iff then if r.isEmpty then return []
            if let some r ← applyLeaf ``bool_beq_symm_iff then if r.isEmpty then return []
          if bHead == some ``bne && (rHead == some ``Ne || rHead == some ``Not) then
            if let some r ← applyLeaf ``bool_bne_iff then if r.isEmpty then return []
          if bHead == some ``decide then
            if let some r ← applyLeaf ``bool_decide_iff then if r.isEmpty then return []
            if let some sgs ← tryApplyConst? goal ``bool_decide_bridge then
              let mut rem := []
              for sg in sgs do rem := rem ++ (← closeBoolSpecLeaf sg)
              if rem.isEmpty then return []
          if bHead == some ``Option.isSome then
            if rHead == some ``Exists then
              if let some r ← applyLeaf ``option_isSome_iff then return r
            if rHead == some ``Ne || rHead == some ``Not then
              if let some r ← applyLeaf ``option_isSome_ne_none_iff then return r
          if bHead == some ``Option.isNone && rHead == some ``Eq then
            if let some r ← applyLeaf ``option_isNone_iff then return r
          if bHead == some ``Except.isOk && rHead == some ``Exists then
            if let some r ← applyLeaf ``except_isOk_iff then return r
          if bHead == some ``Except.toBool && rHead == some ``Exists then
            if let some r ← applyLeaf ``except_toBool_iff then return r
          if bHead == some ``ite then
            if rHead == some ``Or then
              if let some r ← applyRec ``bool_ite_iff then return r
            if rHead == some ``And then
              if let some r ← applyRec ``bool_ite_imp_iff then return r
          if bHead == some ``List.all then
            if let some sgs ← tryApplyConst? goal ``list_all_spec_iff then
              let mut rem := []
              for sg in sgs do
                let (_, sgBody) ← sg.introNP 2
                rem := rem ++ (← boolSpecIffStep fuel' sgBody)
              return (← keepUnassigned rem)
          if bHead == some ``List.any then
            if let some sgs ← tryApplyConst? goal ``list_any_spec_iff then
              let mut rem := []
              for sg in sgs do
                let (_, sgBody) ← sg.introNP 2
                rem := rem ++ (← boolSpecIffStep fuel' sgBody)
              return (← keepUnassigned rem)
      if let some unfoldedGoal ← tryUnfoldUserHead goal then
        return (← boolSpecIffStep fuel' unfoldedGoal)
      return (← closeBoolSpecLeaf goal)

/-- **`by bool_spec_iff`**: automatically proves `check x = true ↔ Spec x` and
    `check x = false ↔ ¬ Spec x` across nested Boolean checker combinators. -/
elab "bool_spec_iff" : tactic => do
  let goal ← getMainGoal
  let remaining ← boolSpecIffStep 48 goal
  replaceMainGoal remaining

/-- **`by bool_spec_iff [def1, def2, ...]`**: unfolds the named checker/spec definitions first,
    then synthesizes the bidirectional Boolean-to-`Prop` equivalence proof. -/
elab "bool_spec_iff" "[" ids:ident,* "]" : tactic => do
  let goal ← getMainGoal
  let goal ← introUntilIff goal
  let unfoldedGoals ← evalTacticAt (← `(tactic| try unfold $[$ids]*)) goal
  let mut remaining : List MVarId := []
  for g in unfoldedGoals do
    remaining := remaining ++ (← boolSpecIffStep 48 g)
  replaceMainGoal remaining

/-! ## 2. Verified `Before` & Lexicographic Rank Reflection (`by before_rank`) -/

@[expose] def Before (u v : Nat) : Prop := u < v
@[expose] def BeforeWeak (u v : Nat) : Prop := u ≤ v

/-- Strict lexicographic rank order `(k₁, j₁) <ₗₑₓ (k₂, j₂)` for stage/derivation pairs (`WFS`, `CBV`). -/
@[expose] def LexLt (p q : Nat × Nat) : Prop := p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 < q.2)

/-- Weak lexicographic rank order `(k₁, j₁) ≤ₗₑₓ (k₂, j₂)`. -/
@[expose] def LexLe (p q : Nat × Nat) : Prop := p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 ≤ q.2)

infix:50 " <ₗₑₓ " => LexLt
infix:50 " ≤ₗₑₓ " => LexLe

theorem LexLt.to_lexLe {p q : Nat × Nat} (h : p <ₗₑₓ q) : p ≤ₗₑₓ q := by
  rcases h with hk | ⟨hkeq, hj⟩
  · exact Or.inl hk
  · exact Or.inr ⟨hkeq, Nat.le_of_lt hj⟩

theorem LexLt.trans {p q r : Nat × Nat} (h₁ : p <ₗₑₓ q) (h₂ : q <ₗₑₓ r) : p <ₗₑₓ r := by
  rcases h₁ with hk₁ | ⟨hk₁, hj₁⟩ <;> rcases h₂ with hk₂ | ⟨hk₂, hj₂⟩
  · exact Or.inl (Nat.lt_trans hk₁ hk₂)
  · exact Or.inl (hk₂ ▸ hk₁)
  · exact Or.inl (hk₁ ▸ hk₂)
  · exact Or.inr ⟨hk₁.trans hk₂, Nat.lt_trans hj₁ hj₂⟩

theorem LexLt.lt_of_lt_of_le {p q r : Nat × Nat} (h₁ : p <ₗₑₓ q) (h₂ : q ≤ₗₑₓ r) : p <ₗₑₓ r := by
  rcases h₁ with hk₁ | ⟨hk₁, hj₁⟩ <;> rcases h₂ with hk₂ | ⟨hk₂, hj₂⟩
  · exact Or.inl (Nat.lt_trans hk₁ hk₂)
  · exact Or.inl (hk₂ ▸ hk₁)
  · exact Or.inl (hk₁ ▸ hk₂)
  · exact Or.inr ⟨hk₁.trans hk₂, Nat.lt_of_lt_of_le hj₁ hj₂⟩

theorem LexLt.lt_of_le_of_lt {p q r : Nat × Nat} (h₁ : p ≤ₗₑₓ q) (h₂ : q <ₗₑₓ r) : p <ₗₑₓ r := by
  rcases h₁ with hk₁ | ⟨hk₁, hj₁⟩ <;> rcases h₂ with hk₂ | ⟨hk₂, hj₂⟩
  · exact Or.inl (Nat.lt_trans hk₁ hk₂)
  · exact Or.inl (hk₂ ▸ hk₁)
  · exact Or.inl (hk₁ ▸ hk₂)
  · exact Or.inr ⟨hk₁.trans hk₂, Nat.lt_of_le_of_lt hj₁ hj₂⟩

theorem LexLe.trans {p q r : Nat × Nat} (h₁ : p ≤ₗₑₓ q) (h₂ : q ≤ₗₑₓ r) : p ≤ₗₑₓ r := by
  rcases h₁ with hk₁ | ⟨hk₁, hj₁⟩ <;> rcases h₂ with hk₂ | ⟨hk₂, hj₂⟩
  · exact Or.inl (Nat.lt_trans hk₁ hk₂)
  · exact Or.inl (hk₂ ▸ hk₁)
  · exact Or.inl (hk₁ ▸ hk₂)
  · exact Or.inr ⟨hk₁.trans hk₂, Nat.le_trans hj₁ hj₂⟩

theorem LexLe.refl (p : Nat × Nat) : p ≤ₗₑₓ p := Or.inr ⟨rfl, Nat.le_refl p.2⟩

theorem LexLt.irrefl (p : Nat × Nat) (h : p <ₗₑₓ p) : False := by
  rcases h with hk | ⟨_, hj⟩ <;> omega

theorem lexLt_acc (p : Nat × Nat) : Acc LexLt p := by
  have hProdWf : WellFounded (Prod.Lex (· < ·) (· < ·) : (Nat × Nat) → (Nat × Nat) → Prop) :=
    (Prod.lex Nat.lt_wfRel Nat.lt_wfRel).wf
  have hSub : Subrelation LexLt (Prod.Lex (· < ·) (· < ·)) := by
    rintro ⟨k₁, j₁⟩ ⟨k₂, j₂⟩ (hk | ⟨hkeq, hj⟩)
    · exact Prod.Lex.left j₁ j₂ hk
    · subst hkeq; exact Prod.Lex.right k₁ hj
  exact Subrelation.accessible hSub (hProdWf.apply p)

instance lexLt_wfRel : WellFoundedRelation (Nat × Nat) where
  rel := LexLt
  wf  := ⟨lexLt_acc⟩

@[expose] def lookupRankVar : List Nat → Nat → Nat
  | v :: _, 0 => v | _ :: vs, idx + 1 => lookupRankVar vs idx | [], _ => 0

/-- Inductive syntax of reflected rank expressions over an environment `env : List Nat`. -/
inductive RankExpr where
  | var (idx : Nat) | const (c : Nat) | addConst (idx : Nat) (c : Nat)
  deriving DecidableEq, Repr, Inhabited

@[expose] def RankExpr.eval (env : List Nat) : RankExpr → Nat
  | .var idx => lookupRankVar env idx | .const c => c | .addConst idx c => lookupRankVar env idx + c

/-- Difference-bound edge `lookupRankVar env src + slack ≤ lookupRankVar env dst`. -/
structure DiffConstraint where
  src : Nat
  slack : Nat
  dst : Nat
  deriving DecidableEq, Repr, Inhabited

meta instance : Inhabited DiffConstraint := ⟨⟨0, 0, 0⟩⟩
@[expose] def DiffHolds (env : List Nat) (e : DiffConstraint) : Prop :=
  lookupRankVar env e.src + e.slack ≤ lookupRankVar env e.dst
@[expose] def DiffCtx (env : List Nat) : List DiffConstraint → Prop
  | [] => True | e :: es => DiffHolds env e ∧ DiffCtx env es

theorem diffHolds_of_lt {env : List Nat} {i j : Nat} (h : lookupRankVar env i < lookupRankVar env j) :
    DiffHolds env ⟨i, 1, j⟩ := h
theorem diffHolds_of_before {env : List Nat} {i j : Nat} (h : Before (lookupRankVar env i) (lookupRankVar env j)) :
    DiffHolds env ⟨i, 1, j⟩ := h
theorem diffHolds_of_le {env : List Nat} {i j : Nat} (h : lookupRankVar env i ≤ lookupRankVar env j) :
    DiffHolds env ⟨i, 0, j⟩ := by dsimp only [DiffHolds]; omega
theorem diffHolds_of_beforeWeak {env : List Nat} {i j : Nat} (h : BeforeWeak (lookupRankVar env i) (lookupRankVar env j)) :
    DiffHolds env ⟨i, 0, j⟩ := by dsimp only [DiffHolds, BeforeWeak] at *; omega
theorem diffHolds_of_add_le {env : List Nat} {i j c : Nat} (h : lookupRankVar env i + c ≤ lookupRankVar env j) :
    DiffHolds env ⟨i, c, j⟩ := h
theorem diffHolds_of_add_lt {env : List Nat} {i j c : Nat} (h : lookupRankVar env i + c < lookupRankVar env j) :
    DiffHolds env ⟨i, c + 1, j⟩ := by dsimp only [DiffHolds]; omega
theorem diffHolds_of_eq_fwd {env : List Nat} {i j : Nat} (h : lookupRankVar env i = lookupRankVar env j) :
    DiffHolds env ⟨i, 0, j⟩ := by dsimp only [DiffHolds]; omega
theorem diffHolds_of_eq_bwd {env : List Nat} {i j : Nat} (h : lookupRankVar env i = lookupRankVar env j) :
    DiffHolds env ⟨j, 0, i⟩ := by dsimp only [DiffHolds]; omega

@[expose] def lookupDiffConstraint? : List DiffConstraint → Nat → Option DiffConstraint
  | e :: _, 0 => some e
  | _ :: es, idx + 1 => lookupDiffConstraint? es idx
  | [], _ => none

theorem diffCtx_lookup {env : List Nat} {es : List DiffConstraint} {idx : Nat} {e : DiffConstraint}
    (hCtx : DiffCtx env es) (hGet : lookupDiffConstraint? es idx = some e) :
    DiffHolds env e := by
  induction es generalizing idx with
  | nil => cases hGet
  | cons _ _ ih =>
    cases idx with
    | zero => cases hGet; exact hCtx.1
    | succ _ => exact ih hCtx.2 hGet

@[expose] def traceDiffPath (es : List DiffConstraint) (cur acc : Nat) : List Nat → Option (Nat × Nat)
  | [] => some (cur, acc)
  | edgeIdx :: rest =>
    match lookupDiffConstraint? es edgeIdx with
    | some e => if Nat.beq e.src cur then traceDiffPath es e.dst (acc + e.slack) rest else none
    | none => none

theorem traceDiffPath_sound {env : List Nat} {es : List DiffConstraint} (hCtx : DiffCtx env es) :
    ∀ (path : List Nat) {cur acc endV totalSlack : Nat},
      traceDiffPath es cur acc path = some (endV, totalSlack) →
      lookupRankVar env cur + totalSlack ≤ lookupRankVar env endV + acc
  | [], _, _, _, _, hTrace => by cases hTrace; omega
  | edgeIdx :: rest, cur, acc, endV, totalSlack, hTrace => by
    unfold traceDiffPath at hTrace
    cases hLook : lookupDiffConstraint? es edgeIdx with
    | none => rw [hLook] at hTrace; cases hTrace
    | some e =>
      rw [hLook] at hTrace
      dsimp only at hTrace
      cases hSrc : Nat.beq e.src cur with
      | false => rw [hSrc] at hTrace; cases hTrace
      | true =>
        rw [hSrc] at hTrace
        simp only [ite_true] at hTrace
        have hEqSrc : e.src = cur := Nat.eq_of_beq_eq_true hSrc
        have hEdge : lookupRankVar env e.src + e.slack ≤ lookupRankVar env e.dst :=
          diffCtx_lookup hCtx hLook
        have hRest := traceDiffPath_sound hCtx rest hTrace
        rw [hEqSrc] at hEdge; omega

@[expose] def checkDiffPath (es : List DiffConstraint) (src dst minSlack : Nat) (path : List Nat) : Bool :=
  match traceDiffPath es src 0 path with
  | some (endV, totalSlack) => Nat.beq endV dst && Nat.ble minSlack totalSlack
  | none => false

theorem checkDiffPath_sound {env : List Nat} {es : List DiffConstraint}
    {src dst minSlack : Nat} {path : List Nat}
    (hCtx : DiffCtx env es) (hOk : checkDiffPath es src dst minSlack path = true) :
    lookupRankVar env src + minSlack ≤ lookupRankVar env dst := by
  unfold checkDiffPath at hOk
  cases hTr : traceDiffPath es src 0 path with
  | none => rw [hTr] at hOk; cases hOk
  | some _ =>
    rw [hTr] at hOk
    simp only [Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq] at hOk
    have hBound := traceDiffPath_sound hCtx path hTr
    rcases hOk with ⟨rfl, _⟩; omega

example : checkDiffPath [⟨0, 1, 1⟩, ⟨1, 0, 2⟩] 0 2 1 [0, 1] = true := rfl

theorem checkDiffPath_lt {env : List Nat} {es : List DiffConstraint} {src dst : Nat} {path : List Nat}
    (hCtx : DiffCtx env es) (hOk : checkDiffPath es src dst 1 path = true) :
    lookupRankVar env src < lookupRankVar env dst :=
  checkDiffPath_sound hCtx hOk

theorem checkDiffPath_before {env : List Nat} {es : List DiffConstraint} {src dst : Nat} {path : List Nat}
    (hCtx : DiffCtx env es) (hOk : checkDiffPath es src dst 1 path = true) :
    Before (lookupRankVar env src) (lookupRankVar env dst) :=
  checkDiffPath_sound hCtx hOk

theorem checkDiffPath_le {env : List Nat} {es : List DiffConstraint} {src dst : Nat} {path : List Nat}
    (hCtx : DiffCtx env es) (hOk : checkDiffPath es src dst 0 path = true) :
    lookupRankVar env src ≤ lookupRankVar env dst := by
  have h := checkDiffPath_sound hCtx hOk; omega

theorem checkDiffPath_beforeWeak {env : List Nat} {es : List DiffConstraint} {src dst : Nat} {path : List Nat}
    (hCtx : DiffCtx env es) (hOk : checkDiffPath es src dst 0 path = true) :
    BeforeWeak (lookupRankVar env src) (lookupRankVar env dst) :=
  checkDiffPath_le hCtx hOk

@[expose] def checkDiffCycle (es : List DiffConstraint) (startV : Nat) (path : List Nat) : Bool :=
  checkDiffPath es startV startV 1 path

theorem checkDiffCycle_refutes {env : List Nat} {es : List DiffConstraint} {startV : Nat} {path : List Nat}
    (hCtx : DiffCtx env es) (hCycle : checkDiffCycle es startV path = true) : False := by
  have h := checkDiffPath_sound hCtx hCycle; omega

example : checkDiffCycle [⟨0, 1, 1⟩, ⟨1, 0, 0⟩] 0 [0, 1] = true := rfl

/-- Reflected lexicographic edge `(srcK, srcJ) <ₗₑₓ (dstK, dstJ)` (`strict = true`) or `≤ₗₑₓ`. -/
structure LexConstraint where
  srcK : Nat
  srcJ : Nat
  dstK : Nat
  dstJ : Nat
  strict : Bool
  deriving DecidableEq, Repr, Inhabited

meta instance : Inhabited LexConstraint := ⟨⟨0, 0, 0, 0, false⟩⟩

@[expose] def LexHolds (env : List Nat) (le : LexConstraint) : Prop :=
  if le.strict then
    (lookupRankVar env le.srcK, lookupRankVar env le.srcJ) <ₗₑₓ
      (lookupRankVar env le.dstK, lookupRankVar env le.dstJ)
  else
    (lookupRankVar env le.srcK, lookupRankVar env le.srcJ) ≤ₗₑₓ
      (lookupRankVar env le.dstK, lookupRankVar env le.dstJ)

@[expose] def LexCtx (env : List Nat) : List LexConstraint → Prop
  | [] => True
  | le :: les => LexHolds env le ∧ LexCtx env les

@[expose] def lookupLexConstraint? : List LexConstraint → Nat → Option LexConstraint
  | le :: _, 0 => some le
  | _ :: les, idx + 1 => lookupLexConstraint? les idx
  | [], _ => none

theorem lexCtx_lookup {env : List Nat} {les : List LexConstraint} {idx : Nat} {le : LexConstraint}
    (hCtx : LexCtx env les) (hGet : lookupLexConstraint? les idx = some le) :
    LexHolds env le := by
  induction les generalizing idx with
  | nil => cases hGet
  | cons _ _ ih =>
    cases idx with
    | zero => cases hGet; exact hCtx.1
    | succ _ => exact ih hCtx.2 hGet

/-- Single hop in a reflected lexicographic rank certificate. -/
inductive LexHop where
  | directLex (lexIdx : Nat)
  | stageStrict (dstK dstJ : Nat) (kPath : List Nat)
  | stageEqStep (dstK dstJ : Nat) (strictStep : Bool) (kFwdPath kBwdPath jPath : List Nat)
  deriving DecidableEq, Repr, Inhabited

@[expose] def checkLexHop (es : List DiffConstraint) (les : List LexConstraint)
    (curK curJ : Nat) : LexHop → Option (Nat × Nat × Bool)
  | .directLex idx =>
    match lookupLexConstraint? les idx with
    | some le =>
      if Nat.beq le.srcK curK && Nat.beq le.srcJ curJ then some (le.dstK, le.dstJ, le.strict) else none
    | none => none
  | .stageStrict dstK dstJ kPath =>
    if checkDiffPath es curK dstK 1 kPath then some (dstK, dstJ, true) else none
  | .stageEqStep dstK dstJ strictStep kFwd kBwd jPath =>
    if checkDiffPath es curK dstK 0 kFwd &&
       checkDiffPath es dstK curK 0 kBwd &&
       checkDiffPath es curJ dstJ (if strictStep then 1 else 0) jPath then
      some (dstK, dstJ, strictStep)
    else none

theorem checkLexHop_sound {env : List Nat} {es : List DiffConstraint} {les : List LexConstraint}
    (hDiff : DiffCtx env es) (hLex : LexCtx env les)
    {curK curJ nextK nextJ : Nat} {isStrict : Bool} {hop : LexHop}
    (hHop : checkLexHop es les curK curJ hop = some (nextK, nextJ, isStrict)) :
    if isStrict then
      (lookupRankVar env curK, lookupRankVar env curJ) <ₗₑₓ (lookupRankVar env nextK, lookupRankVar env nextJ)
    else
      (lookupRankVar env curK, lookupRankVar env curJ) ≤ₗₑₓ (lookupRankVar env nextK, lookupRankVar env nextJ) := by
  cases hop with
  | directLex idx =>
    simp only [checkLexHop] at hHop
    cases hLook : lookupLexConstraint? les idx with
    | none => rw [hLook] at hHop; cases hHop
    | some le =>
      rw [hLook] at hHop; dsimp only at hHop
      cases hMatch : (Nat.beq le.srcK curK && Nat.beq le.srcJ curJ) with
      | false => rw [hMatch] at hHop; cases hHop
      | true =>
        rw [hMatch] at hHop; cases hHop
        simp only [Bool.and_eq_true, Nat.beq_eq] at hMatch
        have hHolds := lexCtx_lookup hLex hLook
        unfold LexHolds at hHolds
        rw [hMatch.1, hMatch.2] at hHolds; exact hHolds
  | stageStrict dstK dstJ kPath =>
    simp only [checkLexHop] at hHop
    cases hK : checkDiffPath es curK dstK 1 kPath with
    | false => rw [hK] at hHop; cases hHop
    | true => rw [hK] at hHop; cases hHop; exact Or.inl (checkDiffPath_lt hDiff hK)
  | stageEqStep dstK dstJ strictStep kFwd kBwd jPath =>
    simp only [checkLexHop] at hHop
    cases hAll :
        (checkDiffPath es curK dstK 0 kFwd &&
         checkDiffPath es dstK curK 0 kBwd &&
         checkDiffPath es curJ dstJ (if strictStep then 1 else 0) jPath) with
    | false => rw [hAll] at hHop; cases hHop
    | true =>
      rw [hAll] at hHop; cases hHop
      simp only [Bool.and_eq_true] at hAll
      have hKEq : lookupRankVar env curK = lookupRankVar env nextK :=
        Nat.le_antisymm (checkDiffPath_le hDiff hAll.1.1) (checkDiffPath_le hDiff hAll.1.2)
      cases isStrict with
      | true => exact Or.inr ⟨hKEq, checkDiffPath_lt hDiff hAll.2⟩
      | false => exact Or.inr ⟨hKEq, checkDiffPath_le hDiff hAll.2⟩

@[expose] def traceLexChain (es : List DiffConstraint) (les : List LexConstraint)
    (curK curJ : Nat) (seenStrict : Bool) : List LexHop → Option (Nat × Nat × Bool)
  | [] => some (curK, curJ, seenStrict)
  | hop :: rest =>
    match checkLexHop es les curK curJ hop with
    | some (nextK, nextJ, hopStrict) => traceLexChain es les nextK nextJ (seenStrict || hopStrict) rest
    | none => none

theorem traceLexChain_sound {env : List Nat} {es : List DiffConstraint} {les : List LexConstraint}
    (hDiff : DiffCtx env es) (hLex : LexCtx env les) :
    ∀ (hops : List LexHop) {curK curJ : Nat} {seenStrict : Bool} {endK endJ : Nat} {outStrict : Bool},
      traceLexChain es les curK curJ seenStrict hops = some (endK, endJ, outStrict) →
      (seenStrict = false →
        if outStrict then
          (lookupRankVar env curK, lookupRankVar env curJ) <ₗₑₓ (lookupRankVar env endK, lookupRankVar env endJ)
        else
          (lookupRankVar env curK, lookupRankVar env curJ) ≤ₗₑₓ (lookupRankVar env endK, lookupRankVar env endJ)) ∧
      (seenStrict = true →
        outStrict = true ∧
          (lookupRankVar env curK, lookupRankVar env curJ) ≤ₗₑₓ (lookupRankVar env endK, lookupRankVar env endJ))
  | [], _, _, _, _, _, _, hTr => by
    cases hTr
    exact ⟨fun hF => by subst hF; exact LexLe.refl _, fun hT => by subst hT; exact ⟨rfl, LexLe.refl _⟩⟩
  | hop :: rest, curK, curJ, seenStrict, endK, endJ, outStrict, hTr => by
    unfold traceLexChain at hTr
    cases hHop : checkLexHop es les curK curJ hop with
    | none => rw [hHop] at hTr; cases hTr
    | some triple =>
      rw [hHop] at hTr
      rcases triple with ⟨nextK, nextJ, hopStrict⟩
      have hStep := checkLexHop_sound hDiff hLex hHop
      have ih := traceLexChain_sound hDiff hLex rest hTr
      constructor
      · intro hSeenFalse; subst hSeenFalse
        cases hopStrict with
        | false =>
          have ihFalse := ih.1 rfl
          cases outStrict with
          | false => exact LexLe.trans hStep ihFalse
          | true => exact LexLt.lt_of_le_of_lt hStep ihFalse
        | true =>
          have ⟨hOutTrue, ihLe⟩ := ih.2 rfl
          subst hOutTrue; exact LexLt.lt_of_lt_of_le hStep ihLe
      · intro hSeenTrue; subst hSeenTrue
        have ⟨hOutTrue, ihLe⟩ := ih.2 rfl
        have hStepLe :
            (lookupRankVar env curK, lookupRankVar env curJ) ≤ₗₑₓ
              (lookupRankVar env nextK, lookupRankVar env nextJ) := by
          cases hopStrict with
          | false => exact hStep
          | true => exact LexLt.to_lexLe hStep
        exact ⟨hOutTrue, LexLe.trans hStepLe ihLe⟩

@[expose] def checkLexChain (es : List DiffConstraint) (les : List LexConstraint)
    (srcK srcJ dstK dstJ : Nat) (reqStrict : Bool) (hops : List LexHop) : Bool :=
  match traceLexChain es les srcK srcJ false hops with
  | some (endK, endJ, outStrict) => Nat.beq endK dstK && Nat.beq endJ dstJ && (!reqStrict || outStrict)
  | none => false

theorem checkLexChain_lt_sound {env : List Nat} {es : List DiffConstraint} {les : List LexConstraint}
    {srcK srcJ dstK dstJ : Nat} {hops : List LexHop}
    (hDiff : DiffCtx env es) (hLex : LexCtx env les)
    (hOk : checkLexChain es les srcK srcJ dstK dstJ true hops = true) :
    (lookupRankVar env srcK, lookupRankVar env srcJ) <ₗₑₓ
      (lookupRankVar env dstK, lookupRankVar env dstJ) := by
  unfold checkLexChain at hOk
  cases hTr : traceLexChain es les srcK srcJ false hops with
  | none => rw [hTr] at hOk; cases hOk
  | some res =>
    rw [hTr] at hOk; rcases res with ⟨endK, endJ, outStrict⟩
    simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, Nat.beq_eq] at hOk
    rcases hOk with ⟨⟨rfl, rfl⟩, rfl⟩
    exact (traceLexChain_sound hDiff hLex hops hTr).1 rfl

example : checkLexChain [⟨0, 1, 2⟩] [] 0 1 2 3 true [.stageStrict 2 3 [0]] = true := rfl

theorem checkLexChain_le_sound {env : List Nat} {es : List DiffConstraint} {les : List LexConstraint}
    {srcK srcJ dstK dstJ : Nat} {hops : List LexHop}
    (hDiff : DiffCtx env es) (hLex : LexCtx env les)
    (hOk : checkLexChain es les srcK srcJ dstK dstJ false hops = true) :
    (lookupRankVar env srcK, lookupRankVar env srcJ) ≤ₗₑₓ
      (lookupRankVar env dstK, lookupRankVar env dstJ) := by
  unfold checkLexChain at hOk
  cases hTr : traceLexChain es les srcK srcJ false hops with
  | none => rw [hTr] at hOk; cases hOk
  | some res =>
    rw [hTr] at hOk; rcases res with ⟨endK, endJ, outStrict⟩
    simp only [Bool.not_false, Bool.true_or, Bool.and_true, Bool.and_eq_true, Nat.beq_eq] at hOk
    rcases hOk with ⟨rfl, rfl⟩
    have hMain := (traceLexChain_sound hDiff hLex hops hTr).1 rfl
    cases outStrict with
    | false => exact hMain
    | true => exact LexLt.to_lexLe hMain

@[expose] def checkLexCycle (es : List DiffConstraint) (les : List LexConstraint)
    (startK startJ : Nat) (hops : List LexHop) : Bool :=
  checkLexChain es les startK startJ startK startJ true hops

theorem checkLexCycle_refutes {env : List Nat} {es : List DiffConstraint} {les : List LexConstraint}
    {startK startJ : Nat} {hops : List LexHop}
    (hDiff : DiffCtx env es) (hLex : LexCtx env les)
    (hCycle : checkLexCycle es les startK startJ hops = true) : False :=
  LexLt.irrefl _ (checkLexChain_lt_sound hDiff hLex hCycle)

example : checkLexCycle [] [⟨0, 1, 2, 3, true⟩, ⟨2, 3, 0, 1, false⟩] 0 1 [.directLex 0, .directLex 1] = true := rfl

/-- Executable DAG topological rank assignment checker (`Before` certificate for `ExprCAM` / `WFS`). -/
@[expose] def checkDagRankAssignment (ranks : List Nat) : List (Nat × Nat) → Bool
  | [] => true
  | (u, v) :: rest =>
    Nat.blt (lookupRankVar ranks u) (lookupRankVar ranks v) && checkDagRankAssignment ranks rest

theorem checkDagRankAssignment_sound {ranks : List Nat} {edges : List (Nat × Nat)}
    (hOk : checkDagRankAssignment ranks edges = true) :
    ∀ u v, (u, v) ∈ edges → Before (lookupRankVar ranks u) (lookupRankVar ranks v) := by
  induction edges with
  | nil => intro _ _ hMem; cases hMem
  | cons hd tl ih =>
    rcases hd with ⟨u₀, v₀⟩
    unfold checkDagRankAssignment at hOk
    simp only [Bool.and_eq_true, Nat.blt_eq] at hOk
    intro u v hMem
    rcases List.mem_cons.mp hMem with hEq | hTail
    · cases hEq; exact hOk.1
    · exact ih hOk.2 u v hTail

example : checkDagRankAssignment [0, 1, 2] [(0, 1), (1, 2)] = true := rfl

/-! ### `MetaM` Reifier & Bellman–Ford / Lexicographic Certificate Synthesizer for `by before_rank` -/

private meta structure RawDiffEdge where
  constraint : DiffConstraint
  proofExpr  : Expr
  deriving Inhabited

private meta structure RawLexEdge where
  constraint : LexConstraint
  proofExpr  : Expr
  deriving Inhabited

private meta structure RankReifyState where
  vars      : Array Expr := #[]
  diffEdges : Array RawDiffEdge := #[]
  lexEdges  : Array RawLexEdge := #[]

private meta def internRankVar (e : Expr) (st : RankReifyState) : MetaM (Nat × RankReifyState) := do
  let e := stripMData (← instantiateMVars e)
  for h : idx in [0 : st.vars.size] do
    if ← withoutModifyingState (isDefEq e st.vars[idx]) then return (idx, st)
  return (st.vars.size, { st with vars := st.vars.push e })

private meta def splitPairExpr (p : Expr) : MetaM (Expr × Expr) := do
  let p := stripMData (← instantiateMVars p)
  if (stripMData p.getAppFn).isConstOf ``Prod.mk && p.getAppArgs.size == 4 then
    let args := p.getAppArgs
    return (stripMData args[2]!, stripMData args[3]!)
  return (Expr.proj ``Prod 0 p, Expr.proj ``Prod 1 p)

private meta def parseVarPlusConst? (e : Expr) : Option (Expr × Nat) :=
  let e := stripMData e
  let fn := stripMData e.getAppFn
  let args := e.getAppArgs
  if fn.isConstOf ``HAdd.hAdd && args.size == 6 then
    let rhs := stripMData args[5]!
    match rhs.rawNatLit? with
    | some c => some (stripMData args[4]!, c)
    | none =>
      if (stripMData rhs.getAppFn).isConstOf ``OfNat.ofNat && rhs.getAppArgs.size >= 2 then
        (stripMData rhs.getAppArgs[1]!).rawNatLit?.map (stripMData args[4]!, ·)
      else none
  else if fn.isConstOf ``Nat.add && args.size == 2 then
    (stripMData args[1]!).rawNatLit?.map (stripMData args[0]!, ·)
  else none

private meta def buildNatEnvExpr (vars : Array Expr) : MetaM Expr :=
  mkListLit (mkConst ``Nat) vars.toList

private meta partial def harvestRankHyp (proofExpr hypTy : Expr) (st : RankReifyState) :
    MetaM RankReifyState := do
  let ty := stripMData (← instantiateMVars hypTy)
  let fn := stripMData ty.getAppFn
  let args := ty.getAppArgs
  if fn.isConstOf ``And && args.size == 2 then
    let st ← harvestRankHyp (Expr.proj ``And 0 proofExpr) args[0]! st
    return (← harvestRankHyp (Expr.proj ``And 1 proofExpr) args[1]! st)
  if fn.isConstOf ``Before && args.size == 2 then
    let (i, st) ← internRankVar args[0]! st
    let (j, st) ← internRankVar args[1]! st
    let envE ← buildNatEnvExpr st.vars
    let prf ← mkAppOptM ``diffHolds_of_before #[some envE, some (toExpr i), some (toExpr j), some proofExpr]
    return { st with diffEdges := st.diffEdges.push ⟨⟨i, 1, j⟩, prf⟩ }
  if fn.isConstOf ``BeforeWeak && args.size == 2 then
    let (i, st) ← internRankVar args[0]! st
    let (j, st) ← internRankVar args[1]! st
    let envE ← buildNatEnvExpr st.vars
    let prf ← mkAppOptM ``diffHolds_of_beforeWeak #[some envE, some (toExpr i), some (toExpr j), some proofExpr]
    return { st with diffEdges := st.diffEdges.push ⟨⟨i, 0, j⟩, prf⟩ }
  if (fn.isConstOf ``LexLt || fn.isConstOf ``LexLe) && args.size == 2 then
    let (pk, pj) ← splitPairExpr args[0]!
    let (qk, qj) ← splitPairExpr args[1]!
    let (ik, st) ← internRankVar pk st
    let (ij, st) ← internRankVar pj st
    let (jk, st) ← internRankVar qk st
    let (jj, st) ← internRankVar qj st
    return { st with lexEdges := st.lexEdges.push ⟨⟨ik, ij, jk, jj, fn.isConstOf ``LexLt⟩, proofExpr⟩ }
  if (fn.isConstOf ``LT.lt || fn.isConstOf ``GT.gt) && args.size == 4 &&
      (stripMData args[0]!).isConstOf ``Nat then
    let lhs := if fn.isConstOf ``LT.lt then args[2]! else args[3]!
    let rhs := if fn.isConstOf ``LT.lt then args[3]! else args[2]!
    if let some (base, c) := parseVarPlusConst? lhs then
      let (i, st) ← internRankVar base st
      let (j, st) ← internRankVar rhs st
      let envE ← buildNatEnvExpr st.vars
      let prf ← mkAppOptM ``diffHolds_of_add_lt
        #[some envE, some (toExpr i), some (toExpr j), some (toExpr c), some proofExpr]
      return { st with diffEdges := st.diffEdges.push ⟨⟨i, c + 1, j⟩, prf⟩ }
    let (i, st) ← internRankVar lhs st
    let (j, st) ← internRankVar rhs st
    let envE ← buildNatEnvExpr st.vars
    let prf ← mkAppOptM ``diffHolds_of_lt #[some envE, some (toExpr i), some (toExpr j), some proofExpr]
    return { st with diffEdges := st.diffEdges.push ⟨⟨i, 1, j⟩, prf⟩ }
  if (fn.isConstOf ``LE.le || fn.isConstOf ``GE.ge) && args.size == 4 &&
      (stripMData args[0]!).isConstOf ``Nat then
    let lhs := if fn.isConstOf ``LE.le then args[2]! else args[3]!
    let rhs := if fn.isConstOf ``LE.le then args[3]! else args[2]!
    if let some (base, c) := parseVarPlusConst? lhs then
      let (i, st) ← internRankVar base st
      let (j, st) ← internRankVar rhs st
      let envE ← buildNatEnvExpr st.vars
      let prf ← mkAppOptM ``diffHolds_of_add_le
        #[some envE, some (toExpr i), some (toExpr j), some (toExpr c), some proofExpr]
      return { st with diffEdges := st.diffEdges.push ⟨⟨i, c, j⟩, prf⟩ }
    let (i, st) ← internRankVar lhs st
    let (j, st) ← internRankVar rhs st
    let envE ← buildNatEnvExpr st.vars
    let prf ← mkAppOptM ``diffHolds_of_le #[some envE, some (toExpr i), some (toExpr j), some proofExpr]
    return { st with diffEdges := st.diffEdges.push ⟨⟨i, 0, j⟩, prf⟩ }
  if fn.isConstOf ``Eq && args.size == 3 && (stripMData args[0]!).isConstOf ``Nat then
    let (i, st) ← internRankVar args[1]! st
    let (j, st) ← internRankVar args[2]! st
    let envE ← buildNatEnvExpr st.vars
    let prfFwd ← mkAppOptM ``diffHolds_of_eq_fwd #[some envE, some (toExpr i), some (toExpr j), some proofExpr]
    let prfBwd ← mkAppOptM ``diffHolds_of_eq_bwd #[some envE, some (toExpr i), some (toExpr j), some proofExpr]
    return { st with diffEdges := (st.diffEdges.push ⟨⟨i, 0, j⟩, prfFwd⟩).push ⟨⟨j, 0, i⟩, prfBwd⟩ }
  return st

private meta def buildDiffCtxProof (envE : Expr) (edges : Array RawDiffEdge) : MetaM (Expr × Expr) := do
  let mut listE ← mkListLit (mkConst ``DiffConstraint) []
  let mut ctxPrf := mkConst ``True.intro
  let mut idx := edges.size
  while idx > 0 do
    idx := idx - 1
    let raw := edges[idx]!
    let cE := mkApp3 (mkConst ``DiffConstraint.mk)
      (toExpr raw.constraint.src) (toExpr raw.constraint.slack) (toExpr raw.constraint.dst)
    let edgePrf := mkAppN raw.proofExpr.getAppFn (raw.proofExpr.getAppArgs.set! 0 envE)
    ctxPrf := mkApp4 (mkConst ``And.intro)
      (mkApp2 (mkConst ``DiffHolds) envE cE) (mkApp2 (mkConst ``DiffCtx) envE listE) edgePrf ctxPrf
    listE ← mkAppM ``List.cons #[cE, listE]
  return (listE, ctxPrf)

private meta def buildLexCtxProof (envE : Expr) (edges : Array RawLexEdge) : MetaM (Expr × Expr) := do
  let mut listE ← mkListLit (mkConst ``LexConstraint) []
  let mut ctxPrf := mkConst ``True.intro
  let mut idx := edges.size
  while idx > 0 do
    idx := idx - 1
    let raw := edges[idx]!
    let le := raw.constraint
    let cE := mkApp5 (mkConst ``LexConstraint.mk)
      (toExpr le.srcK) (toExpr le.srcJ) (toExpr le.dstK) (toExpr le.dstJ) (toExpr le.strict)
    ctxPrf := mkApp4 (mkConst ``And.intro)
      (mkApp2 (mkConst ``LexHolds) envE cE) (mkApp2 (mkConst ``LexCtx) envE listE) raw.proofExpr ctxPrf
    listE ← mkAppM ``List.cons #[cE, listE]
  return (listE, ctxPrf)

private meta def solveScalarPaths (numVars : Nat) (edges : Array DiffConstraint) (cap : Nat := 16) :
    Array (Array (Option (Nat × List Nat))) := Id.run do
  let mut dist : Array (Array (Option (Nat × List Nat))) :=
    Array.replicate numVars (Array.replicate numVars none)
  for v in [0 : numVars] do
    dist := dist.set! v (dist[v]!.set! v (some (0, [])))
  for eIdx in [0 : edges.size] do
    let e := edges[eIdx]!
    if e.src < numVars && e.dst < numVars then
      let cand := Nat.min cap e.slack
      let better := match dist[e.src]![e.dst]! with
        | none => true
        | some (curS, _) => cand > curS || (e.src == e.dst && curS == 0 && cand >= 1)
      if better then dist := dist.set! e.src (dist[e.src]!.set! e.dst (some (cand, [eIdx])))
  for _ in [0 : numVars] do
    for u in [0 : numVars] do
      for eIdx in [0 : edges.size] do
        let e := edges[eIdx]!
        if e.src < numVars && e.dst < numVars then
          if let some (s₁, p₁) := dist[u]![e.src]! then
            let cand := Nat.min cap (s₁ + e.slack)
            let improve := match dist[u]![e.dst]! with
              | none => true
              | some (curS, _) => cand > curS
            if improve then dist := dist.set! u (dist[u]!.set! e.dst (some (cand, p₁ ++ [eIdx])))
  return dist

private meta def findScalarCycle? (numVars : Nat) (dist : Array (Array (Option (Nat × List Nat)))) :
    Option (Nat × List Nat) := Id.run do
  for v in [0 : numVars] do
    if let some (s, p) := dist[v]![v]! then
      if s >= 1 && !p.isEmpty then return some (v, p)
  return none

private meta def solveLexGraph (pairs : Array (Nat × Nat))
    (dist : Array (Array (Option (Nat × List Nat)))) (lexEdges : Array LexConstraint) :
    Array (Array (Option (Bool × List LexHop))) := Id.run do
  let m := pairs.size
  let mut ldist : Array (Array (Option (Bool × List LexHop))) :=
    Array.replicate m (Array.replicate m none)
  let findPairIdx? := fun (k j : Nat) => Id.run do
    for idx in [0 : m] do if pairs[idx]! == (k, j) then return some idx
    return none
  for lIdx in [0 : lexEdges.size] do
    let le := lexEdges[lIdx]!
    if let (some u, some v) := (findPairIdx? le.srcK le.srcJ, findPairIdx? le.dstK le.dstJ) then
      let better := match ldist[u]![v]! with | none => true | some (curS, _) => le.strict && !curS
      if better then ldist := ldist.set! u (ldist[u]!.set! v (some (le.strict, [.directLex lIdx])))
  for u in [0 : m] do
    let (k₁, j₁) := pairs[u]!
    for v in [0 : m] do
      let (k₂, j₂) := pairs[v]!
      if let some (sk, pk) := dist[k₁]![k₂]! then
        if sk >= 1 then
          let already := match ldist[u]![v]! with | some (true, _) => true | _ => false
          if !already then ldist := ldist.set! u (ldist[u]!.set! v (some (true, [.stageStrict k₂ j₂ pk])))
        else if let some (_, pkBwd) := dist[k₂]![k₁]! then
          if let some (sj, pj) := dist[j₁]![j₂]! then
            let isStr := sj >= 1
            let better := match ldist[u]![v]! with
              | none => u != v || isStr
              | some (curS, _) => isStr && !curS
            if better then
              ldist := ldist.set! u (ldist[u]!.set! v (some (isStr, [.stageEqStep k₂ j₂ isStr pk pkBwd pj])))
  for k in [0 : m] do
    for u in [0 : m] do
      for v in [0 : m] do
        if let (some (s₁, h₁), some (s₂, h₂)) := (ldist[u]![k]!, ldist[k]![v]!) then
          let comb := s₁ || s₂
          let better := match ldist[u]![v]! with
            | none => u != v || comb
            | some (curS, _) => comb && !curS
          if better then ldist := ldist.set! u (ldist[u]!.set! v (some (comb, h₁ ++ h₂)))
  return ldist

private meta def lexHopToExpr : LexHop → MetaM Expr
  | .directLex idx => return mkApp (mkConst ``LexHop.directLex) (toExpr idx)
  | .stageStrict dstK dstJ kPath => do
    let pE ← mkListLit (mkConst ``Nat) (kPath.map toExpr)
    return mkApp3 (mkConst ``LexHop.stageStrict) (toExpr dstK) (toExpr dstJ) pE
  | .stageEqStep dstK dstJ strictStep kFwd kBwd jPath => do
    let fE ← mkListLit (mkConst ``Nat) (kFwd.map toExpr)
    let bE ← mkListLit (mkConst ``Nat) (kBwd.map toExpr)
    let jE ← mkListLit (mkConst ``Nat) (jPath.map toExpr)
    return mkApp6 (mkConst ``LexHop.stageEqStep)
      (toExpr dstK) (toExpr dstJ) (toExpr strictStep) fE bE jE

meta partial def beforeRankCore (goal : MVarId) : TacticM (List MVarId) :=
  goal.withContext do
    if ← goal.isAssigned then return []
    let mut g := goal
    let mut keepIntro := true
    while keepIntro do
      let tgt ← g.withContext do pure (stripMData (← instantiateMVars (← g.getType)))
      if ((stripMData tgt.getAppFn).isConstOf ``Not && tgt.getAppArgs.size == 1) || tgt.isForall then
        let (_, g') ← g.intro1P
        g := g'
      else keepIntro := false
    g.withContext do
      let tgt := stripMData (← instantiateMVars (← g.getType))
      let mut st : RankReifyState := {}
      for ldecl in ← getLCtx do
        if !ldecl.isImplementationDetail then st ← harvestRankHyp ldecl.toExpr ldecl.type st
      let fn := stripMData tgt.getAppFn
      let args := tgt.getAppArgs
      let mut goalScalar : Option (Nat × Nat × Nat × Name) := none
      let mut goalLex : Option (Nat × Nat × Nat × Nat × Bool) := none
      if fn.isConstOf ``Before && args.size == 2 then
        let (u, st') ← internRankVar args[0]! st
        let (v, st'') ← internRankVar args[1]! st'
        st := st''; goalScalar := some (u, v, 1, ``checkDiffPath_before)
      else if fn.isConstOf ``BeforeWeak && args.size == 2 then
        let (u, st') ← internRankVar args[0]! st
        let (v, st'') ← internRankVar args[1]! st'
        st := st''; goalScalar := some (u, v, 0, ``checkDiffPath_beforeWeak)
      else if (fn.isConstOf ``LT.lt || fn.isConstOf ``GT.gt) && args.size == 4 &&
              (stripMData args[0]!).isConstOf ``Nat then
        let lhs := if fn.isConstOf ``LT.lt then args[2]! else args[3]!
        let rhs := if fn.isConstOf ``LT.lt then args[3]! else args[2]!
        let (u, st') ← internRankVar lhs st
        let (v, st'') ← internRankVar rhs st'
        st := st''; goalScalar := some (u, v, 1, ``checkDiffPath_lt)
      else if (fn.isConstOf ``LE.le || fn.isConstOf ``GE.ge) && args.size == 4 &&
              (stripMData args[0]!).isConstOf ``Nat then
        let lhs := if fn.isConstOf ``LE.le then args[2]! else args[3]!
        let rhs := if fn.isConstOf ``LE.le then args[3]! else args[2]!
        if let some (base, c) := parseVarPlusConst? lhs then
          let (u, st') ← internRankVar base st
          let (v, st'') ← internRankVar rhs st'
          st := st''; goalScalar := some (u, v, c, ``checkDiffPath_sound)
        else
          let (u, st') ← internRankVar lhs st
          let (v, st'') ← internRankVar rhs st'
          st := st''; goalScalar := some (u, v, 0, ``checkDiffPath_le)
      else if (fn.isConstOf ``LexLt || fn.isConstOf ``LexLe) && args.size == 2 then
        let (pk, pj) ← splitPairExpr args[0]!
        let (qk, qj) ← splitPairExpr args[1]!
        let (sk, st1) ← internRankVar pk st
        let (sj, st2) ← internRankVar pj st1
        let (dk, st3) ← internRankVar qk st2
        let (dj, st4) ← internRankVar qj st3
        st := st4; goalLex := some (sk, sj, dk, dj, fn.isConstOf ``LexLt)
      let nVars := st.vars.size
      if nVars == 0 then
        throwError "before_rank: no rank variables or inequality hypotheses found in goal or context"
      let dist := solveScalarPaths nVars (st.diffEdges.map (·.constraint)) 32
      let envE ← buildNatEnvExpr st.vars
      let (diffListE, diffCtxPrf) ← buildDiffCtxProof envE st.diffEdges
      if let some (src, dst, reqSlack, soundThm) := goalScalar then
        if let some (gotSlack, path) := dist[src]![dst]! then
          if gotSlack >= reqSlack then
            let pathE ← mkListLit (mkConst ``Nat) (path.map toExpr)
            let reflTrue ← mkEqRefl (mkConst ``true)
            let prf ←
              if soundThm == ``checkDiffPath_sound then
                mkAppOptM soundThm #[some envE, some diffListE, some (toExpr src), some (toExpr dst),
                  some (toExpr reqSlack), some pathE, some diffCtxPrf, some reflTrue]
              else
                mkAppOptM soundThm #[some envE, some diffListE, some (toExpr src), some (toExpr dst),
                  some pathE, some diffCtxPrf, some reflTrue]
            g.assign prf; return []
      let mut pairs : Array (Nat × Nat) := #[]
      let pushPair := fun (ps : Array (Nat × Nat)) (p : Nat × Nat) => if ps.contains p then ps else ps.push p
      for le in st.lexEdges do
        pairs := pushPair (pushPair pairs (le.constraint.srcK, le.constraint.srcJ))
          (le.constraint.dstK, le.constraint.dstJ)
      if let some (sk, sj, dk, dj, _) := goalLex then
        pairs := pushPair (pushPair pairs (sk, sj)) (dk, dj)
      let ldist := solveLexGraph pairs dist (st.lexEdges.map (·.constraint))
      if let some (sk, sj, dk, dj, reqStr) := goalLex then
        let mut srcIdx? : Option Nat := none
        let mut dstIdx? : Option Nat := none
        for idx in [0 : pairs.size] do
          if pairs[idx]! == (sk, sj) then srcIdx? := some idx
          if pairs[idx]! == (dk, dj) then dstIdx? := some idx
        if let (some u, some v) := (srcIdx?, dstIdx?) then
          if let some (gotStr, hops) := ldist[u]![v]! then
            if !reqStr || gotStr then
              let (lexListE, lexCtxPrf) ← buildLexCtxProof envE st.lexEdges
              let hopExprs ← liftMetaM (hops.mapM lexHopToExpr)
              let hopsE ← mkListLit (mkConst ``LexHop) hopExprs
              let reflTrue ← mkEqRefl (mkConst ``true)
              let thmName := if reqStr then ``checkLexChain_lt_sound else ``checkLexChain_le_sound
              let prf ← mkAppOptM thmName #[some envE, some diffListE, some lexListE,
                some (toExpr sk), some (toExpr sj), some (toExpr dk), some (toExpr dj),
                some hopsE, some diffCtxPrf, some lexCtxPrf, some reflTrue]
              g.assign prf; return []
      if let some (startV, cycPath) := findScalarCycle? nVars dist then
        let pathE ← mkListLit (mkConst ``Nat) (cycPath.map toExpr)
        let reflTrue ← mkEqRefl (mkConst ``true)
        let falsePrf ← mkAppOptM ``checkDiffCycle_refutes
          #[some envE, some diffListE, some (toExpr startV), some pathE, some diffCtxPrf, some reflTrue]
        g.assign (← if tgt.isConstOf ``False then pure falsePrf else mkFalseElim tgt falsePrf)
        return []
      for u in [0 : pairs.size] do
        if let some (true, cycHops) := ldist[u]![u]! then
          let (startK, startJ) := pairs[u]!
          let (lexListE, lexCtxPrf) ← buildLexCtxProof envE st.lexEdges
          let hopExprs ← liftMetaM (cycHops.mapM lexHopToExpr)
          let hopsE ← mkListLit (mkConst ``LexHop) hopExprs
          let reflTrue ← mkEqRefl (mkConst ``true)
          let falsePrf ← mkAppOptM ``checkLexCycle_refutes #[some envE, some diffListE, some lexListE,
            some (toExpr startK), some (toExpr startJ), some hopsE, some diffCtxPrf, some lexCtxPrf, some reflTrue]
          g.assign (← if tgt.isConstOf ``False then pure falsePrf else mkFalseElim tgt falsePrf)
          return []
      throwError "before_rank: could not synthesize a rank chain or cycle refutation from local hypotheses"

/-- **`by before_rank`**: verified Bellman–Ford / lexicographic rank reflection tactic proving
    `Before`, `<`, `≤`, `<ₗₑₓ`, `≤ₗₑₓ` chains and synthesizing strict-cycle refutations via `rfl`. -/
elab "before_rank" : tactic => do
  let goal ← getMainGoal
  let remaining ← beforeRankCore goal
  replaceMainGoal remaining

/-! ## 3. Constructive Permutation Witness Reflection (`by perm_cert` & `LinMemBalance`) -/

/-- Consume-once linear memory multiset balance (`Init ⊎ Produced = Consumed ⊎ Final`). -/
@[expose] def LinMemBalance {α : Type u} (init produced consumed final : List α) : Prop :=
  List.Perm (init ++ produced) (consumed ++ final)

@[expose] def extractPermAt {α : Type u} [BEq α] (x : α) : Nat → List α → Option (List α)
  | 0, y :: ys => if x == y then some ys else none
  | idx + 1, y :: ys =>
    match extractPermAt x idx ys with
    | some rest => some (y :: rest)
    | none => none
  | _, [] => none

theorem extractPermAt_perm {α : Type u} [BEq α] [LawfulBEq α] {x : α} :
    ∀ (idx : Nat) (ys : List α) {ys' : List α},
      extractPermAt x idx ys = some ys' → List.Perm (x :: ys') ys
  | 0, [], _, h => by cases h
  | _ + 1, [], _, h => by cases h
  | 0, y :: ys, ys', h => by
    simp only [extractPermAt] at h
    cases hEq : (x == y) with
    | false => rw [hEq] at h; cases h
    | true =>
      rw [hEq] at h; cases h
      rw [beq_iff_eq.mp hEq]
  | idx + 1, y :: ys, ys', h => by
    simp only [extractPermAt] at h
    cases hSub : extractPermAt x idx ys with
    | none => rw [hSub] at h; cases h
    | some rest =>
      rw [hSub] at h; cases h
      exact (List.Perm.swap y x rest).trans ((extractPermAt_perm idx ys hSub).cons y)

/-- Kernel-reducible permutation witness verifier: checks that `w` extracts `xs` element-by-element from `ys`. -/
@[expose] def checkPermWitness {α : Type u} [BEq α] : List α → List α → List Nat → Bool
  | [], [], [] => true
  | x :: xs, ys, idx :: ws =>
    match extractPermAt x idx ys with
    | some ys' => checkPermWitness xs ys' ws
    | none => false
  | _, _, _ => false

/-- **Soundness of `checkPermWitness`**: any witness accepted by `rfl` proves `List.Perm xs ys`. -/
theorem checkPermWitness_sound {α : Type u} [BEq α] [LawfulBEq α]
    {xs ys : List α} {w : List Nat} (h : checkPermWitness xs ys w = true) :
    List.Perm xs ys := by
  induction xs generalizing ys w with
  | nil => cases ys <;> cases w <;> cases h; exact List.Perm.nil
  | cons x tl ih =>
    cases w with
    | nil => cases h
    | cons idx ws =>
      unfold checkPermWitness at h
      cases hExt : extractPermAt x idx ys with
      | none => rw [hExt] at h; cases h
      | some ys' => rw [hExt] at h; exact ((ih h).cons x).trans (extractPermAt_perm idx ys hExt)

example : checkPermWitness [1, 2, 3] [3, 1, 2] [1, 1, 0] = true := rfl

def findFirstIndexAndRest {α : Type u} [BEq α] (x : α) : List α → Option (Nat × List α)
  | [] => none
  | y :: ys =>
    if x == y then some (0, ys)
    else (findFirstIndexAndRest x ys).map fun (idx, rest) => (idx + 1, y :: rest)

def synthesizePermWitness {α : Type u} [BEq α] : List α → List α → Option (List Nat)
  | [], [] => some []
  | x :: xs, ys =>
    match findFirstIndexAndRest x ys with
    | some (idx, ys') => (synthesizePermWitness xs ys').map (idx :: ·)
    | none => none
  | _, _ => none

/-! ### Typeclass-Free Symbolic `SymListExpr` Reflection for Open `LinMem` Goals -/

inductive SymPermToken where
  | elem (idx : Nat) | chunk (idx : Nat)
  deriving Repr

@[expose] def SymPermToken.beq : SymPermToken → SymPermToken → Bool
  | .elem i, .elem j => Nat.beq i j | .chunk i, .chunk j => Nat.beq i j | _, _ => false

instance : BEq SymPermToken where beq := SymPermToken.beq
instance : LawfulBEq SymPermToken where
  eq_of_beq {a b} h := by
    cases a <;> cases b <;> unfold BEq.beq instBEqSymPermToken SymPermToken.beq at h
    · exact congrArg SymPermToken.elem (Nat.eq_of_beq_eq_true h)
    · cases h
    · cases h
    · exact congrArg SymPermToken.chunk (Nat.eq_of_beq_eq_true h)
  rfl {a} := by cases a <;> exact Nat.beq_refl _

inductive SymListExpr where
  | nil | cons (elemIdx : Nat) (tail : SymListExpr) | append (l r : SymListExpr) | chunk (chunkIdx : Nat)
  deriving Repr

@[expose] def prependSymElem {α : Type u} : List α → Nat → List α → List α
  | x :: _, 0, acc => x :: acc | _ :: xs, idx + 1, acc => prependSymElem xs idx acc | [], _, acc => acc
@[expose] def lookupSymChunk {α : Type u} : List (List α) → Nat → List α
  | c :: _, 0 => c | _ :: cs, idx + 1 => lookupSymChunk cs idx | [], _ => []
@[expose] def evalSymListExpr {α : Type u} (elems : List α) (chunks : List (List α)) : SymListExpr → List α
  | .nil => []
  | .cons idx tl => prependSymElem elems idx (evalSymListExpr elems chunks tl)
  | .append l r => evalSymListExpr elems chunks l ++ evalSymListExpr elems chunks r
  | .chunk idx => lookupSymChunk chunks idx
@[expose] def evalSymToken {α : Type u} (elems : List α) (chunks : List (List α)) : SymPermToken → List α
  | .elem idx => prependSymElem elems idx [] | .chunk idx => lookupSymChunk chunks idx
@[expose] def evalSymTokens {α : Type u} (elems : List α) (chunks : List (List α)) : List SymPermToken → List α
  | [] => [] | t :: ts => evalSymToken elems chunks t ++ evalSymTokens elems chunks ts
@[expose] def flattenSymListExpr : SymListExpr → List SymPermToken
  | .nil => [] | .cons idx tl => .elem idx :: flattenSymListExpr tl
  | .append l r => flattenSymListExpr l ++ flattenSymListExpr r | .chunk idx => [.chunk idx]

theorem prependSymElem_eq_append {α : Type u} (elems : List α) (idx : Nat) (acc : List α) :
    prependSymElem elems idx acc = prependSymElem elems idx [] ++ acc := by
  induction elems generalizing idx with
  | nil => rfl
  | cons _ _ ih => cases idx with | zero => rfl | succ k => exact ih k

theorem evalSymTokens_append {α : Type u} (elems : List α) (chunks : List (List α))
    (t₁ t₂ : List SymPermToken) :
    evalSymTokens elems chunks (t₁ ++ t₂) =
      evalSymTokens elems chunks t₁ ++ evalSymTokens elems chunks t₂ := by
  induction t₁ with
  | nil => rfl
  | cons _ _ ih => simp only [List.cons_append, evalSymTokens, ih, List.append_assoc]

theorem evalSymListExpr_eq_tokens {α : Type u} (elems : List α) (chunks : List (List α)) :
    ∀ (e : SymListExpr), evalSymListExpr elems chunks e = evalSymTokens elems chunks (flattenSymListExpr e)
  | .nil => rfl
  | .cons _ tl => by
    simp only [evalSymListExpr, flattenSymListExpr, evalSymTokens, evalSymToken]
    rw [prependSymElem_eq_append, evalSymListExpr_eq_tokens elems chunks tl]
  | .append l r => by
    simp only [evalSymListExpr, flattenSymListExpr, evalSymTokens_append,
      evalSymListExpr_eq_tokens elems chunks l, evalSymListExpr_eq_tokens elems chunks r]
  | .chunk idx => (List.append_nil (lookupSymChunk chunks idx)).symm

theorem evalSymTokens_perm_of_perm {α : Type u} (elems : List α) (chunks : List (List α))
    {t₁ t₂ : List SymPermToken} (hp : List.Perm t₁ t₂) :
    List.Perm (evalSymTokens elems chunks t₁) (evalSymTokens elems chunks t₂) := by
  induction hp with
  | nil => exact List.Perm.nil
  | cons x _ ih => exact List.Perm.append_left (evalSymToken elems chunks x) ih
  | swap _ _ _ =>
    simp only [evalSymTokens]; rw [← List.append_assoc, ← List.append_assoc]
    exact List.Perm.append_right _ List.perm_append_comm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

@[expose] def checkSymPermWitness (lhs rhs : SymListExpr) (w : List Nat) : Bool :=
  checkPermWitness (flattenSymListExpr lhs) (flattenSymListExpr rhs) w

theorem checkSymPermWitness_sound {α : Type u} (elems : List α) (chunks : List (List α))
    {lhs rhs : SymListExpr} {w : List Nat} (h : checkSymPermWitness lhs rhs w = true) :
    List.Perm (evalSymListExpr elems chunks lhs) (evalSymListExpr elems chunks rhs) := by
  rw [evalSymListExpr_eq_tokens, evalSymListExpr_eq_tokens]
  exact evalSymTokens_perm_of_perm elems chunks (checkPermWitness_sound h)

example : checkSymPermWitness (.append (.cons 0 .nil) (.chunk 0)) (.append (.chunk 0) (.cons 0 .nil)) [1, 0] = true := rfl

private meta structure SymPermReifyState where
  elems  : Array Expr := #[]
  chunks : Array Expr := #[]

private meta def internPermElem (e : Expr) (st : SymPermReifyState) : MetaM (Nat × SymPermReifyState) := do
  let e := stripMData (← instantiateMVars e)
  for h : idx in [0 : st.elems.size] do
    if ← withoutModifyingState (isDefEq e st.elems[idx]) then return (idx, st)
  return (st.elems.size, { st with elems := st.elems.push e })

private meta def internPermChunk (e : Expr) (st : SymPermReifyState) : MetaM (Nat × SymPermReifyState) := do
  let e := stripMData (← instantiateMVars e)
  for h : idx in [0 : st.chunks.size] do
    if ← withoutModifyingState (isDefEq e st.chunks[idx]) then return (idx, st)
  return (st.chunks.size, { st with chunks := st.chunks.push e })

private meta partial def reifySymList (e : Expr) (st : SymPermReifyState) :
    MetaM (SymListExpr × SymPermReifyState) := do
  let e := stripMData (← instantiateMVars e)
  let fn := stripMData e.getAppFn
  let args := e.getAppArgs
  if fn.isConstOf ``List.nil && args.size == 1 then return (.nil, st)
  if fn.isConstOf ``List.cons && args.size == 3 then
    let (idx, st) ← internPermElem args[1]! st
    let (tlSym, st) ← reifySymList args[2]! st
    return (.cons idx tlSym, st)
  if fn.isConstOf ``HAppend.hAppend && args.size == 6 then
    let (lSym, st) ← reifySymList args[4]! st
    let (rSym, st) ← reifySymList args[5]! st
    return (.append lSym rSym, st)
  if fn.isConstOf ``List.append && args.size == 3 then
    let (lSym, st) ← reifySymList args[1]! st
    let (rSym, st) ← reifySymList args[2]! st
    return (.append lSym rSym, st)
  let (cIdx, st) ← internPermChunk e st
  return (.chunk cIdx, st)

private meta def symListExprToExpr : SymListExpr → Expr
  | .nil => mkConst ``SymListExpr.nil
  | .cons idx tl => mkApp2 (mkConst ``SymListExpr.cons) (toExpr idx) (symListExprToExpr tl)
  | .append l r => mkApp2 (mkConst ``SymListExpr.append) (symListExprToExpr l) (symListExprToExpr r)
  | .chunk idx => mkApp (mkConst ``SymListExpr.chunk) (toExpr idx)

private meta def flattenSymMeta : SymListExpr → List SymPermToken
  | .nil => []
  | .cons idx tl => .elem idx :: flattenSymMeta tl
  | .append l r => flattenSymMeta l ++ flattenSymMeta r
  | .chunk idx => [.chunk idx]

private meta def symTokEqMeta : SymPermToken → SymPermToken → Bool
  | .elem i, .elem j => i == j
  | .chunk i, .chunk j => i == j
  | _, _ => false

private meta def findFirstSymTok (x : SymPermToken) : List SymPermToken → Option (Nat × List SymPermToken)
  | [] => none
  | y :: ys =>
    if symTokEqMeta x y then some (0, ys)
    else (findFirstSymTok x ys).map fun (idx, rest) => (idx + 1, y :: rest)

private meta def synthSymPermWitness : List SymPermToken → List SymPermToken → Option (List Nat)
  | [], [] => some []
  | x :: xs, ys =>
    match findFirstSymTok x ys with
    | some (idx, ys') => (synthSymPermWitness xs ys').map (idx :: ·)
    | none => none
  | _, _ => none

private meta partial def extractWhnfListElems? (e : Expr) : MetaM (Option (Array Expr)) := do
  let mut cur := e
  let mut acc : Array Expr := #[]
  for _ in [0 : 1024] do
    let w ← whnf cur
    let fn := stripMData w.getAppFn
    let args := w.getAppArgs
    if fn.isConstOf ``List.nil && args.size == 1 then return some acc
    else if fn.isConstOf ``List.cons && args.size == 3 then
      acc := acc.push args[1]!; cur := args[2]!
    else return none
  return none

private meta def findDefEqPermWitness? (xs ys : Array Expr) : MetaM (Option (List Nat)) := do
  if xs.size != ys.size then return none
  let mut rem := ys.toList
  let mut wit : Array Nat := #[]
  for x in xs do
    let mut foundIdx? : Option Nat := none
    let mut prefixRev : List Expr := []
    let mut cur := rem
    let mut idx := 0
    while !cur.isEmpty && foundIdx?.isNone do
      match cur with
      | [] => break
      | y :: tail =>
        if ← withoutModifyingState (isDefEq x y) then
          foundIdx? := some idx; rem := prefixRev.reverse ++ tail
        else
          prefixRev := y :: prefixRev; cur := tail; idx := idx + 1
    match foundIdx? with
    | some i => wit := wit.push i
    | none => return none
  return some wit.toList

meta partial def permCertCore (goal : MVarId) : TacticM (List MVarId) :=
  goal.withContext do
    if ← goal.isAssigned then return []
    let mut g := goal
    let mut keepIntro := true
    while keepIntro do
      let tgt ← g.withContext do pure (stripMData (← instantiateMVars (← g.getType)))
      if tgt.isForall then
        let (_, g') ← g.intro1P; g := g'
      else keepIntro := false
    g.withContext do
      if ← tryCloseFromLCtx g then return []
      let rawTgt := stripMData (← instantiateMVars (← g.getType))
      let g ←
        if (stripMData rawTgt.getAppFn).isConstOf ``LinMemBalance then
          let gs ← evalTacticAt (← `(tactic| unfold LinMemBalance)) g
          pure (gs.headD g)
        else pure g
      g.withContext do
        let tgt := stripMData (← instantiateMVars (← g.getType))
        let fn := stripMData tgt.getAppFn
        let args := tgt.getAppArgs
        unless fn.isConstOf ``List.Perm && args.size == 3 do
          throwError "perm_cert: expected goal `List.Perm xs ys` or `LinMemBalance init prod cons final`, got:\n  {tgt}"
        let alphaTy := args[0]!
        let lhsE := args[1]!
        let rhsE := args[2]!
        let (lhsSym, st1) ← reifySymList lhsE {}
        let (rhsSym, st2) ← reifySymList rhsE st1
        if let some w := synthSymPermWitness (flattenSymMeta lhsSym) (flattenSymMeta rhsSym) then
          let elemsListE ← mkListLit alphaTy st2.elems.toList
          let listAlphaTy ← mkAppM ``List #[alphaTy]
          let chunksListE ← mkListLit listAlphaTy st2.chunks.toList
          let wE ← mkListLit (mkConst ``Nat) (w.map toExpr)
          let reflTrue ← mkEqRefl (mkConst ``true)
          let prf ← mkAppOptM ``checkSymPermWitness_sound
            #[some alphaTy, some elemsListE, some chunksListE,
              some (symListExprToExpr lhsSym), some (symListExprToExpr rhsSym),
              some wE, some reflTrue]
          if ← isDefEq (← inferType prf) tgt then
            g.assign prf; return []
        if let (some xsArr, some ysArr) ← (return (← extractWhnfListElems? lhsE, ← extractWhnfListElems? rhsE)) then
          if let some w ← findDefEqPermWitness? xsArr ysArr then
            let wE ← mkListLit (mkConst ``Nat) (w.map toExpr)
            let reflTrue ← mkEqRefl (mkConst ``true)
            let saved ← saveState
            try
              let beqInst ← synthInstance (← mkAppM ``BEq #[alphaTy])
              let lawfulInst ← synthInstance (← mkAppOptM ``LawfulBEq #[some alphaTy, some beqInst])
              let prf ← mkAppOptM ``checkPermWitness_sound
                #[some alphaTy, some beqInst, some lawfulInst, some lhsE, some rhsE, some wE, some reflTrue]
              if ← isDefEq (← inferType prf) tgt then
                g.assign prf; return []
            catch _ => restoreState saved
            -- Fallback for types without `[LawfulBEq α]`: reify the WHNF-reduced element arrays symbolically!
            let lhsRed ← mkListLit alphaTy xsArr.toList
            let rhsRed ← mkListLit alphaTy ysArr.toList
            let (lSym2, s1) ← reifySymList lhsRed {}
            let (rSym2, s2) ← reifySymList rhsRed s1
            if let some wSym := synthSymPermWitness (flattenSymMeta lSym2) (flattenSymMeta rSym2) then
              let elemsE ← mkListLit alphaTy s2.elems.toList
              let chunksE ← mkListLit (← mkAppM ``List #[alphaTy]) s2.chunks.toList
              let wSymE ← mkListLit (mkConst ``Nat) (wSym.map toExpr)
              let prf ← mkAppOptM ``checkSymPermWitness_sound
                #[some alphaTy, some elemsE, some chunksE,
                  some (symListExprToExpr lSym2), some (symListExprToExpr rSym2),
                  some wSymE, some reflTrue]
              if ← isDefEq (← inferType prf) tgt then
                g.assign prf; return []
        throwError "perm_cert: lists are not certified permutations of each other:\n  lhs: {lhsE}\n  rhs: {rhsE}"

/-- **`by perm_cert`**: constructive `List.Perm` & `LinMemBalance` reflection tactic computing an
    extraction witness in `MetaM` and verifying `checkPermWitness` / `checkSymPermWitness` by `rfl`
    in Lean's kernel (zero `native_decide`). -/
elab "perm_cert" : tactic => do
  let goal ← getMainGoal
  let remaining ← permCertCore goal
  replaceMainGoal remaining

end Obend.Tactic.SymbolicCert
end
