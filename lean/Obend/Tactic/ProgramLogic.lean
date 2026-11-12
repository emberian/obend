module
/-
# Obend.Tactic.ProgramLogic — `TacticM` Symbolic Execution, Spatial AC Canceller & `GPaco` Automation

Provides three genuine `Lean.Elab.Tactic.TacticM` / `MetaM` proof-automation tactics over
`Obend.Logic.MultiTurnHoare`, `Obend.Logic.SeparationFrame`, and `Obend.Paco.GPaco`:

1. **`by sep_cancel`**:
   - Reifies arbitrary nested `P₁ ∗ P₂ ∗ …` and `sepEmp` trees over *any* `[LawfulPCM M]` into
     canonical `sepAll` lists in `MetaM`, constructing explicit kernel `Eq.trans` / `sep_congr_eq` /
     `sepAll_append` proofs (`reifySepExpr`).
   - Performs greedy AC matching and cancellation via `sepCancel_match` / `sepCancel_defer_rhs`,
     discharges `SepProp` equalities (`sepEntails_antisymm`), pointwise heap hypotheses, and
     automatically synthesizes unknown frame metavariables `?R` (`sepAll_entails_singleton_sepNice`)!

2. **`by obend_wp`**:
   - Goal-directed symbolic execution engine over both `SafeWP` / `SafeWPGen` and `HoareSep`:
     - On `HoareSep P op Q`: resolves local/known `IsLocalOp` + sub-specifications, applies
       `hoare_sep_conseq_frame`, and invokes `sepCancelGoal` to synthesize the untouched spatial
       frame `?R` and cancel AC postconditions automatically.
     - On `SafeWP` / `SafeWPGen`: evaluates `Obend.Logic.yields?` and `Obend.Law.step?` in `MetaM`
       (`whnf`) to emit `rfl`-checked `wp_perform_of_yields?` and `wp_step_of_step?` transitions,
       splits symbolic `decide` / `Bool` / `Nat` conditionals, decomposes demonic `ProtocolSpec`
       response disjunctions, applies local `SafeWP` hypotheses (`wp_monoGen`, `wp_seqNat`), and
       discharges arithmetic postconditions via `omega`.

3. **`by gpaco_step` (`by gpaco_step using seedRel`)**:
   - Automates `Obend.Paco.GPaco` coinduction initiation (`gpaco_init`, `gpaco_coind`,
     `gpaco_clo_cofix`), productive `F`-step unfolding (`gpaco_fold`, `paco_fold`) releasing
     guarded hypotheses into `gupaco`, and recursive relational-union hypothesis routing across
     `⊔`, `gupaco`, `gpaco`, and `upaco`.
-/

public import Lean
public meta import Lean
public import Obend.Logic.MultiTurnHoare
public import Obend.Logic.SeparationFrame
public import Obend.Paco.GPaco

public section

namespace Obend.Tactic.ProgramLogic

open Obend.Core.Term
open Obend.Core.Data (Data)
open Obend.Logic
open Obend.Paco

set_option autoImplicit false

universe u

/-! ## 1. Kernel Reflection & Normalization Lemmas for `sep_cancel` and `gpaco_step` -/

section SepHelpers

variable {M : Type u} [LawfulPCM M]

/-- Clean right-associated `SepProp` rendering without trailing `∗ sepEmp`. -/
@[expose] def sepNice : List (SepProp M) → SepProp M
  | [] => sepEmp
  | [P] => P
  | P :: Ps => P ∗ sepNice Ps

theorem sepNice_eq_sepAll : ∀ (xs : List (SepProp M)), sepNice xs = sepAll xs
  | [] => rfl
  | [P] => (sep_emp P).symm
  | P₁ :: P₂ :: Ps => by
    change (P₁ ∗ sepNice (P₂ :: Ps)) = (P₁ ∗ sepAll (P₂ :: Ps))
    rw [sepNice_eq_sepAll (P₂ :: Ps)]

theorem sepAll_entails_singleton_sepNice (xs : List (SepProp M)) :
    sepAll xs ⊢ₛ sepAll [sepNice xs] := by
  have heq : sepAll [sepNice xs] = sepAll xs := by
    change (sepNice xs ∗ sepEmp) = sepAll xs
    rw [sep_emp, sepNice_eq_sepAll]
  rw [heq]
  exact sepEntails_refl _

theorem sepCancel_defer_rhs {Q : SepProp M} {lhs r₁ r₂ : List (SepProp M)}
    (h : sepAll lhs ⊢ₛ sepAll (r₁ ++ Q :: r₂)) :
    sepAll lhs ⊢ₛ (Q ∗ sepAll (r₁ ++ r₂)) := by
  rw [← sepAll_extract Q r₁ r₂]
  exact h

omit [LawfulPCM M] in
theorem sepEntails_apply_at {P Q : SepProp M} {m : M}
    (hEntails : P ⊢ₛ Q) (hPm : P m) : Q m :=
  hEntails m hPm

end SepHelpers

section GPacoHelpers

variable {α : Type u}

theorem gfp_to_gpaco {F : MonoRel α} {x y : α}
    (h : gpaco F ⊥ ⊥ x y) : F.gfp x y := by
  rw [← gpaco_init F]
  exact h

theorem gpaco_fold_at {F : MonoRel α} {r g : Rel α} {x y : α}
    (h : F (gupaco F r g) x y) : gpaco F r g x y :=
  gpaco_fold F r g x y h

theorem paco_fold_at {F : MonoRel α} {r : Rel α} {x y : α}
    (h : F (upaco F r) x y) : paco F r x y :=
  paco_fold F r x y h

end GPacoHelpers

/-! ## 2. `by sep_cancel` — `MetaM` Spatial AC Normalizer & Frame Synthesizer -/

open Lean Meta Elab Tactic

/-- Strip outer `Expr.mdata` wrappers. -/
meta partial def stripMData (e : Expr) : Expr :=
  match e with
  | .mdata _ inner => stripMData inner
  | _ => e

/-- Keep only unassigned metavariables. -/
meta def keepUnassigned (gs : List MVarId) : MetaM (List MVarId) :=
  gs.filterM fun g => return !(← g.isAssigned)

/-- Build a typed `List (SepProp M)` expression from `atoms`. -/
meta def mkSepPropListExpr (mType : Expr) (atoms : List Expr) : MetaM Expr := do
  let sepPropTy ← mkAppM ``Obend.Logic.SepProp #[mType]
  mkListLit sepPropTy atoms

/-- Build a right-associated syntactic `sepConj` chain `P₁ ∗ (P₂ ∗ …)` matching `sepNice`. -/
meta def mkSepConjChain (mType pcmInst : Expr) : List Expr → MetaM Expr
  | [] => mkAppOptM ``Obend.Logic.sepEmp #[mType, pcmInst]
  | [p] => pure p
  | p :: ps => do
    let rest ← mkSepConjChain mType pcmInst ps
    mkAppOptM ``Obend.Logic.sepConj #[mType, pcmInst, p, rest]

/-- Reify an arbitrary `SepProp M` expression `e` into `(atoms, pf)` where
    `pf : e = sepAll atoms.toList`. -/
meta partial def reifySepExpr (mType pcmInst e : Expr) : MetaM (Array Expr × Expr) := do
  let eClean := stripMData (← instantiateMVars e)
  let fn := stripMData eClean.getAppFn
  let args := eClean.getAppArgs
  -- Do not split a naked metavariable `?R` into atoms; keep it as a single frame atom.
  if eClean.isMVar then
    let pf ← mkAppOptM ``Obend.Logic.sepAll_singleton_eq #[mType, pcmInst, eClean]
    return (#[eClean], pf)
  if fn.isConstOf ``Obend.Logic.sepEmp && args.size == 2 then
    let empAll ← mkAppOptM ``Obend.Logic.sepAll_nil #[mType, pcmInst]
    return (#[], empAll)
  if fn.isConstOf ``Obend.Logic.sepConj && args.size == 4 then
    let lhs := args[2]!
    let rhs := args[3]!
    let (atomsL, pfL) ← reifySepExpr mType pcmInst lhs
    let (atomsR, pfR) ← reifySepExpr mType pcmInst rhs
    let listL ← mkSepPropListExpr mType atomsL.toList
    let listR ← mkSepPropListExpr mType atomsR.toList
    let sepAllL ← mkAppOptM ``Obend.Logic.sepAll #[mType, pcmInst, listL]
    let sepAllR ← mkAppOptM ``Obend.Logic.sepAll #[mType, pcmInst, listR]
    let pfCongr ← mkAppOptM ``Obend.Logic.sep_congr_eq
      #[mType, pcmInst, lhs, sepAllL, rhs, sepAllR, pfL, pfR]
    let pfAppend ← mkAppOptM ``Obend.Logic.sepAll_append #[mType, pcmInst, listL, listR]
    let pfTotal ← mkEqTrans pfCongr pfAppend
    return (atomsL ++ atomsR, pfTotal)
  let pfAtom ← mkAppOptM ``Obend.Logic.sepAll_singleton_eq #[mType, pcmInst, eClean]
  return (#[eClean], pfAtom)

/-- Find the first index in `lhsAtoms` definitionally equal to `q` (without assigning `lhs` mvars). -/
meta def findMatchingAtomIdx? (lhsAtoms : List Expr) (q : Expr) : MetaM (Option Nat) := do
  if q.isMVar then return none
  let mut idx : Nat := 0
  for p in lhsAtoms do
    let pClean := stripMData (← instantiateMVars p)
    if !pClean.isMVar then
      let ok ← withoutModifyingState (isDefEq pClean q)
      if ok then
        return some idx
    idx := idx + 1
  return none

/-- Try matching `ptsTo k v₁` with `ptsTo k v₂` when keys match and values are equal by `omega`! -/
meta def tryCloseResidualPtsTo (goal : MVarId) : TacticM (List MVarId) :=
  goal.withContext do
    let rem ← evalTacticAt
      (← `(tactic| (
        try simp only [sepNice_eq_sepAll, sepAll, emp_sep, sep_emp]
        try exact sepEntails_refl _
        try (
          have hEq : _ = _ := by congr 1 <;> omega
          rw [hEq]
          exact sepEntails_refl _
        )
      )))
      goal
    return rem

/-- Apply a 1-premise lemma `fn : Premise → Target` to `goal` directly via `mkFreshExprMVar`,
    returning ONLY the single `Premise` subgoal without collecting metavariables inside `Target`! -/
meta def applyOnePremise (goal : MVarId) (fn : Expr) : MetaM MVarId :=
  goal.withContext do
    let fnTy ← whnf (← inferType fn)
    let .forallE _ domTy _ _ := fnTy
      | throwError "applyOnePremise: expected function type, got {fnTy}"
    let gNext ← mkFreshExprMVar domTy
    let prf := mkApp fn gNext
    let _ ← isDefEq (← goal.getType) (← inferType prf)
    goal.assign prf
    return gNext.mvarId!

/-- Cancel `sepAll lhsAtoms ⊢ₛ sepAll rhsAtoms` by constructing explicit `sepCancel_match` chains. -/
meta partial def cancelSepAllLoop (mType pcmInst : Expr)
    (lhsAtoms rhsAtoms deferredRhs : List Expr) (goal : MVarId) : TacticM (List MVarId) :=
  goal.withContext do
    if ← goal.isAssigned then return []
    match rhsAtoms with
    | [] =>
      match deferredRhs with
      | [] =>
        if lhsAtoms.isEmpty then
          let empExpr ← mkAppOptM ``Obend.Logic.sepEmp #[mType, pcmInst]
          let pf ← mkAppOptM ``Obend.Logic.sepEntails_refl #[mType, empExpr]
          goal.assign pf
          return []
        else
          return (← tryCloseResidualPtsTo goal)
      | [mvarAtom] =>
        let mClean := stripMData (← instantiateMVars mvarAtom)
        if mClean.isMVar then
          let lhsListExpr ← mkSepPropListExpr mType lhsAtoms
          let niceFrame ← mkSepConjChain mType pcmInst lhsAtoms
          let unified ← isDefEq mClean niceFrame
          if unified then
            let pf ← mkAppOptM ``sepAll_entails_singleton_sepNice #[mType, pcmInst, lhsListExpr]
            let _ ← isDefEq (← goal.getType) (← inferType pf)
            goal.assign pf
            return []
        return (← tryCloseResidualPtsTo goal)
      | _ =>
        return (← tryCloseResidualPtsTo goal)
    | q :: rRest =>
      let qClean := stripMData (← instantiateMVars q)
      -- Defer frame metavariables `?R` until all concrete RHS atoms have been cancelled!
      if qClean.isMVar then
        let lhsListExpr ← mkSepPropListExpr mType lhsAtoms
        let r1Expr ← mkSepPropListExpr mType rRest
        let r2Expr ← mkSepPropListExpr mType deferredRhs
        let gNext ← applyOnePremise goal (← mkAppOptM ``sepCancel_defer_rhs
          #[mType, pcmInst, qClean, lhsListExpr, r1Expr, r2Expr])
        return (← cancelSepAllLoop mType pcmInst lhsAtoms rRest (deferredRhs ++ [qClean]) gNext)
      if let some idx ← findMatchingAtomIdx? lhsAtoms qClean then
        let p := lhsAtoms[idx]!
        let _ ← isDefEq p qClean
        let before := lhsAtoms.take idx
        let after := lhsAtoms.drop (idx + 1)
        let beforeExpr ← mkSepPropListExpr mType before
        let afterExpr ← mkSepPropListExpr mType after
        let rAllRest := rRest ++ deferredRhs
        let rRestExpr ← mkSepPropListExpr mType rAllRest
        let gNext ← applyOnePremise goal (← mkAppOptM ``Obend.Logic.sepCancel_match
          #[mType, pcmInst, qClean, beforeExpr, afterExpr, rRestExpr])
        return (← cancelSepAllLoop mType pcmInst (before ++ after) rRest deferredRhs gNext)
      else
        -- Defer unmatched concrete atom (e.g. `ptsTo dst (b₂ + amt)` vs `ptsTo dst (amt + b₂)`)
        let lhsListExpr ← mkSepPropListExpr mType lhsAtoms
        let r1Expr ← mkSepPropListExpr mType rRest
        let r2Expr ← mkSepPropListExpr mType deferredRhs
        let gNext ← applyOnePremise goal (← mkAppOptM ``sepCancel_defer_rhs
          #[mType, pcmInst, qClean, lhsListExpr, r1Expr, r2Expr])
        return (← cancelSepAllLoop mType pcmInst lhsAtoms rRest (deferredRhs ++ [qClean]) gNext)

/-- Core spatial cancellation tactic on a single `MVarId`. -/
meta partial def sepCancelGoal (goal : MVarId) : TacticM (List MVarId) :=
  goal.withContext do
    if ← goal.isAssigned then return []
    let tgt := stripMData (← instantiateMVars (← goal.getType))
    let fn := stripMData tgt.getAppFn
    let args := tgt.getAppArgs
    -- Case 1: `sepEntails P Q` (`P ⊢ₛ Q`)
    if fn.isConstOf ``Obend.Logic.sepEntails && args.size == 3 then
      let mType := args[0]!
      let lhs := args[1]!
      let rhs := args[2]!
      let pcmType ← mkAppM ``Obend.Logic.LawfulPCM #[mType]
      let pcmInst ← synthInstance pcmType
      let (atomsL, pfL) ← reifySepExpr mType pcmInst lhs
      let (atomsR, pfR) ← reifySepExpr mType pcmInst rhs
      let listL ← mkSepPropListExpr mType atomsL.toList
      let listR ← mkSepPropListExpr mType atomsR.toList
      let sepAllL ← mkAppOptM ``Obend.Logic.sepAll #[mType, pcmInst, listL]
      let sepAllR ← mkAppOptM ``Obend.Logic.sepAll #[mType, pcmInst, listR]
      let gNorm ← applyOnePremise goal (← mkAppOptM ``Obend.Logic.sepEntails_congr
        #[mType, lhs, sepAllL, rhs, sepAllR, pfL, pfR])
      let rem ← cancelSepAllLoop mType pcmInst atomsL.toList atomsR.toList [] gNorm
      -- If a single arithmetic `ptsTo` mismatch remains, try `sep_mono` + `omega`
      let mut finalRem : List MVarId := []
      for rg in rem do
        if !(← rg.isAssigned) then
          let r2 ← evalTacticAt
            (← `(tactic| (
              try simp only [sepAll, emp_sep, sep_emp]
              try exact sepEntails_refl _
              try (
                refine sep_mono ?_ ?_ <;>
                first
                  | exact sepEntails_refl _
                  | (have hEq : _ = _ := by congr 1 <;> omega
                     rw [hEq]; exact sepEntails_refl _)
              )
            )))
            rg
          finalRem := finalRem ++ r2
      return (← keepUnassigned finalRem)
    -- Case 2: Equality `P = Q` on `SepProp M`
    if fn.isConstOf ``Eq && args.size == 3 then
      let eqTy ← whnf args[0]!
      if eqTy.isForall then
        let mType := eqTy.bindingDomain!
        let pcmType ← mkAppM ``Obend.Logic.LawfulPCM #[mType]
        if let .some _pcmInst ← trySynthInstance pcmType then
          let subgoals ← goal.apply (← mkAppOptM ``Obend.Logic.sepEntails_antisymm
            #[mType, args[1]!, args[2]!])
          let mut rem : List MVarId := []
          for sg in subgoals do
            rem := rem ++ (← sepCancelGoal sg)
          return (← keepUnassigned rem)
    -- Case 3: Pointwise spatial goal `Q m` given local hypothesis `h : P m`
    if tgt.isApp then
      let mArg := tgt.appArg!
      let qPred := tgt.appFn!
      let mType ← inferType mArg
      let pcmType ← mkAppM ``Obend.Logic.LawfulPCM #[mType]
      if let .some _pcmInst ← trySynthInstance pcmType then
        for ldecl in ← getLCtx do
          if ldecl.isImplementationDetail then continue
          let hTy := stripMData (← instantiateMVars ldecl.type)
          if hTy.isApp then
            let hArg := hTy.appArg!
            let pPred := hTy.appFn!
            let sameHeap ← withoutModifyingState (isDefEq hArg mArg)
            if sameHeap then
              let subgoals ← goal.apply (← mkAppOptM ``sepEntails_apply_at
                #[mType, pPred, qPred, mArg])
              match subgoals with
              | [gEnt, gHyp] =>
                gHyp.assign ldecl.toExpr
                return (← sepCancelGoal gEnt)
              | _ => continue
    return [goal]

/-- **`by sep_cancel`**: AC spatial normalizer, canceller, and frame synthesizer over `[LawfulPCM M]`. -/
elab "sep_cancel" : tactic => do
  let goal ← getMainGoal
  let rem ← sepCancelGoal goal
  replaceMainGoal rem

/-! ## 3. `by obend_wp` — `TacticM` Symbolic Execution Engine for `SafeWP` & `HoareSep` -/

/-- Build a kernel `Value t` proof directly when `t` has a syntactic `Core4` value constructor. -/
meta def proveSyntacticValue? (t : Expr) : MetaM (Option Expr) := do
  let tClean := stripMData (← instantiateMVars t)
  let fn := stripMData tClean.getAppFn
  let args := tClean.getAppArgs
  if fn.isConstOf ``Term.lam && args.size == 1 then
    return some (← mkAppM ``Value.function #[args[0]!])
  if fn.isConstOf ``Term.nat && args.size == 1 then
    return some (← mkAppM ``Value.natural #[args[0]!])
  if fn.isConstOf ``Term.boolean && args.size == 1 then
    return some (← mkAppM ``Value.boolean #[args[0]!])
  if fn.isConstOf ``Term.label && args.size == 1 then
    return some (← mkAppM ``Value.label #[args[0]!])
  if fn.isConstOf ``Term.record && args.size == 1 then
    return some (← mkAppM ``Value.record #[args[0]!])
  if fn.isConstOf ``Term.specification && args.size == 2 then
    return some (← mkAppM ``Value.specification #[args[0]!, args[1]!])
  if fn.isConstOf ``Term.prototype && args.size == 2 then
    return some (← mkAppM ``Value.prototype #[args[0]!, args[1]!])
  if fn.isConstOf ``Term.inject && args.size == 2 then
    return some (← mkAppM ``Value.inject #[args[0]!, args[1]!])
  return none

/-- Search local context for a matching `SafeWPGen` / `SafeWP` hypothesis on `(proto, ep, t)`. -/
meta def findMatchingSafeWPHyp? (protoExpr epExpr tExpr : Expr) : MetaM (Option Expr) := do
  for ldecl in ← getLCtx do
    if ldecl.isImplementationDetail then continue
    let hTy := stripMData (← instantiateMVars ldecl.type)
    let fn := stripMData hTy.getAppFn
    let args := hTy.getAppArgs
    if fn.isConstOf ``Obend.Logic.SafeWP && args.size == 3 then
      let expDerived ← mkAppM ``Obend.Logic.ExpectedPlan #[args[0]!]
      let ok ← withoutModifyingState do
        let mp ← isDefEq protoExpr args[0]!
        let me ← isDefEq epExpr expDerived
        let mt ← isDefEq tExpr args[1]!
        pure (mp && me && mt)
      if ok then
        let _ ← isDefEq protoExpr args[0]!
        let _ ← isDefEq epExpr expDerived
        let _ ← isDefEq tExpr args[1]!
        return some ldecl.toExpr
    if fn.isConstOf ``Obend.Logic.SafeWPGen && args.size == 4 then
      let ok ← withoutModifyingState do
        let mp ← isDefEq protoExpr args[0]!
        let me ← isDefEq epExpr args[1]!
        let mt ← isDefEq tExpr args[2]!
        pure (mp && me && mt)
      if ok then
        let _ ← isDefEq protoExpr args[0]!
        let _ ← isDefEq epExpr args[1]!
        let _ ← isDefEq tExpr args[2]!
        return some ldecl.toExpr
  return none

/-- Synthesize `IsLocalOp op` from local hypotheses or standard `SeparationFrame` heap primitives. -/
meta def synthIsLocalOp? (opExpr : Expr) : MetaM (Option Expr) := do
  let opClean := stripMData (← instantiateMVars opExpr)
  for ldecl in ← getLCtx do
    if ldecl.isImplementationDetail then continue
    let hTy := stripMData (← instantiateMVars ldecl.type)
    if (stripMData hTy.getAppFn).isConstOf ``Obend.Logic.IsLocalOp && hTy.getAppArgs.size >= 1 then
      let opArg := hTy.getAppArgs.back!
      let ok ← withoutModifyingState (isDefEq opClean opArg)
      if ok then
        let _ ← isDefEq opClean opArg
        return some ldecl.toExpr
  let fn := stripMData opClean.getAppFn
  let args := opClean.getAppArgs
  if fn.isConstOf ``Obend.Logic.readCell && args.size == 2 then
    return some (← mkAppOptM ``Obend.Logic.readCell_local #[args[0]!, args[1]!])
  if fn.isConstOf ``Obend.Logic.writeCell && args.size == 3 then
    return some (← mkAppOptM ``Obend.Logic.writeCell_local #[args[0]!, args[1]!, args[2]!])
  if fn.isConstOf ``Obend.Logic.transferCells && args.size == 3 then
    return some (← mkAppM ``Obend.Logic.transferCells_local #[args[0]!, args[1]!, args[2]!])
  return none

/-- Find a matching `HoareSep` sub-specification in local context (or `transferCells_spec`). -/
meta def findHoareSepSubSpec? (opExpr : Expr) : TacticM (Option (Expr × List MVarId)) := do
  let opClean := stripMData (← instantiateMVars opExpr)
  for ldecl in ← getLCtx do
    if ldecl.isImplementationDetail then continue
    let hTy := stripMData (← instantiateMVars ldecl.type)
    if (stripMData hTy.getAppFn).isConstOf ``Obend.Logic.HoareSep && hTy.getAppArgs.size == 5 then
      let opHyp := hTy.getAppArgs[3]!
      let ok ← withoutModifyingState (isDefEq opClean opHyp)
      if ok then
        let _ ← isDefEq opClean opHyp
        return some (ldecl.toExpr, [])
  let fn := stripMData opClean.getAppFn
  let args := opClean.getAppArgs
  if fn.isConstOf ``Obend.Logic.transferCells && args.size == 3 then
    let natTy := mkConst ``Nat
    let b1 ← mkFreshExprMVar natTy
    let b2 ← mkFreshExprMVar natTy
    let leTy ← mkAppM ``LE.le #[args[2]!, b1]
    let hLe ← mkFreshExprMVar leTy
    let specPrf ← mkAppM ``Obend.Logic.transferCells_spec #[args[0]!, args[1]!, args[2]!, b1, b2, hLe]
    return some (specPrf, [hLe.mvarId!])
  return none

/-- Discharge pure postconditions, existential value witnesses, and `ExpectedPlan` obligations. -/
meta def dischargeWpSideGoal (goal : MVarId) : TacticM (List MVarId) :=
  goal.withContext do
    if ← goal.isAssigned then return []
    let rem ← evalTacticAt
      (← `(tactic| (
        try dsimp only [ExpectedPlan] at *
        try assumption
        try rfl
        try trivial
        try omega
        try (refine ⟨_, rfl, ?_⟩ <;> first | trivial | omega | rfl | assumption)
        try (refine ⟨_, Or.inl ⟨rfl, Or.inl rfl⟩⟩)
        try (refine ⟨_, Or.inl ⟨⟨_, rfl⟩, Or.inl rfl⟩⟩)
        try (refine ⟨_, Or.inr ⟨rfl, rfl⟩⟩)
        try (refine ⟨_, ⟨_, rfl⟩, Or.inl rfl⟩)
        try simp (config := { failIfUnchanged := false }) only [
          Nat.mul_zero, Nat.zero_mul, Nat.add_zero, Nat.zero_add,
          and_self, true_and, and_true
        ] at *
        try (refine ⟨_, rfl, ?_⟩ <;> first | trivial | omega | rfl | assumption)
        try omega
      )))
      goal
    return (← keepUnassigned rem)

/-- Unfold user/library `Core4` `Term` helper definitions (e.g. `guardedRetryStep`,
    `nextCooldownStreak`, `counterBump`, `seqNat`) inside `e` while preserving `Term` constructors
    and `Term.substitute`/`Term.rename`/`instantiate` for `simp`. -/
meta def unfoldTermAbbrevs (e : Expr) : MetaM Expr :=
  Meta.transform e (pre := fun sub => do
    let fn := stripMData sub.getAppFn
    if let .const declName _ := fn then
      let pfx := declName.getPrefix
      if pfx != `Obend.Core.Term.Term &&
         declName != ``instantiate &&
         declName != ``Term.substitute &&
         declName != ``Term.rename &&
         declName != ``liftSubstitution &&
         declName != ``liftRename then
        let ty ← inferType sub
        if (stripMData ty).isConstOf ``Obend.Core.Term.Term then
          if let some unfolded ← unfoldDefinition? sub then
            let used := unfolded.getUsedConstants
            if !used.contains declName && !used.contains ``WellFounded.fix then
              return .visit unfolded
    return .continue)

mutual
  /-- Decompose demonic protocol response hypotheses (`Or`, `And`, `Exists`, `Eq`, impossible tags)
      and recursively symbolically execute every surviving branch! -/
  meta partial def splitDemonicHypAndExec (fuel : Nat) (respFVar hFVar : FVarId) (goal : MVarId) :
      TacticM (List MVarId) :=
    goal.withContext do
      if ← goal.isAssigned then return []
      let hDecl ← hFVar.getDecl
      let hTy ← whnf (stripMData (← instantiateMVars hDecl.type))
      let fn := stripMData hTy.getAppFn
      -- `False`: contradiction
      if fn.isConstOf ``False then
        let sub ← goal.cases hFVar
        return (← keepUnassigned (sub.toList.map (·.mvarId)))
      -- `Or A B`: split into two demonic response branches
      if fn.isConstOf ``Or then
        let subgoals ← goal.cases hFVar
        let mut rem : List MVarId := []
        for s in subgoals do
          if let #[newHyp] := s.fields then
            if newHyp.isFVar then
              rem := rem ++ (← splitDemonicHypAndExec fuel respFVar newHyp.fvarId! s.mvarId)
            else
              rem := rem ++ (← obendWpCore fuel s.mvarId)
          else
            rem := rem ++ (← obendWpCore fuel s.mvarId)
        return (← keepUnassigned rem)
      -- `And A B`: unpack both conjuncts and inspect each
      if fn.isConstOf ``And then
        let subgoals ← goal.cases hFVar
        let mut rem : List MVarId := []
        for s in subgoals do
          if s.fields.size == 2 then
            let f1 := s.fields[0]!
            let f2 := s.fields[1]!
            let subRem ← s.mvarId.withContext do
              let closedByCases ← if f1.isFVar then
                let saved ← saveState
                let (_, gRev) ← s.mvarId.revert #[f1.fvarId!]
                let gAfter ← evalTacticAt
                  (← `(tactic| (intro hImp; try (first | cases hImp | (simp at hImp)))))
                  gRev
                if gAfter.isEmpty then
                  pure true
                else
                  restoreState saved
                  pure false
              else pure false
              if closedByCases then
                pure []
              else if f2.isFVar then
                splitDemonicHypAndExec fuel respFVar f2.fvarId! s.mvarId
              else
                obendWpCore fuel s.mvarId
            rem := rem ++ subRem
          else
            rem := rem ++ (← obendWpCore fuel s.mvarId)
        return (← keepUnassigned rem)
      -- `Eq lhs rhs`: substitute `resp` or eliminate impossible constructor equality!
      if fn.isConstOf ``Eq then
        let (_, gRev) ← goal.revert #[hFVar]
        let afterCases ← evalTacticAt
          (← `(tactic| (
            intro hEq
            try subst hEq
            try (first | cases hEq | (simp at hEq))
          )))
          gRev
        let mut rem : List MVarId := []
        for g in afterCases do
          let gNorm ← evalTacticAt
            (← `(tactic| dsimp only [
              plugContext, plug, List.foldl, SourceFrame.plug, writtenResponse, refusedResponse,
              Obend.Core.Data.Data.term
            ]))
            g
          for gn in gNorm do
            rem := rem ++ (← obendWpCore fuel gn)
        return (← keepUnassigned rem)
      let gNorm ← evalTacticAt
        (← `(tactic| dsimp only [
          plugContext, plug, List.foldl, SourceFrame.plug, writtenResponse, refusedResponse,
          Obend.Core.Data.Data.term
        ]))
        goal
      let mut rem : List MVarId := []
      for gn in gNorm do
        rem := rem ++ (← obendWpCore fuel gn)
      return (← keepUnassigned rem)

  /-- Recursive symbolic execution engine for `SafeWP` / `SafeWPGen` and `HoareSep`. -/
  meta partial def obendWpCore (fuel : Nat) (goal : MVarId) : TacticM (List MVarId) :=
    goal.withContext do
      if ← goal.isAssigned then return []
      match fuel with
      | 0 => return [goal]
      | fuel' + 1 =>
        let tgt := stripMData (← instantiateMVars (← goal.getType))
        let fn := stripMData tgt.getAppFn
        let args := tgt.getAppArgs

        -- Branch A: Separation Hoare Triple `HoareSep P op Q`
        if fn.isConstOf ``Obend.Logic.HoareSep && args.size == 5 then
          let opExpr := args[3]!
          if let some hLocal ← synthIsLocalOp? opExpr then
            if let some (hSub, sideGoals) ← findHoareSepSubSpec? opExpr then
              let subgoals ← goal.apply (← mkConstWithFreshMVarLevels ``Obend.Logic.hoare_sep_conseq_frame)
              match subgoals with
              | gLoc :: gSub :: gPre :: gPost :: rest =>
                let _ ← isDefEq (← gLoc.getType) (← inferType hLocal)
                gLoc.assign hLocal
                let _ ← isDefEq (← gSub.getType) (← inferType hSub)
                gSub.assign hSub
                let rPre ← sepCancelGoal gPre
                let (_, gPostBody) ← gPost.intro1P
                let rPost ← sepCancelGoal gPostBody
                let mut rSide : List MVarId := []
                for sg in sideGoals do
                  if !(← sg.isAssigned) then
                    rSide := rSide ++ (← dischargeWpSideGoal sg)
                return (← keepUnassigned (rPre ++ rPost ++ rSide ++ rest))
              | _ => return subgoals
          return [goal]

        -- Branch B: Multi-turn `SafeWP` or `SafeWPGen`
        let wpParts? : Option (Expr × Expr × Expr × Expr) ← do
          if fn.isConstOf ``Obend.Logic.SafeWP && args.size == 3 then
            let ep ← mkAppM ``Obend.Logic.ExpectedPlan #[args[0]!]
            pure (some (args[0]!, ep, args[1]!, args[2]!))
          else if fn.isConstOf ``Obend.Logic.SafeWPGen && args.size == 4 then
            pure (some (args[0]!, args[1]!, args[2]!, args[3]!))
          else
            pure none

        let some (protoExpr, epExpr, tRaw, postExpr) := wpParts?
          | return (← dischargeWpSideGoal goal)
        let tExpr := stripMData (← instantiateMVars tRaw)

        -- 1. Direct local `SafeWP` hypothesis match
        if let some hHyp ← findMatchingSafeWPHyp? protoExpr epExpr tExpr then
          let subgoals ← goal.apply (← mkConstWithFreshMVarLevels ``Obend.Logic.wp_monoGen)
          match subgoals with
          | gHyp :: gImp :: rest =>
            let _ ← isDefEq (← gHyp.getType) (← inferType hHyp)
            gHyp.assign hHyp
            let (_, gImpBody) ← gImp.introNP 3
            let rImp ← dischargeWpSideGoal gImpBody
            return (← keepUnassigned (rImp ++ rest))
          | _ => return subgoals

        -- 2. Modular `seqNat e body` when `e` matches a local `SafeWP` hypothesis
        let tFn := stripMData tExpr.getAppFn
        let tArgs := tExpr.getAppArgs
        if tFn.isConstOf ``Obend.Logic.seqNat && tArgs.size == 2 then
          if let some hSub ← findMatchingSafeWPHyp? protoExpr epExpr tArgs[0]! then
            let subgoals ← goal.apply (← mkConstWithFreshMVarLevels ``Obend.Logic.wp_seqNat)
            match subgoals with
            | gSub :: gCont :: rest =>
              let ok ← isDefEq (← gSub.getType) (← inferType hSub)
              if ok then
                gSub.assign hSub
                let (_, gContBody) ← gCont.introNP 2
                let gSimp ← withOptions (fun o => linter.unusedSimpArgs.set o false) <|
                  evalTacticAt
                    (← `(tactic| simp (config := { failIfUnchanged := false }) [
                      instantiate, Term.substitute, liftSubstitution, Term.rename, liftRename
                    ]))
                    gContBody
                let mut rem : List MVarId := []
                for gs in gSimp do
                  rem := rem ++ (← obendWpCore fuel' gs)
                return (← keepUnassigned (rem ++ rest))
            | _ => pure ()

        -- Unfold exposed `Core4` `Term` helper macros inside `tExpr` before stepping/substitution!
        let tUnf ← unfoldTermAbbrevs tExpr
        let (goal, tExpr) ← if tUnf == tExpr then
          pure (goal, tExpr)
        else
          let newTgt ← if fn.isConstOf ``Obend.Logic.SafeWP then
            mkAppM ``Obend.Logic.SafeWP #[protoExpr, tUnf, postExpr]
          else
            mkAppM ``Obend.Logic.SafeWPGen #[protoExpr, epExpr, tUnf, postExpr]
          let g' ← goal.replaceTargetDefEq newTgt
          pure (g', tUnf)
        let tFn := stripMData tExpr.getAppFn
        let tArgs := tExpr.getAppArgs

        -- 3. Syntactic `Core4` value -> `SafeWPGen.val`
        if let some valPrf ← proveSyntacticValue? tExpr then
          let appPrf ← mkAppOptM ``Obend.Logic.SafeWPGen.val
            #[protoExpr, epExpr, tExpr, postExpr, valPrf]
          let subgoals ← goal.apply appPrf
          let mut rem : List MVarId := []
          for sg in subgoals do
            rem := rem ++ (← dischargeWpSideGoal sg)
          return (← keepUnassigned rem)

        -- 4. Symbolic `ifBool (.boolean condBool) wt wf` split when `condBool` is `decide P` or fvar!
        if tFn.isConstOf ``Term.ifBool && tArgs.size == 3 then
          let condExpr := stripMData tArgs[0]!
          if (stripMData condExpr.getAppFn).isConstOf ``Term.boolean && condExpr.getAppArgs.size == 1 then
            let bArg := stripMData condExpr.getAppArgs[0]!
            if !bArg.isConstOf ``Bool.true && !bArg.isConstOf ``Bool.false then
              if (stripMData bArg.getAppFn).isConstOf ``Decidable.decide && bArg.getAppArgs.size >= 1 then
                let propExpr := bArg.getAppArgs[0]!
                let propStx ← PrettyPrinter.delab propExpr
                let splitGoals ← withOptions (fun o => linter.unusedSimpArgs.set o false) <|
                  evalTacticAt
                    (← `(tactic| (
                      by_cases hCond : $propStx <;>
                      simp (config := { failIfUnchanged := false }) only [hCond, decide_true, decide_false]
                    )))
                    goal
                if splitGoals.length == 2 then
                  let mut rem : List MVarId := []
                  for sg in splitGoals do
                    rem := rem ++ (← obendWpCore fuel' sg)
                  return (← keepUnassigned rem)
              if bArg.isFVar then
                let subgoals ← goal.cases bArg.fvarId!
                let mut rem : List MVarId := []
                for s in subgoals do
                  rem := rem ++ (← obendWpCore fuel' s.mvarId)
                return (← keepUnassigned rem)

        -- 5. Symbolic `ifZero (.nat n) z s` split when `n` is a free `Nat` variable
        if tFn.isConstOf ``Term.ifZero && tArgs.size == 3 then
          let vExpr := stripMData tArgs[0]!
          if (stripMData vExpr.getAppFn).isConstOf ``Term.nat && vExpr.getAppArgs.size == 1 then
            let nArg := stripMData vExpr.getAppArgs[0]!
            if nArg.isFVar then
              let subgoals ← goal.cases nArg.fvarId!
              let mut rem : List MVarId := []
              for s in subgoals do
                rem := rem ++ (← obendWpCore fuel' s.mvarId)
              return (← keepUnassigned rem)

        -- 6. Check `yields? tExpr` in `MetaM` (`whnf`): emit `wp_perform_of_yields?` with `rfl`!
        let yieldsCall ← mkAppM ``Obend.Logic.yields? #[tExpr]
        let yieldsWhnf ← whnf yieldsCall
        if (stripMData yieldsWhnf.getAppFn).isConstOf ``Option.some && yieldsWhnf.getAppArgs.size == 2 then
          let pairWhnf ← whnf yieldsWhnf.getAppArgs[1]!
          if (stripMData pairWhnf.getAppFn).isConstOf ``Prod.mk && pairWhnf.getAppArgs.size == 4 then
            let planExpr := pairWhnf.getAppArgs[2]!
            let ctxExpr := pairWhnf.getAppArgs[3]!
            let eqRefl ← mkEqRefl (← mkAppM ``Option.some #[pairWhnf])
            let stepThm ← mkAppOptM ``Obend.Logic.wp_perform_of_yields?
              #[protoExpr, epExpr, tExpr, planExpr, ctxExpr, postExpr, eqRefl]
            let subgoals ← goal.apply stepThm
            match subgoals with
            | [gExp, gCont] =>
              let rExp ← dischargeWpSideGoal gExp
              let (fvars, gContBody) ← gCont.introNP 2
              if fvars.size == 2 then
                let rCont ← splitDemonicHypAndExec fuel' fvars[0]! fvars[1]! gContBody
                return (← keepUnassigned (rExp ++ rCont))
              else
                return (← keepUnassigned (rExp ++ [gContBody]))
            | _ => return subgoals

        -- 7. Check deterministic `Obend.Law.step? tExpr` in `MetaM` (`whnf`): emit `wp_step_of_step?`!
        let stepCall ← mkAppM ``Obend.Law.step? #[tExpr]
        let stepWhnf ← whnf stepCall
        if (stripMData stepWhnf.getAppFn).isConstOf ``Option.some && stepWhnf.getAppArgs.size == 2 then
          let nextTerm := stepWhnf.getAppArgs[1]!
          let eqRefl ← mkEqRefl (← mkAppM ``Option.some #[nextTerm])
          let stepThm ← mkAppOptM ``Obend.Logic.wp_step_of_step?
            #[protoExpr, epExpr, tExpr, nextTerm, postExpr, eqRefl]
          let subgoals ← goal.apply stepThm
          match subgoals with
          | [gNext] =>
            let normGoals ← withOptions (fun o => linter.unusedSimpArgs.set o false) <|
              evalTacticAt
                (← `(tactic| simp (config := { failIfUnchanged := false }) [
                  instantiate, Term.substitute, liftSubstitution,
                  Term.rename, liftRename, List.map
                ]))
                gNext
            let mut rem : List MVarId := []
            for gn in normGoals do
              rem := rem ++ (← obendWpCore fuel' gn)
            return (← keepUnassigned rem)
          | _ => return subgoals

        return [goal]
end

/-- **`by obend_wp`**: `TacticM` symbolic executor for `SafeWP` / `SafeWPGen` and `HoareSep`. -/
elab "obend_wp" : tactic => do
  let goal ← getMainGoal
  let rem ← obendWpCore 96 goal
  replaceMainGoal rem

/-! ## 4. `by gpaco_step` — `TacticM` Coinduction & Guarded Hypothesis Router for `GPaco` -/

/-- Recursively route a relational goal `(A ⊔ B) x y`, `gupaco F r g x y`, `gpaco F r g x y`, or
    `upaco F r x y` to a matching hypothesis in `LocalContext` (or ground `Eq`/`And` seed leaf)
    without unfolding `F`. -/
meta partial def tryRouteRelHyp (goal : MVarId) : MetaM Bool :=
  goal.withContext do
    if ← goal.isAssigned then return true
    let tgt := (stripMData (← instantiateMVars (← goal.getType))).headBeta
    -- 1. Direct assumption match
    for ldecl in ← getLCtx do
      if ldecl.isImplementationDetail then continue
      let ok ← withoutModifyingState (isDefEq tgt ldecl.type)
      if ok then
        let _ ← isDefEq tgt ldecl.type
        goal.assign ldecl.toExpr
        return true
    let fn := stripMData tgt.getAppFn
    let args := tgt.getAppArgs
    -- 1b. Ground `Eq lhs rhs` seed leaf (`rfl`)
    if fn.isConstOf ``Eq && args.size == 3 then
      let ok ← withoutModifyingState (isDefEq args[1]! args[2]!)
      if ok then
        let _ ← isDefEq args[1]! args[2]!
        goal.assign (← mkEqRefl args[1]!)
        return true
    -- 1c. Ground `And A B` seed leaf (`⟨..., ...⟩`)
    if fn.isConstOf ``And && args.size == 2 then
      let saved ← saveState
      let subAnd ← try goal.apply (mkConst ``And.intro) catch _ => pure []
      if let [gA, gB] := subAnd then
        if ← tryRouteRelHyp gA then
          if ← tryRouteRelHyp gB then
            return true
      restoreState saved
    -- 2. `Rel.union A B x y` / `Or`
    if (fn.isConstOf ``Obend.Paco.Rel.union && args.size == 5) ||
       (fn.isConstOf ``Or && args.size == 2) then
      let saved ← saveState
      let subL ← try goal.apply (mkConst ``Or.inl) catch _ => pure []
      if let [gL] := subL then
        if ← tryRouteRelHyp gL then return true
      restoreState saved
      let subR ← try goal.apply (mkConst ``Or.inr) catch _ => pure []
      if let [gR] := subR then
        if ← tryRouteRelHyp gR then return true
      restoreState saved
    -- 3. `gupaco F r g x y` (= `(gpaco F r g ⊔ g) x y`)
    if fn.isConstOf ``Obend.Paco.gupaco && args.size == 6 then
      let saved ← saveState
      let subR ← try goal.apply (mkConst ``Or.inr) catch _ => pure []
      if let [gR] := subR then
        if ← tryRouteRelHyp gR then return true
      restoreState saved
      let subL ← try goal.apply (mkConst ``Or.inl) catch _ => pure []
      if let [gL] := subL then
        if ← tryRouteRelHyp gL then return true
      restoreState saved
    -- 4. `gpaco F r g x y` (= `(paco F (r ⊔ g) ⊔ r) x y`)
    if fn.isConstOf ``Obend.Paco.gpaco && args.size == 6 then
      let saved ← saveState
      let subR ← try goal.apply (mkConst ``Or.inr) catch _ => pure []
      if let [gR] := subR then
        if ← tryRouteRelHyp gR then return true
      restoreState saved
      let subL ← try goal.apply (mkConst ``Or.inl) catch _ => pure []
      if let [gL] := subL then
        if ← tryRouteRelHyp gL then return true
      restoreState saved
    -- 5. `upaco F r x y` (= `(paco F r ⊔ r) x y`)
    if fn.isConstOf ``Obend.Paco.upaco && args.size == 5 then
      let saved ← saveState
      let subR ← try goal.apply (mkConst ``Or.inr) catch _ => pure []
      if let [gR] := subR then
        if ← tryRouteRelHyp gR then return true
      restoreState saved
      let subL ← try goal.apply (mkConst ``Or.inl) catch _ => pure []
      if let [gL] := subL then
        if ← tryRouteRelHyp gL then return true
      restoreState saved
    return false

/-- Simplify an unfolded `F R x y` goal, splitting conjunctions whose pure observation side closes
    by `rfl` / `decide` and routing coinductive hypotheses automatically! -/
meta partial def simplifyPostUnfold (goal : MVarId) : TacticM (List MVarId) :=
  goal.withContext do
    if ← goal.isAssigned then return []
    if ← tryRouteRelHyp goal then return []
    let tgtWhnf ← whnf (stripMData (← instantiateMVars (← goal.getType)))
    let goal ← goal.replaceTargetDefEq tgtWhnf
    goal.withContext do
      if ← tryRouteRelHyp goal then return []
      if (stripMData tgtWhnf.getAppFn).isConstOf ``And && tgtWhnf.getAppArgs.size == 2 then
        let saved ← saveState
        let sub ← goal.apply (mkConst ``And.intro)
        if let [g1, g2] := sub then
          let r1 ← evalTacticAt (← `(tactic| first | rfl | assumption | trivial)) g1
          if r1.isEmpty then
            if ← tryRouteRelHyp g2 then
              return []
            return [g2]
          else
            restoreState saved
      return [goal]

/-- Core `TacticM` implementation of `by gpaco_step` and `by gpaco_step using seed`. -/
meta def gpacoStepCore (seedStx? : Option (TSyntax `term)) (goal : MVarId) : TacticM (List MVarId) :=
  goal.withContext do
    if ← goal.isAssigned then return []
    let mut curGoal := goal
    let tgt0 := stripMData (← instantiateMVars (← curGoal.getType))
    -- 1. Normalize `F.gfp x y` -> `gpaco F ⊥ ⊥ x y`
    if (stripMData tgt0.getAppFn).isConstOf ``Obend.Paco.MonoRel.gfp && tgt0.getAppArgs.size == 4 then
      let sub ← curGoal.apply (← mkConstWithFreshMVarLevels ``gfp_to_gpaco)
      if let [gGpaco] := sub then
        curGoal := gGpaco
      else
        return sub

    curGoal.withContext do
      let tgt := stripMData (← instantiateMVars (← curGoal.getType))
      let fn := stripMData tgt.getAppFn
      let args := tgt.getAppArgs

      -- 2. `using seed` coinduction initiation (`gpaco_coind` or `gpaco_clo_cofix`)
      if let some seedStx := seedStx? then
        if fn.isConstOf ``Obend.Paco.gpaco && args.size == 6 then
          let relTy ← inferType args[2]!
          let seedExpr ← elabTermEnsuringType seedStx (some relTy)
          let coindThm ← mkAppOptM ``Obend.Paco.gpaco_coind
            #[args[0]!, args[1]!, seedExpr, args[2]!, args[3]!, args[4]!, args[5]!]
          let subgoals ← curGoal.apply coindThm
          match subgoals with
          | [gPost, gInit] =>
            let rInit ← if ← tryRouteRelHyp gInit then pure [] else
              evalTacticAt
                (← `(tactic| (
                  try dsimp
                  try exact ⟨rfl, rfl⟩
                  try rfl
                  try assumption
                  try trivial
                )))
                gInit
            let (fvars, gPostBody) ← gPost.introNP 3
            -- Try destructing simple `x = c ∧ y = d` or `Or` seeds and stepping automatically!
            let postGoals ← gPostBody.withContext do
              if fvars.size == 3 then
                let (_, gRev) ← gPostBody.revert #[fvars[2]!]
                evalTacticAt
                  (← `(tactic| (
                    intro hSeed
                    try rcases hSeed with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩
                    all_goals try subst_vars
                  )))
                  gRev
              else
                pure [gPostBody]
            let mut rem : List MVarId := []
            for pg in postGoals do
              -- Try `Or.inl` (productive `F` step) and simplify
              let saved ← saveState
              let subInl ← try pg.apply (mkConst ``Or.inl) catch _ => pure [pg]
              if let [gF] := subInl then
                let rF ← simplifyPostUnfold gF
                if rF.isEmpty then
                  pure ()
                else
                  rem := rem ++ rF
              else
                restoreState saved
                rem := rem ++ [pg]
            return (← keepUnassigned (rem ++ rInit))
          | _ => return subgoals

        if fn.isConstOf ``Obend.Paco.gpaco_clo && args.size == 7 then
          let relTy ← inferType args[3]!
          let seedExpr ← elabTermEnsuringType seedStx (some relTy)
          let cofixThm ← mkAppOptM ``Obend.Paco.gpaco_clo_cofix
            #[args[0]!, args[1]!, args[2]!, args[3]!, args[4]!, seedExpr, args[5]!, args[6]!]
          let subgoals ← curGoal.apply cofixThm
          match subgoals with
          | [gPost, gInit] =>
            let rInit ← evalTacticAt
              (← `(tactic| (
                try dsimp
                try exact ⟨rfl, rfl⟩
                try rfl
                try assumption
                try trivial
              )))
              gInit
            let (_, gPostBody) ← gPost.introNP 3
            return (← keepUnassigned ([gPostBody] ++ rInit))
          | _ => return subgoals

      -- 3. Try direct relational routing (`gupaco`, `upaco`, `⊔`, base `r`)
      if ← tryRouteRelHyp curGoal then
        return []

      -- 4. Unfold one productive step of `gpaco`, `gupaco`, or `paco`
      if fn.isConstOf ``Obend.Paco.gpaco && args.size == 6 then
        let sub ← curGoal.apply (← mkConstWithFreshMVarLevels ``gpaco_fold_at)
        if let [gF] := sub then
          return (← simplifyPostUnfold gF)
        return sub

      if fn.isConstOf ``Obend.Paco.gupaco && args.size == 6 then
        -- Step from `gupaco F r g` into `gpaco F r g` (`Or.inl`), then unfold `gpaco_fold_at`
        let sub1 ← curGoal.apply (mkConst ``Or.inl)
        if let [gGpaco] := sub1 then
          let sub2 ← gGpaco.apply (← mkConstWithFreshMVarLevels ``gpaco_fold_at)
          if let [gF] := sub2 then
            return (← simplifyPostUnfold gF)
        return sub1

      if fn.isConstOf ``Obend.Paco.paco && args.size == 5 then
        let sub ← curGoal.apply (← mkConstWithFreshMVarLevels ``paco_fold_at)
        if let [gF] := sub then
          return (← simplifyPostUnfold gF)
        return sub

      return [curGoal]

/-- **`by gpaco_step` / `by gpaco_step using seedRel`**: `TacticM` coinduction and guard-release
    step automation over `Obend.Paco.GPaco`. -/
elab "gpaco_step" : tactic => do
  let goal ← getMainGoal
  let rem ← gpacoStepCore none goal
  replaceMainGoal rem

elab "gpaco_step" " using " seed:term : tactic => do
  let goal ← getMainGoal
  let rem ← gpacoStepCore (some seed) goal
  replaceMainGoal rem

end Obend.Tactic.ProgramLogic
end
