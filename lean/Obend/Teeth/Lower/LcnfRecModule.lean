module
/-
# `Obend/Teeth/Lower/LcnfRecModule.lean` — the closed recursive LCNF module run (tier 2)

Moved from `Obend/Lower/LCNF.lean` (Wave C2): a closed run of one recursive module that needs
`maxHeartbeats 800000`, outside the tier-1 heartbeat baseline (`Obend/Census.lean`). The universal
contract stays in tier 1 (`lcnf_jp_lexical_capture_sound`). Only `Obend.Lower.LCNF` is imported with
its bodies, as in its home module, so `LExpr.inst` and friends stay sealed for `simp`.
-/
public import Obend.Lower.LCNF
import all Obend.Lower.LCNF

namespace Obend.Lower.LCNF
open Obend.Core
open Obend.Core.Term
open Obend.Core.Ty (Ty)
open Obend.Lower
set_option autoImplicit false


set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem sampleLcnfRecModule_runs :
    SSteps (compileLcnfModuleToLExpr sampleLcnfRecModule) (.lit 42) := by
  simp only [compileLcnfModuleToLExpr, sampleLcnfRecModule,
    compileLcnfModuleToLExpr.bindDecls, lcnfFunDeclToLExpr, sampleLcnfRecDecl,
    compileLcnfToLExpr, codeUsesState, letValueUsesState, compileLcnfWithCtx,
    lcnfLetValueToLExprCtx, lcnfArgToLExprCtx, LcnfLowerCtx.pushVar,
    LcnfLowerCtx.lookupVar, wrapMinorBvars, List.map_cons, List.map_nil,
    List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
    Bool.false_or, Bool.or_false, Bool.false_eq_true, ite_false, Nat.add_zero]
  repeat
    first
    | exact .refl _
    | (refine .next (.zeta _ _ _) ?_)
    | (refine .next (.beta _ _ _) ?_)
    | (refine .next (.appFun _ (.unfold _ _ _)) ?_)
    | (refine .next (.boolRecTrue _ _ _) ?_)
    | (refine .next (.boolRecFalse _ _ _) ?_)
    | (refine .next (.boolRecMajor _ _ _ (.binLit _ _ _)) ?_)
    | (refine .next (.boolRecMajor _ _ _ (.binLeft _ _ (.binLit _ _ _))) ?_)
    | (refine .next (.boolRecMajor _ _ _ (.binLeft _ _ (.binLeft _ _ (.binLit _ _ _)))) ?_)
    | simp [LExpr.inst, LExpr.subst, LExpr.single, LExpr.liftSubst,
        LExpr.rename, liftRename, NatOp.eval]

/-- The same closed recursive module evaluates to 42 through the interpreter,
source reduction, and Core4. -/
theorem sampleLcnfRecModule_eval_agreed :
    evalLcnfModule 32 sampleLcnfRecModule = some (42, []) ∧
    SSteps (compileLcnfModuleToLExpr sampleLcnfRecModule) (.lit 42) ∧
    Evaluates (compileLcnfModuleToCore4 sampleLcnfRecModule) (.nat 42) := by
  refine ⟨rfl, sampleLcnfRecModule_runs, ?_⟩
  simpa [compileLcnfModuleToCore4, lowerT] using lower_sound_nat sampleLcnfRecModule_runs
end Obend.Lower.LCNF
