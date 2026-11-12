module
/-
# `tests/metasystem/SkolemChaseCoreTest.lean` — Verification & `#tooth` Suite for `SkolemChaseCore`

End-to-end kernel verification, executable `#guard` fixtures, inhabitedness witnesses,
4 `#tooth` mutation kills, and compile-time axiom / `0 Classical.choice` / `0 sorryAx`
verification for `Obend.SymbolicZk.SkolemChaseCore`.
-/

public import Obend.AssertAxioms
public import Obend.Tactic.Tooth
public import Obend.SymbolicZk.SkolemChaseCore
import all Obend.AssertAxioms
import all Obend.Tactic.Tooth
import all Obend.SymbolicZk.SkolemChaseCore

public section
namespace Obend.Tests.Metasystem.SkolemChaseCoreTest

open Obend.SymbolicZk.SkolemChaseCore

set_option autoImplicit false

/-! ## §0. Whole-Tree Axiom Audit & Compile-Time `0 Classical.choice` / `0 sorryAx` Gate -/

#assert_axioms_tree

open Lean Elab Command in
run_cmd do
  let targets : List Name := [
    ``Obend.SymbolicZk.SkolemChaseCore.termEq_iff,
    ``Obend.SymbolicZk.SkolemChaseCore.stepChaseExec_eq_spec,
    ``Obend.SymbolicZk.SkolemChaseCore.runBoundedChaseExec_eq_spec,
    ``Obend.SymbolicZk.SkolemChaseCore.chase_fixpoint_models_rules,
    ``Obend.SymbolicZk.SkolemChaseCore.skolemChase_universal_homomorphism,
    ``Obend.SymbolicZk.SkolemChaseCore.weaklyAcyclic_rank_bound,
    ``Obend.SymbolicZk.SkolemChaseCore.checkRetractionCore_sound,
    ``Obend.SymbolicZk.SkolemChaseCore.checkRetractionCore_preserves_ucq
  ]
  for decl in targets do
    let axs ← liftCoreM <| collectAxioms decl
    if axs.contains ``Classical.choice then
      throwError m!"{decl} depends on forbidden Classical.choice: {axs.toList}"
    if axs.contains ``sorryAx then
      throwError m!"{decl} depends on forbidden sorryAx: {axs.toList}"


/-! ## §1. Weakly Acyclic Ontology Fixtures & Restricted Skolem Chase Execution -/

def relEmp : RelId := 1
def relManages : RelId := 2
def relDeptOf : RelId := 3
def relAuditDept : RelId := 4

def cAlice : ConstId := 1
def cBob : ConstId := 2
def cCarol : ConstId := 3
def cEngDept : ConstId := 4
def cChiefAuditor : ConstId := 5

/-- Rule 10: $\forall x.\, \text{Emp}(x) \to \exists m, d.\, \text{Manages}(m, x) \wedge \text{DeptOf}(x, d)$. -/
def ruleEmpDept : TgdRule where
  id := 10
  frontierVars := [0]
  existVars := [1, 2]
  body := [{ rel := relEmp, args := [.var 0] }]
  head := [
    { rel := relManages, args := [.var 1, .var 0] },
    { rel := relDeptOf, args := [.var 0, .var 2] }
  ]

/-- Rule 20: $\forall x, d.\, \text{DeptOf}(x, d) \to \exists a.\, \text{AuditDept}(d, a)$. -/
def ruleDeptAudit : TgdRule where
  id := 20
  frontierVars := [0, 1]
  existVars := [2]
  body := [{ rel := relDeptOf, args := [.var 0, .var 1] }]
  head := [{ rel := relAuditDept, args := [.var 1, .var 2] }]

def sampleOntology : List TgdRule := [ruleEmpDept, ruleDeptAudit]

/-- Non-weakly-acyclic cycle $\forall x, y.\, \text{Manages}(x, y) \to \exists z.\, \text{Manages}(y, z)$. -/
def cyclicChainRule : TgdRule where
  id := 99
  frontierVars := [0, 1]
  existVars := [2]
  body := [{ rel := relManages, args := [.var 0, .var 1] }]
  head := [{ rel := relManages, args := [.var 1, .var 2] }]

def sampleRank : PosRankMap := [
  ({ rel := relEmp, pos := 0 }, 0),
  ({ rel := relManages, pos := 0 }, 1),
  ({ rel := relManages, pos := 1 }, 0),
  ({ rel := relDeptOf, pos := 0 }, 0),
  ({ rel := relDeptOf, pos := 1 }, 1),
  ({ rel := relAuditDept, pos := 0 }, 1),
  ({ rel := relAuditDept, pos := 1 }, 2)
]

#guard WfRuleSet sampleOntology == true
#guard WfRuleSet [ruleEmpDept, { ruleDeptAudit with id := 10 }] == false
#guard maxRankOf sampleRank == 2
#guard checkWeaklyAcyclic sampleRank sampleOntology == true
#guard checkWeaklyAcyclic sampleRank [cyclicChainRule] == false

/-- `Bob` already has `(Carol, EngDept)`, so `ruleEmpDept` fires ONLY on `Alice` (`!isSatisfied`). -/
def sampleBaseI : FactSet := [
  { rel := relEmp, args := [.const cAlice] },
  { rel := relEmp, args := [.const cBob] },
  { rel := relManages, args := [.const cCarol, .const cBob] },
  { rel := relDeptOf, args := [.const cBob, .const cEngDept] }
]

#guard IsBaseFactSet sampleBaseI == true

def saturatedSpec : FactSet := runBoundedChase sampleOntology 5 sampleBaseI
def saturatedExec : Array (Atom Term) :=
  runBoundedChaseExec sampleOntology.toArray 5 sampleBaseI.toArray

#guard saturatedExec.toList == saturatedSpec
#guard allRulesSatisfied sampleOntology saturatedSpec == true
#guard allRulesSatisfiedExec sampleOntology.toArray saturatedExec == true
#guard saturatedSpec.length == 8
#guard runBoundedChase sampleOntology 50 sampleBaseI == saturatedSpec

def skAliceDept : Term := .skolem 10 2 [.const cAlice]
def skAliceAuditor : Term := .skolem 20 2 [.const cAlice, skAliceDept]

#guard skolemDepth skAliceAuditor == 2
#guard saturatedSpec.contains { rel := relAuditDept, args := [skAliceDept, skAliceAuditor] } == true
#guard saturatedSpec.contains { rel := relDeptOf, args := [.const cBob, .skolem 10 2 [.const cBob]] } == false


/-! ## §2. Concrete Homomorphism Target Model `N` & Core Retraction / BCQ Preservation -/

def targetN : List (Atom ConstId) := [
  { rel := relEmp, args := [cAlice] },
  { rel := relEmp, args := [cBob] },
  { rel := relManages, args := [cCarol, cBob] },
  { rel := relDeptOf, args := [cBob, cEngDept] },
  { rel := relManages, args := [cCarol, cAlice] },
  { rel := relDeptOf, args := [cAlice, cEngDept] },
  { rel := relAuditDept, args := [cEngDept, cChiefAuditor] }
]

def targetChooseWitness (rId : RuleId) (_frontier : List ConstId) (existVar : VarId) : ConstId :=
  if rId == 10 then (if existVar == 1 then cCarol else cEngDept) else cChiefAuditor

#guard (saturatedSpec.all fun a =>
  targetN.contains (mapAtom (evalSkolemHom id targetChooseWitness) a)) == true

def skRedundantMgr : Term := .skolem 10 1 [.const cBob]
def skRedundantDept : Term := .skolem 10 2 [.const cBob]

def nonMinimalM : FactSet := [
  { rel := relEmp, args := [.const cBob] },
  { rel := relManages, args := [.const cCarol, .const cBob] },
  { rel := relDeptOf, args := [.const cBob, .const cEngDept] },
  { rel := relManages, args := [skRedundantMgr, .const cBob] },
  { rel := relDeptOf, args := [.const cBob, skRedundantDept] }
]

def retractedCoreC : FactSet := [
  { rel := relEmp, args := [.const cBob] },
  { rel := relManages, args := [.const cCarol, .const cBob] },
  { rel := relDeptOf, args := [.const cBob, .const cEngDept] }
]

def validRetractionCert : RetractionCert where
  termMap := [(skRedundantMgr, .const cCarol), (skRedundantDept, .const cEngDept)]

def invalidConstMoveCert : RetractionCert where
  termMap := [(.const cBob, .const cAlice)]

def incompleteCoreC : FactSet := [
  { rel := relEmp, args := [.const cBob] },
  { rel := relManages, args := [.const cCarol, .const cBob] }
]

#guard checkRetractionCore validRetractionCert nonMinimalM retractedCoreC == true
#guard checkRetractionCore invalidConstMoveCert nonMinimalM retractedCoreC == false
#guard checkRetractionCore validRetractionCert nonMinimalM incompleteCoreC == false

def bcqBobManagedInDept : ConjunctiveQuery where
  atoms := [
    { rel := relEmp, args := [.const cBob] },
    { rel := relManages, args := [.var 0, .const cBob] },
    { rel := relDeptOf, args := [.const cBob, .var 1] }
  ]

def bcqCarolManaged : ConjunctiveQuery where
  atoms := [{ rel := relManages, args := [.var 0, .const cCarol] }]

#guard evalBCQ bcqBobManagedInDept nonMinimalM == true
#guard evalBCQ bcqBobManagedInDept retractedCoreC == true
#guard evalBCQ bcqCarolManaged nonMinimalM == false
#guard evalBCQ bcqCarolManaged retractedCoreC == false
#guard evalUCQ [bcqCarolManaged, bcqBobManagedInDept] nonMinimalM ==
       evalUCQ [bcqCarolManaged, bcqBobManagedInDept] retractedCoreC

example (q : ConjunctiveQuery) : evalBCQ q nonMinimalM = evalBCQ q retractedCoreC :=
  (checkRetractionCore_sound validRetractionCert nonMinimalM retractedCoreC (by decide)).2.2.2 q

example : ∀ a ∈ saturatedSpec, ∀ t ∈ a.args, skolemDepth t ≤ 2 :=
  weaklyAcyclic_rank_bound sampleRank sampleOntology 5 sampleBaseI (by decide) (by decide)


/-! ## §3. `#tooth` Mutation-Sensitivity Kills & Axiom Checks -/

#tooth Obend.SymbolicZk.SkolemChaseCore.chase_fixpoint_models_rules by
  mutation Obend.SymbolicZk.SkolemChaseCore.isSatisfied := fun _ _ _ _ => true

#tooth Obend.SymbolicZk.SkolemChaseCore.skolemChase_universal_homomorphism by
  mutation Obend.SymbolicZk.SkolemChaseCore.mapAtom := fun _ a => { rel := a.rel, args := [] }

#tooth Obend.SymbolicZk.SkolemChaseCore.checkRetractionCore_sound by
  mutation Obend.SymbolicZk.SkolemChaseCore.checkRetractionCore := fun _ _ _ => true

#tooth Obend.SymbolicZk.SkolemChaseCore.weaklyAcyclic_rank_bound by
  mutation Obend.SymbolicZk.SkolemChaseCore.checkWeaklyAcyclic := fun _ _ => true

#tooth Obend.SymbolicZk.SkolemChaseCore.skolem_ruleId_non_aliasing by
  mutation Obend.SymbolicZk.SkolemChaseCore.WfRuleSet := fun rules => rules.all WfRule

#print axioms Obend.SymbolicZk.SkolemChaseCore.runBoundedChaseExec_eq_spec
#print axioms Obend.SymbolicZk.SkolemChaseCore.chase_fixpoint_models_rules
#print axioms Obend.SymbolicZk.SkolemChaseCore.skolemChase_universal_homomorphism
#print axioms Obend.SymbolicZk.SkolemChaseCore.weaklyAcyclic_rank_bound
#print axioms Obend.SymbolicZk.SkolemChaseCore.checkRetractionCore_sound

end Obend.Tests.Metasystem.SkolemChaseCoreTest
end
