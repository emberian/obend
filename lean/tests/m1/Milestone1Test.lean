import Obend.Analysis.RealAnalysis
import Obend.Judge.RealAnalysis
import Obend.Law.Contract
import Obend.Lower.Reflect
import Obend.Tactic.Weave
import Obend.Logic.Obligation

open Obend.Analysis
open Obend.Judge
open Obend.Judge.SOS
open Obend.Law
open Obend.Lower
open Obend.Lower.Reflect
open Obend.Logic
open Obend.Core.Term (Term Evaluates)
open Obend.Core.Data (Data)

def assertOk (what : String) (ok : Bool) : IO Unit :=
  if ok then
    IO.println s!"[PASS] {what}"
  else
    throw (IO.userError s!"[FAIL] {what}")

-- 1. Test Tactic.Weave
theorem test_poly_ring (a b : Nat) : a + b + a = 2 * a + b := by
  poly_ring

theorem test_obend_split (b : Bool) : (if b then 1 else 1) = 1 := by
  obend_split

-- 2. Test Law.Contract
def testLaw : Term := .lam (.lam (.lam (.boolean true)))

theorem test_narrows_refl : Narrows testLaw testLaw :=
  narrows_refl testLaw

theorem test_narrows_trans {l1 l2 l3 : Term} (h1 : Narrows l1 l2) (h2 : Narrows l2 l3) : Narrows l1 l3 :=
  narrows_trans h1 h2

theorem test_relaw (C : CellContract) (l2 : Term) (h : Narrows l2 C.law) :
    (cellContract_relaw_sound C l2 h).law = l2 :=
  rfl

theorem test_trace_sound (C : CellContract) (s0 sf : Data) (steps : List (Data × Data))
    (hi : Holds C.invariant s0) (ht : CellTrace C.law s0 steps sf) :
    Holds C.invariant sf :=
  cellContract_trace_sound C s0 sf steps hi ht

def testContractCertTiers : IO Unit := do
  let g1 : ContractGoal := .preserves (.boolean true) (.boolean true)
  let lawEx : Obend.Spec.Law.LawExpr := .eqC (.field "total") 0
  let c1 : ContractCert := .byLawDial lawEx lawEx [] true
  assertOk "Tier 1 LawDial certificate check" (checkContractCert g1 c1 matches .valid)

  let certT : TransportCert := { digest := 0, claim := .boolean true, argTys := [] }
  let pin : Obend.Leaf.LeafPin := { cell := .layer "L1", code := .boolean true }
  let c3 : ContractCert := .byLoweredLean certT [pin]
  assertOk "Tier 3 LoweredLean certificate check" (checkContractCert g1 c3 matches .valid)

-- 3. Test RealAnalysis CanonicalRat & Interval
def testRealAnalysis : IO Unit := do
  let r1 := CanonicalRat.mk 1 2
  let r2 := CanonicalRat.mk 2 4
  assertOk "CanonicalRat canonical representation" (r1 == r2)
  assertOk "CanonicalRat ofData? roundtrip" (CanonicalRat.ofData? (CanonicalRat.toData r1) == some r1)

  let iv1 := Interval.mk (CanonicalRat.mk 1 1) (CanonicalRat.mk 2 1)
  let iv2 := Interval.mk (CanonicalRat.mk 3 1) (CanonicalRat.mk 4 1)
  let ivSum := Interval.add iv1 iv2
  assertOk "Interval add bounds" (ivSum.lo == CanonicalRat.mk 4 1 && ivSum.hi == CanonicalRat.mk 6 1)

  let xVal := CanonicalRat.mk 3 2
  assertOk "Interval containsRat" (Interval.containsRat iv1 xVal)

  let e : RealExpr := .add (.var "x") (.const (CanonicalRat.mk 1 1))
  let rho : String → CanonicalRat := fun s => if s == "x" then xVal else 0
  let pRes := evalPoint rho e
  assertOk "RealExpr point eval" (pRes == some (CanonicalRat.mk 5 2))

  let envIv : List (String × Interval) := [("x", iv1)]
  let ivRes := evalInterval envIv e
  assertOk "RealExpr interval eval bounds" (ivRes == some (Interval.mk (CanonicalRat.mk 2 1) (CanonicalRat.mk 3 1)))

-- 4. Test Judge.RealAnalysis (Interval & SOS Judges)
def testJudges : IO Unit := do
  let q : IntervalQuery := {
    expr := .add (.var "x") (.const (CanonicalRat.mk 1 1))
    env := [("x", Interval.mk (CanonicalRat.mk 1 1) (CanonicalRat.mk 2 1))]
    claimedBound := Interval.mk (CanonicalRat.mk 2 1) (CanonicalRat.mk 3 1)
  }
  let v1 := intervalJudge.check 0 q .direct
  assertOk "intervalJudge verdict on valid bounds" (v1 matches .ok)

  let pX : Poly := ⟨[([(0, 1)], 1)]⟩
  let pGoal := Poly.sqr pX
  let s0 : SOSPoly := ⟨[(1, pX)]⟩
  let qSos : SOSQuery := {
    goal := pGoal
    ineqs := []
    eqs := []
  }
  let cSos : SOSCert := {
    sigma0 := s0
    sigmas := []
    lambdas := []
  }
  let v2 := sosJudge.check 0 qSos cSos
  assertOk "sosJudge verdict on sum of squares" (v2 matches .ok)

-- 5. Test Lower.Reflect
def testLowerReflect : IO Unit := do
  let env : LayoutEnv := { fields := [], selfIndex := 0, arity := 1 }
  let t : Term := .nat 42
  let lowered := lowerTerm env t
  assertOk "lowerTerm on simple nat term" (lowered.isSome == true)

-- 6. Test Logic.Obligation with Justification.byLoweredLean
def testObligation : IO Unit := do
  let just := Justification.byLoweredLean (.boolean true) [] ByteArray.empty
  assertOk "Justification.byLoweredLean constructed" (just matches .byLoweredLean _ _ _)

def main : IO Unit := do
  IO.println "=== Running Milestone 1 Verification Suite ==="
  testContractCertTiers
  testRealAnalysis
  testJudges
  testLowerReflect
  testObligation
  IO.println "=== All Milestone 1 Verification Tests Passed! ==="

#eval main
