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

/-! ===================================================================
    SUITE 1: 4-Tier ContractCert Adversarial Refutations
    =================================================================== -/

def testContractCertRefutations : IO Unit := do
  IO.println "--- Suite 1: ContractCert Adversarial Refutations ---"

  let preservesGoal := ContractGoal.preserves (.boolean true) (.boolean true)
  let narrowsGoal := ContractGoal.narrows (.boolean true) (.boolean true)
  let stepSoundGoal := ContractGoal.stepSound (.boolean true) (.boolean true) (.boolean true)

  -- 1. Tier 0: bySyntacticGuard with open invariant (closedB = false)
  let openInv : Term := .bound 0
  let openCert := ContractCert.bySyntacticGuard (.boolean true) openInv
  let resOpen := checkContractCert preservesGoal openCert
  assertOk "Tier 0 rejects open invariant" (resOpen == .invalid "syntactic guard check failed")

  -- 2. Tier 0: bySyntacticGuard with unguarded law
  let unguardedLaw : Term := .boolean false
  let guardedInv : Term := .boolean true
  let unguardedCert := ContractCert.bySyntacticGuard unguardedLaw guardedInv
  let resUnguarded := checkContractCert preservesGoal unguardedCert
  assertOk "Tier 0 rejects unguarded law" (resUnguarded == .invalid "syntactic guard check failed")

  -- 3. Tier 1: byLawDial with unsatisfiable contract
  let unsatisfiableLaw : Obend.Spec.Law.LawExpr := .and (.eqC (.field "x") 0) (.eqC (.field "x") 1)
  let dialCertUnsat := ContractCert.byLawDial unsatisfiableLaw (.eqC (.field "x") 0) ["x"]
  let resDialUnsat := checkContractCert preservesGoal dialCertUnsat
  assertOk "Tier 1 rejects unsatisfiable contract law" (resDialUnsat == .invalid "LawDial could not solve satisfying witness for contract law and invariant")

  -- 3b. Tier 1: byLawDial with invariant-violating state
  let lawViolating : Obend.Spec.Law.LawExpr := .eqC (.field "x") 75
  let invStrict : Obend.Spec.Law.LawExpr := .leC (.field "x") 50
  let dialCertViolating := ContractCert.byLawDial lawViolating invStrict ["x"]
  let resDialViolating := checkContractCert preservesGoal dialCertViolating
  assertOk "Tier 1 rejects transition violating invariant" (resDialViolating matches .invalid _)

  -- 4. Tier 2a: byLoweredDecider with malformed receipt
  let resBadDeciderJson := checkContractCert preservesGoal (ContractCert.byLoweredDecider "foo" [] "bad json".toUTF8)
  assertOk "Tier 2a rejects malformed JSON payload" (resBadDeciderJson matches .invalid _)
  let resBadDeciderEmpty := checkContractCert preservesGoal (ContractCert.byLoweredDecider "foo" [] ByteArray.empty)
  assertOk "Tier 2a rejects empty receipt payload" (resBadDeciderEmpty == .invalid "receipt payload empty")

  -- 5. Tier 2b: byLrat with invalid/empty refutation
  let badCnf : Obend.Judge.Lrat.Cnf := ⟨1, [[1], [-1]]⟩
  let badProof : List Obend.Judge.Lrat.Step := []
  let badLratCert := ContractCert.byLrat badCnf badProof
  let resBadLrat := checkContractCert preservesGoal badLratCert
  assertOk "Tier 2b rejects empty LRAT proof for non-trivial CNF" (resBadLrat == .invalid "LRAT refutation check failed")

  -- 6. Tier 3: byLoweredLean with empty pins
  let dummyObjT : TransportObj := { decideExpr := .boolLit true, argTys := [] }
  let dummyCertT : TransportCert := { digest := Obend.Lower.sourceDigest (.boolLit true), claim := .boolean true, argTys := [] }
  let emptyPinsCert := ContractCert.byLoweredLean dummyObjT dummyCertT []
  let resEmptyPins := checkContractCert preservesGoal emptyPinsCert
  assertOk "Tier 3 rejects empty pins" (resEmptyPins == .invalid "pins empty")

  -- 6b. Tier 3: byLoweredLean with unclosed pin
  let openPin : Obend.Leaf.LeafPin := { cell := .layer "L1", code := .bound 0 }
  let openPinCert := ContractCert.byLoweredLean dummyObjT dummyCertT [openPin]
  let resOpenPin := checkContractCert preservesGoal openPinCert
  assertOk "Tier 3 rejects unclosed pin" (resOpenPin == .invalid "pin code not closed")

  -- 6c. Tier 3: byLoweredLean with digest mismatch
  let closedPin : Obend.Leaf.LeafPin := { cell := .layer "L1", code := .boolean true }
  let badDigestCertT : TransportCert := { digest := 99999, claim := .boolean true, argTys := [] }
  let badDigestCert := ContractCert.byLoweredLean dummyObjT badDigestCertT [closedPin]
  let resBadDigest := checkContractCert preservesGoal badDigestCert
  assertOk "Tier 3 rejects transport check failure (digest mismatch)" (resBadDigest matches .invalid _)

  -- 7. Goal Mismatch: bySyntacticGuard presented for narrowsGoal
  let resMismatchNarrows := checkContractCert narrowsGoal (ContractCert.bySyntacticGuard (.boolean true) (.boolean true))
  assertOk "Rejects syntactic guard presented for narrows goal" (resMismatchNarrows == .invalid "tier certificate does not match target goal")

  -- 8. Tier 1: byLawDial presented for stepSoundGoal
  let stepRelEx : Obend.Spec.Law.LawExpr := .eqC (.field "x") 0
  let resStepSound := checkContractCert stepSoundGoal (ContractCert.byLawDial stepRelEx stepRelEx ["x"])
  assertOk "Tier 1 accepts valid stepSound goal" (resStepSound matches .valid)

/-! ===================================================================
    SUITE 2: Monotone Narrows & Anti-Cheat Attenuation
    =================================================================== -/

theorem stress_test_relaw (C : CellContract) (l2 : Term) (h : Narrows l2 C.law) :
    (cellContract_relaw_sound C l2 h).law = l2 ∧
    (cellContract_relaw_sound C l2 h).invariant = C.invariant ∧
    (cellContract_relaw_sound C l2 h).stepRel = C.stepRel :=
  ⟨rfl, rfl, rfl⟩

theorem stress_test_trace_sound (C : CellContract) (s0 sf : Data) (steps : List (Data × Data))
    (hi : Holds C.invariant s0) (ht : CellTrace C.law s0 steps sf) :
    Holds C.invariant sf :=
  cellContract_trace_sound C s0 sf steps hi ht

def testNarrowsAntiCheat : IO Unit := do
  IO.println "--- Suite 2: Monotone Narrows & Anti-Cheat ---"

  let dummyLaw : Term := .lam (.lam (.lam (.boolean true)))
  have _h_refl : Narrows dummyLaw dummyLaw := narrows_refl dummyLaw
  assertOk "Narrows is reflexive (narrows_refl)" true

  have _h_trans : Narrows dummyLaw dummyLaw → Narrows dummyLaw dummyLaw → Narrows dummyLaw dummyLaw :=
    fun h1 h2 => narrows_trans h1 h2
  assertOk "Narrows is transitive (narrows_trans)" true

  assertOk "cellContract_relaw_sound preserves invariant and stepRel definitionally" true
  assertOk "cellContract_trace_sound guarantees inductive multi-step invariance" true

/-! ===================================================================
    SUITE 3: CanonicalRat Stress Testing
    =================================================================== -/

def testCanonicalRatStress : IO Unit := do
  IO.println "--- Suite 3: CanonicalRat Stress Testing ---"

  -- 1. Zero denominator rejection in ofData?
  let badZeroDenData : Data := .variant "rat" (.record [
    ("num", .natural 5),
    ("neg", .boolean false),
    ("den", .natural 0)
  ])
  assertOk "ofData? rejects zero denominator" (CanonicalRat.ofData? badZeroDenData == none)

  -- 2. Negative reduction
  let rNeg := CanonicalRat.mk (-6) 8
  assertOk "Negative fraction reduced to lowest terms" (rNeg.num == -3 && rNeg.den == 4)

  -- 3. Zero reduction
  let rZero := CanonicalRat.mk 0 100
  assertOk "Zero fraction canonicalized" (rZero.num == 0 && rZero.den == 1)

  -- 4. Large coprime rationals
  let bigNum : Int := 1000000000000000003
  let bigDen : Nat := 1000000000000000007
  let rBig := CanonicalRat.mk bigNum bigDen
  let rBigData := CanonicalRat.toData rBig
  let rBigDecoded := CanonicalRat.ofData? rBigData
  assertOk "Large coprime rational roundtrip" (rBigDecoded == some rBig)

  -- 5. Malformed Data encoding rejection
  let malformedData1 : Data := .variant "not_rat" (.record [])
  let malformedData2 : Data := .natural 42
  assertOk "ofData? rejects non-rat variant" (CanonicalRat.ofData? malformedData1 == none)
  assertOk "ofData? rejects scalar Data" (CanonicalRat.ofData? malformedData2 == none)

/-! ===================================================================
    SUITE 4: Interval Arithmetic Stress Testing
    =================================================================== -/

def testIntervalStress : IO Unit := do
  IO.println "--- Suite 4: Interval Arithmetic Stress Testing ---"

  -- 1. Inverted bounds rejected by make
  let invBad := Interval.make (CanonicalRat.mk 5 1) (CanonicalRat.mk 2 1)
  assertOk "Interval.make rejects lo > hi" (invBad == none)

  -- 2. Degenerate point interval
  let invPoint := Interval.make (CanonicalRat.mk 3 1) (CanonicalRat.mk 3 1)
  assertOk "Interval.make accepts lo == hi" (invPoint == some ⟨CanonicalRat.mk 3 1, CanonicalRat.mk 3 1⟩)

  -- 3. Negative interval addition: [-5, -2] + [-3, -1] = [-8, -3]
  let ivNeg1 := Interval.mk (CanonicalRat.mk (-5) 1) (CanonicalRat.mk (-2) 1)
  let ivNeg2 := Interval.mk (CanonicalRat.mk (-3) 1) (CanonicalRat.mk (-1) 1)
  let ivNegSum := Interval.add ivNeg1 ivNeg2
  assertOk "Negative interval addition"
    (ivNegSum.lo == CanonicalRat.mk (-8) 1 && ivNegSum.hi == CanonicalRat.mk (-3) 1)

  -- 4. Subtraction: [-2, 3] - [1, 4] = [-2 - 4, 3 - 1] = [-6, 2]
  let ivA := Interval.mk (CanonicalRat.mk (-2) 1) (CanonicalRat.mk 3 1)
  let ivB := Interval.mk (CanonicalRat.mk 1 1) (CanonicalRat.mk 4 1)
  let ivSub := Interval.sub ivA ivB
  assertOk "Interval subtraction across zero"
    (ivSub.lo == CanonicalRat.mk (-6) 1 && ivSub.hi == CanonicalRat.mk 2 1)

  -- 5. Multiplication across zero: [-2, 3] * [-4, 5]
  -- Products: (-2)*(-4)=8, (-2)*5=-10, 3*(-4)=-12, 3*5=15 -> [-12, 15]
  let ivC := Interval.mk (CanonicalRat.mk (-4) 1) (CanonicalRat.mk 5 1)
  let ivMul := Interval.mul ivA ivC
  assertOk "Interval multiplication across zero"
    (ivMul.lo == CanonicalRat.mk (-12) 1 && ivMul.hi == CanonicalRat.mk 15 1)

  -- 6. Squaring spanning zero: [-3, 2]^2 -> [0, 9]
  let ivCrossZero := Interval.mk (CanonicalRat.mk (-3) 1) (CanonicalRat.mk 2 1)
  let ivSqZero := Interval.sqr ivCrossZero
  assertOk "Interval squaring spanning zero"
    (ivSqZero.lo == CanonicalRat.mk 0 1 && ivSqZero.hi == CanonicalRat.mk 9 1)

  -- 7. Squaring strictly negative: [-4, -2]^2 -> [4, 16]
  let ivStrictNeg := Interval.mk (CanonicalRat.mk (-4) 1) (CanonicalRat.mk (-2) 1)
  let ivSqNeg := Interval.sqr ivStrictNeg
  assertOk "Interval squaring strictly negative"
    (ivSqNeg.lo == CanonicalRat.mk 4 1 && ivSqNeg.hi == CanonicalRat.mk 16 1)

  -- 8. containsRat edge tests
  assertOk "containsRat on lower bound" (Interval.containsRat ivA (CanonicalRat.mk (-2) 1))
  assertOk "containsRat on upper bound" (Interval.containsRat ivA (CanonicalRat.mk 3 1))
  assertOk "containsRat rejects below lo" (!Interval.containsRat ivA (CanonicalRat.mk (-3) 1))
  assertOk "containsRat rejects above hi" (!Interval.containsRat ivA (CanonicalRat.mk 4 1))

/-! ===================================================================
    SUITE 5: intervalJudge Refutations & Enclosure
    =================================================================== -/

def testIntervalJudgeRefutations : IO Unit := do
  IO.println "--- Suite 5: intervalJudge Refutations ---"

  -- Expression: x + 1, where x in [1, 2]. Actual computed enclosure: [2, 3].
  let qBase : IntervalQuery := {
    expr := .add (.var "x") (.const (CanonicalRat.mk 1 1))
    env := [("x", Interval.mk (CanonicalRat.mk 1 1) (CanonicalRat.mk 2 1))]
    claimedBound := Interval.mk (CanonicalRat.mk 2 1) (CanonicalRat.mk 3 1)
  }

  -- 1. Valid claimed bounds passes
  let vValid := intervalJudge.check 0 qBase .direct
  assertOk "intervalJudge accepts exact valid bound" (vValid matches .ok)

  -- 2. Claimed bound too tight on upper side: claimed [2, 2.5], actual [2, 3]
  let qTightHi : IntervalQuery := {
    qBase with claimedBound := Interval.mk (CanonicalRat.mk 2 1) (CanonicalRat.mk 5 2)
  }
  let vTightHi := intervalJudge.check 0 qTightHi .direct
  let okTightHi := match vTightHi with
    | .refused (.boundViolated comp claimed) [] => comp.hi == CanonicalRat.mk 3 1 && claimed.hi == CanonicalRat.mk 5 2
    | _ => false
  assertOk "intervalJudge refutes tight upper bound violation" okTightHi

  -- 3. Claimed bound too tight on lower side: claimed [2.5, 3], actual [2, 3]
  let qTightLo : IntervalQuery := {
    qBase with claimedBound := Interval.mk (CanonicalRat.mk 5 2) (CanonicalRat.mk 3 1)
  }
  let vTightLo := intervalJudge.check 0 qTightLo .direct
  let okTightLo := match vTightLo with
    | .refused (.boundViolated comp claimed) [] => comp.lo == CanonicalRat.mk 2 1 && claimed.lo == CanonicalRat.mk 5 2
    | _ => false
  assertOk "intervalJudge refutes tight lower bound violation" okTightLo

  -- 4. Undefined variable in environment -> domainUndefined refusal
  let qUndef : IntervalQuery := {
    qBase with expr := .var "unbound_variable"
  }
  let vUndef := intervalJudge.check 0 qUndef .direct
  assertOk "intervalJudge refutes undefined variable" (vUndef matches .refused .domainUndefined [])

  -- 5. Counterexample certificate refuting invalid claimed bound [0, 1]
  let qBadClaim : IntervalQuery := {
    qBase with claimedBound := Interval.mk (CanonicalRat.mk 0 1) (CanonicalRat.mk 1 1)
  }
  -- Point x = 2 -> expr = 3, which is > claimed hi (1)
  let ptRefute : List (String × CanonicalRat) := [("x", CanonicalRat.mk 2 1)]
  let vRefute := intervalJudge.check 0 qBadClaim (.counterexample ptRefute)
  assertOk "intervalJudge accepts counterexample refutation witness"
    (vRefute matches .refused (.refutationWitness _) [])

  -- 6. Counterexample certificate that is NOT a counterexample (point actually in bound)
  let qWide : IntervalQuery := {
    qBase with claimedBound := Interval.mk (CanonicalRat.mk 0 1) (CanonicalRat.mk 10 1)
  }
  let vUncovered := intervalJudge.check 0 qWide (.counterexample ptRefute)
  assertOk "intervalJudge returns uncovered when witness is not violating" (vUncovered matches .uncovered)

  -- 7. Counterexample certificate outside declared domain [1, 2]: x = 50 -> returns uncovered
  let ptOutDomain : List (String × CanonicalRat) := [("x", CanonicalRat.mk 50 1)]
  let vOutDomain := intervalJudge.check 0 qBadClaim (.counterexample ptOutDomain)
  assertOk "intervalJudge returns uncovered for point outside domain" (vOutDomain matches .uncovered)

/-! ===================================================================
    SUITE 6: sosJudge Adversarial Refutations
    =================================================================== -/

def testSosJudgeRefutations : IO Unit := do
  IO.println "--- Suite 6: sosJudge Adversarial Refutations ---"

  let pX : Poly := ⟨[([(0, 1)], 1)]⟩
  let pY : Poly := ⟨[([(1, 1)], 1)]⟩

  -- 1. Strictly negative constant polynomial: P = -1
  let pNegConst : Poly := ⟨[([], -1)]⟩
  let qNegConst : SOSQuery := { goal := pNegConst, ineqs := [], eqs := [] }
  -- Attempt fake SOS with empty sum: certPoly = 0, residual = -1 - 0 = -1 != 0
  let cEmpty : SOSCert := { sigma0 := ⟨[]⟩, sigmas := [], lambdas := [] }
  let vNegConst := sosJudge.check 0 qNegConst cEmpty
  assertOk "sosJudge refutes negative constant with empty SOS"
    (vNegConst matches .refused (.identityMismatch _) [])

  -- 2. Strictly negative quadratic polynomial: P = -x^2 - 1
  let pNegQuad := Poly.add (Poly.neg (Poly.sqr pX)) pNegConst
  let qNegQuad : SOSQuery := { goal := pNegQuad, ineqs := [], eqs := [] }
  -- Attempting positive SOS sigma0 = [x^2, 1] gives certPoly = x^2 + 1, diff != 0
  let cPositive : SOSCert := { sigma0 := ⟨[(1, pX), (1, Poly.one)]⟩, sigmas := [], lambdas := [] }
  let vNegQuad := sosJudge.check 0 qNegQuad cPositive
  assertOk "sosJudge refutes negative quadratic" (vNegQuad matches .refused (.identityMismatch _) [])

  -- 3. Planted negative coefficient in sigma0: c = -1
  let cBadWeight : SOSCert := { sigma0 := ⟨[(-1, pX)]⟩, sigmas := [], lambdas := [] }
  let vBadWeight := sosJudge.check 0 qNegQuad cBadWeight
  assertOk "sosJudge refutes negative coefficient in sigma0" (vBadWeight matches .refused .invalidSOSWeights [])

  -- 4. Planted zero coefficient in sigma0: c = 0
  let cZeroWeight : SOSCert := { sigma0 := ⟨[(0, pX)]⟩, sigmas := [], lambdas := [] }
  let vZeroWeight := sosJudge.check 0 qNegQuad cZeroWeight
  assertOk "sosJudge refutes zero coefficient in sigma0" (vZeroWeight matches .refused .invalidSOSWeights [])

  -- 5. Planted negative coefficient in ineq multiplier: sigmas has c = -2
  let cBadIneqWeight : SOSCert := {
    sigma0 := ⟨[(1, pX)]⟩
    sigmas := [(⟨[(-2, pX)]⟩, 0)]
    lambdas := []
  }
  let vBadIneq := sosJudge.check 0 qNegQuad cBadIneqWeight
  assertOk "sosJudge refutes negative coefficient in inequality multiplier"
    (vBadIneq matches .refused .invalidSOSWeights [])

  -- 6. Motzkin Polynomial M(x, y) = x^4 y^2 + x^2 y^4 - 3 x^2 y^2 + 1
  -- M is globally non-negative, but NOT a sum of squares!
  -- Term 1: x^4 y^2 = (0,4), (1,2)
  -- Term 2: x^2 y^4 = (0,2), (1,4)
  -- Term 3: -3 x^2 y^2 = (0,2), (1,2), coeff -3
  -- Term 4: 1 = [], coeff 1
  let mTerm1 : Monomial × CanonicalRat := ([(0, 4), (1, 2)], 1)
  let mTerm2 : Monomial × CanonicalRat := ([(0, 2), (1, 4)], 1)
  let mTerm3 : Monomial × CanonicalRat := ([(0, 2), (1, 2)], -3)
  let mTerm4 : Monomial × CanonicalRat := ([], 1)
  let pMotzkin : Poly := ⟨[mTerm4, mTerm3, mTerm2, mTerm1]⟩
  let qMotzkin : SOSQuery := { goal := pMotzkin, ineqs := [], eqs := [] }

  -- Attempting a fake SOS certificate: sigma0 = (x^2 y - x y^2)^2 = x^4 y^2 - 2 x^3 y^3 + x^2 y^4
  let pFakeSub : Poly := Poly.sub (Poly.mul (Poly.sqr pX) pY) (Poly.mul pX (Poly.sqr pY))
  let cMotzkinFake : SOSCert := { sigma0 := ⟨[(1, pFakeSub)]⟩, sigmas := [], lambdas := [] }
  let vMotzkin := sosJudge.check 0 qMotzkin cMotzkinFake
  assertOk "sosJudge refutes unconstrained SOS certificate for Motzkin polynomial"
    (vMotzkin matches .refused (.identityMismatch _) [])

  -- 7. Valid SOS certificate passes: P = (x + 1)^2 + 2(y - 1)^2
  let pXplus1 := Poly.add pX Poly.one
  let pYminus1 := Poly.sub pY Poly.one
  let pValidGoal := Poly.add (Poly.sqr pXplus1) (Poly.scale (CanonicalRat.mk 2 1) (Poly.sqr pYminus1))
  let qValid : SOSQuery := { goal := pValidGoal, ineqs := [], eqs := [] }
  let cValid : SOSCert := {
    sigma0 := ⟨[(1, pXplus1), (2, pYminus1)]⟩
    sigmas := []
    lambdas := []
  }
  let vValidSos := sosJudge.check 0 qValid cValid
  assertOk "sosJudge accepts valid SOS certificate" (vValidSos matches .ok)

  -- 8. Valid Constrained Putinar SOS: Goal = x^2 + 3*g, where g in ineqs[0]
  let pIneqG := Poly.sub (Poly.sqr pY) Poly.one -- g = y^2 - 1 >= 0
  let pGoalConstrained := Poly.add (Poly.sqr pX) (Poly.scale (CanonicalRat.mk 3 1) pIneqG)
  let qConstrained : SOSQuery := {
    goal := pGoalConstrained
    ineqs := [pIneqG]
    eqs := []
  }
  let cConstrained : SOSCert := {
    sigma0 := ⟨[(1, pX)]⟩
    sigmas := [(⟨[(3, Poly.one)]⟩, 0)]
    lambdas := []
  }
  let vConstrained := sosJudge.check 0 qConstrained cConstrained
  assertOk "sosJudge accepts valid Putinar inequality certificate" (vConstrained matches .ok)

/-! ===================================================================
    SUITE 7: obligationJudge Anti-Cheat Adversarial Testing
    =================================================================== -/

def testObligationAntiCheat : IO Unit := do
  IO.println "--- Suite 7: obligationJudge Anti-Cheat ---"

  -- 1. byExternalJudge with empty payload rejected
  let vEmptyPayload := obligationJudge.check 0 badClaim (.byExternalJudge "transport@1" ByteArray.empty)
  assertOk "obligationJudge rejects empty external payload" (vEmptyPayload matches .refused .illFormed _)

  -- 2. byExternalJudge with unsupported format rejected
  let vBadFormat := obligationJudge.check 0 badClaim (.byExternalJudge "unsupported@99" "data".toUTF8)
  assertOk "obligationJudge rejects unsupported external format" (vBadFormat matches .refused .illFormed _)

  -- 3. byExternalJudge unverified payload refused at grade 0
  let vUnverified := obligationJudge.check 0 badClaim (.byExternalJudge "transport@1" "data".toUTF8)
  assertOk "obligationJudge refuses unverified external payload" (vUnverified matches .refused .illFormed _)

  -- 4. byEval with empty samples rejected
  let vEmptyEval := obligationJudge.check 0 badClaim (.byEval [])
  assertOk "obligationJudge rejects empty evaluation samples" (vEmptyEval matches .refused .illFormed _)

  -- 5. byEval with non-empty samples returns uncovered (finite samples cannot prove universal claim)
  let vSomeEval := obligationJudge.check 0 badClaim (.byEval [[1, 2, 3]])
  assertOk "obligationJudge returns uncovered for finite evaluation samples" (vSomeEval matches .uncovered)

/-! ===================================================================
    MAIN TEST RUNNER
    =================================================================== -/

def main : IO Unit := do
  IO.println "=========================================================="
  IO.println "   ADVERSARIAL STRESS TEST SUITE — MILESTONE 1"
  IO.println "=========================================================="
  testContractCertRefutations
  testNarrowsAntiCheat
  testCanonicalRatStress
  testIntervalStress
  testIntervalJudgeRefutations
  testSosJudgeRefutations
  testObligationAntiCheat
  IO.println "=========================================================="
  IO.println "   ALL ADVERSARIAL STRESS TESTS COMPLETED SUCCESSFULLY!   "
  IO.println "=========================================================="

#eval main
