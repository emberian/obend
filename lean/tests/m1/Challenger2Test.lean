import Obend.Lower.Reflect
import Obend.Tactic.Weave
import Obend.Leaf.Emit
import Obend.Leaf.Flatten
import Obend.Leaf.Specialize
import Obend.Slot.World
import Obend.Slot.Selection
import Obend.Core.Term
import Obend.Logic.LateBinding

open Obend.Core.Term (Term)
open Obend.Lower.Reflect
open Obend.Tactic.Weave
open Obend.Leaf
open Obend.Slot
open Obend.Slot.World
open Obend.Logic

def assertOk (what : String) (ok : Bool) : IO Unit :=
  if ok then
    IO.println s!"[PASS] {what}"
  else
    throw (IO.userError s!"[FAIL] {what}")

-- =========================================================================
-- SECTION 1: Weave Tactics Stress Theorems
-- =========================================================================

-- 1. poly_ring stress tests
theorem test_poly_ring_distrib (a b c : Nat) : a * (b + c) = a * b + a * c := by
  poly_ring

theorem test_poly_ring_assoc_comm (a b c : Nat) : (a + b) + (c + a) = 2 * a + b + c := by
  poly_ring

theorem test_poly_ring_linear_comb (x y : Nat) : 3 * (x + 2 * y) + 4 * x = 7 * x + 6 * y := by
  poly_ring

-- 2. obend_split stress tests
theorem test_obend_split_simple (b : Bool) : (if b then 42 else 42) = 42 := by
  obend_split

theorem test_obend_split_nested (b1 b2 : Bool) :
    (if b1 then (if b2 then 1 else 1) else 1) = 1 := by
  obend_split
  obend_split

theorem test_obend_split_two_branches (b : Bool) (x y : Nat) :
    (if b then x + y else y + x) = x + y := by
  obend_split
  omega

-- 3. obend_unfold stress tests
theorem test_obend_unfold_holds (I : Term) (d : Obend.Core.Data.Data) :
    Obend.Law.Holds I d = Obend.Core.Term.Evaluates (.app I d.term) (.boolean true) := by
  rfl

theorem test_obend_unfold_keeps (I : Term) (d : Obend.Core.Data.Data) :
    Obend.Law.Keeps I d ↔ Obend.Law.Holds I d := by
  rfl

-- 4. obend_law master contract tactic
theorem test_obend_law_concrete_beq : (42 == 42) = true := by
  obend_law

theorem test_obend_law_le (n : Nat) : n ≤ n := by
  obend_law

theorem test_obend_law_linear (x y : Nat) (h : x + 2 * y ≤ 50) : x ≤ 50 := by
  obend_law

theorem test_obend_law_split (b : Bool) (n : Nat) :
    (if b then n + 0 else 0 + n) = n := by
  obend_law

theorem test_obend_law_trivial : True := by
  obend_law



-- 5. obend_tooth diagnostic tactic
theorem test_obend_tooth_diagnostic (x : Nat) (h : x + 1 = x) : False := by
  obend_tooth
  omega

-- 6. reflect_override_blocks formal theorem instantiation
theorem test_formal_reflect_override_blocks
    (v : LeafView) (ref : ReflectedObject)
    (hj : ref.composition.closedB = true)
    {p : LeafPin} (hp : p ∈ ref.pins) (hd : holdsAt v p = false) :
    ∃ dead, specSlot.read (holdsAt v) (some (.book ref.name ref.composition)) =
      .blocked (.book ref.name ref.composition) dead ∧ p ∈ dead := by
  exact reflect_override_blocks v ref hj hp hd

-- =========================================================================
-- SECTION 2: Dynamic Lowering Bridge & Pin Invalidation Stress Tests
-- =========================================================================

def testComp : Composition :=
  let L : Layer := {
    name := "L1",
    metadata := .record [],
    fields := [("val", .nat 42)],
    flat := false
  }
  {
    top := L,
    below := [],
    seed := []
  }

def testLowerBridge : IO Unit := do
  let env : LayoutEnv := { fields := [], selfIndex := 0, arity := 1 }

  -- 1. Exhaustive primitive lowering checks
  let tAdd := Term.binary .add (.nat 10) (.nat 20)
  assertOk "lowerTerm add" (lowerTerm env tAdd matches some (.natBin .add (.lit 10) (.lit 20)))

  let tSub := Term.binary .subtract (.nat 20) (.nat 5)
  assertOk "lowerTerm subtract" (lowerTerm env tSub matches some (.natBin .sub (.lit 20) (.lit 5)))

  let tMul := Term.binary .multiply (.nat 3) (.nat 7)
  assertOk "lowerTerm multiply" (lowerTerm env tMul matches some (.natBin .mul (.lit 3) (.lit 7)))

  let tDiv := Term.binary .divide (.nat 10) (.nat 2)
  assertOk "lowerTerm divide" (lowerTerm env tDiv matches some (.natBin .div (.lit 10) (.lit 2)))

  let tMod := Term.binary .modulo (.nat 10) (.nat 3)
  assertOk "lowerTerm modulo" (lowerTerm env tMod matches some (.natBin .mod (.lit 10) (.lit 3)))

  let tEq := Term.binary .equal (.nat 4) (.nat 4)
  assertOk "lowerTerm equal" (lowerTerm env tEq matches some (.natBin .beq (.lit 4) (.lit 4)))

  let tLe := Term.binary .lessEqual (.nat 3) (.nat 5)
  assertOk "lowerTerm lessEqual" (lowerTerm env tLe matches some (.natBin .ble (.lit 3) (.lit 5)))

  -- 2. Term constructors: boolean, bound, app, lam, get, record, ifBool
  let tBool := Term.boolean true
  assertOk "lowerTerm bool true" (lowerTerm env tBool matches some (.boolLit true))

  let tBound := Term.bound 2
  assertOk "lowerTerm bound" (lowerTerm env tBound matches some (.bvar 2))

  let tApp := Term.app (.lam (.bound 0)) (.nat 99)
  assertOk "lowerTerm app/lam" (lowerTerm env tApp matches some (.app (.lam _ (.bvar 0)) (.lit 99)))

  let tGet := Term.get (.record [("x", .nat 1)]) "x"
  assertOk "lowerTerm get/record" (lowerTerm env tGet matches some (.proj "x" (.record [("x", .lit 1)])))

  let tIf := Term.ifBool (.boolean true) (.nat 1) (.nat 2)
  assertOk "lowerTerm ifBool" (lowerTerm env tIf matches some (.boolRec _ (.lit 2) (.lit 1) (.boolLit true)))

  -- 3. Fuel boundary stress tests
  assertOk "fuel 0 returns none" ((lowerTermFuel env 0 (.nat 1)).isNone == true)
  assertOk "fuel 1 on complex term returns none" ((lowerTermFuel env 1 tAdd).isNone == true)
  assertOk "fuel 2 on add succeeds" (lowerTermFuel env 2 tAdd matches some _)

  -- 4. Unsupported terms properly rejected
  let tFix := Term.fix (.nat 0) (.nat 0)
  assertOk "unsupported Term.fix rejected" ((lowerTerm env tFix).isNone == true)

  let tMix := Term.mix (.nat 0) (.nat 0)
  assertOk "unsupported Term.mix rejected" ((lowerTerm env tMix).isNone == true)

  let tPerform := Term.perform (.nat 0)
  assertOk "unsupported Term.perform rejected" ((lowerTerm env tPerform).isNone == true)

  let tSplit := Term.split (.nat 0) ["x"] (.nat 0)
  assertOk "unsupported Term.split rejected" ((lowerTerm env tSplit).isNone == true)

  let tInject := Term.inject "lbl" (.nat 0)
  assertOk "unsupported Term.inject rejected" ((lowerTerm env tInject).isNone == true)

  let tCase := Term.case (.nat 0) [("lbl", .nat 1)]
  assertOk "unsupported Term.case rejected" ((lowerTerm env tCase).isNone == true)

  let tHole := Term.hole 0 []
  assertOk "unsupported Term.hole rejected" ((lowerTerm env tHole).isNone == true)

def testOverridePinInvalidation : IO Unit := do
  let env : LayoutEnv := { fields := [], selfIndex := 0, arity := 1 }
  let some ref := reflectComposition "obj1" testComp env
    | throw (IO.userError "reflectComposition failed on testComp")

  assertOk "reflected object has correct pins count (1 object + 1 layer)" (ref.pins.length == 2)

  let vClean := viewOf 0 "obj1" testComp

  -- Under clean view, all pins hold
  let allHold := ref.pins.all (fun p => holdsAt vClean p == true)
  assertOk "clean view: all pins hold" allHold
  assertOk "clean view: specSlot is usable" (specSlot.usable (holdsAt vClean) (.book "obj1" testComp) == true)
  assertOk "clean view: specSlot read is usable" (specSlot.read (holdsAt vClean) (some (.book "obj1" testComp)) matches .usable (.book "obj1" _) _)

  -- Mutate layer L1
  let vMutLayer : LeafView := {
    clock := 1,
    decl := fun
      | .layer "L1" => some (.nat 99999) -- mutated layer code!
      | other => vClean.decl other
  }

  let layerPin : LeafPin := { cell := .layer "L1", code := (testComp.top).code }
  assertOk "layer mutation: holdsAt is false" (holdsAt vMutLayer layerPin == false)
  assertOk "layer mutation: specSlot is NOT usable" (specSlot.usable (holdsAt vMutLayer) (.book "obj1" testComp) == false)
  let readMutLayer := specSlot.read (holdsAt vMutLayer) (some (.book "obj1" testComp))
  match readMutLayer with
  | .blocked (.book "obj1" _) dead =>
    assertOk "layer mutation: read transitions to .blocked" true
    assertOk "layer mutation: dead contains the mutated layer pin" (dead.any (·.cell == .layer "L1"))
  | _ =>
    assertOk "layer mutation: expected .blocked" false

  -- Mutate object composition
  let vMutObj : LeafView := {
    clock := 2,
    decl := fun
      | .object "obj1" => some (.boolean false) -- mutated composition code!
      | other => vClean.decl other
  }
  let objPin : LeafPin := { cell := .object "obj1", code := testComp.code }
  assertOk "object mutation: holdsAt is false" (holdsAt vMutObj objPin == false)
  assertOk "object mutation: specSlot is NOT usable" (specSlot.usable (holdsAt vMutObj) (.book "obj1" testComp) == false)
  let readMutObj := specSlot.read (holdsAt vMutObj) (some (.book "obj1" testComp))
  match readMutObj with
  | .blocked (.book "obj1" _) dead =>
    assertOk "object mutation: read transitions to .blocked" true
    assertOk "object mutation: dead contains the mutated object pin" (dead.any (·.cell == .object "obj1"))
  | _ =>
    assertOk "object mutation: expected .blocked" false

  -- Delete / remove layer entirely (none)
  let vDelLayer : LeafView := {
    clock := 3,
    decl := fun
      | .layer "L1" => none -- layer removed!
      | other => vClean.decl other
  }
  assertOk "layer removal: holdsAt is false" (holdsAt vDelLayer layerPin == false)
  let readDelLayer := specSlot.read (holdsAt vDelLayer) (some (.book "obj1" testComp))
  match readDelLayer with
  | .blocked (.book "obj1" _) dead =>
    assertOk "layer removal: read transitions to .blocked" true
    assertOk "layer removal: dead contains the missing layer pin" (dead.any (·.cell == .layer "L1"))
  | _ =>
    assertOk "layer removal: expected .blocked" false

  -- Unclosed / invalid composition guard
  let openComp : Composition := {
    top := { name := "openTop", metadata := .record [], fields := [("bad", .bound 99)], flat := false },
    below := [],
    seed := []
  }
  assertOk "open composition: closedB is false" (openComp.closedB == false)
  assertOk "open composition: reflectComposition is refused (none)" ((reflectComposition "open" openComp env).isNone == true)

  -- Composition with unlowerable method code
  let unlowerableComp : Composition := {
    top := { name := "unlowTop", metadata := .record [], fields := [("bad", .fix (.nat 0) (.nat 0))], flat := false },
    below := [],
    seed := []
  }
  assertOk "unlowerable method: reflectComposition is refused (none)" ((reflectComposition "unlow" unlowerableComp env).isNone == true)

def main : IO Unit := do
  IO.println "=== Running Challenger 2 Adversarial Stress Suite ==="
  testLowerBridge
  testOverridePinInvalidation
  IO.println "=== All Challenger 2 Adversarial Stress Tests Passed! ==="

#eval main
