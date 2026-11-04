module
/- Fixtures and teeth for `Obend.Leaf.Static` (tier 2). These are concrete `decide +kernel`
instances; they are not theorems about the folder, they are checks that it folds what the
docstrings say it folds, and that a folder which does nothing is refused (`#tooth`).

* a reader applied to a literal environment record folds through the field selection, the
  constructor case and the addition to the literal `50`;
* `specializeBook` on a four-slot book with `mode`, `threshold` and `helper` pinned propagates the
  constants, drops both dead branches, inlines `self.helper`, and leaves `dispatch` reading no slot;
  applied to `5` the residual folds to `30`, and `evalBook` of the residual is `evalBook` of the
  original. -/
public import Obend.Tactic.Tooth
import all Obend.Leaf.Specialize
import all Obend.Leaf.Served
import all Obend.Leaf.Static
public import Obend.Leaf.Static
@[expose] public section
open Obend.Core.Term Obend.Leaf Obend.Leaf.Static

namespace Obend.Teeth.Leaf.Static

/-! ## A pinned environment, read -/

/-- Two declarations: `"Nat.zero"` holding `0` and `"Answer"` holding `42`. -/
def sampleEnvPinTable : EnvPinTable :=
  [ ("Nat.zero", .inject "constInfo" (.nat 0))
  , ("Answer", .inject "constInfo" (.nat 42)) ]

/-- A reader that selects `"Answer"`, cases on `"constInfo"`, and adds `8`. -/
def sampleElabLookupTerm : Term :=
  .lam
    (.case (.get (.bound 0) "Answer")
      [ ("constInfo", .binary .add (.bound 0) (.nat 8))
      , ("axiomInfo", .nat 0) ])

/-- The reader at the environment folds to `50`. -/
theorem envLookup_sample_folds :
    dataPinSpecialize (.app sampleElabLookupTerm (pinTableToTerm sampleEnvPinTable)) = .nat 50 := by
  simp [dataPinSpecialize, dataPinSteps, dataPinPass, resolveApp, resolveGet, resolveCase,
    resolveBinary, sampleElabLookupTerm, pinTableToTerm, sampleEnvPinTable,
    instantiate, Term.substitute, liftSubstitution, primitiveResult]

/-- A folder that folds nothing. -/
def dataPinSpecializeNoOp (t : Term) : Term := t

#tooth Obend.Teeth.Leaf.Static.envLookup_sample_folds by mutation
  Obend.Leaf.Static.dataPinSpecialize := dataPinSpecializeNoOp

/-! ## A four-slot book, specialized -/

/-- Slots `mode` (a cell holding `0`), `threshold` (a cell holding `9`), `helper` (`λself. λx. x + 16`)
and `dispatch`, which reads all three:
`λself. λx. ifZero self.mode (ifBool (self.threshold ≤ 10) (self.helper x + self.threshold) 999) (λp. 888)`. -/
def sampleSpecializableBook : Book where
  items :=
    [ .slot { member := "mode", slot := 0, kind := .cell, code := .lam (.lam (.nat 0)), reads := [] }
    , .slot { member := "threshold", slot := 1, kind := .cell, code := .lam (.lam (.nat 9)), reads := [] }
    , .slot { member := "helper", slot := 2, kind := .method, code := .lam (.lam (.binary .add (.bound 0) (.nat 16))), reads := [] }
    , .slot
        { member := "dispatch"
          slot := 3
          kind := .method
          code :=
            .lam
              (.lam
                (.ifZero (.get (.bound 1) "mode")
                  (.ifBool (.binary .lessEqual (.get (.bound 1) "threshold") (.nat 10))
                    (.binary .add (.app (.get (.bound 1) "helper") (.bound 0)) (.get (.bound 1) "threshold"))
                    (.nat 999))
                  (.lam (.nat 888))))
          reads := [0, 1, 2] } ]

/-- `mode ↦ 0`, `threshold ↦ 9`, `helper ↦ λx. x + 16`. -/
def sampleBookPins : List LeafPin :=
  [ ⟨.layer "mode", .nat 0⟩
  , ⟨.layer "threshold", .nat 9⟩
  , ⟨.layer "helper", .lam (.binary .add (.bound 0) (.nat 16))⟩ ]

/-- `dispatch` after specialization: `λself. λx. (x + 16) + 9`, reading no slot; at `5` it folds to `30`. -/
theorem specializeBook_sample_folds :
    lookupBookCode (specializeBook sampleSpecializableBook sampleBookPins) "dispatch" =
      some (.lam (.lam (.binary .add (.binary .add (.bound 0) (.nat 16)) (.nat 9)))) ∧
    ((specializeBook sampleSpecializableBook sampleBookPins).defs.find? (·.member == "dispatch")).map (·.reads) =
      some [] ∧
    evalResidualBookAt (specializeBook sampleSpecializableBook sampleBookPins) "dispatch" (.nat 5) =
      some (.nat 30) ∧
    evalBook (specializeBook sampleSpecializableBook sampleBookPins) "dispatch" =
      evalBook sampleSpecializableBook "dispatch" := by
  refine ⟨optTermEq_sound (by decide +kernel), by decide +kernel,
    optTermEq_sound (by decide +kernel), optTermEq_sound (by decide +kernel)⟩

/-- A specializer that returns the book unchanged. -/
def specializeBookNoOp (B : Book) (_pins : List LeafPin) : Book := B

#tooth Obend.Teeth.Leaf.Static.specializeBook_sample_folds by mutation
  Obend.Leaf.Static.specializeBook := specializeBookNoOp

/-! ## A pin that holds at a view is not a pin the dispatcher serves

The counterexample to "pins that hold at a view justify the specialized book": `b = λself. self.a + 1`
with `a = λself. 1`. The pin `a := 5` holds at a view whose cell `a` holds `5`, but the book's own
dispatcher serves `1` for `a`, so binding the pin changes `b` from `2` to `6`. The judge of the
specialized book (`specializedJudgeB`) refuses that pin and admits `a := 1`, under which `b` is
still `2`; `Obend.Leaf.Served.link_bequiv_bindBookPins` is the theorem whose hypothesis this is. -/

/-- `a = λself. 1`, `b = λself. self.a + 1`. -/
def servedBook : Book where
  items :=
    [ .slot { member := "a", slot := 0, kind := .method, code := .lam (.nat 1), reads := [] }
    , .slot { member := "b", slot := 1, kind := .method,
              code := .lam (.binary .add (.get (.bound 0) "a") (.nat 1)), reads := [0] } ]

/-- The pin `a := 5`: not what the dispatcher serves. -/
def unservedPin : LeafPin := ⟨.layer "a", .nat 5⟩

/-- The pin `a := 1`: what the dispatcher serves. -/
def servedPin : LeafPin := ⟨.layer "a", .nat 1⟩

/-- A view whose cell `a` holds `5`, so `unservedPin` holds there. -/
def viewHoldingFive : LeafView := ⟨0, fun c => if c = .layer "a" then some (.nat 5) else none⟩

/-- The unserved pin holds at that view. -/
example : Obend.Slot.World.holdsAt viewHoldingFive unservedPin = true := by decide +kernel

/-- The book's `b` is `2`. -/
example : optTermEq (Obend.Law.run 1000 (.get servedBook.link "b")) (some (.nat 2)) = true := by decide +kernel

/-- Under the unserved pin, `b` is `6`: the pin changed the behaviour. -/
example : optTermEq (Obend.Law.run 1000 (.get (specializeBook servedBook [unservedPin]).link "b")) (some (.nat 6)) = true := by
  decide +kernel

/-- The judge refuses the unserved pin. -/
example : specializedJudgeB servedBook [unservedPin] = false := by decide +kernel

/-- The judge admits the served pin, and `b` stays `2`. -/
example : specializedJudgeB servedBook [servedPin] = true := by decide +kernel
example : optTermEq (Obend.Law.run 1000 (.get (specializeBook servedBook [servedPin]).link "b")) (some (.nat 2)) = true := by
  decide +kernel

/-- A judge that does not run the dispatcher. -/
def judgeWithoutServing (B : Book) (pins : List LeafPin) : Bool :=
  Obend.Law.closedB B.link && Obend.Law.closedB (bindBookPins B pins).link && B.lamCodesB

#tooth Obend.Leaf.Served.served_of_judgeB by mutation
  Obend.Leaf.specializedJudgeB := judgeWithoutServing

end Obend.Teeth.Leaf.Static

end
