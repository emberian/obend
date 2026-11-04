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

end Obend.Teeth.Leaf.Static

end
