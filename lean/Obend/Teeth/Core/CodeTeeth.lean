module
/-
# Obend.Teeth.Core.CodeTeeth — a quotation under two package revisions; kinds across an import

The importer (`Obend.Core.Code.importWith`) at work on one quotation, `λk. k.n` checked at
`Kilo → Nat` against version 1 of `Units.Kilo` (layout `{n}`), read by three readers: one holding
version 1, one holding version 2 (layout `{n, note}`) with no migration judgment, and one whose
judgment migrates 1 to 2. The identity `Units.Kilo` is the same in both revisions; the versions
differ, and that difference is a judgment, never assumed:

* `same_revision_imports`: the reader holding version 1 imports it;
* `revised_kind_refused`: the reader holding version 2 refuses it by name, `kindVersion Kilo 1 2`;
* `migration_rechecks`: the migrating reader rechecks it under its own rules and kinds, and its
  checker refuses the old annotation at the new layout: a migration is a recheck, not a replay;
* `reannotated_imports`: the term annotated and pinned under version 2 imports under version 2;
* `identity_stable`: both revisions' types name one kind;
* `import_crossing_refused`: the same quotation imported where a `Mile → Nat` is expected is
  refused, naming the two kinds: nominal identity survives the import boundary.
-/
public import Obend.Core.Code
import all Obend.Core.Code
import all Obend.Core.Nominal
import all Obend.Core.Check
import all Obend.Core.Ty
import all Obend.Core.TypeGraph
import all Obend.Core.FiniteBisimulation
import all Obend.Core.RecursiveAgreement
import all Obend.Core.EquiRecursiveAgreement
import all Obend.Elab.Work
@[expose] public section
namespace Obend.Core.Code
open Obend.Core.Ty Obend.Core.Check Obend.Core.Term
set_option autoImplicit false

def kilo1 : Ty := Ty.kinded "Units.Kilo" (.field "n" .natural .emptyRow)
def kilo2 : Ty := Ty.kinded "Units.Kilo" (.field "n" .natural (.field "note" .natural .emptyRow))

/-- `λk. k.n`, annotated over `k`'s type. -/
def readN : Term := .lam (.get (.bound 0) "n")
def readNAt (k : Ty) (pin : Nat) : Held :=
  ⟨readN, .node (some ⟨k, .natural, .unrestricted, .reusable⟩) [], {}, [⟨"Units.Kilo", pin⟩]⟩

def at1 : Ty := .arrow .reusable .unrestricted kilo1 .natural
def at2 : Ty := .arrow .reusable .unrestricted kilo2 .natural

def rev1 : Reader := ⟨0, 1000, [⟨"Units.Kilo", 1⟩], fun _ _ _ => false⟩
def rev2 : Reader := ⟨0, 1000, [⟨"Units.Kilo", 2⟩], fun _ _ _ => false⟩
def rev2migrating : Reader :=
  ⟨0, 1000, [⟨"Units.Kilo", 2⟩], fun k a b => k == "Units.Kilo" && a == 1 && b == 2⟩

/-- Which refusal an import ended in, as a word (`accepted` when it did not refuse). -/
def outcome {α : Type} : Except ImportRefusal α → String × List String × List Nat
  | .ok _ => ("accepted", [], [])
  | .error (.kindVersion k a b) => ("kindVersion", [k], [a, b])
  | .error (.kindsCrossed _ k k') => ("kindsCrossed", [k, k'], [])
  | .error (.rejected _) => ("rejected", [], [])
  | .error _ => ("other", [], [])

theorem same_revision_imports :
    outcome (importWith rev1 [] at1 {} (quotation 0 (readNAt kilo1 1))) = ("accepted", [], []) := by
  decide +kernel

theorem revised_kind_refused :
    outcome (importWith rev2 [] at2 {} (quotation 0 (readNAt kilo1 1))) = ("kindVersion", ["Units.Kilo"], [1, 2]) := by
  decide +kernel

theorem migration_rechecks :
    outcome (importWith rev2migrating [] at2 {} (quotation 0 (readNAt kilo1 1))) = ("rejected", [], []) := by
  decide +kernel

theorem reannotated_imports :
    outcome (importWith rev2 [] at2 {} (quotation 0 (readNAt kilo2 2))) = ("accepted", [], []) := by
  decide +kernel

theorem identity_stable :
    Obend.Core.Nominal.kindOf kilo1 = some "Units.Kilo" ∧ Obend.Core.Nominal.kindOf kilo2 = some "Units.Kilo" := by
  decide +kernel

theorem import_crossing_refused :
    outcome (importWith rev1 [] (.arrow .reusable .unrestricted
      (Ty.kinded "Units.Mile" (.field "n" .natural .emptyRow)) .natural) {} (quotation 0 (readNAt kilo1 1))) =
      ("kindsCrossed", ["Units.Mile", "Units.Kilo"], []) := by
  decide +kernel

end Obend.Core.Code

end
