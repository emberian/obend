module
/-
# Obend.Law.Fold — the law judge over a log of writes, as an audited fold

The second instance of `Obend.Fold.Admission` (`Legal` is the first, `Obend.Run.Fold`), to show the
structure is not shaped around `Legal`. The accumulator's rest is the object's current value; a row
is a write `(new, request)`, judged by the machine's verdict on the law (`Obend.Law.judge`) from the
current value, and an accepted write makes `new` the current value. The law reads no world: the
world component is `Unit`, a row reads no fact, and the receipt of a row is the current value and
the write (`receipt_sufficient` holds trivially). The one world-move row is `none`, a no-op. The
refusal names the law's reason, or that the probe gave no verdict.
-/
public import Obend.Fold
public import Obend.Law.Machine
@[expose] public section

namespace Obend.Law

open Obend.Core.Term (Term)
open Obend.Core.Data (Data Budget)
open Obend.Core.Machine (State Limits)

/-- Why a write was refused: the law's reason, or no verdict within the limits. -/
inductive WriteRefusal where
  | refused (why : String)
  | noVerdict
  deriving DecidableEq, Repr

/-- One write, judged at the current value. -/
def judgeWrite (policy : State → Bool) (limits : Limits) (budget : Budget) (law : Term) (old : Data) :
    Option (Data × Data) → Except WriteRefusal Data
  | none => .ok old
  | some (new, rq) =>
    match judge policy limits budget law old new rq with
    | some .ok => .ok new
    | some (.refused why) => .error (.refused why)
    | none => .error .noVerdict

/-- **The law judge as an audited fold** over writes. -/
def lawAdmission (policy : State → Bool) (limits : Limits) (budget : Budget) (law : Term) :
    Obend.Fold.Admission Unit Data (Option (Data × Data)) Empty WriteRefusal where
  step a r := (judgeWrite policy limits budget law a.2 r).map fun d => ((), d)
  reads _ _ := []
  look _ e := nomatch e
  moves r := r.isNone
  observe _ := none
  allowed _ _ := true
  keeps_world _ _ _ _ _ := rfl
  step_of_reads a w' r _ _ := by cases a; cases w'; cases (judgeWrite policy limits budget law _ r) <;> rfl
  observe_ok _ _ l _ := rfl

/-- The fold accepts a log of writes exactly when each is judged `ok` from the value the previous
ones left. -/
theorem lawAdmission_run_cons (policy : State → Bool) (limits : Limits) (budget : Budget) (law : Term)
    (old new rq : Data) (rest : List (Option (Data × Data))) :
    (lawAdmission policy limits budget law).run ((), old) (some (new, rq) :: rest) =
      match judge policy limits budget law old new rq with
      | some .ok => (lawAdmission policy limits budget law).run ((), new) rest
      | some (.refused why) => .error (.refused why)
      | none => .error .noVerdict := by
  simp only [Obend.Fold.Admission.run, List.foldlM_cons, lawAdmission, judgeWrite]
  split <;> rfl

end Obend.Law

end
