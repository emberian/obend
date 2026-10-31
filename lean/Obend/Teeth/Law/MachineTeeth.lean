/-
# Obend.Law.Proofs.MachineTeeth — the machine judging real laws (a legacy leaf)

Not a `module`: these run the demand machine (`execute`) on concrete probes by `rfl`, through
`Array` functions whose bodies `Init` does not expose to `module` files (`Obend.Run.Core4Example`
gives the same reason). Nothing imports this file.

The machine's verdicts on `bounded` and on the effective law of `boardLaws` are read back through
`judge_sound`/`judgeEffective_names`, so each instance inhabits a premise of the general theorems,
and each admission is paired with a refusal naming its reason (and, for the effective law, the
ancestor). The `#tooth` lines mutate the probe's reader: with `asLabel` the identity a refusal
whose payload is `true` would read as `ok`, and the soundness proofs no longer check.
-/
import Obend.Law.Proofs.Machine
import Obend.Tactic.Tooth
open Obend.Law Obend.Core.Machine Obend.Core.Data

namespace Obend.Law.MachineTeeth

def L : Limits := ⟨4096, 4096⟩
def B : Budget := ⟨4, 4096, 4096⟩

theorem bounded_admits_on_machine :
    judge (fun _ => true) L B (bounded unitTy "total" 5) (totalIs 0) (totalIs 3) (rqBy "ann" "ann" writeO) =
      some .ok := by rfl

theorem bounded_refuses_on_machine :
    judge (fun _ => true) L B (bounded unitTy "total" 5) (totalIs 0) (totalIs 9) (rqBy "ann" "ann" writeO) =
      some (.refused "total over the bound") := by decide +kernel

/-- The machine's verdicts read back through soundness: the admission is `Admits`, the refusal is
the law's own refusal with its reason. -/
theorem bounded_machine_meaning :
    Admits (bounded unitTy "total" 5) (totalIs 0) (totalIs 3) (rqBy "ann" "ann" writeO) ∧
      RefusesAs (bounded unitTy "total" 5) (totalIs 0) (totalIs 9) (rqBy "ann" "ann" writeO) "total over the bound" :=
  ⟨judge_sound (by decide +kernel) bounded_admits_on_machine,
   judge_sound (by decide +kernel) bounded_refuses_on_machine⟩

theorem board_admits_on_machine :
    judgeEffective (fun _ => true) L B (effective boardLaws) (totalIs 0) (totalIs 3) (rqBy "ann" "ann" writeO) =
      some .ok := by decide +kernel

theorem board_room_on_machine :
    judgeEffective (fun _ => true) L B (effective boardLaws) (totalIs 0) (totalIs 9) (rqBy "ann" "ann" writeO) =
      some (.refusedBy "room" "total over the bound") := by decide +kernel

theorem board_board_on_machine :
    judgeEffective (fun _ => true) L B (effective boardLaws) (totalIs 0) (totalIs 3) (rqBy "eve" "eve" writeO) =
      some (.refusedBy "board" "not on the allowlist") := by decide +kernel

/-- **The machine names the ancestor**, read back: `room` refused (its predecessors admitted), and on
another request `board`. -/
theorem board_machine_names :
    (∃ pre L post, boardLaws = pre ++ ("room", L) :: post ∧
      (∀ q ∈ pre, Admits q.2 (totalIs 0) (totalIs 9) (rqBy "ann" "ann" writeO)) ∧
      RefusesAs L (totalIs 0) (totalIs 9) (rqBy "ann" "ann" writeO) "total over the bound") ∧
    (∃ pre L post, boardLaws = pre ++ ("board", L) :: post ∧
      (∀ q ∈ pre, Admits q.2 (totalIs 0) (totalIs 3) (rqBy "eve" "eve" writeO)) ∧
      RefusesAs L (totalIs 0) (totalIs 3) (rqBy "eve" "eve" writeO) "not on the allowlist") ∧
    ∀ p ∈ boardLaws, Admits p.2 (totalIs 0) (totalIs 3) (rqBy "ann" "ann" writeO) :=
  ⟨(judgeEffective_names boardLaws_closed).2 _ _ board_room_on_machine,
   (judgeEffective_names boardLaws_closed).2 _ _ board_board_on_machine,
   (judgeEffective_names boardLaws_closed).1 board_admits_on_machine⟩

-- A refusal read as an admission: the soundness proofs no longer check.
#tooth judge_sound by mutation Verdict.ofData := fun d => match d with
  | .boolean true => some .ok
  | .label _ => some .ok
  | _ => none
-- A refusal read with the wrong ancestor: the naming proof no longer checks.
#tooth judgeEffective_names by mutation judgeEffective := fun policy limits budget law o n rq =>
  match (runProbe policy limits budget (blameProbe "reason" law o n rq)).bind Verdict.ofData with
  | some .ok => some .ok
  | some (.refused why) => some (.refusedBy why why)
  | none => none

end Obend.Law.MachineTeeth
