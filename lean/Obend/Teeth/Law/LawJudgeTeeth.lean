/-
# Obend.Law.Proofs.LawJudgeTeeth — the law-judged runner at a real object (a legacy leaf)

Not a `module`: the runner here judges by running the demand machine, by `decide +kernel`, through
`Array` functions whose bodies `Init` does not expose to `module` files (as `Obend.Run.Core4Example`).
Nothing imports this file.

The object holds a natural `total`; its one operation writes a new total. Its effective law is
`boardLaws` (`board2 → board → room`: the owner signs, the signer is on the allowlist, the total is at
most 5). The deployment's own spec requires and spends nothing, so every refusal below is the law's.
-/
import Obend.Run.LawJudge
import Obend.Run.Proofs.Invariant
import Obend.Tactic.Tooth
open Obend.Slot.Protocol Obend.Run Obend.Law Obend.Core.Machine Obend.Core.Data

namespace Obend.Law.LawJudgeTeeth

/-- One operation: write the total `k`; the reply is `()`. -/
abbrev sig : Sig Unit := ⟨fun _ => Nat, fun _ => Unit, fun _ _ => ()⟩

abbrev Op := Σ i, sig.Op i
instance : DecidableEq Op := inferInstanceAs (DecidableEq (Σ _ : Unit, Nat))

def NoHole : Unit → Type := fun _ => Empty
instance : ∀ i, DecidableEq (NoHole i) := fun _ => inferInstanceAs (DecidableEq Empty)

abbrev Fact := LawFact Op

/-- The object: write `k`, then stop. -/
def obj (k : Nat) : Open sig NoHole (fun _ => Unit) Unit Fact Unit () where
  template := .call (S := sig) k fun _ => .ret ()
  Ω := fun _ h => nomatch h
  σ := fun _ _ => none
  Γ := []
  Δ := []
  Q := fun _ _ => True
  Φ := []
  hist := ⟨[], none⟩

/-- The world is the object's current total; the host allows everything. -/
def host : Host Nat Unit Fact := ⟨fun _ _ => true, fun _ => ⟨fun _ => true, fun _ => true⟩⟩

/-- The deployment requires and spends nothing. -/
def sp : Spec sig Unit Fact Unit := ⟨fun _ => none, fun _ => [], fun _ => []⟩

/-- The board's effective law judges the write, signed by `agent`. -/
def J (agent : String) : LawJudge Nat Fact Op where
  embed := id
  classify := some
  classify_embed := fun _ => rfl
  act := fun v o => some (totalIs v, totalIs o.2, rqBy agent agent writeO)
  lin := boardLaws
  policy := fun _ => true
  limits := ⟨4096, 4096⟩
  budget := ⟨4, 4096, 4096⟩

/-- The missing facts of a refusal. -/
def missingIn : Except (Refusal sig NoHole Unit Fact) (Cfg sig NoHole (fun _ => Unit) Unit Fact Unit Nat ()) → List Fact
  | .error (.unadmitted _ m _) => m
  | _ => []

def accepted : Except (Refusal sig NoHole Unit Fact) (Cfg sig NoHole (fun _ => Unit) Unit Fact Unit Nat ()) → Bool
  | .ok _ => true
  | .error _ => false

/-- **Writing 9 is refused, naming `room`**: the runner's missing facts are the verdict and the
`room` clause. -/
theorem room_refused :
    missingIn (Obend.Run.run (lawHost host (J "ann")) (lawSpec sp (J "ann")) (Cfg.init (obj 9) 0) (.dispatch ⟨(), 9⟩)) =
      [.admitted ⟨(), 9⟩, .clause ⟨(), 9⟩ "room"] := by decide +kernel

/-- **Eve writing 3 is refused, naming `board`.** -/
theorem board_refused :
    missingIn (Obend.Run.run (lawHost host (J "eve")) (lawSpec sp (J "eve")) (Cfg.init (obj 3) 0) (.dispatch ⟨(), 3⟩)) =
      [.admitted ⟨(), 3⟩, .clause ⟨(), 3⟩ "board"] := by decide +kernel

/-- **Ann writing 3 is admitted.** -/
theorem ann_admitted :
    accepted (Obend.Run.run (lawHost host (J "ann")) (lawSpec sp (J "ann")) (Cfg.init (obj 3) 0) (.dispatch ⟨(), 3⟩)) = true := by
  decide +kernel

/-- The general refusal theorem at the fixture: the runner refuses, and the law it names refused. -/
theorem room_named :
    (∃ missing dead, Obend.Run.run (lawHost host (J "ann")) (lawSpec sp (J "ann")) (Cfg.init (obj 9) 0) (.dispatch ⟨(), 9⟩) =
        .error (.unadmitted ⟨(), 9⟩ missing dead) ∧ LawFact.clause ⟨(), 9⟩ "room" ∈ missing) ∧
      ∃ pre L post, boardLaws = pre ++ ("room", L) :: post ∧
        (∀ q ∈ pre, Admits q.2 (totalIs 0) (totalIs 9) (rqBy "ann" "ann" writeO)) ∧
        RefusesAs L (totalIs 0) (totalIs 9) (rqBy "ann" "ann" writeO) "total over the bound" :=
  dispatch_refused_names (J := J "ann") boardLaws_closed (k := fun _ => .ret ()) rfl rfl rfl rfl
    (by decide +kernel)

/-- The general admission theorem at the fixture: Ann's accepted dispatch reaches a configuration
whose log is `Legal`, and its write was admitted by every law on the board's precedence list. -/
theorem ann_law_admitted : ∃ c, Reachable (lawHost host (J "ann")) (lawSpec sp (J "ann")) (Cfg.init (obj 3) 0) c ∧
    ∀ p ∈ boardLaws, Admits p.2 (totalIs 0) (totalIs 3) (rqBy "ann" "ann" writeO) := by
  cases h : Obend.Run.run (lawHost host (J "ann")) (lawSpec sp (J "ann")) (Cfg.init (obj 3) 0) (.dispatch ⟨(), 3⟩) with
  | error w =>
      have := ann_admitted
      rw [h] at this
      cases this
  | ok c =>
      have reach : Reachable _ _ _ c := .step _ .init h
      refine ⟨c, reach, ?_⟩
      have hlog : c.log = [.dispatch ⟨(), 3⟩] := run_dispatch_log h
      have := reachable_law_admitted boardLaws_closed reach 0 ⟨(), 3⟩ (by rw [hlog]; rfl)
        (totalIs 0) (totalIs 3) (rqBy "ann" "ann" writeO) rfl
      exact this.2

-- Without the law's requirements the runner admits what the law refuses: the proof no longer checks.
#tooth legal_law_admitted by mutation lawRequires := fun _ _ => []
#tooth dispatch_refused_names by mutation lawRequires := fun _ _ => []

end Obend.Law.LawJudgeTeeth
