/-
# Obend.Run.Core4Example — a real Core4 activity through the runner (legacy leaf)

Not a `module`, for the reason `Obend.Core.Teeth.Collect` gives: these theorems run the demand machine
(`runBounded`, `yieldedPlan`) on a concrete term by `rfl`, through `Array` functions whose bodies
`Init` does not expose to `module` files (a `module` copy of `yields` fails `rfl`; probed 2026-10-31).
Nothing imports this file.

`yieldingTerm` (`Obend.Core.Proofs.Collect`) yields the Plan `5`. Each Plan spends a one-use ticket.
-/
import Obend.Run.Proofs.Core4
import Obend.Core.Proofs.Collect
import Obend.AxiomPin

namespace Obend.Run.Core4.Example
open Obend.Slot.Protocol Obend.Core.Machine Obend.Core.Data Obend.Core.Collect

/-- The machine's first turn yields the Plan `5`. -/
theorem yields : ∃ y, turn exampleLimits 32 exampleBudget (initial yieldingTerm) = .vis (.natural 5) y :=
  ⟨_, rfl⟩

/-- Plans spend the one ticket; nothing else is required or owed. -/
def spec : Spec planSig Unit Unit Unit where
  consumes := fun _ => some ()
  requires := fun _ => []
  establishes := fun _ => []

/-- A world that says whether the ticket is live. -/
def host (live : Bool) : Host Unit Unit Unit := ⟨fun _ _ => true, fun _ => ⟨fun _ => true, fun _ => live⟩⟩

def O : Open planSig NoHole (fun _ => Stop) Unit Unit Unit () :=
  activity exampleLimits 32 exampleBudget 2 (initial yieldingTerm) [] [()] []

/-- The machine's one-turn transcript: yield `5`, be answered `7`. -/
theorem transcript : ∃ s', Transcript exampleLimits 32 exampleBudget (initial yieldingTerm)
    [⟨(), .natural 5, .natural 7⟩] s' := by
  obtain ⟨y, hy⟩ := yields
  obtain ⟨s', hs⟩ := turn_vis_resumes hy (Data.natural 7).term
  exact ⟨s', .turn hy hs (.nil _)⟩

/-- **The general adapter theorem at a real program**: the turn is a runner trace under `Legal`. -/
theorem turn_is_trace : ∃ s',
    (session (host true) spec (Cfg.init O ()) (eventsOf [⟨(), .natural 5, .natural 7⟩])).2 = [none, none] ∧
    (session (host true) spec (Cfg.init O ()) (eventsOf [⟨(), .natural 5, .natural 7⟩])).1.res =
      ⟨(), unfold exampleLimits 32 exampleBudget 1 s'⟩ ∧
    Legal (host true) spec O () (session (host true) spec (Cfg.init O ())
      (eventsOf [⟨(), .natural 5, .natural 7⟩])).1.log := by
  obtain ⟨s', ht⟩ := transcript
  obtain ⟨h1, _, h3, h4⟩ := run_is_trace (host := host true) (sp := spec) (Γ := []) (Δ := [()])
    (Φ := ([] : List Unit)) 1 () ht (fun e he => by simp at he; subst he; rfl) (by decide)
  exact ⟨s', h1, h3, h4⟩

/-- **Where `Preview` admits nothing, the runner admits**: with the ticket not live the same Plan is
refused before the program sees a response, naming the ticket. -/
theorem dead_ticket_refused :
    (session (host false) spec (Cfg.init O ()) (eventsOf [⟨(), .natural 5, .natural 7⟩])).2 =
      [some (.unadmitted ⟨(), .natural 5⟩ [] (some ())), some (.unsolicited ⟨(), .natural 5, .natural 7⟩)] :=
  rfl

#assert_axioms yields transcript turn_is_trace dead_ticket_refused

end Obend.Run.Core4.Example
