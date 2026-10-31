/-
# Obend.Run.Core4Example — a real Core4 activity through the runner (legacy leaf)

Not a `module`, for the reason `Obend.Core.Teeth.Collect` gives: these theorems run the demand machine
(`runBounded`, `yieldedPlan`) on a concrete term by `rfl`, through `Array` functions whose bodies
`Init` does not expose to `module` files (a `module` copy of `yields` fails `rfl`; probed 2026-10-31).
Nothing imports this file.

`yieldingTerm` (`Obend.Core.Proofs.Collect`) yields the Plan `5`. Each Plan spends a one-use ticket.
-/
import Obend.Run.Proofs.Core4
import Obend.Run.Proofs.Adapter
import Obend.Tactic.Tooth
import Obend.Core.Proofs.Collect

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
    Legal (host true) spec O () (fun _ _ => []) (session (host true) spec (Cfg.init O ())
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

/-! ## The completed adapter (`Obend.Run.Adapter`): four fixtures the bare adapter gets wrong -/

/-- The example deployed: responses are naturals; `alts` and `supports` as each fixture says. -/
def deploy (alts : Data → Option (List Data)) (supports : Data → List Unit) (v₀ : Bool) :
    Deploy Unit Unit Unit Bool where
  L := exampleLimits
  budget := exampleBudget
  alts := alts
  resp := .natural
  supports := supports
  s₀ := initial yieldingTerm
  Γ := []
  Δ := [()]
  Φ := []
  v₀ := v₀

/-- A world that says whether the one support holds; the ticket is live. -/
def bhost : Host Bool Unit Unit := ⟨fun _ _ => true, fun v => ⟨fun _ => v, fun _ => true⟩⟩

def plain : Deploy Unit Unit Unit Bool := deploy (fun _ => none) (fun _ => []) true

/-- **Response typing.** The bare adapter accepts the reply `true` to a Plan whose declared response
type is a natural; the adapter refuses it by name and takes the natural. -/
theorem bare_illTyped :
    (session bhost spec (Cfg.init (activity exampleLimits 32 exampleBudget 2 (initial yieldingTerm)
      ([] : List Unit) [()] ([] : List Unit)) true)
      [.dispatch ⟨(), .natural 5⟩, .respond ⟨(), .natural 5, .boolean true⟩]).2 = [none, none] := rfl

theorem typed_receipt :
    (asession plain bhost spec (plain.start ⟨2, 32, []⟩)
      [.dispatch (.natural 5), .respond (.natural 5) (.boolean true), .respond (.natural 5) (.natural 7)]).2 =
      [none, some (.illTyped (.natural 5) (.boolean true)), none] := rfl

/-- **Depth.** Unfolded to depth 0, the bare adapter can never dispatch the first Plan; the adapter
deepens mid-run and dispatches it. -/
theorem bare_depth_stuck :
    (session bhost spec (Cfg.init (activity exampleLimits 32 exampleBudget 0 (initial yieldingTerm)
      ([] : List Unit) [()] ([] : List Unit)) true) [.dispatch ⟨(), .natural 5⟩]).2 =
      [some (.notNext ⟨(), .natural 5⟩)] := rfl

theorem deepen_receipt :
    (asession plain bhost spec (plain.start ⟨0, 32, []⟩)
      [.dispatch (.natural 5), .deepen 1, .dispatch (.natural 5), .respond (.natural 5) (.natural 7)]).2 =
      [some (.run (.notNext ⟨(), .natural 5⟩)), none, none, none] := rfl

/-- **Ticks.** With one tick a turn the first turn is cut short: the bare adapter's protocol has
ended; the adapter gives the turns more ticks and the Plan is yielded and dispatched. -/
theorem bare_ticks_ended :
    (session bhost spec (Cfg.init (activity exampleLimits 1 exampleBudget 2 (initial yieldingTerm)
      ([] : List Unit) [()] ([] : List Unit)) true) [.dispatch ⟨(), .natural 5⟩]).2 =
      [some (.notNext ⟨(), .natural 5⟩)] := rfl

theorem ticks_receipt :
    (asession plain bhost spec (plain.start ⟨2, 1, []⟩)
      [.dispatch (.natural 5), .moreTicks 31, .dispatch (.natural 5)]).2 =
      [some (.run (.notNext ⟨(), .natural 5⟩)), none, none] := rfl

/-- The Plan `5` is a choice between `6` and `7`; choosing `7` cites the one support. -/
def chooser : Deploy Unit Unit Unit Bool :=
  deploy (fun p => if p = .natural 5 then some [.natural 6, .natural 7] else none)
    (fun q => if q = .natural 7 then [()] else []) true

/-- **A choice point.** The bare adapter dispatches the choice point itself, as if it were an
operation. The adapter refuses it (the run stands at a choice point), refuses `8` (not an
alternative), takes `7`; once `7`'s support is revoked its dispatch is refused naming it; the
choice is changed to `6` before anything was dispatched, and `6` goes out and is answered. -/
theorem bare_choice_dispatched :
    (session bhost spec (Cfg.init (activity exampleLimits 32 exampleBudget 2 (initial yieldingTerm)
      ([] : List Unit) [()] ([] : List Unit)) true) [.dispatch ⟨(), .natural 5⟩]).2 = [none] := rfl

theorem choice_receipt :
    (asession chooser bhost spec (chooser.start ⟨2, 32, []⟩)
      [.dispatch (.natural 5), .choose (.natural 8), .choose (.natural 7), .world false,
       .dispatch (.natural 7), .choose (.natural 6), .dispatch (.natural 6),
       .respond (.natural 6) (.natural 1)]).2 =
      [some (.run (.notNext ⟨(), .natural 5⟩)), some (.notAlternative (.natural 8)), none, none,
       some (.choiceUnsupported (.natural 7) [()]), none, none, none] := rfl

/-- The general theorem at the choice run: its log is `Legal` for the activity with the choice
made, every reply typed, every chosen Plan's citation held at its dispatch. -/
theorem choice_inv :
    AInv chooser bhost spec (asession chooser bhost spec (chooser.start ⟨2, 32, []⟩)
      [.dispatch (.natural 5), .choose (.natural 8), .choose (.natural 7), .world false,
       .dispatch (.natural 7), .choose (.natural 6), .dispatch (.natural 6),
       .respond (.natural 6) (.natural 1)]).1 :=
  areachable_inv (asession_reachable .init _)

/-- The general theorem at the deepened run: it is a run of the machine, its answered history the
machine's one-turn transcript, at depth 1. -/
theorem deepen_trace :
    let a := (asession plain bhost spec (plain.start ⟨0, 32, []⟩)
      [.dispatch (.natural 5), .deepen 1, .dispatch (.natural 5), .respond (.natural 5) (.natural 7)]).1
    a.par.depth = 1 ∧ a.cfg.obj.hist.answered = [⟨(), .natural 5, .natural 7⟩] ∧
      ∃ s' m, Transcript exampleLimits 32 exampleBudget (initial yieldingTerm) a.cfg.obj.hist.answered s' ∧
        a.par.depth = a.cfg.obj.hist.answered.length + m :=
  have h := plain_trace (D := plain) (host := bhost) (sp := spec) (par₀ := ⟨0, 32, []⟩) (fun _ => rfl) (asession_reachable .init
    [.dispatch (.natural 5), .deepen 1, .dispatch (.natural 5), .respond (.natural 5) (.natural 7)])
  ⟨rfl, rfl, by obtain ⟨_, s', m, ht, hn, _⟩ := h; exact ⟨s', m, ht, hn⟩⟩

#tooth typed_receipt by mutation typedReply := fun {_ _ _ _} _ _ => true
#tooth choice_receipt by mutation choiceGuard := fun {_ _ _ _} _ _ _ _ => []

end Obend.Run.Core4.Example
