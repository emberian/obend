module
/-
# Obend.Run.Core4 — an emitted Core4 activity as the runner's protocol

A Core4 activity runs to a yield, its Plan (`Data`) is extracted, the kernel answers with a response
(`Data`, resumed as a closed term), and it runs to the next yield: the turns `Spec.Preview.runTurns`
executes and `Core.Interaction` gives as the reference tree (`node_of_chain_vis`: a machine yield is
the reference `Vis` of every state in a chain with it). Here the same turns become an open protocol:
one operation per Plan, one response per `Data`, `turn` the machine's own run, `unfold n` the
protocol of the activity to depth `n`. What a Plan requires, spends and establishes is a `Spec` over
Plans the DEPLOYMENT supplies (`Core4` Plans carry no authority of their own); the runner enforces it
at dispatch exactly as for any protocol.

Theorems: `Obend.Run.Proofs.Core4`. The gaps this leaves (depth, ticks, response typing, choice points)
are closed by the adapter over it, `Obend.Run.Adapter`.
-/
public import Obend.Run.Runner
public import Obend.Core.Data
public section

namespace Obend.Run.Core4

open Obend.Slot.Protocol Obend.Core.Machine Obend.Core.Data

mutual
/-- Decided equality of Plans (`Data` derives only `Repr`). -/
def decData : (a b : Data) → Decidable (a = b)
  | .natural x, .natural y => if h : x = y then isTrue (by rw [h]) else isFalse (by intro e; cases e; exact h rfl)
  | .natural _, .boolean _ => isFalse (by intro h; cases h)
  | .natural _, .label _ => isFalse (by intro h; cases h)
  | .natural _, .record _ => isFalse (by intro h; cases h)
  | .natural _, .variant _ _ => isFalse (by intro h; cases h)
  | .boolean _, .natural _ => isFalse (by intro h; cases h)
  | .boolean x, .boolean y => if h : x = y then isTrue (by rw [h]) else isFalse (by intro e; cases e; exact h rfl)
  | .boolean _, .label _ => isFalse (by intro h; cases h)
  | .boolean _, .record _ => isFalse (by intro h; cases h)
  | .boolean _, .variant _ _ => isFalse (by intro h; cases h)
  | .label _, .natural _ => isFalse (by intro h; cases h)
  | .label _, .boolean _ => isFalse (by intro h; cases h)
  | .label x, .label y => if h : x = y then isTrue (by rw [h]) else isFalse (by intro e; cases e; exact h rfl)
  | .label _, .record _ => isFalse (by intro h; cases h)
  | .label _, .variant _ _ => isFalse (by intro h; cases h)
  | .record _, .natural _ => isFalse (by intro h; cases h)
  | .record _, .boolean _ => isFalse (by intro h; cases h)
  | .record _, .label _ => isFalse (by intro h; cases h)
  | .record fs, .record gs => match decFields fs gs with
    | isTrue h => isTrue (by rw [h])
    | isFalse h => isFalse (by intro e; cases e; exact h rfl)
  | .record _, .variant _ _ => isFalse (by intro h; cases h)
  | .variant _ _, .natural _ => isFalse (by intro h; cases h)
  | .variant _ _, .boolean _ => isFalse (by intro h; cases h)
  | .variant _ _, .label _ => isFalse (by intro h; cases h)
  | .variant _ _, .record _ => isFalse (by intro h; cases h)
  | .variant l p, .variant m q =>
    if hl : l = m then
      match decData p q with
      | isTrue h => isTrue (by rw [hl, h])
      | isFalse h => isFalse (by intro e; cases e; exact h rfl)
    else isFalse (by intro e; cases e; exact hl rfl)
def decFields : (fs gs : List (String × Data)) → Decidable (fs = gs)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse (by intro h; cases h)
  | _ :: _, [] => isFalse (by intro h; cases h)
  | (n, a) :: fs, (m, b) :: gs =>
    if hn : n = m then
      match decData a b, decFields fs gs with
      | isTrue h, isTrue h' => isTrue (by rw [hn, h, h'])
      | isFalse h, _ => isFalse (by intro e; cases e; exact h rfl)
      | _, isFalse h => isFalse (by intro e; cases e; exact h rfl)
    else isFalse (by intro e; cases e; exact hn rfl)
end

instance : DecidableEq Data := decData

/-- One operation per Plan; the response is `Data`; the protocol has one index. -/
@[expose] def planSig : Sig Unit where
  Op := fun _ => Data
  Resp := fun _ => Data
  next := fun _ _ => ()

instance : DecidableEq (Σ i, planSig.Op i) := inferInstanceAs (DecidableEq (Σ _ : Unit, Data))

/-- A Core4 activity's protocol has no holes: its plan is the program. -/
@[expose] def NoHole : Unit → Type := fun _ => Empty

instance : ∀ i, DecidableEq (NoHole i) := fun _ => inferInstanceAs (DecidableEq Empty)

/-- How the activity's protocol ends. -/
inductive Stop where
  /-- the machine finished, suspended, diverged or refused within the turn -/
  | ended (o : Outcome)
  /-- it yielded a Plan that is not Data within the budget -/
  | unextractable (f : Failure)
  /-- the yielded state did not take the response (never: `turn_vis_resumes`) -/
  | unresumable
  /-- the unfolding's depth -/
  | depth
  /-- a yielded Plan that is a choice among these alternatives, none chosen at its position yet
  (the adapter's frontier, `Obend.Run.Adapter`) -/
  | choice (alts : List Data)

/-- One turn of the machine: a yield with its extracted Plan and the state to resume, or a stop. -/
inductive Turn where
  | vis (plan : Data) (yielded : State)
  | stop (s : Stop)

/-- One turn under the machine's limits, a tick bound per turn, and the extraction budget. -/
def turn (L : Limits) (ticks : Nat) (budget : Budget) (s : State) : Turn :=
  match runBounded L ticks s with
  | .yielded _ y =>
    match yieldedPlan L budget y with
    | .ok r => .vis r.value r.state
    | .error (f, _) => .stop (.unextractable f)
  | o => .stop (.ended o)

abbrev P := Prot planSig NoHole (fun _ => Stop) ()

/-- The activity at `s` as a protocol, to depth `n`: each yield is a call of its Plan whose
continuation, for every response, is the activity resumed with it. -/
def unfold (L : Limits) (ticks : Nat) (budget : Budget) : Nat → State → P
  | 0, _ => .ret .depth
  | n + 1, s =>
    match turn L ticks budget s with
    | .vis p y => .call (S := planSig) p fun r =>
      match resume r.term y with
      | some s' => unfold L ticks budget n s'
      | none => .ret .unresumable
    | .stop x => .ret x

/-- The open object of an activity: the protocol, nothing to choose, hypotheses `Γ`, tokens `Δ`,
obligation bound `Φ`. -/
def activity {Tok Fact Ob : Type} (L : Limits) (ticks : Nat) (budget : Budget) (n : Nat) (s : State)
    (Γ : List Fact) (Δ : List Tok) (Φ : List Ob) : Open planSig NoHole (fun _ => Stop) Tok Fact Ob () where
  template := unfold L ticks budget n s
  Ω := fun _ h => nomatch h
  σ := fun _ _ => none
  Γ := Γ
  Δ := Δ
  Q := fun _ _ => True
  Φ := Φ
  hist := ⟨[], none⟩

/-- The machine's own run of turns: from `s`, yield Plan `p`, be resumed with `r`, go on; the
transcript is the list of (Plan, response) pairs and the state it ends in. Stated of the machine,
not of the runner. -/
inductive Transcript (L : Limits) (ticks : Nat) (budget : Budget) :
    State → Trace planSig → State → Prop
  | nil (s : State) : Transcript L ticks budget s [] s
  | turn {s y s' s'' : State} {p r : Data} {t : Trace planSig} :
      turn L ticks budget s = .vis p y → resume r.term y = some s' →
      Transcript L ticks budget s' t s'' →
      Transcript L ticks budget s (⟨(), p, r⟩ :: t) s''

/-- The runner's events for a transcript: each Plan dispatched, then its response. -/
def eventsOf {V : Type} : Trace planSig → List (Event planSig NoHole (fun _ => Stop) Fact V)
  | [] => []
  | e :: t => .dispatch ⟨e.1, e.2.1⟩ :: .respond e :: eventsOf t

end Obend.Run.Core4

end
