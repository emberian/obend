module
/-
# Obend.Run.Spec — what an accepted event log must satisfy, stated of the log alone

The declarative specification the runner (`Obend.Run.Runner.run`) refines. Nothing here reads a
configuration or calls `run`: every clause is a property of the list of accepted events, the host,
the operation accounts, and the object the run started from. The world, spent tokens, history and
plan at a point of the log are recomputed from the log's prefix (`worldOf`, `spentBy`, `histOf`,
`planOf`), and each clause is a property of every position (`AtEach`):

- `WorldSteps`: every world event is a step the host's world takes from the world then current;
- `Authorized`: every dispatched call was admitted (`admitOp`) at the view current when it was
  dispatched: the world's view then, with every token an earlier dispatch spent dead;
- `OnceSpent`: no token is spent by two dispatches;
- `Paired`: a call is dispatched only with nothing in flight, and a reply is accepted only for the
  call in flight;
- `ReplansUnentered`: no replan touched a hole the history had entered (`Dispatched`) when the replan
  was accepted;
- `Kept`: the history is a history (`Started`) of the plan in force.

`Legal` is their conjunction. The theorem that every reachable configuration's log is `Legal`, and
that the configuration is the log's (its world, spent tokens, history, plan and residual are the
recomputed ones), is `Obend.Run.Proofs.Invariant.refines`.
-/
public import Obend.Run.Runner
public import Obend.Slot.Proofs.ProtocolTyping
@[expose] public section

namespace Obend.Run

open Obend.Slot Obend.Slot.Protocol

/-- `Q` holds at every position of the log, of the prefix before it and the event there. -/
def AtEach {α : Type} (Q : List α → α → Prop) (log : List α) : Prop :=
  ∀ n z, log[n]? = some z → Q (log.take n) z

section
variable {Ix : Type} {S : Sig Ix} {Hole : Ix → Type} {A : Ix → Type} {Tok Fact Ob V : Type}

/-- The world after a log, from `v₀`: the last world event's. -/
def worldOf (v₀ : V) (log : List (Event S Hole A V)) : V :=
  log.foldl (fun v e => match e with
    | .world v' => v'
    | _ => v) v₀

/-- The tokens a log's dispatches spent, in order. -/
def spentBy (sp : Spec S Tok Fact Ob) (log : List (Event S Hole A V)) : List Tok :=
  log.filterMap fun e => match e with
    | .dispatch o => sp.consumes o.2
    | _ => none

/-- The view current after a log: the world's view, with every spent token dead. -/
def viewAt [DecidableEq Tok] (host : Host V Tok Fact) (sp : Spec S Tok Fact Ob) (v₀ : V)
    (log : List (Event S Hole A V)) : View Tok Fact :=
  View.mask (host.view (worldOf v₀ log)) (spentBy sp log)

/-- The history after a log: the replies, in order, and the call dispatched and not yet answered. -/
def histOf (log : List (Event S Hole A V)) : Hist S :=
  log.foldl (fun H e => match e with
    | .dispatch o => ⟨H.answered, some o⟩
    | .respond r => ⟨H.answered ++ [r], none⟩
    | _ => H) ⟨[], none⟩

/-- The calls a log dispatched, in order. -/
def dispatchesOf (log : List (Event S Hole A V)) : List (Σ i, S.Op i) :=
  log.filterMap fun e => match e with
    | .dispatch o => some o
    | _ => none

/-- A reply event. -/
def Event.isRespond : Event S Hole A V → Bool
  | .respond _ => true
  | _ => false

/-- Every world event is a step the host's world takes. -/
def WorldSteps (host : Host V Tok Fact) (v₀ : V) : List (Event S Hole A V) → Prop :=
  AtEach fun pre e => ∀ v, e = .world v → host.allowed (worldOf v₀ pre) v = true

/-- Every dispatched call was admitted at the view current when it was dispatched. -/
def Authorized [DecidableEq Tok] (host : Host V Tok Fact) (sp : Spec S Tok Fact Ob) (v₀ : V) :
    List (Event S Hole A V) → Prop :=
  AtEach fun pre e => ∀ o, e = .dispatch o → admitOp sp (viewAt host sp v₀ pre) o.2 = true

/-- No token is spent twice. -/
def OnceSpent (sp : Spec S Tok Fact Ob) (log : List (Event S Hole A V)) : Prop :=
  (spentBy sp log).Nodup

/-- Dispatch only with nothing in flight; a reply only to the call in flight. -/
def Paired : List (Event S Hole A V) → Prop :=
  AtEach fun pre e =>
    (∀ o, e = .dispatch o → (histOf pre).inflight = none) ∧
      (∀ r, e = .respond r → (histOf pre).inflight = some ⟨r.1, r.2.1⟩)

/-- No replan touched a hole the history had entered when it was accepted. -/
def ReplansUnentered {i : Ix} (P : Prot S Hole A i) : List (Event S Hole A V) → Prop :=
  AtEach fun pre e => ∀ (j : Ix) (h : Hole j) (f : Prot S Hole A j),
    e = .replan h f → ¬ Dispatched P (histOf pre) j h

variable [DecidableEq Ix] [∀ i, DecidableEq (Hole i)]

/-- The plan in force after a log: `σ₀` with each replan's filling installed. -/
def planOf (σ₀ : Subst S Hole A) (log : List (Event S Hole A V)) : Subst S Hole A :=
  log.foldl (fun σ e => match e with
    | .replan h f => setHole σ h f
    | _ => σ) σ₀

/-- The history is a history of the plan in force. -/
def Kept {i : Ix} (Ω : Ctx S Hole A Tok Fact Ob) (σ₀ : Subst S Hole A) (P : Prot S Hole A i)
    (log : List (Event S Hole A V)) : Prop :=
  Started (fill Ω (planOf σ₀ log) P) (histOf log)

/-- The specification of an accepted log, for a run of the object `O` from world `v₀`. -/
structure Legal [DecidableEq Tok] (host : Host V Tok Fact) (sp : Spec S Tok Fact Ob) {i : Ix}
    (O : Open S Hole A Tok Fact Ob i) (v₀ : V) (log : List (Event S Hole A V)) : Prop where
  steps : WorldSteps host v₀ log
  authorized : Authorized host sp v₀ log
  once : OnceSpent sp log
  paired : Paired log
  frozen : ReplansUnentered O.template log
  kept : Kept O.Ω O.σ O.template log

end

end Obend.Run

end
