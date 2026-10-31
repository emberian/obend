module
/-
# Obend.Run.Runner — the guarded runner

An executable transition system over an open object (`Obend.Slot.Protocol.Open`). A configuration
holds the object (template, interface, current substitution, accepted history), the host's current
world, the durable spent-token state, the residual protocol (what the current plan still has to do
after the answered history) and the log of accepted events. `run` takes a raw proposed event and
returns the next configuration or a named refusal:

- `world v'`: the host's world moves, if `Host.allowed` says the step is one its world takes. Nothing
  else moves: in particular a world that says a spent token is live again does not unspend it.
- `replan h f cites`: put `f` in hole `h`, a decision citing `cites` (the selected candidate's
  supports; body and citations are installed by the one event and frozen together). Refused unless `h` is a hole this party chooses and the history
  has not entered it (`entered`, the executable `Dispatched`); refused BY NAME when the entered hole
  holds the in-flight call (`replacesInflight`) or answered calls (`replacesAnswered`).
- `dispatch o`: expose `o` to the handler. Refused while a call is in flight (`busy`), unless `o` is
  the residual's next call (`notNext`), and unless `admitOp` accepts it at the CURRENT view: the
  world's view with every durably spent token dead (`unadmitted`, naming the facts that do not hold
  and the token that is not live), and `unsupported` unless every fact the decision of the call's
  hole cites holds now (`decisionDead`): a selection is a proposal rechecked at every exposure, not
  a permit. On acceptance the token is spent before anything else happens.
- `respond e`: the reply `e`, accepted only for the recorded in-flight call (`unsolicited`).
- `abandon o`: give up on the call `o` in flight (`notInflight` otherwise). The call stays in the
  history as dispatched and never answered, so its obligation stands (`Hist.established`); the run is
  ENDED (`closedBy`): every later replan, dispatch, reply or abandonment is refused `abandoned`, and
  only the world still moves.

The declarative specification the runner refines is `Obend.Run.Spec`; the invariant and its proof
are `Obend.Run.Proofs.Invariant`; the handler-driven loop and its agreement with `interpret` are
`drive` here and `Obend.Run.Proofs.Interpret`.
-/
public import Obend.Slot.Integrity
@[expose] public section

namespace Obend.Run

open Obend.Slot Obend.Slot.Protocol

/-- The host's world, as the runner sees it: views `V`, whether the world takes a step from one view
to another (decided), and what holds and what is live at a view. -/
structure Host (V Tok Fact : Type) where
  allowed : V → V → Bool
  view : V → View Tok Fact

/-- A `World`'s audited step, decided, with what is live at a view: a host. -/
def Host.ofWorld {V Fact Tok : Type} [World V Fact]
    (dec : ∀ v v' : V, Decidable (World.Step (Fact := Fact) v v')) (live : V → Tok → Bool) :
    Host V Tok Fact where
  allowed := fun v v' => @decide _ (dec v v')
  view := fun v => ⟨World.holdsAt v, live v⟩

/-- A view with every token of `spent` dead: what the durable spent state adds to the world's. -/
def View.mask {Tok Fact : Type} [DecidableEq Tok] (v : View Tok Fact) (spent : List Tok) :
    View Tok Fact :=
  ⟨v.holds, fun t => v.live t && !decide (t ∈ spent)⟩

section
variable {Ix : Type} {S : Sig Ix} {Hole : Ix → Type} {A : Ix → Type}

/-- A raw proposed event. -/
inductive Event (S : Sig Ix) (Hole : Ix → Type) (A : Ix → Type) (Fact V : Type) where
  /-- the host's world moves to `v` -/
  | world (v : V)
  /-- fill hole `h` with `f` from now on, a decision citing the facts `cites` (a selected
  candidate's supports; `[]` for a decision that cites nothing): every later dispatch of a call
  in that hole rechecks them at its own view -/
  | replan {j : Ix} (h : Hole j) (f : Prot S Hole A j) (cites : List Fact)
  /-- expose the call `o` to the handler -/
  | dispatch (o : Σ i, S.Op i)
  /-- the reply `e` arrives -/
  | respond (e : Entry S)
  /-- give up on the call `o` in flight: it is settled as permanently unanswered (its obligation
  stands), the plan ends, and nothing more is committed or replanned -/
  | abandon (o : Σ i, S.Op i)

/-- Why the runner refused an event. -/
inductive Refusal (S : Sig Ix) (Hole : Ix → Type) (Tok Fact : Type) where
  /-- the host's world does not take that step -/
  | worldStep
  /-- a call is in flight: no new commitment until its reply -/
  | busy (inflight : Σ i, S.Op i)
  /-- not the next call of the current plan -/
  | notNext (o : Σ i, S.Op i)
  /-- not admissible now: the required facts that do not hold, and the token that is not live -/
  | unadmitted (o : Σ i, S.Op i) (missing : List Fact) (dead : Option Tok)
  /-- a reply to no call in flight, or to a call other than the one in flight -/
  | unsolicited (e : Entry S)
  /-- the hole holds the call in flight: its plan stays until the reply -/
  | replacesInflight (inflight : Σ i, S.Op i) (h : Σ j, Hole j)
  /-- the hole holds answered calls: the accepted history stays -/
  | replacesAnswered (h : Σ j, Hole j)
  /-- not a hole this party chooses -/
  | notMine (h : Σ j, Hole j)
  /-- the replanned protocol does not have the history (never, at a reachable configuration whose
  replan is otherwise accepted: `Proofs.Invariant.replan_accepted`) -/
  | inconsistent
  /-- the run was ended by abandoning this call: only the world still moves -/
  | abandoned (o : Σ i, S.Op i)
  /-- abandoning a call that is not the one in flight -/
  | notInflight (o : Σ i, S.Op i)
  /-- the call lies in a hole whose decision cites facts that do not hold now -/
  | unsupported (o : Σ i, S.Op i) (h : Option (Σ j, Hole j)) (dead : List Fact)

/-- A configuration: the open object, the host's world, the durable spent tokens, the residual
protocol, and the accepted events in order. -/
structure Cfg (S : Sig Ix) (Hole : Ix → Type) (A : Ix → Type) (Tok Fact Ob V : Type) (i : Ix) where
  obj : Open S Hole A Tok Fact Ob i
  world : V
  spent : List Tok
  res : Σ j, Prot S Hole A j
  log : List (Event S Hole A Fact V)
  /-- the call abandoned, if the run was ended that way -/
  ended : Option (Σ i, S.Op i)
  /-- what each hole's decision cites (installed with its filling, frozen with it) -/
  cites : (j : Ix) → Hole j → List Fact

/-- The start: the object with an empty history at world `v`, its current protocol the residual,
and `cites₀` what the initial plan's decisions cite (rechecked at dispatch exactly as a replanned
decision's; `[]` for a plan that cites nothing). -/
def Cfg.init {Tok Fact Ob V : Type} {i : Ix} (O : Open S Hole A Tok Fact Ob i) (v : V)
    (cites₀ : (j : Ix) → Hole j → List Fact := fun _ _ => []) : Cfg S Hole A Tok Fact Ob V i :=
  ⟨{ O with hist := ⟨[], none⟩ }, v, [], ⟨i, fill O.Ω O.σ O.template⟩, [], none, cites₀⟩

/-- The view admission is judged at: the world's, with the durably spent tokens dead. -/
def Cfg.admitView {Tok Fact Ob V : Type} [DecidableEq Tok] {i : Ix} (host : Host V Tok Fact)
    (c : Cfg S Hole A Tok Fact Ob V i) : View Tok Fact :=
  View.mask (host.view c.world) c.spent

/-! ## The guards, by name (each is a `#tooth` mutation target) -/

/-- The dispatch guard: admission at the current view. -/
def dispatchGuard {Tok Fact Ob : Type} (sp : Spec S Tok Fact Ob) (v : View Tok Fact) {i : Ix}
    (op : S.Op i) : Bool :=
  admitOp sp v op

/-- Durable spending: the spent state after `op` is dispatched. -/
def spendOn {Tok Fact Ob : Type} (sp : Spec S Tok Fact Ob) (spent : List Tok) {i : Ix}
    (op : S.Op i) : List Tok :=
  spent ++ (sp.consumes op).toList

/-- The no-new-commitment guard: the call in flight, which a dispatch must wait for. -/
def awaiting (H : Hist S) : Option (Σ i, S.Op i) := H.inflight

/-- The no-new-commitment-after-abandon guard: the call the run was ended by, if any. -/
def closedBy {Tok Fact Ob V : Type} {i : Ix} (c : Cfg S Hole A Tok Fact Ob V i) :
    Option (Σ i, S.Op i) :=
  c.ended

/-- What a refused admission names. -/
def missingOf {Tok Fact Ob : Type} (sp : Spec S Tok Fact Ob) (v : View Tok Fact) {i : Ix}
    (op : S.Op i) : List Fact × Option Tok :=
  ((sp.requires op).filter fun f => !v.holds f,
    match sp.consumes op with
    | some t => if v.live t then none else some t
    | none => none)

/-! ## Following a trace through a protocol -/

variable [DecidableEq (Σ i, S.Op i)]

/-- One reply through a residual: the continuation it selects, when the residual is a call of the
reply's operation. -/
def follow : (Σ j, Prot S Hole A j) → Entry S → Option (Σ j, Prot S Hole A j)
  | ⟨j, .call op k⟩, e =>
    if h : (⟨e.1, e.2.1⟩ : Σ i, S.Op i) = ⟨j, op⟩ then
      some ⟨_, k (cast (congrArg (fun o : Σ i, S.Op i => S.Resp o.2) h) e.2.2)⟩
    else none
  | _, _ => none

/-- A trace through a residual (`Proofs.Invariant.advance_iff`: exactly `Reach`). -/
def advance (R : Σ j, Prot S Hole A j) : Trace S → Option (Σ j, Prot S Hole A j)
  | [] => some R
  | e :: t => match follow R e with
    | some R' => advance R' t
    | none => none

/-- The hole of the template the history has entered, if any: the template's prefix along the
answered calls reaches it and something after it was answered or is in flight
(`Proofs.Invariant.entered_iff`: exactly `Dispatched`). -/
def entered : {i : Ix} → Prot S Hole A i → Trace S → Bool → Option (Σ j, Hole j)
  | _, .ret _, _, _ => none
  | j, .hole h, t, infl => if t.isEmpty && !infl then none else some ⟨j, h⟩
  | _, .call _ _, [], _ => none
  | j, .call op k, e :: t, infl =>
    if h : (⟨e.1, e.2.1⟩ : Σ i, S.Op i) = ⟨j, op⟩ then
      entered (k (cast (congrArg (fun o : Σ i, S.Op i => S.Resp o.2) h) e.2.2)) t infl
    else none

/-- The in-flight call (if any) is the residual's next call. -/
def nextIs : (Σ j, Prot S Hole A j) → Option (Σ i, S.Op i) → Bool
  | _, none => true
  | ⟨j, .call op _⟩, some o => decide (o = ⟨j, op⟩)
  | _, some _ => false

/-- The replan guard (a `#tooth` mutation target): the hole the history has entered, which no replan may touch. -/
def frozenHole {Tok Fact Ob : Type} {i : Ix} (O : Open S Hole A Tok Fact Ob i) :
    Option (Σ j, Hole j) :=
  entered O.template O.hist.answered O.hist.inflight.isSome

/-- The hole a dispatch of the residual's next call would enter: the call belongs to that hole's
decision (`UsesChoice`). -/
def owner {Tok Fact Ob : Type} {i : Ix} (O : Open S Hole A Tok Fact Ob i) : Option (Σ j, Hole j) :=
  entered O.template O.hist.answered true

/-- The decision guard (a `#tooth` mutation target): the cited facts of the hole the call
belongs to that do not hold now. -/
def decisionDead {Tok Fact Ob : Type} {i : Ix} (O : Open S Hole A Tok Fact Ob i)
    (cites : (j : Ix) → Hole j → List Fact) (v : View Tok Fact) : List Fact :=
  match owner O with
  | some ⟨j, h⟩ => (cites j h).filter fun f => !v.holds f
  | none => []

variable [DecidableEq Ix] [∀ i, DecidableEq (Hole i)]

/-- The citations with hole `h`'s replaced. -/
def setCites {Fact : Type} (cs : (j : Ix) → Hole j → List Fact) {j : Ix} (h : Hole j)
    (fs : List Fact) : (j : Ix) → Hole j → List Fact :=
  fun i h' => if (⟨i, h'⟩ : Σ j, Hole j) = ⟨j, h⟩ then fs else cs i h'

/-- `σ` with hole `h` filled by `f`. -/
def setHole (σ : Subst S Hole A) {j : Ix} (h : Hole j) (f : Prot S Hole A j) : Subst S Hole A :=
  fun i h' =>
    if e : (⟨i, h'⟩ : Σ j, Hole j) = ⟨j, h⟩ then
      some (cast (congrArg (fun x : Σ j, Hole j => Prot S Hole A x.1) e).symm f)
    else σ i h'

/-- `h` is a hole of `Ω` that this party chooses. -/
def isMine {Tok Fact Ob : Type} (Ω : Ctx S Hole A Tok Fact Ob) {j : Ix} (h : Hole j) : Bool :=
  match Ω j h with
  | some I => decide (I.chooser = .me)
  | none => false

/-! ## The runner -/

variable {Tok Fact Ob V : Type} [DecidableEq Tok]

/-- One raw proposed event: the next configuration, or a refusal. -/
def run (host : Host V Tok Fact) (sp : Spec S Tok Fact Ob) {i : Ix}
    (c : Cfg S Hole A Tok Fact Ob V i) :
    Event S Hole A Fact V → Except (Refusal S Hole Tok Fact) (Cfg S Hole A Tok Fact Ob V i)
  | .world v' =>
    if host.allowed c.world v' then .ok { c with world := v', log := c.log ++ [.world v'] }
    else .error .worldStep
  | .replan (j := j) h f fs =>
    match closedBy c with
    | some e => .error (.abandoned e)
    | none =>
    if !isMine c.obj.Ω h then .error (.notMine ⟨j, h⟩)
    else if frozenHole c.obj = some ⟨j, h⟩ then
      match c.obj.hist.inflight with
      | some o => .error (.replacesInflight o ⟨j, h⟩)
      | none => .error (.replacesAnswered ⟨j, h⟩)
    else
      let O' := c.obj.replan (setHole c.obj.σ h f)
      match advance ⟨i, O'.current⟩ c.obj.hist.answered with
      | some R =>
        if nextIs R c.obj.hist.inflight then
          .ok { c with
            obj := O'
            res := R
            cites := setCites c.cites h fs
            log := c.log ++ [.replan h f fs] }
        else .error .inconsistent
      | none => .error .inconsistent
  | .dispatch o =>
    match closedBy c with
    | some e => .error (.abandoned e)
    | none =>
    match awaiting c.obj.hist with
    | some o' => .error (.busy o')
    | none =>
      match c.res with
      | ⟨j, .call op _⟩ =>
        if o = ⟨j, op⟩ then
          if dispatchGuard sp (c.admitView host) op then
            match decisionDead c.obj c.cites (c.admitView host) with
            | [] => .ok { c with
              obj := { c.obj with hist := ⟨c.obj.hist.answered, some ⟨j, op⟩⟩ }
              spent := spendOn sp c.spent op
              log := c.log ++ [.dispatch ⟨j, op⟩] }
            | d =>
              .error (.unsupported ⟨j, op⟩ (owner c.obj) d)
          else
            let m := missingOf sp (c.admitView host) op
            .error (.unadmitted ⟨j, op⟩ m.1 m.2)
        else .error (.notNext o)
      | _ => .error (.notNext o)
  | .respond e =>
    match closedBy c with
    | some e' => .error (.abandoned e')
    | none =>
    match c.obj.hist.inflight with
    | none => .error (.unsolicited e)
    | some o =>
      if (⟨e.1, e.2.1⟩ : Σ i, S.Op i) = o then
        match follow c.res e with
        | some R =>
          .ok { c with
            obj := { c.obj with hist := ⟨c.obj.hist.answered ++ [e], none⟩ }
            res := R
            log := c.log ++ [.respond e] }
        | none => .error (.unsolicited e)
      else .error (.unsolicited e)
  | .abandon o =>
    match closedBy c with
    | some e => .error (.abandoned e)
    | none =>
      match awaiting c.obj.hist with
      | some o' =>
        if o = o' then .ok { c with ended := some o, log := c.log ++ [.abandon o] }
        else .error (.notInflight o)
      | none => .error (.notInflight o)

/-- The configurations the runner reaches from `c₀` by accepted events. -/
inductive Reachable (host : Host V Tok Fact) (sp : Spec S Tok Fact Ob) {i : Ix}
    (c₀ : Cfg S Hole A Tok Fact Ob V i) : Cfg S Hole A Tok Fact Ob V i → Prop
  | init : Reachable host sp c₀ c₀
  | step {c c' : Cfg S Hole A Tok Fact Ob V i} (ev : Event S Hole A Fact V) :
      Reachable host sp c₀ c → run host sp c ev = .ok c' → Reachable host sp c₀ c'

/-- A session: every proposed event in order, each accepted or refused; a refused event leaves the
configuration as it was. The receipt pairs each event's index with its refusal, if any. -/
def session (host : Host V Tok Fact) (sp : Spec S Tok Fact Ob) {i : Ix} :
    Cfg S Hole A Tok Fact Ob V i → List (Event S Hole A Fact V) →
      Cfg S Hole A Tok Fact Ob V i × List (Option (Refusal S Hole Tok Fact))
  | c, [] => (c, [])
  | c, ev :: evs =>
    match run host sp c ev with
    | .ok c' => let r := session host sp c' evs; (r.1, none :: r.2)
    | .error w => let r := session host sp c evs; (r.1, some w :: r.2)

/-! ## Driven by a handler -/

/-- How a handler-driven run ends. -/
inductive Drive (S : Sig Ix) (Hole : Ix → Type) (A : Ix → Type) (Tok Fact Ob V St : Type) (i : Ix) where
  /-- the residual is a result or a hole: nothing more to dispatch -/
  | halted (c : Cfg S Hole A Tok Fact Ob V i) (s : St)
  /-- the runner refused the residual's next call: the handler never saw it -/
  | refused (c : Cfg S Hole A Tok Fact Ob V i) (w : Refusal S Hole Tok Fact) (s : St)
  /-- out of fuel -/
  | fuel (c : Cfg S Hole A Tok Fact Ob V i) (s : St)

/-- Drive the runner with a handler (over a state that does not vary with the index): dispatch the
residual's next call; only once the runner has accepted it (admitted, token spent) does the handler
see it; its reply is the response event. The world does not move. -/
def drive {St : Type} (host : Host V Tok Fact) (sp : Spec S Tok Fact Ob)
    (H : Handler S (fun _ => St)) {i : Ix} :
    Nat → Cfg S Hole A Tok Fact Ob V i → St → Drive S Hole A Tok Fact Ob V St i
  | 0, c, s => .fuel c s
  | n + 1, c, s =>
    match c.res with
    | ⟨j, .call op _⟩ =>
      match run host sp c (.dispatch ⟨j, op⟩) with
      | .error w => .refused c w s
      | .ok c' =>
        match H.handle op s with
        | ⟨r, s'⟩ =>
          match run host sp c' (.respond ⟨j, op, r⟩) with
          | .error w => .refused c' w s'
          | .ok c'' => drive host sp H n c'' s'
    | _ => .halted c s

/-- A halted run read as `interpret`'s result. -/
def Drive.result? {St : Type} {i : Ix} :
    Drive S Hole A Tok Fact Ob V St i → Option (Result Hole A (fun _ => St))
  | .halted c s => match c.res with
    | ⟨j, .ret a⟩ => some (.done j a s)
    | ⟨j, .hole h⟩ => some (.stuck j h s)
    | ⟨_, .call _ _⟩ => none
  | _ => none

/-- The refusal a driven run stopped at, if any. -/
def Drive.refusal? {St : Type} {i : Ix} :
    Drive S Hole A Tok Fact Ob V St i → Option (Refusal S Hole Tok Fact)
  | .refused _ w _ => some w
  | _ => none

/-- The handler's state where a driven run stopped. -/
def Drive.state {St : Type} {i : Ix} : Drive S Hole A Tok Fact Ob V St i → St
  | .halted _ s => s
  | .refused _ _ s => s
  | .fuel _ s => s

/-! ## Replanning by a slot -/

/-- Re-resolve hole `h` by a slot at the current world: the replan event for the first usable
candidate's body, or the slot's refusal naming every candidate's dead supports. -/
def resolveEvent {Cand : Type} (host : Host V Tok Fact) {i : Ix}
    (c : Cfg S Hole A Tok Fact Ob V i) (Sl : Slot Fact Cand) {j : Ix} (h : Hole j)
    (body : Cand → Prot S Hole A j) (order : List Cand) :
    Except (Slot.Refusal Fact Cand) (Event S Hole A Fact V) :=
  (Sl.select (host.view c.world).holds order).map fun cand => Event.replan h (body cand) (Sl.supports cand)

/-- The chooser's explicit choice of `cand` for hole `h` (an OVERRIDE when it supersedes a choice
that is still usable): its body, citing its supports. Its authority is the hole's chooser
(`isMine`), checked by `run`; it needs nothing of the choice it replaces. -/
def chooseEvent {Cand : Type} (Sl : Slot Fact Cand) {j : Ix} (h : Hole j)
    (body : Cand → Prot S Hole A j) (cand : Cand) : Event S Hole A Fact V :=
  .replan h (body cand) (Sl.supports cand)

/-- Re-resolve hole `h` by a stored-selection POLICY (`Obend.Slot.Advance`: how a stored selection
moves when the view changes; the slot's own is incumbent-first `slotAdvance`): the replan event for
the candidate the policy keeps or selects at the current world, or its refusal. -/
def resolveEventBy {Cand : Type} (adv : Advance V Fact Cand) {i : Ix}
    (c : Cfg S Hole A Tok Fact Ob V i) (Sl : Slot Fact Cand) {j : Ix} (h : Hole j)
    (body : Cand → Prot S Hole A j) (order : List Cand) (stored : Option Cand) :
    Except (Slot.Refusal Fact Cand) (Event S Hole A Fact V) :=
  (adv.advance Sl c.world order stored).map fun cand =>
    Event.replan h (body cand) (Sl.supports cand)

end

end Obend.Run

end
