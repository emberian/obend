module
/-
# Obend.Run.Adapter — the Core4 adapter, completed

`Obend.Run.Core4` runs an emitted Core4 activity through the guarded runner, with four gaps
(`lean/docs/REPORT-RUNNER-20261031.md` §9). Here each is closed by an adapter over the runner, with
the clause it adds to what an accepted log satisfies and a fixture the bare adapter got wrong
(`Obend.Run.Core4Example`):

- **Response typing.** A reply is accepted only if it conforms to the activity's declared response
  type (`Data.conforms`, as `Spec.Preview.runTurns` checks): `ResponsesTyped`.
- **Depth deepening mid-run.** The activity's protocol is an unfolding to a depth; at the depth
  frontier the bare runner stops for good (`notNext`). `deepen m` re-bases the run on the unfolding
  `m` deeper: the SAME accepted log replayed from the activity's start (`rebase`). The run is then a
  run of the deeper activity: its log is `Legal` for it.
- **Ticks exhausted within a turn.** A turn that runs out of ticks ends the bare protocol
  (`Stop.ended (.suspended .ticks _)`). `moreTicks m` re-bases on the unfolding whose turns have `m`
  more ticks; the same log replays, and the turn the ticks cut short now yields.
- **Choice points in emitted plans.** A yielded Plan the deployment reads as a choice among
  alternative Plans (`Deploy.alts`) is a CHOICE POINT: the bare adapter would dispatch the Plan
  itself; here the unfolding stops there (`Stop.choice`) until a Plan is chosen for that position
  (`choose q`, the position being the number of answered calls), and the choice is a decision citing
  `Deploy.supports q`, rechecked at its dispatch (`choiceUnsupported`): `ChoicesHeld`. A slot over the
  alternatives (`chooseBy`) makes the choice by any stored-selection policy, so the selection
  machinery reaches Core4 plans. A choice can be changed until its Plan is dispatched, never after.

A re-base is checked when it is made: every event of the old log must be accepted again, else the
re-base is refused (`replay`); `Obend.Run.Proofs.Adapter` proves what holds of every adapter run.
-/
public import Obend.Run.Core4
public import Obend.Slot.Integrity
@[expose] public section

namespace Obend.Run.Core4

open Obend.Slot Obend.Slot.Protocol Obend.Core.Machine Obend.Core.Data

/-- The adapter's parameters of the activity's unfolding. -/
structure Par where
  depth : Nat
  ticks : Nat
  /-- the Plan chosen at each choice point, by its position (the answered calls before it) -/
  choices : List (Nat × Data)

/-- The Plan chosen at position `pos`, if any. -/
def choiceAt (cs : List (Nat × Data)) (pos : Nat) : Option Data :=
  (cs.find? fun e => e.1 == pos).map Prod.snd

/-- Choose `q` at position `pos`, replacing any earlier choice there. -/
def setChoice (cs : List (Nat × Data)) (pos : Nat) (q : Data) : List (Nat × Data) :=
  (pos, q) :: cs.filter fun e => e.1 != pos

/-- The activity at `s`, at position `pos`, unfolded `n` turns deep under `par`: each yielded Plan
is a call, except a choice point, which is the call of the Plan chosen at its position if that is
one of its alternatives, and otherwise the frontier `Stop.choice`. -/
def aunfold (L : Limits) (budget : Budget) (alts : Data → Option (List Data)) (par : Par) :
    Nat → Nat → State → P
  | _, 0, _ => .ret .depth
  | pos, n + 1, s =>
    match turn L par.ticks budget s with
    | .vis p y =>
      match alts p with
      | none => .call (S := planSig) p fun r =>
        match resume r.term y with
        | some s' => aunfold L budget alts par (pos + 1) n s'
        | none => .ret .unresumable
      | some as =>
        match choiceAt par.choices pos with
        | some q =>
          if q ∈ as then .call (S := planSig) q fun r =>
            match resume r.term y with
            | some s' => aunfold L budget alts par (pos + 1) n s'
            | none => .ret .unresumable
          else .ret (.choice as)
        | none => .ret (.choice as)
    | .stop x => .ret x

/-- What a deployment fixes of an activity run through the adapter. -/
structure Deploy (Tok Fact Ob V : Type) where
  L : Limits
  budget : Budget
  /-- which yielded Plans are choice points, and their alternatives -/
  alts : Data → Option (List Data)
  /-- the declared response type -/
  resp : Obend.Core.Ty.Ty
  /-- what choosing a Plan cites: rechecked when the chosen Plan is dispatched -/
  supports : Data → List Fact
  s₀ : State
  Γ : List Fact
  Δ : List Tok
  Φ : List Ob
  v₀ : V

variable {Tok Fact Ob V : Type}

/-- The activity's open object under `par`. -/
def Deploy.obj (D : Deploy Tok Fact Ob V) (par : Par) : Open planSig NoHole (fun _ => Stop) Tok Fact Ob () :=
  { activity D.L par.ticks D.budget par.depth D.s₀ D.Γ D.Δ D.Φ with
    template := aunfold D.L D.budget D.alts par 0 par.depth D.s₀ }

abbrev ACfg' (Tok Fact Ob V : Type) := Cfg planSig NoHole (fun _ => Stop) Tok Fact Ob V ()

/-- An adapter configuration: the parameters, and the runner's configuration of the activity under
them. -/
structure ACfg (Tok Fact Ob V : Type) where
  par : Par
  cfg : ACfg' Tok Fact Ob V

/-- An adapter event. -/
inductive AEvent (V : Type) where
  | world (v : V)
  | dispatch (p : Data)
  | respond (p r : Data)
  | abandon (p : Data)
  /-- unfold `m` turns deeper -/
  | deepen (m : Nat)
  /-- give every turn `m` more ticks -/
  | moreTicks (m : Nat)
  /-- choose `q` at the choice point the run is at -/
  | choose (q : Data)

/-- Why the adapter refused an event. -/
inductive ARefusal (Tok Fact : Type) where
  | run (r : Refusal planSig NoHole Tok Fact)
  /-- the reply does not conform to the declared response type -/
  | illTyped (p r : Data)
  /-- the chosen Plan's cited supports that do not hold now -/
  | choiceUnsupported (q : Data) (dead : List Fact)
  /-- `q` is not an alternative of the choice point the run is at -/
  | notAlternative (q : Data)
  /-- a call is in flight: no choice now -/
  | busy
  /-- the old log is not accepted again under the new parameters (event `n`) -/
  | replay (n : Nat)

/-- What `q`'s choice cites that does not hold at the current view. -/
def choiceDead (D : Deploy Tok Fact Ob V) (host : Host V Tok Fact) (c : ACfg' Tok Fact Ob V) (q : Data) :
    List Fact :=
  (D.supports q).filter fun f => !(host.view c.world).holds f

variable [DecidableEq Tok]

/-- The first refused event of a replay, if any. -/
def firstRefused : List (Option (Refusal planSig NoHole Tok Fact)) → Option Nat
  | [] => none
  | none :: rs => (firstRefused rs).map (· + 1)
  | some _ :: _ => some 0

/-- Re-base on `par'`: replay the accepted log from the activity's start under `par'`. -/
def rebase (D : Deploy Tok Fact Ob V) (host : Host V Tok Fact) (sp : Spec planSig Tok Fact Ob)
    (a : ACfg Tok Fact Ob V) (par' : Par) : Except (ARefusal Tok Fact) (ACfg Tok Fact Ob V) :=
  let r := session host sp (Cfg.init (D.obj par') D.v₀) a.cfg.log
  match firstRefused r.2 with
  | some n => .error (.replay n)
  | none => .ok ⟨par', r.1⟩

def lift (a : ACfg Tok Fact Ob V)
    (r : Except (Refusal planSig NoHole Tok Fact) (ACfg' Tok Fact Ob V)) :
    Except (ARefusal Tok Fact) (ACfg Tok Fact Ob V) :=
  match r with
  | .ok c => .ok ⟨a.par, c⟩
  | .error w => .error (.run w)

/-- The adapter's choice guard (a `#tooth` mutation target): what the Plan chosen at the run's
position, if `p` is it, cites that does not hold now. -/
def choiceGuard (D : Deploy Tok Fact Ob V) (host : Host V Tok Fact) (a : ACfg Tok Fact Ob V) (p : Data) :
    List Fact :=
  match choiceAt a.par.choices a.cfg.obj.hist.answered.length with
  | some q => if q = p then choiceDead D host a.cfg q else []
  | none => []

/-- The response guard (a `#tooth` mutation target). -/
def typedReply (D : Deploy Tok Fact Ob V) (r : Data) : Bool := r.conforms D.resp

/-- One adapter event. -/
def arun (D : Deploy Tok Fact Ob V) (host : Host V Tok Fact) (sp : Spec planSig Tok Fact Ob)
    (a : ACfg Tok Fact Ob V) : AEvent V → Except (ARefusal Tok Fact) (ACfg Tok Fact Ob V)
  | .world v => lift a (run host sp a.cfg (.world v))
  | .abandon p => lift a (run host sp a.cfg (.abandon ⟨(), p⟩))
  | .respond p r =>
    if typedReply D r then lift a (run host sp a.cfg (.respond ⟨(), p, r⟩))
    else .error (.illTyped p r)
  | .dispatch p =>
    match choiceGuard D host a p with
    | [] => lift a (run host sp a.cfg (.dispatch ⟨(), p⟩))
    | d => .error (.choiceUnsupported p d)
  | .deepen m => rebase D host sp a { a.par with depth := a.par.depth + m }
  | .moreTicks m => rebase D host sp a { a.par with ticks := a.par.ticks + m }
  | .choose q =>
    if a.cfg.obj.hist.inflight.isSome then .error .busy
    else match choiceDead D host a.cfg q with
      | [] =>
        match rebase D host sp a { a.par with
            choices := setChoice a.par.choices a.cfg.obj.hist.answered.length q } with
        | .error w => .error w
        | .ok a' =>
          match a'.cfg.res with
          | ⟨(), .call p _⟩ => if decData p q matches .isTrue _ then .ok a' else .error (.notAlternative q)
          | _ => .error (.notAlternative q)
      | d => .error (.choiceUnsupported q d)

/-- Choose at the run's choice point by a stored-selection policy over a slot of alternatives: the
policy's candidate, or its refusal naming every alternative's dead supports. -/
def chooseBy {Cand : Type} [Obend.Slot.World V Fact] (adv : Advance V Fact Cand) (a : ACfg Tok Fact Ob V)
    (Sl : Slot Fact Cand) (plan : Cand → Data) (order : List Cand) (stored : Option Cand) :
    Except (Obend.Slot.Refusal Fact Cand) (AEvent V) :=
  (adv.advance Sl a.cfg.world order stored).map fun c => .choose (plan c)

/-- The adapter configurations reachable from `a₀`. -/
inductive AReachable (D : Deploy Tok Fact Ob V) (host : Host V Tok Fact) (sp : Spec planSig Tok Fact Ob)
    (a₀ : ACfg Tok Fact Ob V) : ACfg Tok Fact Ob V → Prop
  | init : AReachable D host sp a₀ a₀
  | step {a a' : ACfg Tok Fact Ob V} (ev : AEvent V) :
      AReachable D host sp a₀ a → arun D host sp a ev = .ok a' → AReachable D host sp a₀ a'

/-- The start under `par`. -/
def Deploy.start (D : Deploy Tok Fact Ob V) (par : Par) : ACfg Tok Fact Ob V :=
  ⟨par, Cfg.init (D.obj par) D.v₀⟩

/-- An adapter session. -/
def asession (D : Deploy Tok Fact Ob V) (host : Host V Tok Fact) (sp : Spec planSig Tok Fact Ob) :
    ACfg Tok Fact Ob V → List (AEvent V) → ACfg Tok Fact Ob V × List (Option (ARefusal Tok Fact))
  | a, [] => (a, [])
  | a, ev :: evs =>
    match arun D host sp a ev with
    | .ok a' => let r := asession D host sp a' evs; (r.1, none :: r.2)
    | .error w => let r := asession D host sp a evs; (r.1, some w :: r.2)

end Obend.Run.Core4

end
