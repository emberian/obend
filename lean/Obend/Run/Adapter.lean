module
/-
# Obend.Run.Adapter — the Core4 adapter, completed with live $O(T)$ `Checkpoint` stepping

`Obend.Run.Core4` runs an emitted Core4 activity through the guarded runner, with four gaps
(`lean/docs/REPORT-RUNNER-20261031.md` §9). Here each is closed by an adapter over the runner, with
the clause it adds to what an accepted log satisfies:

- **Response typing.** A reply is accepted only if it conforms to the activity's declared response
  type (`Data.conforms`, as `Spec.Preview.runTurns` checks): `ResponsesTyped`.
- **Depth deepening mid-run.** The activity's protocol is an unfolding to a depth; at the depth
  frontier the bare runner stops for good (`notNext`). `deepen m` extends the remaining unfolding
  depth by `m` (`stepCheckpoint` updates the live frontier in $O(1)$; cold `rebase` replays the
  accepted log from genesis).
- **Ticks exhausted within a turn.** A turn that runs out of ticks ends the bare protocol
  (`Stop.ended (.suspended .ticks _)`). `moreTicks m` increases the per-turn tick bound by `m`
  (`stepCheckpoint` updates `par.ticks` in $O(1)$ without replaying historical turns, because every
  already-yielded turn yields identically at `ticks + m`).
- **Choice points in emitted plans.** A yielded Plan the deployment reads as a choice among
  alternative Plans (`Deploy.alts`) is a CHOICE POINT: the unfolding stops at `Stop.choice` until a
  Plan is chosen for that position (`choose q`, the position being the number of answered calls),
  citing `Deploy.supports q` and rechecked at dispatch (`choiceUnsupported`): `ChoicesHeld`.

`Checkpoint` + `stepCheckpoint` + `checkpointSession` provide the $O(T)$ live adapter execution
engine (maintaining the live `frontier : State`, settled & garbage-collected `settled : State` via
`Obend.Core.Collect.checkpoint`, cached in-flight continuation state, and contiguous `Array`
buffers without replaying `Log` from `D.s₀`), proved equivalent to cold `Log` replay (`arun` /
`asession`) and refined against `Obend.Core.Collect.typed_checkpoint` in `Obend.Run.Proofs.Adapter`.
-/
public import Obend.Run.Core4
public import Obend.Slot.Integrity
public section

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

/-- Active Plan exposed at position `pos` when a turn yields `rawPlan` under `par`, if any. -/
def nextPlanOf (alts : Data → Option (List Data)) (par : Par) (pos : Nat) (rawPlan : Data) :
    Option Data :=
  match alts rawPlan with
  | none => some rawPlan
  | some as =>
    match choiceAt par.choices pos with
    | some q => if q ∈ as then some q else none
    | none => none

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

/-- What `q`'s choice cites that does not hold at world `w`. -/
def choiceDeadAt (D : Deploy Tok Fact Ob V) (host : Host V Tok Fact) (w : V) (q : Data) :
    List Fact :=
  (D.supports q).filter fun f => !(host.view w).holds f

/-- What `q`'s choice cites that does not hold at the current view. -/
def choiceDead (D : Deploy Tok Fact Ob V) (host : Host V Tok Fact) (c : ACfg' Tok Fact Ob V) (q : Data) :
    List Fact :=
  choiceDeadAt D host c.world q

variable [DecidableEq Tok]

/-- The first refused event of a replay, if any. -/
def firstRefused : List (Option (Refusal planSig NoHole Tok Fact)) → Option Nat
  | [] => none
  | none :: rs => (firstRefused rs).map (· + 1)
  | some _ :: _ => some 0

/-- Cold crash-recovery / specification re-base on `par'`: replay the accepted log from the
activity's start under `par'`. -/
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

/-- Reference adapter step (cold log-replay specification). -/
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

/-- Reference adapter session (cold log-replay specification). -/
def asession (D : Deploy Tok Fact Ob V) (host : Host V Tok Fact) (sp : Spec planSig Tok Fact Ob) :
    ACfg Tok Fact Ob V → List (AEvent V) → ACfg Tok Fact Ob V × List (Option (ARefusal Tok Fact))
  | a, [] => (a, [])
  | a, ev :: evs =>
    match arun D host sp a ev with
    | .ok a' => let r := asession D host sp a' evs; (r.1, none :: r.2)
    | .error w => let r := asession D host sp a evs; (r.1, some w :: r.2)

/-! ## Live $O(T)$ `Checkpoint` State & Zero-Replay Adapter Engine -/

/-- Live $O(T)$ adapter `Checkpoint` state eliminating $O(M^2 T)$ full-history `Log` replay:
- `frontier`: live machine state $s_k$ after $k = \text{answered.size}$ answered calls;
- `settled`: settled & garbage-collected checkpoint `Obend.Core.Collect.checkpoint y` of the
  latest extracted yield (initialized to `Obend.Core.Collect.checkpoint D.s₀`), refined against
  `Obend.Core.Collect.typed_checkpoint`;
- `inflight`: `some (dispPlan, y)` when call `dispPlan` is in flight with yielded continuation
  state `y`, enabling $O(1)$ `resume` on `.respond`;
- `remDepth`: remaining unfolding depth (`par.depth - answered.size`);
- `spent`, `answered`, `log`: contiguous `Array` buffers updated via `Array.push`. -/
structure Checkpoint (Tok Fact Ob V : Type) where
  par : Par
  frontier : State
  settled : State
  inflight : Option (Data × State)
  remDepth : Nat
  world : V
  spent : Array Tok
  answered : Array (Entry planSig)
  log : Array (Event planSig NoHole (fun _ => Stop) Fact V)
  ended : Option Data

omit [DecidableEq Tok] in
/-- Initial live `Checkpoint` at `D.s₀` and `D.v₀` under `par`. -/
def Checkpoint.init (D : Deploy Tok Fact Ob V) (par : Par) : Checkpoint Tok Fact Ob V where
  par := par
  frontier := D.s₀
  settled := Obend.Core.Collect.checkpoint D.s₀
  inflight := none
  remDepth := par.depth
  world := D.v₀
  spent := #[]
  answered := #[]
  log := #[]
  ended := none

omit [DecidableEq Tok] in
/-- Refinement projection from a live `Checkpoint` to its specification `ACfg`. -/
def Checkpoint.toACfg (D : Deploy Tok Fact Ob V) (ck : Checkpoint Tok Fact Ob V) :
    ACfg Tok Fact Ob V :=
  let O := D.obj ck.par
  ⟨ck.par,
    { obj := { O with hist := ⟨ck.answered.toList, ck.inflight.map fun x => ⟨(), x.1⟩⟩ }
      world := ck.world
      spent := ck.spent.toList
      res := ⟨(), aunfold D.L D.budget D.alts ck.par ck.answered.size ck.remDepth ck.frontier⟩
      log := ck.log.toList
      ended := ck.ended.map fun p => ⟨(), p⟩
      cites := fun _ _ => [] }⟩

omit [DecidableEq Tok] in
/-- Live choice guard on `Checkpoint` (`O(1)` lookup at `ck.answered.size`, a `#tooth` target). -/
def choiceGuardCheckpoint (D : Deploy Tok Fact Ob V) (host : Host V Tok Fact)
    (ck : Checkpoint Tok Fact Ob V) (p : Data) : List Fact :=
  match choiceAt ck.par.choices ck.answered.size with
  | some q => if q = p then choiceDeadAt D host ck.world q else []
  | none => []

private def pushConsumedTok (spent : Array Tok) : Option Tok → Array Tok
  | some t => spent.push t
  | none => spent

/-- Live $O(T)$ single-event adapter transition on `Checkpoint` (a `#tooth` mutation target):
executes `.world`, `.abandon`, `.respond`, `.deepen`, and `.moreTicks` in $O(1)$ without running
`turn` or replaying `ck.log`, and executes `.dispatch` and `.choose` via a single `turnFast` call
at `ck.frontier`. -/
def stepCheckpoint (D : Deploy Tok Fact Ob V) (host : Host V Tok Fact)
    (sp : Spec planSig Tok Fact Ob) (ck : Checkpoint Tok Fact Ob V) :
    AEvent V → Except (ARefusal Tok Fact) (Checkpoint Tok Fact Ob V)
  | .world v' =>
    if host.allowed ck.world v' then
      .ok { ck with world := v', log := ck.log.push (.world v') }
    else
      .error (.run .worldStep)
  | .abandon p =>
    match ck.ended with
    | some e => .error (.run (.abandoned ⟨(), e⟩))
    | none =>
      match ck.inflight with
      | some (o', _) =>
        if p = o' then
          .ok { ck with ended := some p, log := ck.log.push (.abandon ⟨(), p⟩) }
        else
          .error (.run (.notInflight ⟨(), p⟩))
      | none => .error (.run (.notInflight ⟨(), p⟩))
  | .respond p r =>
    if typedReply D r then
      match ck.ended with
      | some e => .error (.run (.abandoned ⟨(), e⟩))
      | none =>
        match ck.inflight with
        | none => .error (.run (.unsolicited ⟨(), p, r⟩))
        | some (o', y) =>
          if p = o' then
            match resume r.term y with
            | some s' =>
              .ok { ck with
                frontier := s'
                inflight := none
                remDepth := ck.remDepth - 1
                answered := ck.answered.push ⟨(), o', r⟩
                log := ck.log.push (.respond ⟨(), o', r⟩) }
            | none => .error (.run (.unsolicited ⟨(), p, r⟩))
          else
            .error (.run (.unsolicited ⟨(), p, r⟩))
    else
      .error (.illTyped p r)
  | .dispatch p =>
    match choiceGuardCheckpoint D host ck p with
    | d@(_ :: _) => .error (.choiceUnsupported p d)
    | [] =>
      match ck.ended with
      | some e => .error (.run (.abandoned ⟨(), e⟩))
      | none =>
        match ck.inflight with
        | some (o', _) => .error (.run (.busy ⟨(), o'⟩))
        | none =>
          match ck.remDepth with
          | 0 => .error (.run (.notNext ⟨(), p⟩))
          | _ + 1 =>
            match turnFast D.L ck.par.ticks D.budget ck.frontier with
            | .stop _ => .error (.run (.notNext ⟨(), p⟩))
            | .vis rawPlan y =>
              match nextPlanOf D.alts ck.par ck.answered.size rawPlan with
              | none => .error (.run (.notNext ⟨(), p⟩))
              | some op =>
                if p = op then
                  let v := View.maskArray (host.view ck.world) ck.spent
                  if dispatchGuard (S := planSig) (i := ()) sp v op then
                    .ok { ck with
                      inflight := some (op, y)
                      settled := Obend.Core.Collect.checkpoint y
                      spent := pushConsumedTok ck.spent (sp.consumes (i := ()) op)
                      log := ck.log.push (.dispatch ⟨(), op⟩) }
                  else
                    let m := missingOf (S := planSig) (i := ()) sp v op
                    .error (.run (.unadmitted ⟨(), op⟩ m.1 m.2))
                else
                  .error (.run (.notNext ⟨(), p⟩))
  | .deepen m =>
    .ok { ck with
      par := { ck.par with depth := ck.par.depth + m }
      remDepth := ck.remDepth + m }
  | .moreTicks m =>
    .ok { ck with
      par := { ck.par with ticks := ck.par.ticks + m } }
  | .choose q =>
    if ck.inflight.isSome then .error .busy
    else
      match choiceDeadAt D host ck.world q with
      | d@(_ :: _) => .error (.choiceUnsupported q d)
      | [] =>
        match ck.remDepth with
        | 0 => .error (.notAlternative q)
        | _ + 1 =>
          match turnFast D.L ck.par.ticks D.budget ck.frontier with
          | .stop _ => .error (.notAlternative q)
          | .vis rawPlan _ =>
            let okAlt : Bool :=
              match D.alts rawPlan with
              | none => decide (rawPlan = q)
              | some as => decide (q ∈ as)
            if okAlt then
              .ok { ck with
                par := { ck.par with choices := setChoice ck.par.choices ck.answered.size q } }
            else
              .error (.notAlternative q)

/-- Live `Checkpoint` configurations reachable from `ck₀` via `stepCheckpoint`. -/
inductive CheckpointReachable (D : Deploy Tok Fact Ob V) (host : Host V Tok Fact)
    (sp : Spec planSig Tok Fact Ob) (ck₀ : Checkpoint Tok Fact Ob V) :
    Checkpoint Tok Fact Ob V → Prop
  | init : CheckpointReachable D host sp ck₀ ck₀
  | step {ck ck' : Checkpoint Tok Fact Ob V} (ev : AEvent V) :
      CheckpointReachable D host sp ck₀ ck →
      stepCheckpoint D host sp ck ev = .ok ck' →
      CheckpointReachable D host sp ck₀ ck'

/-- Multi-turn live `Checkpoint` session running `evs` in $O(M \cdot T)$ total work without log replay. -/
def checkpointSession (D : Deploy Tok Fact Ob V) (host : Host V Tok Fact)
    (sp : Spec planSig Tok Fact Ob) :
    Checkpoint Tok Fact Ob V → List (AEvent V) →
      Checkpoint Tok Fact Ob V × List (Option (ARefusal Tok Fact))
  | ck, [] => (ck, [])
  | ck, ev :: evs =>
    match stepCheckpoint D host sp ck ev with
    | .ok ck' => let r := checkpointSession D host sp ck' evs; (r.1, none :: r.2)
    | .error w => let r := checkpointSession D host sp ck evs; (r.1, some w :: r.2)

end Obend.Run.Core4

end
