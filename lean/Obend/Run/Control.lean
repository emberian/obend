module
/-
# Obend.Run.Control — who may decide a slot, under which policy, and what a decision keeps

`astra/ASTRA-SELECTION-20261031.md` §7–8, on top of the guarded runner. The runner's own authority
for a replan is the hole's `.me` chooser: whoever can submit an event is the chooser, and a
decision cites only its candidate's supports. This layer puts a SELECTION CONTROL descriptor beside
each controlled slot and decides it only through that descriptor:

- **Authenticated principals.** A choice is made by a principal `p` with a credential the
  deployment verifies (`Authority.verify`), and only while `p` holds the slot's chooser OFFICE: the
  host fact `Descriptor.office p`, judged at the world current when the choice is made.
- **Decision revisions.** Each controlled slot counts its accepted decisions; a choice names the
  revision it was made against, and a stale one is refused (`staleRevision`): two choosers racing
  on one slot cannot both be accepted against the same revision.
- **What a choice keeps across an office change**, declared per slot (`Tenure`): a `lasting`
  choice survives its chooser leaving office; a `whileInOffice` choice cites the chooser's office
  with its candidate's supports, so the runner's dispatch guard (`decisionDead`) refuses every call
  in the hole once the chooser is out of office. Nothing new is needed of the runner: the
  continuing condition of a decision is a citation.
- **The policy presets** (`Preset`): `firstUsable` (the first usable candidate of the domain at
  every advance, canonical replay), `incumbentFirst` (the stored choice while it is usable, else the
  first usable), `chooserRequired` (the stored choice while it is usable; otherwise nothing is
  installed automatically and the slot awaits its chooser). `Suspension.reapproval` LATCHES: a stored
  choice that was unusable at some world since it was made is not kept again automatically.
  `Descriptor.override` says whether a chooser may supersede a stored choice that is still usable.
- **Honest outcomes** (`Outcome`): `kept`, `chosen`, `awaiting` (a chooser is required and some
  permitted candidate is usable) and `nothingAdmissible`, each non-installing outcome with the EXACT
  diagnostics of every candidate of the domain (`diagnostics`: rejected by the judge, or its dead
  supports, or usable).

Raw replans of a controlled hole are refused (`rawReplan`); every other event goes to `run`
unchanged, so the controlled runner's reachable configurations are the runner's
(`Obend.Run.Proofs.Control.creachable_reachable`) and every theorem of the runner holds of them.
-/
public import Obend.Run.Runner
public import Obend.Slot.Selection
@[expose] public section

namespace Obend.Run.Control

open Obend.Slot Obend.Slot.Protocol

/-- The policy presets of a controlled slot. -/
inductive Preset where
  | firstUsable
  | incumbentFirst
  | chooserRequired
  deriving DecidableEq, Repr

/-- What a duly made choice needs to stay in force when its chooser leaves office. -/
inductive Tenure where
  /-- the choice survives its chooser leaving office -/
  | lasting
  /-- the choice cites its chooser's office: void at dispatch once the chooser is out of office -/
  | whileInOffice
  deriving DecidableEq, Repr

/-- Whether a stored choice that was unusable recovers automatically when it is usable again. -/
inductive Suspension where
  | automatic
  | reapproval
  deriving DecidableEq, Repr

/-- The per-slot selection control descriptor (Astra §8): the chooser office, the policy, the
admitted candidate domain in preference order, override rights, tenure and suspension. -/
structure Descriptor (P Fact Cand : Type) where
  /-- the host fact "principal `p` holds this slot's chooser office" -/
  office : P → Fact
  preset : Preset
  /-- the admitted candidates, in preference order -/
  domain : List Cand
  /-- the descriptor's version (a changed domain or policy is a new version) -/
  version : Nat
  /-- may a chooser supersede a stored choice that is still usable -/
  override : Bool
  tenure : Tenure
  suspension : Suspension

/-- The deployment's authentication of principals. -/
structure Authority (P Cred : Type) where
  verify : P → Cred → Bool

/-- What a candidate is at a view, exactly. -/
inductive Diag (Fact : Type) where
  /-- the judge rejects it -/
  | rejected
  /-- it passes the judge; these cited supports do not hold (at least one) -/
  | dead (fs : List Fact)
  /-- it passes the judge and every cited support holds -/
  | usable
  deriving DecidableEq, Repr

section
variable {P Fact Cand : Type} [DecidableEq Cand]

/-- One candidate's diagnosis at a view. -/
def diagnose (S : Slot Fact Cand) (holds : Fact → Bool) (c : Cand) : Diag Fact :=
  if S.judge c then
    match S.dead holds c with
    | [] => .usable
    | d => .dead d
  else .rejected

/-- The exact diagnostics of every candidate of the domain, in order. -/
def diagnostics (S : Slot Fact Cand) (D : Descriptor P Fact Cand) (holds : Fact → Bool) :
    List (Cand × Diag Fact) :=
  D.domain.map fun c => (c, diagnose S holds c)

/-- The outcome of a policy at a view. -/
inductive Outcome (Fact Cand : Type) where
  /-- the stored choice stays -/
  | kept (c : Cand)
  /-- the policy installs `c` -/
  | chosen (c : Cand)
  /-- a chooser is required; nothing is installed; the domain, diagnosed -/
  | awaiting (diag : List (Cand × Diag Fact))
  /-- no candidate of the domain is usable; the domain, diagnosed -/
  | nothingAdmissible (diag : List (Cand × Diag Fact))
  deriving Repr

/-- The stored choice may be kept: it is in the domain, usable, and not latched. -/
def keepable (S : Slot Fact Cand) (D : Descriptor P Fact Cand) (holds : Fact → Bool)
    (latched : Bool) : Option Cand → Bool
  | some s => decide (s ∈ D.domain) && S.usable holds s && !latched
  | none => false

/-- What the policy does at a view, given the stored choice and whether it is latched. -/
def propose (S : Slot Fact Cand) (D : Descriptor P Fact Cand) (holds : Fact → Bool)
    (stored : Option Cand) (latched : Bool) : Outcome Fact Cand :=
  match D.preset with
  | .firstUsable =>
    match S.select holds D.domain with
    | .ok c => if stored = some c then .kept c else .chosen c
    | .error _ => .nothingAdmissible (diagnostics S D holds)
  | .incumbentFirst =>
    match stored, keepable S D holds latched stored with
    | some s, true => .kept s
    | _, _ =>
      match S.select holds D.domain with
      | .ok c => .chosen c
      | .error _ => .nothingAdmissible (diagnostics S D holds)
  | .chooserRequired =>
    match stored, keepable S D holds latched stored with
    | some s, true => .kept s
    | _, _ =>
      match S.select holds D.domain with
      | .ok _ => .awaiting (diagnostics S D holds)
      | .error _ => .nothingAdmissible (diagnostics S D holds)

/-- What a choice cites: its candidate's supports, and its chooser's office under `whileInOffice`. -/
def citesFor (S : Slot Fact Cand) (D : Descriptor P Fact Cand) (by_ : Option P) (c : Cand) :
    List Fact :=
  S.supports c ++
    match D.tenure, by_ with
    | .whileInOffice, some p => [D.office p]
    | _, _ => []

end

section
variable {Ix : Type} {S : Sig Ix} {Hole : Ix → Type} {A : Ix → Type}

/-- A controlled slot of hole type `j`: the slot, its descriptor, and each candidate's body. -/
structure SlotCtl (S : Sig Ix) (Hole : Ix → Type) (A : Ix → Type) (P Fact Cand : Type) (j : Ix) where
  slot : Slot Fact Cand
  desc : Descriptor P Fact Cand
  body : Cand → Prot S Hole A j

/-- A decision as recorded: the hole, the candidate, who made it (`none`: the policy), the
revision it was made against, the world it was made at, and the runner log's length then. -/
structure Decision (Hole : Ix → Type) (P Cand V : Type) where
  hole : Σ j, Hole j
  cand : Cand
  by_ : Option P
  rev : Nat
  world : V
  at_ : Nat

/-- A controlled configuration: the runner's, each controlled hole's stored choice and revision,
and the decisions accepted, in order. -/
structure CCfg (S : Sig Ix) (Hole : Ix → Type) (A : Ix → Type) (P Cand Tok Fact Ob V : Type) (i : Ix) where
  cfg : Cfg S Hole A Tok Fact Ob V i
  stored : (j : Ix) → Hole j → Option Cand
  rev : (j : Ix) → Hole j → Nat
  decisions : List (Decision Hole P Cand V)

/-- A controlled event. -/
inductive CEvent (S : Sig Ix) (Hole : Ix → Type) (A : Ix → Type) (P Cred Cand Fact V : Type) where
  /-- a runner event (a replan of a controlled hole is refused) -/
  | base (e : Event S Hole A Fact V)
  /-- run the slot's policy at the current world -/
  | advance {j : Ix} (h : Hole j)
  /-- principal `p`, with credential `cred`, chooses `c` for `h` against revision `expected` -/
  | choose (p : P) (cred : Cred) {j : Ix} (h : Hole j) (c : Cand) (expected : Nat)

/-- Why the controlled runner refused an event. -/
inductive CRefusal (S : Sig Ix) (Hole : Ix → Type) (P Cand Tok Fact : Type) where
  /-- the runner's own refusal -/
  | run (r : Refusal S Hole Tok Fact)
  /-- a controlled hole is decided only through its control -/
  | rawReplan (h : Σ j, Hole j)
  /-- the hole has no selection control -/
  | uncontrolled (h : Σ j, Hole j)
  /-- the credential does not authenticate the principal -/
  | unauthenticated (p : P)
  /-- the principal does not hold the slot's chooser office now -/
  | notChooser (p : P) (h : Σ j, Hole j)
  /-- the choice was made against another revision of the slot -/
  | staleRevision (h : Σ j, Hole j) (expected current : Nat)
  /-- the candidate is not in the slot's admitted domain -/
  | notPermitted (c : Cand)
  /-- the candidate is not usable now, exactly why -/
  | unusable (c : Cand) (why : Diag Fact)
  /-- the slot does not allow superseding the stored choice, which is still usable -/
  | noOverride (h : Σ j, Hole j) (stored : Cand)
  /-- the policy awaits its chooser; the domain, diagnosed -/
  | awaiting (h : Σ j, Hole j) (diag : List (Cand × Diag Fact))
  /-- no candidate of the domain is usable; the domain, diagnosed -/
  | nothingAdmissible (h : Σ j, Hole j) (diag : List (Cand × Diag Fact))

variable [DecidableEq Ix] [∀ i, DecidableEq (Hole i)]

/-- `g` with hole `h`'s value replaced. -/
def upd {β : Type} (g : (j : Ix) → Hole j → β) {j : Ix} (h : Hole j) (b : β) :
    (j : Ix) → Hole j → β :=
  fun i h' => if (⟨i, h'⟩ : Σ j, Hole j) = ⟨j, h⟩ then b else g i h'

variable {P Cred Cand Tok Fact Ob V : Type} [DecidableEq Tok] [DecidableEq Cand]
variable [DecidableEq (Σ i, S.Op i)]

/-- The worlds of a log, in order. -/
def worldsOf (log : List (Event S Hole A Fact V)) : List V :=
  log.filterMap fun e => match e with
    | .world v => some v
    | _ => none

/-- The stored choice of `h` is LATCHED: under `reapproval`, the slot's world was one at which it
was not usable at some world event since its decision. -/
def latchedOf (host : Host V Tok Fact) {i : Ix} (k : (j : Ix) → Hole j → Option (SlotCtl S Hole A P Fact Cand j))
    (c : CCfg S Hole A P Cand Tok Fact Ob V i) {j : Ix} (h : Hole j) : Bool :=
  match k j h, c.stored j h with
  | some K, some s =>
    match K.desc.suspension with
    | .automatic => false
    | .reapproval =>
      let since := match c.decisions.reverse.find? (fun d => decide (d.hole = ⟨j, h⟩)) with
        | some d => d.at_
        | none => 0
      (worldsOf (c.cfg.log.drop since)).any fun v => !K.slot.usable (host.view v).holds s
  | _, _ => false

/-- Install `cand` in `h` by a decision of `by_`: the runner's replan with the decision's
citations, then the stored choice, the revision and the decision record. -/
def install (host : Host V Tok Fact) (sp : Spec S Tok Fact Ob) {i : Ix}
    (c : CCfg S Hole A P Cand Tok Fact Ob V i) {j : Ix} (h : Hole j)
    (K : SlotCtl S Hole A P Fact Cand j) (by_ : Option P) (cand : Cand) :
    Except (CRefusal S Hole P Cand Tok Fact) (CCfg S Hole A P Cand Tok Fact Ob V i) :=
  match run host sp c.cfg (.replan h (K.body cand) (citesFor K.slot K.desc by_ cand)) with
  | .error r => .error (.run r)
  | .ok cfg' => .ok
    { cfg := cfg'
      stored := upd c.stored h (some cand)
      rev := upd c.rev h (c.rev j h + 1)
      decisions := c.decisions ++ [⟨⟨j, h⟩, cand, by_, c.rev j h, c.cfg.world, c.cfg.log.length⟩] }

/-- One controlled event. -/
def crun (host : Host V Tok Fact) (sp : Spec S Tok Fact Ob) (au : Authority P Cred)
    (k : (j : Ix) → Hole j → Option (SlotCtl S Hole A P Fact Cand j)) {i : Ix}
    (c : CCfg S Hole A P Cand Tok Fact Ob V i) :
    CEvent S Hole A P Cred Cand Fact V →
      Except (CRefusal S Hole P Cand Tok Fact) (CCfg S Hole A P Cand Tok Fact Ob V i)
  | .base e =>
    match e with
    | .replan (j := j) h f fs =>
      match k j h with
      | some _ => .error (.rawReplan ⟨j, h⟩)
      | none =>
        match run host sp c.cfg (.replan h f fs) with
        | .ok cfg' => .ok { c with cfg := cfg' }
        | .error r => .error (.run r)
    | e =>
      match run host sp c.cfg e with
      | .ok cfg' => .ok { c with cfg := cfg' }
      | .error r => .error (.run r)
  | .advance (j := j) h =>
    match k j h with
    | none => .error (.uncontrolled ⟨j, h⟩)
    | some K =>
      match propose K.slot K.desc (host.view c.cfg.world).holds (c.stored j h) (latchedOf host k c h) with
      | .kept _ => .ok c
      | .chosen cand => install host sp c h K none cand
      | .awaiting d => .error (.awaiting ⟨j, h⟩ d)
      | .nothingAdmissible d => .error (.nothingAdmissible ⟨j, h⟩ d)
  | .choose p cred (j := j) h cand expected =>
    match k j h with
    | none => .error (.uncontrolled ⟨j, h⟩)
    | some K =>
      let holds := (host.view c.cfg.world).holds
      if !au.verify p cred then .error (.unauthenticated p)
      else if !holds (K.desc.office p) then .error (.notChooser p ⟨j, h⟩)
      else if expected ≠ c.rev j h then .error (.staleRevision ⟨j, h⟩ expected (c.rev j h))
      else if cand ∉ K.desc.domain then .error (.notPermitted cand)
      else if !K.slot.usable holds cand then .error (.unusable cand (diagnose K.slot holds cand))
      else match c.stored j h with
        | some s =>
          if s ≠ cand && keepable K.slot K.desc holds (latchedOf host k c h) (some s) && !K.desc.override then
            .error (.noOverride ⟨j, h⟩ s)
          else install host sp c h K (some p) cand
        | none => install host sp c h K (some p) cand

/-- The start: the runner's start, with the initial plan's stored choices (revision 0 each). -/
def CCfg.init {i : Ix} (c : Cfg S Hole A Tok Fact Ob V i) (stored₀ : (j : Ix) → Hole j → Option Cand) :
    CCfg S Hole A P Cand Tok Fact Ob V i :=
  ⟨c, stored₀, fun _ _ => 0, []⟩

/-- The controlled configurations reachable from `c₀` by accepted controlled events. -/
inductive CReachable (host : Host V Tok Fact) (sp : Spec S Tok Fact Ob) (au : Authority P Cred)
    (k : (j : Ix) → Hole j → Option (SlotCtl S Hole A P Fact Cand j)) {i : Ix}
    (c₀ : CCfg S Hole A P Cand Tok Fact Ob V i) : CCfg S Hole A P Cand Tok Fact Ob V i → Prop
  | init : CReachable host sp au k c₀ c₀
  | step {c c' : CCfg S Hole A P Cand Tok Fact Ob V i} (ev : CEvent S Hole A P Cred Cand Fact V) :
      CReachable host sp au k c₀ c → crun host sp au k c ev = .ok c' → CReachable host sp au k c₀ c'

/-- A controlled session: each event accepted or refused; a refusal leaves the configuration. -/
def csession (host : Host V Tok Fact) (sp : Spec S Tok Fact Ob) (au : Authority P Cred)
    (k : (j : Ix) → Hole j → Option (SlotCtl S Hole A P Fact Cand j)) {i : Ix} :
    CCfg S Hole A P Cand Tok Fact Ob V i → List (CEvent S Hole A P Cred Cand Fact V) →
      CCfg S Hole A P Cand Tok Fact Ob V i × List (Option (CRefusal S Hole P Cand Tok Fact))
  | c, [] => (c, [])
  | c, ev :: evs =>
    match crun host sp au k c ev with
    | .ok c' => let r := csession host sp au k c' evs; (r.1, none :: r.2)
    | .error w => let r := csession host sp au k c evs; (r.1, some w :: r.2)

end

end Obend.Run.Control

end
