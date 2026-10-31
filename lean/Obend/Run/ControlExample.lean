module
/-
# Obend.Run.ControlExample — an editorial slot: who may choose, and what an office change voids

The negotiation's provider hole (`Obend.Slot.Protocol.Negotiation`) decided by an EDITOR. The world
also says who holds the editor's office; the deployment authenticates a principal by a credential
(here, the principal's own name). Fixtures, each against what the bare runner does:

- `bare_accepts`: the bare runner kernel takes any proposer's replan (its authority is the
  hole's `.me`), and a choice made by an editor who has since left office still dispatches.
- `editorial_receipt`: under `whileInOffice`, a choice by someone out of office is refused
  `notChooser`; an unauthenticated one `unauthenticated`; a second choice against the old revision
  `staleRevision`; a raw replan `rawReplan`; once Alice leaves office the commitment she chose is
  refused at dispatch (`unsupported`, naming her office), and Bob, now editor, re-decides it at the
  current revision and it goes out.
- `lasting_receipt`: the same run under `lasting`: Alice's choice survives her leaving office.
- `awaiting_receipt` / `incumbent_receipt`: with `p1`'s grant revoked, a `chooserRequired` slot
  installs nothing and awaits its editor, with every candidate diagnosed; an `incumbentFirst` slot
  moves to `p2`.
- `nothing_receipt`: with every grant revoked and the cancellation outside the domain, the advance
  is `nothingAdmissible`, each candidate with its exact dead supports.
- `latch_receipt`: under `reapproval`, `p1` revoked then restored is not kept again automatically;
  under `automatic` it is.
-/
public import Obend.Run.Proofs.Control
public import Obend.Run.Negotiation
public import Obend.Tactic.Tooth
import all Obend.Run.Runner
import all Obend.Run.Negotiation
import all Obend.Run.Control
import all Obend.Run.Proofs.Control
public section

namespace Obend.Run.ControlExample

open Obend.Slot Obend.Slot.Protocol Obend.Slot.Protocol.Negotiation Obend.Run.Control
open Obend.Run.Negotiation (decOp reserveOp commitOp)

/-- The editors. -/
inductive Editor where
  | alice
  | bob
  deriving DecidableEq, Repr

/-- The negotiation's facts, and who holds the editor's office. -/
inductive EFact where
  | base (f : Fact)
  | office (e : Editor)
  deriving DecidableEq, Repr

def espec : Spec sig Tok EFact Ob where
  consumes := spec.consumes
  requires := fun op => (spec.requires op).map .base
  establishes := spec.establishes

def eiface : Iface sig HoleN Res Tok EFact Ob .reserved where
  chooser := .me
  ctx := [.base (.auth .p1), .base (.auth .p2), .base .beforeDeadline]
  need := [.cap]
  post := fun _ _ => True
  owes := [.pay .p1, .pay .p2, .refund]
  accepts := fun _ => True

def eΩ : Ctx sig HoleN Res Tok EFact Ob := fun
  | .reserved, () => some eiface
  | .idle, h => nomatch h
  | .done, h => nomatch h

/-- The negotiation planning on `f`, nothing done. -/
def eobj (f : P .reserved) : Open sig HoleN Res Tok EFact Ob .idle where
  template := template
  Ω := eΩ
  σ := choose f
  Γ := [.base (.auth .p1), .base (.auth .p2), .base .beforeDeadline]
  Δ := [.cap]
  Q := fun _ _ => True
  Φ := [.holdDeposit, .pay .p1, .pay .p2, .refund]
  hist := ⟨[], none⟩

/-- The world: both grants, the deadline, the capability, and who is editor. -/
structure EW where
  grant1 : Bool
  grant2 : Bool
  beforeDeadline : Bool
  capLive : Bool
  aliceIn : Bool
  bobIn : Bool
  deriving DecidableEq, Repr

def eholds (w : EW) : EFact → Bool
  | .base (.auth .p1) => w.grant1
  | .base (.auth .p2) => w.grant2
  | .base .beforeDeadline => w.beforeDeadline
  | .office .alice => w.aliceIn
  | .office .bob => w.bobIn

def ehost : Host EW Tok EFact where
  allowed := fun w w' => w.beforeDeadline || !w'.beforeDeadline
  view := fun w => ⟨eholds w, fun _ => w.capLive⟩

def w₀ : EW := ⟨true, true, true, true, true, false⟩
/-- Alice leaves office; Bob takes it. -/
def handover : EW := ⟨true, true, true, true, false, true⟩
/-- `p1`'s grant revoked. -/
def revoked1 : EW := ⟨false, true, true, true, true, false⟩
/-- Both grants revoked. -/
def revokedAll : EW := ⟨false, false, true, true, true, false⟩

/-- The provider slot: `p` cites its grant and the deadline; cancelling cites nothing. -/
def eslot : Slot EFact (Option Provider) where
  supports := fun
    | some p => [.base (.auth p), .base .beforeDeadline]
    | none => []
  judge := fun _ => true

def ebody : Option Provider → P .reserved
  | some p => plan p
  | none => cancelPlan

def edesc (preset : Preset) (tenure : Tenure) (suspension : Suspension)
    (domain : List (Option Provider) := [some .p1, some .p2, none]) :
    Descriptor Editor EFact (Option Provider) :=
  ⟨fun e => [.office e], preset, domain, 1, true, tenure, suspension⟩

def ek (D : Descriptor Editor EFact (Option Provider)) :
    (j : Phase) → HoleN j → SlotCtl sig HoleN Res Editor EFact (Option Provider) j
  | .reserved, () => ⟨eslot, D, ebody⟩
  | .idle, h => nomatch h
  | .done, h => nomatch h

/-- A credential is the principal's own name. -/
def eau : Authority Editor Editor := ⟨fun p c => decide (p = c)⟩

def stored₀ : (j : Phase) → HoleN j → Option (Option Provider)
  | .reserved, () => some (some .p1)
  | .idle, h => nomatch h
  | .done, h => nomatch h

abbrev ECfg := CCfg sig HoleN Res Editor (Option Provider) Tok EFact Ob EW .idle
abbrev EEv := CEvent sig HoleN Res Editor Editor (Option Provider) EFact EW

def start (w : EW := w₀) : ECfg := CCfg.init (Cfg.init (eobj (plan .p1)) w) stored₀

def prov : HoleN .reserved := ()

def esession (D : Descriptor Editor EFact (Option Provider)) (w : EW) (evs : List EEv) :=
  csession ehost espec eau (ek D) (start w) evs

/-! ## The bare runner -/

/-- **What the bare runner does**: Bob's choice is anyone's choice (the hole is `.me`'s), and Alice's
choice, cited only by its candidate's supports, dispatches after she has left office. -/
theorem bare_accepts :
    (session ehost espec (Cfg.init (eobj (plan .p1)) w₀)
      [.dispatch reserveOp, .respond ⟨.idle, Op.reserve, ()⟩,
       .replan (j := Phase.reserved) prov (ebody (some .p2)) (eslot.supports (some .p2)),
       .world handover, .dispatch (commitOp .p2)]).2 = [none, none, none, none, none] := by rfl

/-! ## The editorial slot -/

def editorial : List EEv :=
  [.base (.dispatch reserveOp), .base (.respond ⟨.idle, Op.reserve, ()⟩),
   .choose .bob .bob (j := Phase.reserved) prov (some .p2) 0,
   .choose .alice .bob (j := Phase.reserved) prov (some .p2) 0,
   .choose .alice .alice (j := Phase.reserved) prov (some .p2) 0,
   .choose .alice .alice (j := Phase.reserved) prov (some .p1) 0,
   .base (.replan (j := Phase.reserved) prov (plan .p1) []),
   .base (.world handover),
   .base (.dispatch (commitOp .p2)),
   .choose .bob .bob (j := Phase.reserved) prov (some .p2) 1,
   .base (.dispatch (commitOp .p2))]

/-- **Under `whileInOffice`**: Bob out of office refused; Alice with Bob's credential refused; Alice
accepted at revision 0; her second choice against revision 0 refused; a raw replan refused; after
the handover the commitment she chose is refused at dispatch, naming her office; Bob re-decides at
revision 1 and the commitment goes out. -/
theorem editorial_receipt :
    (esession (edesc .incumbentFirst .whileInOffice .automatic) w₀ editorial).2 =
      [none, none,
       some (.notChooser .bob ⟨.reserved, ()⟩),
       some (.unauthenticated .alice),
       none,
       some (.staleRevision ⟨.reserved, ()⟩ 0 1),
       some (.rawReplan ⟨.reserved, ()⟩),
       none,
       some (.run (.unsupported (commitOp .p2) (some ⟨.reserved, ()⟩) [.office .alice])),
       none,
       none] := by rfl

/-- **Under `lasting`**: Alice's choice survives her leaving office; the commitment goes out at
once, and Bob's re-decision is a new decision at revision 1 (the call is then in flight, so the
replan is refused by the runner). -/
theorem lasting_receipt :
    (esession (edesc .incumbentFirst .lasting .automatic) w₀ editorial).2 =
      [none, none,
       some (.notChooser .bob ⟨.reserved, ()⟩),
       some (.unauthenticated .alice),
       none,
       some (.staleRevision ⟨.reserved, ()⟩ 0 1),
       some (.rawReplan ⟨.reserved, ()⟩),
       none,
       none,
       some (.run (.replacesInflight (commitOp .p2) ⟨.reserved, ()⟩)),
       some (.run (.busy (commitOp .p2)))] := by rfl

/-- The decisions recorded under `whileInOffice`: Alice's at revision 0 and Bob's at revision 1. -/
theorem editorial_decisions :
    ((esession (edesc .incumbentFirst .whileInOffice .automatic) w₀ editorial).1.decisions.map
      fun d => (d.cand, d.by_, d.rev)) = [(some .p2, some .alice, 0), (some .p2, some .bob, 1)] := by rfl

/-- The general theorems at this run: its runner log is `Legal`, and both decisions are authorized
(permitted, usable when made, each made by its principal in office). -/
theorem editorial_instances :
    let c := (esession (edesc .incumbentFirst .whileInOffice .automatic) w₀ editorial).1
    Legal ehost espec (eobj (plan .p1)) w₀ (fun _ _ => []) c.cfg.log ∧
      DecisionsAuthorized ehost (ek (edesc .incumbentFirst .whileInOffice .automatic)) c.decisions :=
  have hc := csession_reachable (host := ehost) (sp := espec) (au := eau)
    (k := ek (edesc .incumbentFirst .whileInOffice .automatic)) (c₀ := start w₀) .init editorial
  ⟨creachable_legal hc, creachable_authorized rfl hc⟩

-- Without the office in a `whileInOffice` decision's citations, Alice's choice dispatches after she
-- has left office.
#tooth editorial_receipt by mutation citesFor := fun {_ _ _} S _ _ c => S.supports c

/-! ## Chooser-required, nothing admissible, and the latch -/

def afterReserve : List EEv := [.base (.dispatch reserveOp), .base (.respond ⟨.idle, Op.reserve, ()⟩)]

/-- **Chooser-required**: with `p1`'s grant revoked, the advance installs nothing and awaits the
editor, every candidate diagnosed. -/
theorem awaiting_receipt :
    (esession (edesc .chooserRequired .whileInOffice .automatic) w₀
      (afterReserve ++ [.base (.world revoked1), .advance (j := Phase.reserved) prov])).2 =
      [none, none, none,
       some (.awaiting ⟨.reserved, ()⟩
         [(some .p1, .dead [.base (.auth .p1)]), (some .p2, .usable), (none, .usable)])] := by rfl

/-- The same under incumbent-first: the policy moves to `p2`. -/
theorem incumbent_receipt :
    let r := esession (edesc .incumbentFirst .whileInOffice .automatic) w₀
      (afterReserve ++ [.base (.world revoked1), .advance (j := Phase.reserved) prov])
    r.2 = [none, none, none, none] ∧ r.1.stored .reserved () = some (some .p2) ∧
      (r.1.decisions.map fun d => (d.cand, d.by_)) = [(some .p2, none)] := ⟨rfl, rfl, rfl⟩

/-- **Nothing admissible**: both grants revoked and the cancellation outside the domain; every
candidate named with exactly its dead supports. -/
theorem nothing_receipt :
    (esession (edesc .incumbentFirst .whileInOffice .automatic [some .p1, some .p2]) w₀
      (afterReserve ++ [.base (.world revokedAll), .advance (j := Phase.reserved) prov])).2 =
      [none, none, none,
       some (.nothingAdmissible ⟨.reserved, ()⟩
         [(some .p1, .dead [.base (.auth .p1)]), (some .p2, .dead [.base (.auth .p2)])])] := by rfl

/-- **The latch**: `p1` revoked, then restored. Under `reapproval` the editor's slot does not take
`p1` back on its own; under `automatic` it keeps it. -/
theorem latch_receipt :
    (esession (edesc .chooserRequired .whileInOffice .reapproval) w₀
      (afterReserve ++ [.base (.world revoked1), .base (.world w₀), .advance (j := Phase.reserved) prov])).2 =
      [none, none, none, none,
       some (.awaiting ⟨.reserved, ()⟩ [(some .p1, .usable), (some .p2, .usable), (none, .usable)])] ∧
    (esession (edesc .chooserRequired .whileInOffice .automatic) w₀
      (afterReserve ++ [.base (.world revoked1), .base (.world w₀), .advance (j := Phase.reserved) prov])).2 =
      [none, none, none, none, none] := ⟨rfl, rfl⟩

#tooth latch_receipt by mutation latchedOf := fun {_ _ _ _} [_] [_] {_ _ _ _ _ _} _ {_} _ _ {_} _ => false

end Obend.Run.ControlExample

end
