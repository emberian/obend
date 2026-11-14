module
/-
# Obend.Teeth.RunExamplesTeeth — Concrete Negotiation, Editorial Control, Durable Crash-Recovery, and Offline-Fork Fixtures

Evicted from `Obend/Run/{SharedExample, ControlExample, DurableExample, ForkExample}.lean` into
Tier-2B `Obend/Teeth/` (`Wave C2-Core`, `4 → 1`). Preserves original `Obend.Run.*Example`
namespaces for `DurableHostAndZoeSeatTest` and `RunLeafLowerTeeth`.
-/
public import Obend.Run.Negotiation
public import Obend.Run.Proofs.Control
public import Obend.Run.Proofs.Shared
public import Obend.Run.Proofs.Durable
public import Obend.Run.Fork
public import Obend.Run.Proofs.Adapter
public import Obend.Elab.Proofs.PrepareChecks
public import Obend.Elab.PdeSolverElab
public import Obend.Tactic.Tooth
import all Obend.Slot
import all Obend.Slot.World
import all Obend.Slot.Protocol
import all Obend.Slot.Budget
import all Obend.Slot.Integrity
import all Obend.Run.Runner
import all Obend.Run.Spec
import all Obend.Run.Core4
import all Obend.Run.Negotiation
import all Obend.Run.Control
import all Obend.Run.Proofs.Control
import all Obend.Run.Shared
import all Obend.Run.Durable
import all Obend.Run.Fork
import all Obend.Run.Adapter
import all Obend.Run.Proofs.Adapter
import all Obend.Core.Ty
import all Obend.Core.Check
import all Obend.Core.Term
import all Obend.Core.Machine
import all Obend.Core.MachineFast
import all Obend.Core.Data
import all Obend.Core.Collect
import all Obend.Core.Proofs.Force
import all Obend.Core.MachineTyping
import all Obend.Elab.Prepare
import all Obend.Elab.Proofs.PrepareChecks
import all Obend.Analysis.Diff
import all Obend.Analysis.RealAnalysis
import all Obend.Analysis.HyperbolicPdeCert
import all Obend.Analysis.PdeSexprAndApprox
import all Obend.Analysis.NonlinearMultiDPde
import all Obend.Hardware.Types
import all Obend.Hardware.HDL
import all Obend.Hardware.ArrayHypergraph
import all Obend.Hardware.Gpu.SoacOptimize
import all Obend.Hardware.Gpu.StencilTile
import all Obend.Hardware.MultiDStencilTile
import all Obend.Tactic.SymDiffAndFlux
import all Obend.Elab.PdeSolverElab

public section

/-! ## Evicted from `lean/Obend/Run/SharedExample.lean` -/
namespace Obend.Run.SharedExample

open Obend.Slot Obend.Slot.Protocol Obend.Slot.Protocol.Negotiation Obend.Run.Control Obend.Run.Shared
open Obend.Run.Negotiation (Wv everything stepW host O₀ ctl au stored₀ NCand reserveOp commitOp)

/-- The two buyers. -/
inductive Buyer where
  | alice
  | bob
  deriving DecidableEq, Repr

/-- The ledger's record: the raw world, the consumed tokens, the grants. -/
structure NRec where
  raw : Wv
  spent : List Tok
  grants : List (Grant Buyer Tok)
  height : Nat

/-- What an abandonment does to the record (a `#tooth` mutation target): nothing; the consumption
is durable. -/
@[expose] def ledgerAbandon (d : NRec) : NRec := d

/-- **What `Ledger`'s durability fields ask of this record**: an abandonment keeps the consumption
and the grants. The structure consumes exactly this (`nledger.abandon_spent`, `abandon_grants`); the
tooth below is the erasing record, which fails it, so it is not a `Ledger`. -/
theorem ledgerAbandon_durable (d : NRec) : (ledgerAbandon d).spent = d.spent ∧ (ledgerAbandon d).grants = d.grants :=
  ⟨rfl, rfl⟩

/-- The negotiation's ledger. -/
@[expose] def nledger : Ledger Buyer Wv Tok where
  Rec := NRec
  raw := NRec.raw
  spent := NRec.spent
  grants := NRec.grants
  stepRaw := stepW
  commit d i t := ⟨d.raw, d.spent ++ [t], d.grants ++ [⟨t, i, d.grants.length⟩], d.height + 1⟩
  setRaw d w := ⟨w, d.spent, d.grants, d.height + 1⟩
  onAbandon d _ := ledgerAbandon d
  allowed d d' := (decide (d.raw = d'.raw) || stepW d.raw d'.raw) && decide (d.height ≤ d'.height)
  height := NRec.height
  commit_raw _ _ _ := rfl
  commit_spent _ _ _ := rfl
  commit_grants _ _ _ := rfl
  setRaw_raw _ _ := rfl
  setRaw_spent _ _ := rfl
  setRaw_grants _ _ := rfl
  onAbandon_raw _ _ := rfl
  allowed_refl _ := by simp
  allowed_commit _ _ _ := by simp
  allowed_setRaw _ _ h := by simp [h]
  allowed_onAbandon _ _ := by simp [ledgerAbandon]
  commit_height _ _ _ := rfl
  allowed_height _ _ h := by simp only [Bool.and_eq_true, decide_eq_true_eq] at h; exact h.2
  abandon_spent d _ := (ledgerAbandon_durable d).1
  abandon_grants d _ := (ledgerAbandon_durable d).2

/-- The negotiation's ledger is durable (a field: every `Ledger` is). -/
theorem nledger_durable : nledger.Durable := nledger.durable

def base : Wv → View Tok Fact := host.view

def d₀ : NRec := ⟨everything, [], [], 0⟩

abbrev BCfg := JCfg nledger sig HoleN Res Unit NCand Fact Ob .idle
abbrev BEv := JEvent Buyer Wv sig HoleN Res Unit Unit NCand Fact NRec

def J₀ : BCfg := JCfg.init nledger d₀ (fun _ => O₀) (fun _ => stored₀)

def bsession (evs : List BEv) := jsession nledger base (fun _ => spec) (fun _ => au) (fun _ => ctl) J₀ evs

def reserve (b : Buyer) : List BEv :=
  [.dispatch b reserveOp, .own b (.base (.respond ⟨.idle, Op.reserve, ()⟩))]

/-! ## Two separate runners -/

/-- Each buyer's own runner, at its own copy of the world (the negotiation's host, nothing shared). -/
def separate : List (Event sig HoleN Res Fact Wv) :=
  [.dispatch reserveOp, .respond ⟨.idle, Op.reserve, ()⟩, .dispatch (commitOp .p1)]

/-- **Two grants**: each buyer's runner accepts its commitment, each consuming the capability. -/
theorem naive_two_grants :
    (session host spec (Cfg.init O₀ everything) separate).2 = [none, none, none] ∧
      (session host spec (Cfg.init O₀ everything) separate).1.spent = [.cap] := ⟨rfl, rfl⟩

/-- **Local `Legal` does not imply global once-spending**: both logs are `Legal` (each by
`reachable_legal`), and the capability is spent by both. -/
theorem local_legal_does_not_imply_global_once :
    Legal host spec O₀ everything (fun _ _ => []) (session host spec (Cfg.init O₀ everything) separate).1.log ∧
      spentBy spec (session host spec (Cfg.init O₀ everything) separate).1.log ++
        spentBy spec (session host spec (Cfg.init O₀ everything) separate).1.log = [.cap, .cap] :=
  ⟨reachable_legal (session_reachable .init _), rfl⟩

/-! ## Through the ledger -/

def aliceFirst : List BEv :=
  reserve .alice ++ reserve .bob ++ [.dispatch .alice (commitOp .p1), .dispatch .bob (commitOp .p1)]

def bobFirst : List BEv :=
  reserve .alice ++ reserve .bob ++ [.dispatch .bob (commitOp .p1), .dispatch .alice (commitOp .p1)]

/-- **Alice commits first and wins; Bob is refused, naming Alice and epoch 0.** -/
theorem alice_wins :
    (bsession aliceFirst).2 = [none, none, none, none, none, some (.taken .cap .alice 0)] ∧
      ((bsession aliceFirst).1.led.grants.map fun g => (g.tok, g.winner, g.epoch)) = [(.cap, .alice, 0)] :=
  ⟨rfl, rfl⟩

/-- **Bob commits first and wins; Alice is refused, naming Bob and epoch 0.** -/
theorem bob_wins :
    (bsession bobFirst).2 = [none, none, none, none, none, some (.taken .cap .bob 0)] ∧
      ((bsession bobFirst).1.led.grants.map fun g => (g.tok, g.winner, g.epoch)) = [(.cap, .bob, 0)] :=
  ⟨rfl, rfl⟩

def lostReply : List BEv :=
  reserve .alice ++ reserve .bob ++
    [.dispatch .alice (commitOp .p1),
     .world ⟨true, true, true, false, 1⟩,
     .world ⟨true, true, true, true, 2⟩,
     .abandon .alice (commitOp .p1),
     .own .alice (.base (.respond ⟨.reserved, Op.commit .p1, true⟩)),
     .dispatch .bob (commitOp .p1),
     .own .bob (.choose () () (j := Phase.reserved) () (.prov .p2) 0),
     .dispatch .bob (commitOp .p2)]

/-- **A lost reply, a revived live flag, an abandonment**: Alice's commitment goes out and its reply
is lost; the raw world calls the capability dead, then live again; Alice abandons (her late reply is
then refused); Bob's commitment is refused naming Alice and epoch 0, on `p1` and, after he chooses
`p2`, on `p2`. -/
theorem lost_reply_receipt :
    (bsession lostReply).2 =
      [none, none, none, none, none, none, none, none,
       some (.runner .alice (.run (.abandoned (commitOp .p1)))),
       some (.taken .cap .alice 0), none, some (.taken .cap .alice 0)] := by rfl

/-- **Coupling**, at Alice's win: Bob's world is the ledger after Alice's commit (he saw it). -/
theorem coupled_after_commit :
    ((bsession aliceFirst).1.cfgs .bob).cfg.world = (bsession aliceFirst).1.led ∧
      ((bsession aliceFirst).1.cfgs .alice).cfg.world = (bsession aliceFirst).1.led := ⟨rfl, rfl⟩

/-- The general theorems at the two buyers: each buyer's log is `Legal` at its local host, the
capability is granted once, and spent once across both. -/
theorem general_instances :
    let J := (bsession lostReply).1
    (∀ b, Legal (localHost nledger base) spec O₀ d₀ (fun _ _ => []) (J.cfgs b).cfg.log) ∧
      ((nledger.grants J.led).map Grant.tok).Nodup ∧
      ∀ b b' t, t ∈ spentBy spec (J.cfgs b).cfg.log → t ∈ spentBy spec (J.cfgs b').cfg.log → b = b' :=
  have h : JReachable nledger base (fun _ => spec) (fun _ => au) (fun _ => ctl)
      (JCfg.init nledger d₀ (fun _ => O₀) (fun _ => stored₀)) (bsession lostReply).1 :=
    jsession_reachable .init _
  ⟨fun b => joint_reachable_projects_legal rfl rfl h b,
    (joint_reachable_ticket_exclusive rfl rfl h).1,
    (joint_once rfl rfl h).2⟩

end Obend.Run.SharedExample


/-! ## Evicted from `lean/Obend/Run/ControlExample.lean` -/
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
example :
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

end Obend.Run.ControlExample


/-! ## Evicted from `lean/Obend/Run/DurableExample.lean` -/
namespace Obend.Run.DurableExample

open Obend.Slot Obend.Slot.Protocol Obend.Slot.Protocol.Negotiation Obend.Run.Control Obend.Run.Shared
open Obend.Run.Durable Obend.Run.SharedExample
open Obend.Run.Negotiation (Wv host O₀ ctl au stored₀ NCand commitOp)

abbrev HEv := HEvent nledger sig HoleN Res Unit Unit NCand Fact

def submitAll (evs : List BEv) : List HEv := evs.map .submit

def script : List HEv :=
  submitAll (reserve .alice ++ reserve .bob) ++
    [.submit (.dispatch .alice (commitOp .p1)), .expose 4, .crash,
     .submit (.dispatch .bob (commitOp .p1)), .recover,
     .submit (.dispatch .bob (commitOp .p1)), .submit (.dispatch .alice (commitOp .p1)), .expose 4,
     .crash, .crash, .recover]

def run (es : List HEv) :=
  hsession nledger base (fun _ => spec) (fun _ => au) (fun _ => ctl) J₀ (DState.init nledger J₀) es

/-- **The restart**: the session's refusals, in order. -/
theorem restart_receipt :
    (run script).2 =
      [none, none, none, none, none, none, none,
       some .down, none,
       some (.joint (.taken .cap .alice 0)),
       some (.joint (.runner .alice (.run (.busy (commitOp .p1))))),
       some (.exposed 4), none, none, none] := by
  rfl

/-- After the restart: one exposed identity (Alice's commitment, position 4); the reservations
journaled and not yet exposed are pending under their own positions; the memory is back. -/
theorem restart_state :
    (run script).1.outbox = [4] ∧ pending nledger (run script).1 = [0, 2] ∧ (run script).1.mem.isSome = true := by
  refine ⟨rfl, rfl, rfl⟩

/-- **The general theorems at the restart**: the host is reachable, its journal consumes each token
once, and an exposed effect consuming the capability is Alice's at identity 4, the only one. -/
theorem restart_general :
    ((run script).1.journal.flatMap (consumedBy nledger (fun _ => spec))).Nodup ∧
      ∀ n ∈ (run script).1.outbox, ∀ i o, (run script).1.journal[n]? = some (.dispatch i o) →
        spec.consumes o.2 = some .cap → n = 4 ∧ i = .alice := by
  have h := hsession_reachable (L := nledger) (base := base) (sp := fun _ => spec) (au := fun _ => au) (k := fun _ => ctl)
    (J₀ := J₀) .init script
  refine ⟨journal_once rfl rfl h, fun n hn i o hio hc => ?_⟩
  have h4 : (run script).1.journal[4]? = some (.dispatch .alice (commitOp .p1)) := rfl
  obtain ⟨hnm, hij⟩ := exposed_once rfl rfl h hn (show 4 ∈ (run script).1.outbox from by decide) hio h4 hc rfl
  exact ⟨hnm, hij⟩

end Obend.Run.DurableExample


/-! ## Evicted from `lean/Obend/Run/ForkExample.lean` -/
namespace Obend.Run.ForkExample

open Obend.Slot.Protocol.Negotiation (Tok sig spec)
open Obend.Run.Negotiation (ctl au commitOp)
open Obend.Run.Shared Obend.Run.Fork Obend.Run.SharedExample

/-- The capability is the shared ledger's. -/
def shared : Tok → Bool := fun _ => true

abbrev BFork := Fork Tok String (Deferred Buyer sig)

/-- A fork's session. -/
def fsession : BFork → List (FRow Buyer Tok String (Deferred Buyer sig)) → BFork × List (Option (FRefusal Tok))
  | F, [] => (F, [])
  | F, r :: rs =>
    match forkStep shared (tokOf fun _ => spec) F r with
    | .ok F' => let x := fsession F' rs; (x.1, none :: x.2)
    | .error w => let x := fsession F rs; (x.1, some w :: x.2)

/-- Bob's offline work, forked at the start. -/
def bobOffline := fsession (Fork.at nledger d₀) [.grow "quote noted", .spend .bob .cap, .defer (.bob, commitOp .p1)]

/-- The joint stitch of the two buyers. -/
def bstitch (main : BCfg × List String) (F : BFork) :=
  jstitch nledger base (fun _ => spec) (fun _ => au) (fun _ => ctl) main F

/-- Both buyers reserved; nobody committed. -/
def bothReserved : BCfg := (bsession (reserve .alice ++ reserve .bob)).1

/-- **In the fork, the capability is not Bob's**: his spend is refused `notMine`, his commitment is
escalated. -/
theorem fork_refuses :
    bobOffline.2 = [none, some (.notMine .cap), none] ∧ bobOffline.1.escalated = [(.bob, commitOp .p1)] :=
  ⟨rfl, rfl⟩

/-- **The double spend across fork and main is refused, naming Alice and epoch 0**; Bob's note
merges; main keeps Alice's grant only. -/
theorem bob_offline_conflict :
    let r := bstitch ((bsession aliceFirst).1, []) bobOffline.1
    (r.2.map fun c => (c.1.1, c.2)) = [(.bob, .taken .cap .alice 0)] ∧ r.1.2 = ["quote noted"] ∧
      (r.1.1.led.grants.map fun g => (g.tok, g.winner, g.epoch)) = [(.cap, .alice, 0)] := ⟨rfl, rfl, rfl⟩

/-- **Where nobody took it, the escalated commitment is judged by Bob's runner and committed**: Bob
is granted the capability at epoch 0. -/
theorem bob_offline_wins :
    let r := bstitch (bothReserved, []) bobOffline.1
    r.2.isEmpty = true ∧ (r.1.1.led.grants.map fun g => (g.tok, g.winner, g.epoch)) = [(.cap, .bob, 0)] :=
  ⟨rfl, rfl⟩

/-- **The stitch does not bypass the runner**: at a main where Bob never reserved, his escalated
commitment is refused by his own runner (a conflict with a runner refusal), and nothing is granted. -/
theorem runner_judges_escalation :
    let r := bstitch (J₀, []) bobOffline.1
    (r.2.map fun c => (c.1.1, match c.2 with | .runner i _ => some i | _ => none)) = [(.bob, some .bob)] ∧
      r.1.1.led.grants = [] := ⟨rfl, rfl⟩

/-- Bob escalates his commitment twice. -/
def bobTwice := fsession (Fork.at nledger d₀) [.defer (.bob, commitOp .p1), .defer (.bob, commitOp .p1)]

/-- **Atomic**: the first commitment would commit, the second is refused; the stitch returns the one
conflict and main is unchanged: no grant, Bob's log as it was. -/
theorem two_step_atomic :
    let r := bstitch (bothReserved, []) bobTwice.1
    r.2.length = 1 ∧ (r.2.map fun c => c.1) = [(.bob, commitOp .p1)] ∧ r.1.1.led.grants = [] ∧
      (r.1.1.cfgs .bob).cfg.log.length = (bothReserved.cfgs .bob).cfg.log.length := ⟨rfl, rfl, rfl, rfl⟩

/-- The general theorem at the fixture: the conflict is `stitch_double_spend` of Alice's grant. -/
theorem conflict_general :
    ((Buyer.bob, commitOp .p1), JRefusal.taken Tok.cap Buyer.alice 0) ∈
      (bstitch ((bsession aliceFirst).1, []) bobOffline.1).2 :=
  stitch_double_spend (g := ⟨.cap, .alice, 0⟩) rfl rfl ((bsession aliceFirst).1, [])
    (jsession_reachable .init _) bobOffline.1 [] [] .bob rfl rfl rfl rfl (by decide) rfl

end Obend.Run.ForkExample


/-! ## Wave C2-Core `#tooth` Mutation Witnesses & Multi-Turn Inhabitedness Fixtures -/
namespace Obend.Teeth.WaveC2CoreTeeth

-- 1. Bucket-3 #4 (`Obend.Elab.Proofs.PrepareChecks.prepare_checks` over non-empty `Assumptions`):
-- Mutating `letQuantity`, `lookupRow` (`.extend`/`.record`), or `caseRow` (`.case` over
-- equi-recursive aliases) breaks `prepare_checks`.
#tooth Obend.Elab.Proofs.PrepareChecks.prepare_checks by mutation
  Obend.Elab.Prepare.letQuantity := fun _ _ _ _ => .erased

#tooth Obend.Elab.Proofs.PrepareChecks.prepare_checks by mutation
  Obend.Elab.Prepare.lookupRow := fun _ _ _ => some .emptyRow

#tooth Obend.Elab.Proofs.PrepareChecks.prepare_checks by mutation
  Obend.Elab.Prepare.caseRow := fun _ _ => some .emptyRow

/-- Non-vacuity / inhabitedness witness for `prepareChecked_complete` over non-empty
equi-recursive `natListAssumptions` exercising `.case`, `.fix`, `.mix`, and `.extend`. -/
theorem prepare_checks_inhabited_witness :
    (Obend.Elab.Prepare.prepareChecked
      Obend.Elab.Proofs.PrepareChecks.natListProbe
      Obend.Elab.Proofs.PrepareChecks.natListProbeContext
      .natural).toBool = true :=
  Obend.Elab.Proofs.PrepareChecks.natListProbe_prepared

-- 2. `Obend.Elab.PdeSolverElab.checkPdeSolverSpec_sound`:
-- Bypassing the compile-time conservation/CFL/SSA gate breaks `checkPdeSolverSpec_sound`.
#tooth Obend.Elab.PdeSolverElab.checkPdeSolverSpec_sound by mutation
  Obend.Elab.PdeSolverElab.checkPdeSolverSpec := fun _ => true

/-- Concrete inhabited 1D advection conservation-law witness accepted by `checkPdeSolverSpec`
and instantiating `checkPdeSolverSpec_sound` (`0` kernel string-lexer recursion). -/
def advection1DSpec : Obend.Analysis.NonlinearMultiDPde.ConservationLawSpec where
  name := "Advection1D"
  coords := ["x"]
  vars := ["u"]
  params := []
  domain := []
  fluxes := [[.var 0]]
  aMax := 1
  cfl := 1 / 2
  limiter := .minmod

theorem pdeSolverElab_inhabited_witness :
    Obend.Elab.PdeSolverElab.checkPdeSolverSpec advection1DSpec = true := by
  decide +kernel

-- 3. Bucket-3 #11 (`Obend.Run.Core4.stepCheckpoint_eq_replay` & `checkpointReachable_settled_typed`):
-- Dropping `choiceGuardCheckpoint` breaks live-vs-replay simulation (`stepCheckpoint_eq_replay`
-- and `stepCheckpoint_simulates`).
#tooth Obend.Run.Core4.stepCheckpoint_eq_replay by mutation
  Obend.Run.Core4.choiceGuardCheckpoint := fun {_ _ _ _} _ _ _ _ => []

#tooth Obend.Run.Core4.stepCheckpoint_simulates by mutation
  Obend.Run.Core4.choiceGuardCheckpoint := fun {_ _ _ _} _ _ _ _ => []

section CheckpointMultiTurnFixture
open Obend.Slot Obend.Slot.Protocol Obend.Run Obend.Core.Term Obend.Core.Ty Obend.Core.Check
open Obend.Core.Machine Obend.Core.MachineTyping Obend.Core.Data Obend.Run.Core4

/-- Concrete 2-turn Core4 machine term: yields Plan `.boolean true`, branches via `.ifBool` on the
boolean response, and yields Plan `.boolean false` on the second turn. -/
def twoTurnTerm : Term :=
  .ifBool (.perform (.boolean true)) (.perform (.boolean false)) (.boolean false)

def ckHost : Host Bool Nat Nat where
  allowed := fun _ _ => true
  view := fun ok => ⟨fun _ => ok, fun _ => true⟩

def ckSpec : Spec planSig Nat Nat Unit where
  consumes := fun {_} op => match op with
    | .boolean true => some 1
    | _ => none
  requires := fun {_} _ => [0]
  establishes := fun {_} _ => []

def ckDeploy : Deploy Nat Nat Unit Bool where
  L := { heap := 16, stack := 16 }
  budget := { nodes := 32, ticks := 32, bytes := 256 }
  s₀ := initial twoTurnTerm
  Γ := [0]
  Δ := [1]
  Φ := []
  v₀ := true
  resp := .boolean
  alts := fun
    | .boolean true => some [.boolean true, .boolean false]
    | _ => none
  supports := fun _ => [0]

def ckPar₀ : Par := { depth := 1, ticks := 16, choices := [] }

def ckTrace : List (AEvent Bool) :=
  [ .choose (.boolean true)
  , .dispatch (.boolean true)
  , .respond (.boolean true) (.boolean true)
  , .deepen 1
  , .moreTicks 8
  , .dispatch (.boolean false)
  , .respond (.boolean false) (.boolean false) ]

def ckYield1 : State :=
  { heap := #[.cached ⟨.boolean true, []⟩ (.boolean true)]
    stack := [.ifBool (.perform (.boolean false)) (.boolean false) []]
    control := .yielded 0 }

def ckResumed1 : State :=
  { ckYield1 with control := .evaluate (.boolean true) [] }

def ckYield2 : State :=
  { heap := #[.cached ⟨.boolean true, []⟩ (.boolean true),
              .cached ⟨.boolean false, []⟩ (.boolean false)]
    stack := []
    control := .yielded 1 }

private theorem runBounded_step_ticks {L : Limits} {ticks : Nat} {s next : State}
    (h : Obend.Core.Machine.step L s = .suspended .ticks next) :
    runBounded L (ticks + 1) s = runBounded L ticks next := by
  simp [runBounded, h]

private theorem forceWith_step_ticks {L : Limits} {ticks : Nat} {s next : State}
    (h : Obend.Core.Machine.step L s = .suspended .ticks next) :
    forceWith (fun _ => true) L (ticks + 1) s = forceWith (fun _ => true) L ticks next := by
  conv => lhs; unfold forceWith
  cases hc : s.control with
  | complete _ | blackhole _ | refused _ | yielded _ =>
    simp [Obend.Core.Machine.step, hc] at h
  | evaluate _ _ | enter _ | returned _ =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      runBounded_step_ticks (ticks := 0) h]
    cases hnc : next.control <;> cases ticks <;> simp [forceWith, runBounded, hnc]

theorem ckTurn1_eq :
    turnFast { heap := 16, stack := 16 } 16 { nodes := 32, ticks := 32, bytes := 256 }
      (initial twoTurnTerm) = .vis (.boolean true) ckYield1 := by
  rw [turnFast_eq_turn]
  unfold turn
  let s1 : State :=
    { heap := #[]
      stack := [.ifBool (.perform (.boolean false)) (.boolean false) []]
      control := .evaluate (.perform (.boolean true)) [] }
  let y1 : State :=
    { heap := #[.suspended ⟨.boolean true, []⟩]
      stack := [.ifBool (.perform (.boolean false)) (.boolean false) []]
      control := .yielded 0 }
  let f1 : State :=
    { heap := #[.evaluating ⟨.boolean true, []⟩]
      stack := [.update 0]
      control := .evaluate (.boolean true) [] }
  let f2 : State :=
    { heap := #[.evaluating ⟨.boolean true, []⟩]
      stack := [.update 0]
      control := .returned (.boolean true) }
  let f3 : State :=
    { heap := #[.cached ⟨.boolean true, []⟩ (.boolean true)]
      stack := []
      control := .returned (.boolean true) }
  let f4 : State :=
    { heap := #[.cached ⟨.boolean true, []⟩ (.boolean true)]
      stack := []
      control := .complete (.boolean true) }
  rw [runBounded_step_ticks (next := s1)
      (by simp [s1, twoTurnTerm, initial, Obend.Core.Machine.step, stepRaw])]
  rw [runBounded_step_ticks (next := y1)
      (by simp [s1, y1, Obend.Core.Machine.step, stepRaw, forcingShared])]
  have hYield : runBounded { heap := 16, stack := 16 } 14 y1 = .yielded 0 y1 := rfl
  rw [hYield]
  unfold yieldedPlan yieldedPlanWith
  dsimp only [y1]
  rw [forceWith_step_ticks (next := f1)
      (by simp [f1, Obend.Core.Machine.step, stepRaw, Array.set!, Array.setIfInBounds])]
  rw [forceWith_step_ticks (next := f2)
      (by simp [f1, f2, Obend.Core.Machine.step, stepRaw])]
  rw [forceWith_step_ticks (next := f3)
      (by simp [f2, f3, Obend.Core.Machine.step, stepRaw, Array.set!, Array.setIfInBounds])]
  rw [forceWith_step_ticks (next := f4)
      (by simp [f3, f4, Obend.Core.Machine.step, stepRaw])]
  rfl

theorem ckTurn2_eq :
    turnFast { heap := 16, stack := 16 } 24 { nodes := 32, ticks := 32, bytes := 256 }
      ckResumed1 = .vis (.boolean false) ckYield2 := by
  rw [turnFast_eq_turn]
  unfold turn
  let s1 : State :=
    { heap := #[.cached ⟨.boolean true, []⟩ (.boolean true)]
      stack := [.ifBool (.perform (.boolean false)) (.boolean false) []]
      control := .returned (.boolean true) }
  let s2 : State :=
    { heap := #[.cached ⟨.boolean true, []⟩ (.boolean true)]
      stack := []
      control := .evaluate (.perform (.boolean false)) [] }
  let y2 : State :=
    { heap := #[.cached ⟨.boolean true, []⟩ (.boolean true), .suspended ⟨.boolean false, []⟩]
      stack := []
      control := .yielded 1 }
  let f1 : State :=
    { heap := #[.cached ⟨.boolean true, []⟩ (.boolean true), .evaluating ⟨.boolean false, []⟩]
      stack := [.update 1]
      control := .evaluate (.boolean false) [] }
  let f2 : State :=
    { heap := #[.cached ⟨.boolean true, []⟩ (.boolean true), .evaluating ⟨.boolean false, []⟩]
      stack := [.update 1]
      control := .returned (.boolean false) }
  let f3 : State :=
    { heap := #[.cached ⟨.boolean true, []⟩ (.boolean true),
                .cached ⟨.boolean false, []⟩ (.boolean false)]
      stack := []
      control := .returned (.boolean false) }
  let f4 : State :=
    { heap := #[.cached ⟨.boolean true, []⟩ (.boolean true),
                .cached ⟨.boolean false, []⟩ (.boolean false)]
      stack := []
      control := .complete (.boolean false) }
  rw [runBounded_step_ticks (next := s1)
      (by simp [s1, ckResumed1, ckYield1, Obend.Core.Machine.step, stepRaw])]
  rw [runBounded_step_ticks (next := s2)
      (by simp [s1, s2, Obend.Core.Machine.step, stepRaw])]
  rw [runBounded_step_ticks (next := y2)
      (by simp [s2, y2, Obend.Core.Machine.step, stepRaw, forcingShared])]
  have hYield : runBounded { heap := 16, stack := 16 } 21 y2 = .yielded 1 y2 := rfl
  rw [hYield]
  unfold yieldedPlan yieldedPlanWith
  dsimp only [y2]
  rw [forceWith_step_ticks (next := f1)
      (by simp [f1, Obend.Core.Machine.step, stepRaw, Array.set!, Array.setIfInBounds])]
  rw [forceWith_step_ticks (next := f2)
      (by simp [f1, f2, Obend.Core.Machine.step, stepRaw])]
  rw [forceWith_step_ticks (next := f3)
      (by simp [f2, f3, Obend.Core.Machine.step, stepRaw, Array.set!, Array.setIfInBounds])]
  rw [forceWith_step_ticks (next := f4)
      (by simp [f3, f4, Obend.Core.Machine.step, stepRaw])]
  rfl

private theorem resume_ckYield1 :
    resume (.boolean true) ckYield1 = some ckResumed1 := by rfl

private theorem resume_ckYield2 :
    resume (.boolean false) ckYield2 =
      some { ckYield2 with control := .evaluate (.boolean false) [] } := by rfl

/-- Multi-turn inhabitedness witness: `checkpointSession` accepts the full 7-event trace
(`.choose`, `.dispatch`, `.respond`, `.deepen`, `.moreTicks`, `.dispatch`, `.respond`),
records both answered turns, spends token `1` once, and agrees identically with cold `asession`
replay via `checkpointSession_eq_replay`. -/
theorem checkpointFixture_agrees_with_replay :
    let live := checkpointSession ckDeploy ckHost ckSpec (Checkpoint.init ckDeploy ckPar₀) ckTrace
    let cold := asession ckDeploy ckHost ckSpec (ckDeploy.start ckPar₀) ckTrace
    live.2 = [none, none, none, none, none, none, none] ∧
    live.1.answered.size = 2 ∧
    live.1.spent.size = 1 ∧
    Checkpoint.toACfg ckDeploy live.1 = cold.1 ∧
    live.2 = cold.2 := by
  have hSim := checkpointSession_eq_replay (D := ckDeploy) (host := ckHost) (sp := ckSpec)
    ckPar₀ ckTrace
  refine ⟨?_, ?_, ?_, hSim.1, hSim.2⟩
  · simp [checkpointSession, stepCheckpoint, Checkpoint.init, ckTrace, ckPar₀, ckDeploy, ckHost,
      ckSpec, choiceGuardCheckpoint, choiceDeadAt, choiceAt, setChoice, nextPlanOf, typedReply,
      Data.conforms, Data.term, pushConsumedTok, View.maskArray, dispatchGuard, admitOp,
      ckTurn1_eq, ckTurn2_eq, resume_ckYield1, resume_ckYield2]
  · simp [checkpointSession, stepCheckpoint, Checkpoint.init, ckTrace, ckPar₀, ckDeploy, ckHost,
      ckSpec, choiceGuardCheckpoint, choiceDeadAt, choiceAt, setChoice, nextPlanOf, typedReply,
      Data.conforms, Data.term, pushConsumedTok, View.maskArray, dispatchGuard, admitOp,
      ckTurn1_eq, ckTurn2_eq, resume_ckYield1, resume_ckYield2]
  · simp [checkpointSession, stepCheckpoint, Checkpoint.init, ckTrace, ckPar₀, ckDeploy, ckHost,
      ckSpec, choiceGuardCheckpoint, choiceDeadAt, choiceAt, setChoice, nextPlanOf, typedReply,
      Data.conforms, Data.term, pushConsumedTok, View.maskArray, dispatchGuard, admitOp,
      ckTurn1_eq, ckTurn2_eq, resume_ckYield1, resume_ckYield2]

def ckPlanTy : Ty := .variant (.field "op" .natural .emptyRow)

/-- Typed Core4 activity with `.emptyRow` response exercising `conforms_emptyRow_typed` and
`checkpointReachable_settled_typed` across a 5-event multi-turn trace. -/
def emptyRowAnnotated : AnnotatedTerm :=
  { term := .perform (.inject "op" (.nat 1))
    annotations := fun _ => none
    assumptions := {} }

def emptyRowChecked : Checked emptyRowAnnotated [] :=
  ⟨.computation ckPlanTy .emptyRow .emptyRow, [],
    .perform (.inject (fuel := 1) (.natural [] 1) rfl rfl) rfl rfl,
    rfl, rfl, rfl⟩

def ckDeployEmptyRow : Deploy Nat Nat Unit Bool :=
  { ckDeploy with s₀ := initial emptyRowAnnotated.erase, resp := .emptyRow }

def ckTraceEmptyRow : List (AEvent Bool) :=
  [ .world true
  , .moreTicks 8
  , .deepen 1
  , .world true
  , .moreTicks 4 ]

/-- Multi-turn `StateTyping` inhabitedness witness: instantiates `checkpointReachable_settled_typed`
on the reachable 5-event `ckTraceEmptyRow` configuration (where every event is accepted),
certifying `StateTyping` of both `ck.frontier` and the settled/GC-compacted `ck.settled`. -/
theorem checkpointFixture_settled_typed :
    let res := checkpointSession ckDeployEmptyRow ckHost ckSpec
      (Checkpoint.init ckDeployEmptyRow ckPar₀) ckTraceEmptyRow
    res.2 = [none, none, none, none, none] ∧
    (∃ types, Nonempty (StateTyping ({} : Assumptions) types res.1.frontier
      (.computation ckPlanTy .emptyRow .emptyRow))) ∧
    (∃ types, Nonempty (StateTyping ({} : Assumptions) types res.1.settled
      (.computation ckPlanTy .emptyRow .emptyRow))) := by
  have hInit : StateTyping ({} : Assumptions) [] ckDeployEmptyRow.s₀
      (.computation ckPlanTy .emptyRow .emptyRow) :=
    checked_initial_state emptyRowAnnotated emptyRowChecked
  have hReach : CheckpointReachable ckDeployEmptyRow ckHost ckSpec
      (Checkpoint.init ckDeployEmptyRow ckPar₀)
      (checkpointSession ckDeployEmptyRow ckHost ckSpec
        (Checkpoint.init ckDeployEmptyRow ckPar₀) ckTraceEmptyRow).1 :=
    checkpointSession_reachable .init ckTraceEmptyRow
  have hAll := checkpointReachable_settled_typed (D := ckDeployEmptyRow) (host := ckHost) (sp := ckSpec)
    hInit (fun p hp => by cases hp) (fun r => conforms_emptyRow_typed ({} : Assumptions) (r := r)) hReach
  exact ⟨rfl, hAll.1, hAll.2.2.1⟩

end CheckpointMultiTurnFixture

end Obend.Teeth.WaveC2CoreTeeth

end
