module
/-
# Obend.Run.Negotiation — the stranger's example, and the runner's teeth

The negotiation of `Obend.Slot.Protocol.Negotiation` (reserve a deposit, then commit a one-use
capability on a provider the buyer chooses, or cancel), run end to end by the guarded runner against
a host world in which grants come and go and the deadline, once passed, stays passed. Every
decision of the provider hole goes through its selection control (`Obend.Run.Control`): the buyer is
the one principal, the hole's descriptor is incumbent-first over `p1`, `p2`, cancelling (and, last,
`p2` with the other continuation), and a decision is an `advance` or a `choose`, never a raw replan.
The handler-driven runs (`drive`) decide nothing and use the runner directly.
-/
public import Obend.Run.Proofs.Interpret
public import Obend.Run.Proofs.Control
public import Obend.Slot.Proofs.Negotiation
public import Obend.Tactic.Tooth
import all Obend.Run.Runner
import all Obend.Run.Spec
import all Obend.Run.Control
@[expose] public section

namespace Obend.Run.Negotiation

open Obend.Slot Obend.Slot.Protocol Obend.Slot.Protocol.Negotiation Obend.Run.Control

instance decOp : (i : Phase) → DecidableEq (Op i)
  | _, .reserve, .reserve => isTrue rfl
  | _, .commit p, .commit q =>
    if h : p = q then isTrue (by rw [h]) else isFalse (by intro e; cases e; exact h rfl)
  | _, .commit _, .cancel => isFalse (by intro e; cases e)
  | _, .cancel, .commit _ => isFalse (by intro e; cases e)
  | _, .cancel, .cancel => isTrue rfl

instance : DecidableEq (Σ i, sig.Op i) := inferInstanceAs (DecidableEq (Σ i, Op i))

/-! ## The host's world -/

/-- What the host's world says: each provider's grant, the deadline, whether the capability is live,
and the world's clock (every world move is a new version of every cell: a restored grant is a new
grant, not the old one returned). -/
structure Wv where
  grant1 : Bool
  grant2 : Bool
  beforeDeadline : Bool
  capLive : Bool
  clock : Nat
deriving DecidableEq, Repr

def holdsW (v : Wv) : Fact → Bool
  | .auth .p1 => v.grant1
  | .auth .p2 => v.grant2
  | .beforeDeadline => v.beforeDeadline

/-- The world's audited step: anything but un-passing the deadline, with the clock moving forward.
Grants are revoked and restored, and the world may even call the spent capability live again. -/
def stepW (v v' : Wv) : Bool := (v.beforeDeadline || !v'.beforeDeadline) && decide (v.clock < v'.clock)

/-- The world as a `World`: each fact is its own cell, pinned to its truth at the clock's version. -/
instance : World Wv Fact where
  Cell := Fact
  Pin := Nat × Bool
  cell := id
  pin := fun v f => some (v.clock, holdsW v f)
  holdsAt := holdsW
  Step := fun v v' => stepW v v' = true
  holds_congr := fun _ _ _ h => (Prod.mk.inj (Option.some.inj h)).2
  retired_dead := fun _ _ h => by cases h
  retired_step := fun _ _ _ _ h => by cases h
  Ver := Nat × Bool
  ver := fun v f => (v.clock, holdsW v f)
  Past := fun a b => a.1 < b.1
  past_irrefl := fun _ => Nat.lt_irrefl _
  past_trans := fun _ _ _ => Nat.lt_trans
  pinOf := fun _ => some
  pin_ver := fun _ _ => rfl
  ver_step := fun v v' _ h => .inr (by
    simp only [stepW, Bool.and_eq_true, decide_eq_true_eq] at h; exact h.2)

/-- The host: the `World`'s step and truth, the capability live as the world says. -/
def host : Host Wv Tok Fact :=
  Host.ofWorld (fun v v' => inferInstanceAs (Decidable (stepW v v' = true))) fun v _ => v.capLive

/-! ## The object and the provider slot -/

/-- The negotiation, nothing done yet, planning on provider `p1`. -/
def O₀ : Open sig HoleN Res Tok Fact Ob .idle := obj (plan .p1) ⟨[], none⟩

def everything : Wv := ⟨true, true, true, true, 0⟩

/-- The provider hole's candidates: a provider, cancelling, or a provider with the other
continuation (`planFlip`). -/
inductive NCand where
  | prov (p : Provider)
  | cancel
  | flip (p : Provider)
  deriving DecidableEq, Repr

/-- The provider hole as a slot: a provider (either continuation) cites its grant and the deadline;
cancelling cites nothing. -/
def providers : Slot Fact NCand where
  supports := fun
    | .prov p | .flip p => [.auth p, .beforeDeadline]
    | .cancel => []
  judge := fun _ => true

def body : NCand → P .reserved
  | .prov p => plan p
  | .cancel => cancelPlan
  | .flip p => planFlip p

/-- The buyer prefers `p1`, then `p2`, then cancelling; `p2` with the other continuation last. -/
def order : List NCand := [.prov .p1, .prov .p2, .cancel, .flip .p2]

/-- The hole's descriptor: the buyer (`Unit`) holds the office whatever the world; incumbent-first
over `order`; a choice may supersede; a choice lasts; recovery is automatic. -/
def desc : Descriptor Unit Fact NCand := ⟨fun _ => [], .incumbentFirst, order, 1, true, .lasting, .automatic⟩

/-- Selection control, for every hole of the negotiation (there is one). -/
def ctl : (j : Phase) → HoleN j → SlotCtl sig HoleN Res Unit Fact NCand j
  | .reserved, () => ⟨providers, desc, body⟩
  | .idle, h => nomatch h
  | .done, h => nomatch h

/-- The buyer's credential: nothing to verify, there is one principal. -/
def au : Authority Unit Unit := ⟨fun _ _ => true⟩

/-- The initial plan's stored choice: `p1`. -/
def stored₀ : (j : Phase) → HoleN j → Option NCand
  | .reserved, () => some (.prov .p1)
  | .idle, h => nomatch h
  | .done, h => nomatch h

abbrev NCfg := CCfg sig HoleN Res Unit NCand Tok Fact Ob Wv .idle
abbrev NEv := CEvent sig HoleN Res Unit Unit NCand Fact Wv

def c₀ : NCfg := CCfg.init (Cfg.init O₀ everything) stored₀

/-- The controlled session. -/
def nsession (sp' : Spec sig Tok Fact Ob) (c : NCfg) (evs : List NEv) := csession host sp' au ctl c evs

/-- The buyer's choice of `c` against revision `r`. -/
def pick (c : NCand) (r : Nat) : NEv := .choose () () (j := Phase.reserved) () c r

/-! ## The stranger's example -/

def reserveOp : Σ i, sig.Op i := ⟨.idle, Op.reserve⟩
def commitOp (p : Provider) : Σ i, sig.Op i := ⟨.reserved, Op.commit p⟩

/-- The script up to the revocation: reserve, its reply, `p1`'s grant revoked. -/
def opening : List NEv :=
  [.base (.dispatch reserveOp), .base (.respond ⟨.idle, Op.reserve, ()⟩),
   .base (.world ⟨false, true, true, true, 1⟩)]

def c₁ : NCfg := (nsession spec c₀ opening).1

/-- At the revoked view the stored `p1` is no longer usable and the descriptor's policy chooses
`p2` (the former `resolves_p2` / `resolvesBy_p2`). -/
theorem advances_p2 :
    propose providers desc (host.view c₁.cfg.world).holds (c₁.stored .reserved ())
      (latchedOf host ctl c₁ (j := Phase.reserved) ()) = .chosen (.prov .p2) := rfl

/-- The rest: commit on `p1` (refused, the grant is gone), the policy's advance to `p2`, commit on
`p2` (accepted: the capability is spent), then its reply is LOST. The world restores `p1`'s grant and
calls the capability live again; the buyer chooses to cancel, to go back to `p1`, to keep `p2` with
another continuation, and tries to commit on `p1`; a late reply arrives for the commit on `p1`; the
deadline passes, and the world tries to un-pass it. The buyer gives up on the commitment
(`abandon`): the reply that finally arrives, a cancellation and a new commitment are all refused;
the world still moves. -/
def rest : List NEv :=
  [.base (.dispatch (commitOp .p1)),
   .advance (j := Phase.reserved) (),
   .base (.dispatch (commitOp .p2)),
   .base (.world ⟨true, true, true, true, 2⟩),
   pick .cancel 1,
   pick (.prov .p1) 1,
   pick (.flip .p2) 1,
   .base (.dispatch (commitOp .p1)),
   .base (.respond ⟨.reserved, Op.commit .p1, true⟩),
   .base (.world ⟨true, true, false, true, 3⟩),
   .base (.world ⟨true, true, true, true, 4⟩),
   .base (.abandon (commitOp .p2)),
   .base (.respond ⟨.reserved, Op.commit .p2, true⟩),
   pick .cancel 1,
   .base (.dispatch (commitOp .p1)),
   .base (.world ⟨false, false, false, true, 5⟩)]

def script : List NEv := opening ++ rest

def final : NCfg := (nsession spec c₀ script).1

/-- **The receipt**: which events were accepted, and why each refused one was refused. -/
theorem receipt :
    (nsession spec c₀ script).2 =
      [none, none, none,
       some (.run (.unadmitted (commitOp .p1) [.auth .p1] none)),
       none, none, none,
       some (.run (.replacesInflight (commitOp .p2) ⟨.reserved, ()⟩)),
       some (.run (.replacesInflight (commitOp .p2) ⟨.reserved, ()⟩)),
       some (.run (.replacesInflight (commitOp .p2) ⟨.reserved, ()⟩)),
       some (.run (.busy (commitOp .p2))),
       some (.run (.unsolicited ⟨.reserved, Op.commit .p1, true⟩)),
       none,
       some (.run .worldStep),
       none,
       some (.run (.abandoned (commitOp .p2))),
       some (.run (.abandoned (commitOp .p2))),
       some (.run (.abandoned (commitOp .p2))),
       none] := rfl

/-- **What had to stay**: the accepted history is the reservation answered and the commitment to
`p2` dispatched and never answered; the capability is spent once; the plan in force is `p2`'s; the
residual's next call is that commitment; the run is ended by abandoning it, and the obligations
established are the deposit and the payment to `p2`, which the abandonment does not discharge. -/
theorem stayed :
    final.cfg.obj.hist.answered = [⟨.idle, Op.reserve, ()⟩] ∧
      final.cfg.obj.hist.inflight = some (commitOp .p2) ∧ final.cfg.spent = [.cap] ∧
      final.cfg.obj.σ .reserved () = some (plan .p2) ∧ IsCall final.cfg.res (commitOp .p2) ∧
      dispatchesOf final.cfg.log = [reserveOp, commitOp .p2] ∧
      final.cfg.ended = some (commitOp .p2) ∧
      final.cfg.obj.hist.established spec = [.holdDeposit, .pay .p2] ∧
      (final.decisions.map fun d => (d.cand, d.by_, d.rev)) = [(.prov .p2, none, 0)] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **What changed**: the revocation moved the plan from `p1` to `p2` before anything was
dispatched in the hole; the world ends past the deadline with both grants revoked (it moves after
the run has ended). -/
theorem changed :
    c₁.cfg.obj.σ .reserved () = some (plan .p1) ∧ final.cfg.obj.σ .reserved () = some (plan .p2) ∧
      final.cfg.world = ⟨false, false, false, true, 5⟩ := ⟨rfl, rfl, rfl⟩

-- Without the replan guard the three replans in flight are not refused by name (the cancellation
-- and the return to `p1` become `inconsistent`, and the same-first-call `planFlip` is ACCEPTED).
#tooth receipt by mutation frozenHole := fun {_ _ _ _} [_] {_ _ _ _} _ => none
-- Without durable spending the capability the world calls live again is unspent.
#tooth stayed by mutation spendOn := fun {_ _ _ _ _} _ spent {_} _ => spent

/-- The run's log is `Legal`, by the general theorem. -/
theorem script_legal : Legal host spec O₀ everything (fun _ _ => []) final.cfg.log :=
  creachable_legal (csession_reachable .init script)

/-- And its decisions are authorized by the general theorem. -/
theorem script_authorized : DecisionsAuthorized host ctl final.decisions :=
  creachable_authorized rfl (csession_reachable .init script)

/-! ## The fixture the library could not refuse -/

/-- Every required fact false, the capability live (`astra/ASTRA-EVAL-20261031.md`, line 105). -/
def withdrawn : Wv := ⟨false, false, false, true, 0⟩

/-- **Refused**: at the withdrawn view `admitOp` says no to committing on `p1`, `interpret` delivers
it anyway (two calls, delivered), and the runner driven by the same handler refuses it, naming the
two facts that do not hold, after the handler saw only the reservation. -/
theorem withdrawn_refused :
    admitOp spec (host.view withdrawn) (Op.commit .p1) = false ∧
      (match interpret (env true) (fill Ω (choose (plan .p1)) template) 0 with
        | .done _ a n => a && n == 2
        | .stuck _ _ _ => false) = true ∧
      (drive host spec (env true) 3 (Cfg.init O₀ withdrawn) 0).refusal? =
        some (.unadmitted (commitOp .p1) [.auth .p1, .beforeDeadline] none) ∧
      (drive host spec (env true) 3 (Cfg.init O₀ withdrawn) 0).state = 1 := ⟨rfl, rfl, rfl, rfl⟩

#tooth withdrawn_refused by mutation dispatchGuard := fun {_ _ _ _ _} _ _ {_} _ => true

/-- At a world where everything holds, the driven run is `interpret`'s. -/
theorem everything_delivers :
    (drive host spec (env true) 3 c₀.cfg 0).result? =
      some (interpret (env true) (fill Ω (choose (plan .p1)) template) 0) := rfl

/-- **A lost reply is not retried**: with the reservation in flight, a second reservation (which
needs no fact and spends no token, so admission alone would let it through) is refused `busy`. -/
theorem reserve_retry_refused :
    (nsession spec c₀ [.base (.dispatch reserveOp), .base (.dispatch reserveOp)]).2 =
      [none, some (.run (.busy reserveOp))] := rfl

#tooth reserve_retry_refused by mutation awaiting := fun {_ _} _ => none

/-- **After abandonment, no new commitment**: the reservation is abandoned in flight; its late
reply and a commitment on `p1` (admissible: every grant holds) are refused, naming the abandoned
call. Without the guard the late reply would revive the plan and the commitment would go out. -/
theorem abandon_ends :
    (nsession spec c₀ [.base (.dispatch reserveOp), .base (.abandon reserveOp),
      .base (.respond ⟨.idle, Op.reserve, ()⟩), .base (.dispatch (commitOp .p1))]).2 =
      [none, none, some (.run (.abandoned reserveOp)), some (.run (.abandoned reserveOp))] := rfl

#tooth abandon_ends by mutation closedBy := fun {_ _ _ _ _ _ _ _ _} _ => none

/-- The commitment to `p2` dispatched, its reply missing. -/
def c₂ : NCfg :=
  (nsession spec c₀ (opening ++ [.base (.dispatch (commitOp .p1)), .advance (j := Phase.reserved) (),
    .base (.dispatch (commitOp .p2))])).1

/-- The general lost-reply theorem at the stranger's lost reply: whatever the world and the buyer
propose short of a reply (advances and choices included), the history, the spent capability and
the dispatches stay. -/
theorem lost_instance (evs : List NEv) (hno : ∀ ev ∈ evs, ∀ r, ev ≠ .base (.respond r)) :
    (nsession spec c₂ evs).1.cfg.obj.hist = c₂.cfg.obj.hist ∧ (nsession spec c₂ evs).1.cfg.spent = [.cap] ∧
      dispatchesOf (nsession spec c₂ evs).1.cfg.log = [reserveOp, commitOp .p2] ∧
      IsCall (nsession spec c₂ evs).1.cfg.res (commitOp .p2) :=
  clost_reply_frozen (csession_reachable .init _) (o := commitOp .p2) rfl evs hno

/-- The general completeness theorem at the negotiation: the template filled with `p1` is judged at
`Γ₀`, `[cap]`; at the world where everything holds, the driven run is `interpret`'s. -/
theorem typed_instance (H : Handler sig (fun _ => Nat)) (s : Nat) :
    ∃ n, (drive host spec H n c₀.cfg s).result? =
      some (interpret H (fill Ω (choose (plan .p1)) template) s) := by
  refine drive_complete H _ c₀.cfg s Δ₀ rfl rfl rfl (instantiations_hasProt.1 .p1) ?_ ?_ (by decide)
    (fun _ _ _ h => by cases h)
  · intro f hf
    simp only [Γ₀, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl <;> rfl
  · intro t _
    cases t
    exact ⟨rfl, by simp [c₀, Cfg.init, CCfg.init]⟩

/-! ## The selection decision is rechecked at dispatch

Astra's gap (`astra/ASTRA-SELECTION-20261031.md` §7.3): an operation account that omits a grant the
selected candidate cites. `laxSpec` requires nothing of a commitment; the slot still selects `p1`
for citing `p1`'s grant. -/

/-- The negotiation's accounts with every requirement dropped. -/
def laxSpec : Spec sig Tok Fact Ob := { spec with requires := fun _ => [] }

/-- Nothing stored: the start for the selection fixtures. -/
def c₀' : NCfg := CCfg.init (Cfg.init O₀ everything) fun _ _ => none

/-- With nothing stored, the policy chooses `p1` at the world where everything holds, citing its
grant and the deadline (the former `selects_p1`). -/
theorem selects_p1 :
    let c := (nsession laxSpec c₀' (opening.take 2 ++ [.advance (j := Phase.reserved) ()])).1
    c.stored .reserved () = some (.prov .p1) ∧ c.cfg.cites .reserved () = [.auth .p1, .beforeDeadline] :=
  ⟨rfl, rfl⟩

/-- **Refused by the decision**: reserve, the policy chooses `p1` (citing its grant), the grant is
revoked, commit on `p1`. `laxSpec` admits the commitment; the runner refuses it, naming the provider
hole and the grant its decision cited. -/
theorem decision_rechecked :
    (nsession laxSpec c₀' (opening.take 2 ++
      [.advance (j := Phase.reserved) (),
       .base (.world ⟨false, true, true, true, 1⟩),
       .base (.dispatch (commitOp .p1))])).2 =
      [none, none, none, none,
       some (.run (.unsupported (commitOp .p1) (some ⟨.reserved, ()⟩) [.auth .p1]))] :=
  rfl

#tooth decision_rechecked by mutation decisionDead := fun {_ _ _ _ _ _ _ _ _} _ _ _ => []

/-- The initial plan's decision: provider `p1`, citing what the slot's `p1` cites. -/
def initialCites : (j : Phase) → HoleN j → List Fact
  | .reserved, () => providers.supports (.prov .p1)
  | .idle, h => nomatch h
  | .done, h => nomatch h

/-- **The initial plan's decision is rechecked too**: a plan built with `p1` from the start,
`p1`'s grant revoked, an operation account (`laxSpec`) that omits the grant: the commitment is
refused, naming the provider hole and the grant its initial decision cited. -/
theorem initial_decision_rechecked :
    (nsession laxSpec (CCfg.init (Cfg.init O₀ everything initialCites) stored₀)
      (opening ++ [.base (.dispatch (commitOp .p1))])).2 =
      [none, none, none, some (.run (.unsupported (commitOp .p1) (some ⟨.reserved, ()⟩) [.auth .p1]))] :=
  rfl

#tooth initial_decision_rechecked by mutation decisionDead := fun {_ _ _ _ _ _ _ _ _} _ _ _ => []

/-- The contrast: started without citations, the same run goes out. -/
theorem uncited_start_admitted :
    (nsession laxSpec c₀ (opening ++ [.base (.dispatch (commitOp .p1))])).2 = [none, none, none, none] :=
  rfl

/-- The general theorem at the cited start: its log is `Legal` with those citations. -/
theorem initial_legal :
    Legal host laxSpec O₀ everything initialCites
      (nsession laxSpec (CCfg.init (Cfg.init O₀ everything initialCites) stored₀)
        (opening ++ [.base (.dispatch (commitOp .p1))])).1.cfg.log :=
  creachable_legal (csession_reachable .init _)

end Obend.Run.Negotiation

/-! ## Durable spending: a ticket the world keeps calling live -/

namespace Obend.Run.Ticket

open Obend.Slot Obend.Slot.Protocol

inductive Op : Unit → Type
  | use : Op ()

/-- One operation, spending the ticket, used again and again. -/
def sig : Sig Unit where
  Op := Op
  Resp := fun _ => Unit
  next := fun _ _ => ()

instance : DecidableEq (Σ i, sig.Op i) := fun
  | ⟨(), .use⟩, ⟨(), .use⟩ => isTrue rfl

def NoHole : Unit → Type := fun _ => Empty

instance : ∀ i, DecidableEq (NoHole i) := fun _ => inferInstanceAs (DecidableEq Empty)

/-- `use` spends the ticket (`Unit`); nothing is required, nothing owed. -/
def spec : Spec sig Unit Empty Empty where
  consumes := fun _ => some ()
  requires := fun _ => []
  establishes := fun _ => []

/-- A plan that uses the ticket twice (`HasProt` refuses it at one ticket; the runner, untyped,
refuses its second use when it comes). -/
def twice : Prot sig NoHole (fun _ => Unit) () :=
  .call (S := sig) Op.use fun _ => .call (S := sig) Op.use fun _ => .ret ()

def O : Open sig NoHole (fun _ => Unit) Unit Empty Empty () where
  template := twice
  Ω := fun _ h => nomatch h
  σ := fun _ _ => none
  Γ := []
  Δ := [()]
  Q := fun _ _ => True
  Φ := []
  hist := ⟨[], none⟩

/-- A world that always calls the ticket live. -/
def host : Host Unit Unit Empty where
  allowed := fun _ _ => true
  view := fun _ => ⟨(fun e => nomatch e), fun _ => true⟩

def useOp : Σ i, sig.Op i := ⟨(), Op.use⟩

/-- **Spent once**: the second use is refused, naming the ticket, although the world calls it live. -/
theorem second_use_refused :
    (session host spec (Cfg.init O ()) [.dispatch useOp, .respond ⟨(), Op.use, ()⟩, .dispatch useOp]).2 =
      [none, none, some (.unadmitted useOp [] (some ()))] := rfl

#tooth second_use_refused by mutation spendOn := fun {_ _ _ _ _} _ spent {_} _ => spent

end Obend.Run.Ticket

end
