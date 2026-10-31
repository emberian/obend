module
/-
# Obend.Run.Negotiation — the stranger's example, and the runner's teeth

The negotiation of `Obend.Slot.Protocol.Negotiation` (reserve a deposit, then commit a one-use
capability on a provider the buyer chooses, or cancel), run end to end by the guarded runner against
a host world in which grants come and go and the deadline, once passed, stays passed.
-/
public import Obend.Run.Proofs.Interpret
public import Obend.Slot.Proofs.Negotiation
public import Obend.Tactic.Tooth
public import Obend.AxiomPin
import all Obend.Run.Runner
import all Obend.Run.Spec
@[expose] public section

namespace Obend.Run.Negotiation

open Obend.Slot Obend.Slot.Protocol Obend.Slot.Protocol.Negotiation

instance decOp : (i : Phase) → DecidableEq (Op i)
  | _, .reserve, .reserve => isTrue rfl
  | _, .commit p, .commit q =>
    if h : p = q then isTrue (by rw [h]) else isFalse (by intro e; cases e; exact h rfl)
  | _, .commit _, .cancel => isFalse (by intro e; cases e)
  | _, .cancel, .commit _ => isFalse (by intro e; cases e)
  | _, .cancel, .cancel => isTrue rfl

instance : DecidableEq (Σ i, sig.Op i) := inferInstanceAs (DecidableEq (Σ i, Op i))

/-! ## The host's world -/

/-- What the host's world says: each provider's grant, the deadline, whether the capability is live. -/
structure Wv where
  grant1 : Bool
  grant2 : Bool
  beforeDeadline : Bool
  capLive : Bool
deriving DecidableEq, Repr

def holdsW (v : Wv) : Fact → Bool
  | .auth .p1 => v.grant1
  | .auth .p2 => v.grant2
  | .beforeDeadline => v.beforeDeadline

/-- The world's audited step: anything but un-passing the deadline. Grants are revoked and restored,
and the world may even call the spent capability live again. -/
def stepW (v v' : Wv) : Bool := v.beforeDeadline || !v'.beforeDeadline

/-- The world as a `World`: each fact is its own cell, pinned to its truth. -/
instance : World Wv Fact where
  Cell := Fact
  Pin := Bool
  cell := id
  pin := fun v f => some (holdsW v f)
  holdsAt := holdsW
  Step := fun v v' => stepW v v' = true
  holds_congr := fun _ _ _ h => Option.some.inj h
  retired_dead := fun _ _ h => by cases h
  retired_step := fun _ _ _ _ h => by cases h

/-- The host: the `World`'s step and truth, the capability live as the world says. -/
def host : Host Wv Tok Fact :=
  Host.ofWorld (fun v v' => inferInstanceAs (Decidable (stepW v v' = true))) fun v _ => v.capLive

/-! ## The object and the provider slot -/

/-- The negotiation, nothing done yet, planning on provider `p1`. -/
def O₀ : Open sig HoleN Res Tok Fact Ob .idle := obj (plan .p1) ⟨[], none⟩

def everything : Wv := ⟨true, true, true, true⟩

def c₀ : Cfg sig HoleN Res Tok Fact Ob Wv .idle := Cfg.init O₀ everything

/-- The provider hole as a slot: provider `p` cites its grant and the deadline; cancelling cites
nothing. The buyer prefers `p1`, then `p2`, then cancelling. -/
def providers : Slot Fact (Option Provider) where
  supports := fun
    | some p => [.auth p, .beforeDeadline]
    | none => []
  judge := fun _ => true

def body : Option Provider → P .reserved
  | some p => plan p
  | none => cancelPlan

def order : List (Option Provider) := [some .p1, some .p2, none]

/-! ## The stranger's example -/

def reserveOp : Σ i, sig.Op i := ⟨.idle, Op.reserve⟩
def commitOp (p : Provider) : Σ i, sig.Op i := ⟨.reserved, Op.commit p⟩

/-- The script up to the revocation: reserve, its reply, `p1`'s grant revoked. -/
def opening : List (Event sig HoleN Res Fact Wv) :=
  [.dispatch reserveOp, .respond ⟨.idle, Op.reserve, ()⟩, .world ⟨false, true, true, true⟩]

def c₁ : Cfg sig HoleN Res Tok Fact Ob Wv .idle := (session host spec c₀ opening).1

/-- At the revoked view the slot resolves to `p2`. -/
theorem resolves_p2 :
    resolveEvent host c₁ providers (j := Phase.reserved) () body order =
      .ok (.replan (j := Phase.reserved) () (plan .p2) [.auth .p2, .beforeDeadline]) := rfl

/-- The same replan by the slot's incumbent-first policy (`slotAdvance`), with `p1` stored: the stored
selection is no longer usable, so the policy selects `p2`; any other policy with TRANSITION would
be admissible here too (`resolveEventBy_ok`). -/
theorem resolvesBy_p2 :
    resolveEventBy slotAdvance c₁ providers (j := Phase.reserved) () body order (some (some .p1)) =
      .ok (.replan (j := Phase.reserved) () (plan .p2) [.auth .p2, .beforeDeadline]) := rfl

/-- The rest: commit on `p1` (refused, the grant is gone), the slot's replan to `p2`, commit on `p2`
(accepted: the capability is spent), then its reply is LOST. The world restores `p1`'s grant and
calls the capability live again; the buyer tries to cancel, to go back to `p1`, to keep `p2` with
another continuation, to commit on `p1`; a late reply arrives for the commit on `p1`; the deadline
passes, and the world tries to un-pass it. The buyer gives up on the commitment (`abandon`): the
reply that finally arrives, a cancellation and a new commitment are all refused; the world still
moves. -/
def rest : List (Event sig HoleN Res Fact Wv) :=
  [.dispatch (commitOp .p1),
   .replan (j := Phase.reserved) () (plan .p2) [.auth .p2, .beforeDeadline],
   .dispatch (commitOp .p2),
   .world everything,
   .replan (j := Phase.reserved) () cancelPlan [],
   .replan (j := Phase.reserved) () (plan .p1) [.auth .p1, .beforeDeadline],
   .replan (j := Phase.reserved) () (planFlip .p2) [.auth .p2, .beforeDeadline],
   .dispatch (commitOp .p1),
   .respond ⟨.reserved, Op.commit .p1, true⟩,
   .world ⟨true, true, false, true⟩,
   .world everything,
   .abandon (commitOp .p2),
   .respond ⟨.reserved, Op.commit .p2, true⟩,
   .replan (j := Phase.reserved) () cancelPlan [],
   .dispatch (commitOp .p1),
   .world ⟨false, false, false, true⟩]

def script : List (Event sig HoleN Res Fact Wv) := opening ++ rest

def final : Cfg sig HoleN Res Tok Fact Ob Wv .idle := (session host spec c₀ script).1

/-- **The receipt**: which events were accepted, and why each refused one was refused. -/
theorem receipt :
    (session host spec c₀ script).2 =
      [none, none, none,
       some (.unadmitted (commitOp .p1) [.auth .p1] none),
       none, none, none,
       some (.replacesInflight (commitOp .p2) ⟨.reserved, ()⟩),
       some (.replacesInflight (commitOp .p2) ⟨.reserved, ()⟩),
       some (.replacesInflight (commitOp .p2) ⟨.reserved, ()⟩),
       some (.busy (commitOp .p2)),
       some (.unsolicited ⟨.reserved, Op.commit .p1, true⟩),
       none,
       some .worldStep,
       none,
       some (.abandoned (commitOp .p2)),
       some (.abandoned (commitOp .p2)),
       some (.abandoned (commitOp .p2)),
       none] := rfl

/-- **What had to stay**: the accepted history is the reservation answered and the commitment to
`p2` dispatched and never answered; the capability is spent once; the plan in force is `p2`'s; the
residual's next call is that commitment; the run is ended by abandoning it, and the obligations
established are the deposit and the payment to `p2`, which the abandonment does not discharge. -/
theorem stayed :
    final.obj.hist.answered = [⟨.idle, Op.reserve, ()⟩] ∧
      final.obj.hist.inflight = some (commitOp .p2) ∧ final.spent = [.cap] ∧
      final.obj.σ .reserved () = some (plan .p2) ∧ IsCall final.res (commitOp .p2) ∧
      dispatchesOf final.log = [reserveOp, commitOp .p2] ∧
      final.ended = some (commitOp .p2) ∧
      final.obj.hist.established spec = [.holdDeposit, .pay .p2] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **What changed**: the revocation moved the plan from `p1` to `p2` before anything was
dispatched in the hole; the world ends past the deadline with both grants revoked (it moves after
the run has ended). -/
theorem changed :
    c₁.obj.σ .reserved () = some (plan .p1) ∧ final.obj.σ .reserved () = some (plan .p2) ∧
      final.world = ⟨false, false, false, true⟩ := ⟨rfl, rfl, rfl⟩

-- Without the replan guard the three replans in flight are not refused by name (the cancellation
-- and the return to `p1` become `inconsistent`, and the same-first-call `planFlip` is ACCEPTED).
#tooth receipt by mutation frozenHole := fun {_ _ _ _} [_] {_ _ _ _} _ => none
-- Without durable spending the capability the world calls live again is unspent.
#tooth stayed by mutation spendOn := fun {_ _ _ _ _} _ spent {_} _ => spent

/-- The run's log is `Legal`, by the general theorem. -/
theorem script_legal : Legal host spec O₀ everything final.log :=
  reachable_legal (session_reachable .init script)

/-! ## The fixture the library could not refuse -/

/-- Every required fact false, the capability live (`astra/ASTRA-EVAL-20261031.md`, line 105). -/
def withdrawn : Wv := ⟨false, false, false, true⟩

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
    (drive host spec (env true) 3 c₀ 0).result? =
      some (interpret (env true) (fill Ω (choose (plan .p1)) template) 0) := rfl

/-- **A lost reply is not retried**: with the reservation in flight, a second reservation (which
needs no fact and spends no token, so admission alone would let it through) is refused `busy`. -/
theorem reserve_retry_refused :
    (session host spec c₀ [.dispatch reserveOp, .dispatch reserveOp]).2 =
      [none, some (.busy reserveOp)] := rfl

#tooth reserve_retry_refused by mutation awaiting := fun {_ _} _ => none

/-- **After abandonment, no new commitment**: the reservation is abandoned in flight; its late
reply and a commitment on `p1` (admissible: every grant holds) are refused, naming the abandoned
call. Without the guard the late reply would revive the plan and the commitment would go out. -/
theorem abandon_ends :
    (session host spec c₀ [.dispatch reserveOp, .abandon reserveOp,
      .respond ⟨.idle, Op.reserve, ()⟩, .dispatch (commitOp .p1)]).2 =
      [none, none, some (.abandoned reserveOp), some (.abandoned reserveOp)] := rfl

#tooth abandon_ends by mutation closedBy := fun {_ _ _ _ _ _ _ _ _} _ => none

/-- The commitment to `p2` dispatched, its reply missing. -/
def c₂ : Cfg sig HoleN Res Tok Fact Ob Wv .idle :=
  (session host spec c₀ (opening ++ [.dispatch (commitOp .p1),
    .replan (j := Phase.reserved) () (plan .p2) [.auth .p2, .beforeDeadline], .dispatch (commitOp .p2)])).1

/-- The general lost-reply theorem at the stranger's lost reply: whatever the world and the buyer
propose short of a reply, the history, the spent capability and the dispatches stay. -/
theorem lost_instance (evs : List (Event sig HoleN Res Fact Wv)) (hno : ∀ e ∈ evs, e.isRespond = false) :
    (session host spec c₂ evs).1.obj.hist = c₂.obj.hist ∧ (session host spec c₂ evs).1.spent = [.cap] ∧
      dispatchesOf (session host spec c₂ evs).1.log = [reserveOp, commitOp .p2] ∧
      IsCall (session host spec c₂ evs).1.res (commitOp .p2) := by
  have hc : Reachable host spec (Cfg.init O₀ everything) c₂ := session_reachable .init _
  have := lost_reply_frozen hc (o := commitOp .p2) rfl evs hno
  exact this

/-- The general completeness theorem at the negotiation: the template filled with `p1` is judged at
`Γ₀`, `[cap]`; at the world where everything holds, the driven run is `interpret`'s. -/
theorem typed_instance (H : Handler sig (fun _ => Nat)) (s : Nat) :
    ∃ n, (drive host spec H n c₀ s).result? =
      some (interpret H (fill Ω (choose (plan .p1)) template) s) := by
  refine drive_complete H _ c₀ s Δ₀ rfl rfl rfl (instantiations_hasProt.1 .p1) ?_ ?_ (by decide)
    (fun _ _ _ h => by cases h)
  · intro f hf
    simp only [Γ₀, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl <;> rfl
  · intro t _
    cases t
    exact ⟨rfl, by simp [c₀, Cfg.init]⟩

/-! ## The selection decision is rechecked at dispatch

Astra's gap (`astra/ASTRA-SELECTION-20261031.md` §7.3): an operation account that omits a grant the
selected candidate cites. `laxSpec` requires nothing of a commitment; the slot still selects `p1`
for citing `p1`'s grant. -/

/-- The negotiation's accounts with every requirement dropped. -/
def laxSpec : Spec sig Tok Fact Ob := { spec with requires := fun _ => [] }

/-- The slot selects `p1` at the world where everything holds, citing its grant and the deadline. -/
theorem selects_p1 :
    resolveEvent host (session host laxSpec c₀ (opening.take 2)).1 providers (j := Phase.reserved) ()
        body order =
      .ok (.replan (j := Phase.reserved) () (plan .p1) [.auth .p1, .beforeDeadline]) := rfl

/-- **Refused by the decision**: reserve, select `p1` (citing its grant), revoke the grant, commit on
`p1`. `laxSpec` admits the commitment; the runner refuses it, naming the provider hole and the
grant its decision cited. -/
theorem decision_rechecked :
    (session host laxSpec c₀ (opening.take 2 ++
      [.replan (j := Phase.reserved) () (plan .p1) [.auth .p1, .beforeDeadline],
       .world ⟨false, true, true, true⟩,
       .dispatch (commitOp .p1)])).2 =
      [none, none, none, none, some (.unsupported (commitOp .p1) (some ⟨.reserved, ()⟩) [.auth .p1])] :=
  rfl

#tooth decision_rechecked by mutation decisionDead := fun {_ _ _ _ _ _ _ _ _} _ _ _ => []

#assert_axioms resolvesBy_p2 selects_p1 decision_rechecked
#assert_axioms resolves_p2 receipt reserve_retry_refused abandon_ends lost_instance typed_instance stayed changed script_legal withdrawn_refused everything_delivers

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

#assert_axioms second_use_refused

end Obend.Run.Ticket

end
