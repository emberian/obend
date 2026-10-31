module
/-
# Obend.Run.SharedExample — two buyers, one capability: the first instance of the shared layer

Two buyers each run the negotiation (`Obend.Run.Negotiation`: reserve, then commit the one-use
capability on a provider, every decision through the provider hole's selection control) over one
World and one capability. The ledger (`nledger`) is the authoritative record: the raw world, the
consumed tokens, the grants.

- `naive_two_grants` / `local_legal_does_not_imply_global_once`: two separate runners, each at its
  own copy of the world, each log `Legal`, and the capability is granted twice.
- `alice_wins`, `bob_wins`: through the ledger, whichever commits first wins; the other is refused
  naming the winner and the epoch. Both orderings.
- `lost_reply_receipt`: Alice's commitment is dispatched and its reply lost; the raw world calls the
  capability dead and then live again; Alice abandons; Bob is still refused, naming Alice.
- Teeth: without the shared mask (`sharedLive`) Bob is granted too; an abandonment that erases the
  ledger's consumption (`ledgerAbandon`) is not a `Ledger` at all (durability is a field, and the
  record `nledger` fails to be one), and run as a bare record it lets Bob through after Alice
  abandons.
-/
public import Obend.Run.Proofs.Shared
public import Obend.Run.Negotiation
public import Obend.Tactic.Tooth
import all Obend.Run.Runner
import all Obend.Run.Control
import all Obend.Run.Shared
import all Obend.Run.Negotiation
@[expose] public section

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
def ledgerAbandon (d : NRec) : NRec := d

/-- **What `Ledger`'s durability fields ask of this record**: an abandonment keeps the consumption
and the grants. The structure consumes exactly this (`nledger.abandon_spent`, `abandon_grants`); the
tooth below is the erasing record, which fails it, so it is not a `Ledger`. -/
theorem ledgerAbandon_durable (d : NRec) : (ledgerAbandon d).spent = d.spent ∧ (ledgerAbandon d).grants = d.grants :=
  ⟨rfl, rfl⟩

/-- The negotiation's ledger. -/
def nledger : Ledger Buyer Wv Tok where
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
       some (.taken .cap .alice 0), none, some (.taken .cap .alice 0)] := rfl

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

-- Without the shared mask, Bob's commitment is admitted at his own view: two grants.
#tooth alice_wins by mutation sharedLive := fun {_ _ _ _} [_] _ base d t => (base (Ledger.raw _ d)).live t
-- Durability is a field: a record whose abandonment erases the consumption fails the obligation the
-- structure consumes, so it is not a `Ledger` (and `nledger` cannot be rebuilt over it).
#tooth ledgerAbandon_durable by mutation ledgerAbandon := fun d => ⟨d.raw, [], d.grants, d.height⟩
-- Without propagating the ledger's moves, Bob does not see Alice's commit.
#tooth coupled_after_commit by mutation propagate :=
  fun {_ _ _ _ _ _ _ _ _ _ _} _ {_} _ _ cs => .ok cs

end Obend.Run.SharedExample

end
