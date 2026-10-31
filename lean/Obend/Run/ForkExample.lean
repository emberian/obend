module
/-
# Obend.Run.ForkExample — Bob offline, Alice on main, one ticket

The two buyers' joint run (`Obend.Run.SharedExample`). Bob forks the World at the start and works
offline: he notes a fact (monotone), tries to spend the capability in the fork (refused `notMine`:
the fork holds no token of the shared ledger) and defers his commitment (escalated, unjudged).

- Meanwhile Alice wins the capability on main (`aliceFirst`, epoch 0). At the stitch, Bob's note
  merges and his escalated commitment is a conflict naming Alice and epoch 0 (`bob_offline_conflict`).
- Stitched into a main where both reserved and nobody took the capability, the same commitment is
  judged by Bob's runner and committed by the ledger: Bob is granted it at epoch 0 (`bob_offline_wins`).
- Stitched into a main where Bob never reserved, his runner refuses the commitment (the protocol is
  not at a commitment) and nothing is granted (`runner_judges_escalation`): the stitch does not
  bypass the runner. The tooth is the former stitch, a commit through the ledger's step alone.
- Two escalated commitments, the second refused: the first is not committed either and main is
  unchanged (`two_step_atomic`). The tooth is a non-atomic settlement.
-/
public import Obend.Run.Fork
public import Obend.Run.SharedExample
public import Obend.Tactic.Tooth
import all Obend.Run.Fork
import all Obend.Run.Shared
import all Obend.Run.SharedExample
@[expose] public section

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

-- A fork that may spend shared tokens grants the capability twice.
#tooth Obend.Run.ForkExample.fork_refuses by mutation Obend.Run.Fork.forkStep :=
  fun {_ _ _ _} [_] _ _ F r => match r with
    | .spend _ t => .ok { F with spentHere := F.spentHere ++ [t] }
    | .grow m => .ok { F with grown := F.grown ++ [m] }
    | .mint t => .ok { F with own := F.own ++ [t] }
    | .defer e => .ok { F with escalated := F.escalated ++ [e] }
-- Without the shared mask, Bob's runner admits his escalated commitment and it is granted too.
#tooth Obend.Run.ForkExample.bob_offline_conflict by mutation Obend.Run.Shared.sharedLive :=
  fun {_ _ _ _} [_] _ base d t => (base (Obend.Run.Shared.Ledger.raw _ d)).live t
-- The former stitch: each escalated row a commit through the ledger's step alone, bypassing the
-- runner. Bob is granted the capability at a main where he never reserved.
#tooth Obend.Run.ForkExample.runner_judges_escalation by mutation Obend.Run.Fork.jstep :=
  fun {_ _ _ _ _ _ _ _ _ _ _ _} [_] [_] [_] [_] [_] [_] L _ sp _ _ {_} J e =>
    match Obend.Run.Shared.ledgerStep L J.led (Obend.Run.Shared.ledgerRowOf L (sp e.1) J.led e.1 e.2) with
    | .ok d => .ok { J with led := d }
    | .error c => .error (.ledger c)
-- A non-atomic settlement: the first commitment stays committed although the second was refused.
#tooth Obend.Run.ForkExample.two_step_atomic by mutation Obend.Run.Fork.settle :=
  fun {_ _ _} _ tentative _ => tentative
