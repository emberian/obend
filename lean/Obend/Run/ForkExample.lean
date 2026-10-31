module
/-
# Obend.Run.ForkExample — Bob offline, Alice on main, one ticket

The two buyers' ledger (`Obend.Run.SharedExample.nledger`). Bob forks the World at the start and works
offline: he notes a fact (monotone), tries to spend the capability in the fork (refused `notMine`:
the fork holds no token of the shared ledger) and defers his spend of it (escalated). Meanwhile
Alice wins the capability on main (`aliceFirst`, epoch 0). At the stitch, Bob's note merges and his
escalated spend is a conflict naming Alice and epoch 0 (`bob_offline_conflict`). Stitched into a
main where nobody took the capability, the same fork's spend commits through the ledger's step and
Bob is granted it at epoch 0 (`bob_offline_wins`).
-/
public import Obend.Run.Fork
public import Obend.Run.SharedExample
public import Obend.Tactic.Tooth
import all Obend.Run.Fork
import all Obend.Run.Shared
import all Obend.Run.SharedExample
@[expose] public section

namespace Obend.Run.ForkExample

open Obend.Slot.Protocol.Negotiation (Tok)
open Obend.Run.Shared Obend.Run.Fork Obend.Run.SharedExample

/-- The capability is the shared ledger's. -/
def shared : Tok → Bool := fun _ => true

/-- A fork's session. -/
def fsession : Fork Buyer Tok String → List (FRow Buyer Tok String) →
    Fork Buyer Tok String × List (Option (FRefusal Tok))
  | F, [] => (F, [])
  | F, r :: rs =>
    match forkStep shared F r with
    | .ok F' => let x := fsession F' rs; (x.1, none :: x.2)
    | .error w => let x := fsession F rs; (x.1, some w :: x.2)

/-- Bob's offline work, forked at the start. -/
def bobOffline := fsession (Fork.at nledger d₀) [.grow "quote noted", .spend .bob .cap, .defer .bob .cap]

/-- **In the fork, the capability is not Bob's**: his spend is refused `notMine`, his deferral is
escalated. -/
theorem fork_refuses :
    bobOffline.2 = [none, some (.notMine .cap), none] ∧ bobOffline.1.escalated = [(.bob, .cap)] := ⟨rfl, rfl⟩

/-- **The double spend across fork and main is refused, naming Alice and epoch 0**; Bob's note
merges. -/
theorem bob_offline_conflict :
    let r := stitch nledger ((bsession aliceFirst).1.led, []) bobOffline.1
    (r.2.map fun c => (c.1, c.2.1, c.2.2)) = [(.bob, .cap, .taken .cap .alice 0)] ∧ r.1.2 = ["quote noted"] ∧
      (r.1.1.grants.map fun g => (g.tok, g.winner, g.epoch)) = [(.cap, .alice, 0)] := ⟨rfl, rfl, rfl⟩

/-- **Where nobody took it, the escalated spend commits** through the ledger's step: Bob is granted
the capability at epoch 0. -/
theorem bob_offline_wins :
    let r := stitch nledger (d₀, []) bobOffline.1
    r.2.isEmpty = true ∧ (r.1.1.grants.map fun g => (g.tok, g.winner, g.epoch)) = [(.cap, .bob, 0)] := ⟨rfl, rfl⟩

/-- The general theorem at the fixture: the conflict is `stitch_double_spend` of Alice's grant. -/
theorem conflict_general :
    (Buyer.bob, Tok.cap, LClause.taken Tok.cap Buyer.alice 0) ∈
      (stitchRows nledger (bsession aliceFirst).1.led bobOffline.1.escalated).2 :=
  stitch_double_spend nledger [] (bsession aliceFirst).1.led .bob [] (g := ⟨.cap, .alice, 0⟩)
    ⟨rfl, by decide⟩ (by decide)

end Obend.Run.ForkExample

-- A fork that may spend shared tokens grants the capability twice.
#tooth Obend.Run.ForkExample.fork_refuses by mutation Obend.Run.Fork.forkStep :=
  fun {_ _ _} [_] _ F r => match r with
    | .spend _ t => .ok { F with spentHere := F.spentHere ++ [t] }
    | .grow m => .ok { F with grown := F.grown ++ [m] }
    | .mint t => .ok { F with own := F.own ++ [t] }
    | .defer i t => .ok { F with escalated := F.escalated ++ [(i, t)] }
-- A ledger whose commit does not refuse a consumed token stitches Bob's spend: two grants, no conflict.
#tooth Obend.Run.ForkExample.bob_offline_conflict by mutation Obend.Run.Shared.ledgerStep :=
  fun {_ _ _} [_] L d r => match r with
    | .commit i t => .ok (L.commit d i t)
    | .raw w => .ok (L.setRaw d w)
    | .abandon i => .ok (L.onAbandon d i)
    | .observe d' => .ok d'

end
