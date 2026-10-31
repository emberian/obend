module
/-
# Obend.Run.DurableExample — two buyers, one capability, a crash between them

The shared-World negotiation (`Obend.Run.SharedExample`: two buyers, one one-use capability, the
ledger `nledger`) run by the journal-first host (`Obend.Run.Durable`). Both reserve; Alice commits
(journal position 4) and her call is exposed under identity 4; the host crashes. While it is down,
Bob's commitment is refused (`down`). The host recovers by replaying the journal: Bob's commitment
is refused naming Alice and epoch 0, Alice's retried commitment is refused (her call is in flight),
and a second exposure of identity 4 is refused. A second crash in the middle of a recovery changes
nothing. `restart_receipt` is the session; `restart_general` is `exposed_once` at it.

Tooth: a recovery that forgets the journal (`replay` mutated to start over) admits Bob's commitment
after the restart: a second grant of the capability.
-/
public import Obend.Run.Proofs.Durable
public import Obend.Run.SharedExample
public import Obend.Tactic.Tooth
import all Obend.Run.Durable
import all Obend.Run.Shared
import all Obend.Run.SharedExample
@[expose] public section

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

-- A recovery that forgets the journal admits Bob after the restart.
#tooth Obend.Run.DurableExample.restart_receipt by mutation Obend.Run.Durable.replay :=
  fun {_ _ _ _ _ _ _ _ _ _ _ _} [_] [_] [_] [_] [_] [_] _ _ _ _ _ {_} J _ => some J

end
