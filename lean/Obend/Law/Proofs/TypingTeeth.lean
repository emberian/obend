/-
# Obend.Law.Proofs.TypingTeeth — mutation teeth for `Obend.Law.Proofs.Typing` (a legacy leaf)

A `#tooth` re-checks every stored proof downstream of the mutated definition, and the typing
proofs go through the checker's own, whose bodies a `module` cannot see (`Obend/Tactic/Tooth.lean`).
A legacy file sees them, so the teeth live here; nothing imports this file.
-/
import Obend.Law.Proofs.Typing
import Obend.Tactic.Tooth
open Obend.Law Obend.Law.Typing

-- The skeleton's arms must cover the occasion sum, in its order.
#tooth lawOf6_checks by mutation occasionRow := .emptyRow
-- A clause reads the request at its declared type.
#tooth ownerSigns_checks by mutation reqTy := .natural
#tooth bounded_checks by mutation reqTy := .natural
-- A quorum's proposal and a machine's state are the sums the clauses eliminate.
#tooth quorum_checks by mutation proposalTy := fun _ => .natural
#tooth machine_checks by mutation stateTy := fun _ => .natural
-- A `keeps` invariant is a predicate on the state: typed at another codomain, the proof no longer checks.
#tooth keeps_typed by mutation invBinding := fun S => ⟨fnTy S .natural, .unrestricted⟩
