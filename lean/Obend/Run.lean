module
/-
# Obend.Run — the guarded runner

An executable runner for open objects that enforces authorization at dispatch and preserves the
accepted history across replanning, revocation and lost replies.

- `Obend.Run.Runner`: configurations, raw events, named refusals, `run`, `session`, `drive`,
  `resolveEvent`.
- `Obend.Run.Spec`: the declarative specification of an accepted log (`Legal`), stated of the log.
- `Obend.Run.Proofs.Invariant`: `refines` (every reachable configuration satisfies `Inv`, so its log
  is `Legal`), the continuation clauses (`replan_accepted`, `replace_then_dispatch`, `inflight_busy`,
  `inflight_replan_refused`, `lost_reply_frozen`) and the guard (`run_replan_guard`).
- `Obend.Run.Proofs.Interpret`: `drive_sound`, `drive_complete` (the reference handler is an instance).
- `Obend.Run.Core4`, `Obend.Run.Proofs.Core4`: an emitted Core4 activity as the runner's protocol;
  `run_is_trace`, `trace_is_run` (its instance at a real program is the legacy leaf
  `Obend.Run.Core4Example`).
- `Obend.Run.Negotiation`: the stranger's example (revocation, a slot's replan, a lost reply), the
  fixture `interpret` delivers and the runner refuses, and the durable-spending ticket.
-/
public import Obend.Run.Runner
public import Obend.Run.Spec
public import Obend.Run.Proofs.Invariant
public import Obend.Run.Proofs.Interpret
public import Obend.Run.Negotiation
public import Obend.Run.Core4
public import Obend.Run.Proofs.Core4
