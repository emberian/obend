module
/-
# Obend.Run — the guarded runner

An executable runner for open objects that enforces authorization at dispatch and preserves the
accepted history across replanning, revocation and lost replies.

- `Obend.Run.Runner`: configurations, raw events, named refusals, `run`, `session`, `drive`.
- `Obend.Run.Spec`: the declarative specification of an accepted log (`Legal`), stated of the log.
- `Obend.Run.Fold`: `Legal` as one fold over an accumulator (`legal_iff_fold`), an instance of the
  audited fold `Obend.Fold.Admission` (`legal_iff_admission`, `legal_step_of_pins`).
- `Obend.Run.Proofs.Invariant`: `refines` (every reachable configuration satisfies `Inv`, so its log
  is `Legal`), the continuation clauses (`replan_accepted`, `replace_then_dispatch`, `inflight_busy`,
  `inflight_replan_refused`, `lost_reply_frozen`) and the guard (`run_replan_guard`).
- `Obend.Run.Proofs.Interpret`: `drive_sound`, `drive_complete` (the reference handler is an instance).
- `Obend.Run.Core4`, `Obend.Run.Proofs.Core4`: an emitted Core4 activity as the runner's protocol;
  `run_is_trace`, `trace_is_run` (its instance at a real program is the legacy leaf
  `Obend.Run.Core4Example`).
- `Obend.Run.Adapter`, `Obend.Run.Proofs.Adapter`: the Core4 adapter completed: replies typed
  against the declared response type, depth and ticks extended mid-run by re-basing the same log,
  choice points in emitted Plans decided as slots and rechecked at dispatch (`areachable_inv`,
  `plain_trace`; fixtures in `Obend.Run.Core4Example`).
- `Obend.Run.Control`, `Obend.Run.Proofs.Control`: selection control, mandatory for every hole (authenticated
  principals in a chooser office, decision revisions, tenure across an office change, the presets
  first-usable / incumbent-first / chooser-required with their choice laws, honest
  `nothingAdmissible` with exact diagnostics); `Obend.Run.ControlExample`, its fixtures.
- `Obend.Run.Shared`, `Obend.Run.Proofs.Shared`: any number of controlled runners over one World through a
  ledger with an atomic commit boundary, the ledger itself a member of the audited fold; each runner's
  log `Legal` by `Obend.Fold.project_moves_run` applied, grants exclusive,
  `OnceSpent` globally, the loser's refusal naming the winner and epoch; `Obend.Run.SharedExample`, two
  buyers and one capability.
- `Obend.Run.Durable`, `Obend.Run.Proofs.Durable`: the journal-first host (durable journal and outbox,
  volatile memory; the journal append the linearization point; recovery by replay): it refines the
  abstract commit, recovery restores the memory, and two exposed effects consuming one token are one,
  across any crashes; `Obend.Run.DurableExample`, two buyers and a crash between them.
- `Obend.Run.Fork`: the World fork for offline work (no token of the shared ledger, `notMine`;
  monotone rows merge by union; bounded rows escalate unjudged) and `stitch`, which replays each
  escalated dispatch through the joint transition at stitch time (the runner's `crun`, then the
  ledger's commit), atomically: one refusal leaves main unchanged and every refusal is a conflict kept
  as a section; a ticket double-spent across fork and main names the winner and the epoch. `Obend.Run.ForkExample`, Bob offline.
- `Obend.Run.Negotiation`: the stranger's example (revocation, a slot's replan, a lost reply), the
  fixture `interpret` delivers and the runner refuses, and the durable-spending ticket.
-/
public import Obend.Run.Runner
public import Obend.Run.Spec
public import Obend.Run.Fold
public import Obend.Run.Proofs.Invariant
public import Obend.Run.Proofs.Interpret
public import Obend.Run.Negotiation
public import Obend.Run.Core4
public import Obend.Run.Proofs.Core4
public import Obend.Run.Adapter
public import Obend.Run.Proofs.Adapter
public import Obend.Run.Control
public import Obend.Run.Proofs.Control
public import Obend.Run.ControlExample
public import Obend.Run.Shared
public import Obend.Run.Proofs.Shared
public import Obend.Run.SharedExample
public import Obend.Run.Durable
public import Obend.Run.Proofs.Durable
public import Obend.Run.DurableExample
public import Obend.Run.Fork
public import Obend.Run.ForkExample
