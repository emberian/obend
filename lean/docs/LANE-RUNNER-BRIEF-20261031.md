# Lane Runner: the guarded runner and admission-preserving replanning

The contribution theorem Astra named (`astra/ASTRA-EVAL-20261031.md` lines 97–111, read all of it
first): executable admission-preserving replanning across revocation and lost replies. Today the
library is not an authorization-enforcing runner: with every required fact false and the capability
live, `admitOp` says false for a commit while `interpret` still delivers it (line 105; both in
`lean/Obend/Slot/Protocol.lean`, `interpret` at :207, `admitOp` at :290, `Prot` at :80; proofs in
`Slot/Proofs/{Protocol,ProtocolTyping,Negotiation}.lean`). Build the runner that closes that gap and
prove the theorem.

Design: `Obend/Run/` (root `Obend/Run.lean`): a configuration holding the open object, the residual
protocol, the answered and in-flight history, the current support view and the durable spent-token
state; transitions for world update (any allowed `World` step), replan (changes only undispatched
choices, preserves accepted history), dispatch (commits current admission through `admitOp` before
the handler sees the operation, consuming the token) and response (belongs to the recorded in-flight
operation). The invariant over every reachable configuration: every dispatched operation was
admitted at its dispatch view; no consumed token dispatches twice; an unanswered dispatched
operation is never replaced by an alternative plan; before dispatch a compatible currently admitted
replacement can take the next step, and after dispatch a missing reply licenses no new commitment.
State it as one invariant/refinement over the transition system, prove it by induction on reachability,
and connect it to the existing `interpret`/`resolve` so the reference handler is an instance. Add the
countermodel teeth: the fixture at line 105 must be *refused* by the runner, and a replan that
would replace an in-flight operation must be refused by name. Then write the stranger's example:
the negotiation fixture with a grant revoked mid-plan and one lost reply, run end to end, with the
receipt showing what changed and what had to stay.

Work in your own git worktree (`git worktree add /private/tmp/claude-501/-Users-ember-dev-obend/01a18fe9-771b-71b2-b01f-da7ed6517d48/scratchpad/<lane> dev`), since three other lanes build concurrently. Lean v4.35.0; `LEAN_NUM_THREADS=2 lake build 2>&1 | tee build.log` (177 jobs full; build your library by name while iterating). Every file a `module` (`lean/docs/REPORT-20261030.md` §2). Commit named files on `dev`, `git -c commit.gpgsign=false commit -F -`, trailer `Co-Authored-By: Claude Opus <noreply@anthropic.com>`, rebase on `origin/dev` before each push and resolve only your files. No sorry, no axiom, no weakened statement; every theorem that could be vacuous gets a `#tooth` (`Obend/Tactic`). Write a report in `lean/docs/` in the style of `REPORT-20261030.md`. The trees under `~/dev` other than `obend` are read-only. Ember: "Never kill by pattern. No `pkill -f <anything>`, no `pkill -x <bare word>`, no `killall`, no `kill -u`. A process you started is stopped by the PID in its PID file, and only that. Every detached job writes one (`nohup ... & echo $! > job.pid`). No PID file, no kill: tell me instead." When a disk is low: stop writing to it, tell Ember, wait. Reply with the commit range, what is fully proved, and the one decision for Ember.
