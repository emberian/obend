# Lane Runner-2: durable commit, the ledger as a fold member, consensus time, fork and stitch

Worktree: `/private/tmp/claude-501/-Users-ember-dev-obend/01a18fe9-771b-71b2-b01f-da7ed6517d48/scratchpad/runner2`.

Read `lean/docs/REPORT-SLOTRUN-20261031.md` (follow-up: what the shared layer could not cover),
`REPORT-JUDGE-20261031.md` (the decision: should the ledger's view commit pins), `DESIGN.md` §3,
`astra/ASTRA-VISION-20261031.md` §5.2 and §8.E, `review/VISION-CLAUDE-20261031.md` §2.1 items 4–5 and
§7.4 (ledger time, fork and stitch), then `Run/Shared.lean`, `Run/Fold.lean`, `Fold.lean`, `Receipt.lean`.

Deliver, one commit each: (1) the ledger as a fold member: its commit is a member row, so
`joint_reachable_projects_legal` is `project_run` applied and `Ledger.Durable` is a structure field
with an erasing-ledger tooth stated against the structure; (2) the ledger's view commits pins: a
Merkle map per view (cSHAKE over `Digest`) so a World-transition receipt's openings check against the
root and the view becomes `checked`; `dated : View` is that root; `obend verify` re-checks openings;
(3) consensus time: `height` is a ledger fact every law reads, never a request field (`Law.Syntax`'s
request-carried height retired; a request claiming a future height refused); (4) durable commit and
recovery: a journal-first commit with the linearization point stated (authorized state, spent token,
in-flight record, receipt identity durable before exposure), recovery by replay plus a durable outbox,
and the theorem that two competing clients cannot spend one token twice across a restart; (5) World
fork and stitch (`Run/Fork.lean`): a fork holds no token of the shared ledger (`notMine`), `stitch` is a
commit through the shared step, monotone rows merge by union, bounded ones escalate, conflicts are
sections; a double-spent ticket across fork and main refused naming the epoch.

Conventions. Lean v4.35.0; every file a `module` (`lean/docs/REPORT-20261030.md` §2); the census in `Obend/Census.lean` is the only axiom check, add no `#assert_axioms` lines; one measurement build at the start and one at the end, targeted `lake build Obend.<Lib>` between; Mini's cohorts (`python3 lean/tests/run-obend-source.py`) and the receipt tests (`python3 lean/tests/run-receipts.py`) are the control. Named-file commits on `dev`, `git -c commit.gpgsign=false commit -F -`, trailer `Co-Authored-By: Claude Opus <noreply@anthropic.com>`, `git pull --rebase origin dev` before each push and resolve only your own files; five other lanes are live in their own worktrees, listed in `PLAN.md`. No sorry, no axiom; statements may be restructured for compositionality when every former theorem is kept or follows, named in the report; a theorem that could be vacuous gets a `#tooth` (`Obend/Tactic`). Report in `lean/docs/REPORT-<LANE>-20261101.md` in the lane-report style. The trees under `~/dev` other than `obend` are read-only. Ember: "Never kill by pattern. No `pkill -f <anything>`, no `pkill -x <bare word>`, no `killall`, no `kill -u`. A process you started is stopped by the PID in its PID file, and only that. Every detached job writes one (`nohup ... & echo $! > job.pid`). No PID file, no kill: tell me instead." When a disk is low: stop writing to it, tell Ember, wait. Reply with the commit range, what is fully proved, and the one decision for Ember.
