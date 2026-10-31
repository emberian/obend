# Lane Build: tiers, splits, the kernel-evaluable type graph

Worktree: `/private/tmp/claude-501/-Users-ember-dev-obend/01a18fe9-771b-71b2-b01f-da7ed6517d48/scratchpad/build`.

Read `lean/docs/REPORT-PROOFENG-20261031.md` (heuristics; "what would be useful next"), `PLAN.md`
workstream 11, and `lean/lakefile.toml`. Five other lanes are editing `Core/Code`, `Equiv`, `Check`,
`Spec/C4`, `Run` concurrently; you own `lakefile.toml`, `Core/TypeGraph.lean`, `Core/DecisionReduction.lean`,
`Core/Proofs/{Adequacy,Collect,Substitution}.lean` and their split products, `Core/Proofs/Preservation/Base.lean`,
and `lean/README.md`'s build section. Do not touch `@[expose]` sections in definitional modules (that
pass is queued for when the tree is quiet).

Deliver, one commit each: (1) two build tiers: `lake build` builds definitions and proofs; teeth and
the census move to a second target (`lake build Obend.Census Teeth`) run pre-push; document it. (2) Split
`Adequacy` (4,939 lines), `Substitution`, `Collect` and `Preservation/Base` at their section boundaries
into parallel modules with every theorem name kept (deprecated aliases if a name must move); measure the
clean-build wall time once before and once after on this machine. (3) `stepRaw_lexicalInvariant` as one
lemma per transition. (4) The type-graph worklist made kernel-evaluable (structural or fuel-bounded with
the bound a theorem), so `decide +kernel` covers every checker tooth and `equirec_reduce` is deleted.
Gate: the one-edit measurement from `REPORT-20261030.md` §4 repeated once (a private proof edit in
Adequacy's largest piece; an exposed def edit in `Term`) with the numbers in the report.

Conventions. Lean v4.35.0; every file a `module` (`lean/docs/REPORT-20261030.md` §2); the census in `Obend/Census.lean` is the only axiom check, add no `#assert_axioms` lines; one measurement build at the start and one at the end, targeted `lake build Obend.<Lib>` between; Mini's cohorts (`python3 lean/tests/run-obend-source.py`) and the receipt tests (`python3 lean/tests/run-receipts.py`) are the control. Named-file commits on `dev`, `git -c commit.gpgsign=false commit -F -`, trailer `Co-Authored-By: Claude Opus <noreply@anthropic.com>`, `git pull --rebase origin dev` before each push and resolve only your own files; five other lanes are live in their own worktrees, listed in `PLAN.md`. No sorry, no axiom; statements may be restructured for compositionality when every former theorem is kept or follows, named in the report; a theorem that could be vacuous gets a `#tooth` (`Obend/Tactic`). Report in `lean/docs/REPORT-<LANE>-20261101.md` in the lane-report style. The trees under `~/dev` other than `obend` are read-only. Ember: "Never kill by pattern. No `pkill -f <anything>`, no `pkill -x <bare word>`, no `killall`, no `kill -u`. A process you started is stopped by the PID in its PID file, and only that. Every detached job writes one (`nohup ... & echo $! > job.pid`). No PID file, no kill: tell me instead." When a disk is low: stop writing to it, tell Ember, wait. Reply with the commit range, what is fully proved, and the one decision for Ember.
