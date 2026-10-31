# Lane Expose: confine `@[expose]` to what reduction needs

Worktree: `/private/tmp/claude-501/-Users-ember-dev-obend/01a18fe9-771b-71b2-b01f-da7ed6517d48/scratchpad/cost`.

The one build-speed lever left (`lean/docs/REPORT-BUILD-20261101.md` gate table: a private proof
edit 5 s, an exposed def edit in `Term` 198 s under load, 177 of 277 tier-1 modules rebuilt). Read
`lean/docs/REPORT-20261030.md` §2 (the module discipline and why expose-all was chosen as a migration
expedient), `review/KIMI-REVIEW-20261030.md` §3 (the critique), `REPORT-BUILD-20261101.md` (the
measurement script `lean/tools/measure.sh` and the one-edit protocol), and the Lean 4.35 reference
on `module`, `@[expose]`, `public section` and `import all`.

Do: for each definitional module (`Core/{Term,Ty,Check,Machine,Data,Invariant,TypeGraph,Code}`,
`Slot/*`, `Law/*`, `Run/*`, `Doc/*`, `Fold`, `Judge`, `Receipt`, `Intention`, `Kind`, `Spec/*`),
replace the exposed section with `@[expose]` on exactly the definitions some downstream `decide`,
`rfl`, `simp` unfolding or kernel reduction needs (find them by removing exposure and reading the
errors; `import all` where a proof module genuinely needs a private body is acceptable and must be
named in the report), keep every theorem and every build green at each commit (one commit per
library), and repeat the one-edit measurement at the end: private proof edit, exposed def edit in
`Term`, and a body edit of a now-unexposed definition in `Check`, with modules rebuilt and seconds,
on a machine you state the load of. Also fix `GroundExecution`'s `import all` over every Adequacy
piece (REPORT-BUILD "not done"). Target from PLAN workstream 11: a `Check` edit stopping within
about twenty modules.

Conventions. Worktree as named (warm; `git checkout dev && git pull --rebase origin dev`, then branch); Lean v4.35.0; every file a `module`; the census is the only axiom check; set `git config core.hooksPath lean/tools/hooks` in the worktree so tier 2 runs pre-push; one measurement build at the start and one at the end, targeted builds between; Mini's cohorts (`python3 lean/tests/run-obend-source.py`), receipts (`run-receipts.py`), workspaces (`run-workspace.py`) and the vault walkthrough are the control. Named-file commits on `dev`, `git -c commit.gpgsign=false commit -F -`, trailer `Co-Authored-By: Claude Opus <noreply@anthropic.com>`, rebase before each push; one other Lean lane is live. No sorry, no axiom; every former theorem kept or an instance, named in the report. Report in `lean/docs/REPORT-<LANE>-20261101.md`. Ember: "Never kill by pattern. No `pkill -f <anything>`, no `pkill -x <bare word>`, no `killall`, no `kill -u`. A process you started is stopped by the PID in its PID file, and only that. Every detached job writes one (`nohup ... & echo $! > job.pid`). No PID file, no kill: tell me instead." When a disk is low: stop writing to it, tell Ember, wait. Reply with the commit range, what changed in statement, and the one decision for Ember.
