# Lane Kinds: the nominal kind cell, one `Intention` module, C4 proved

Worktree: `/private/tmp/claude-501/-Users-ember-dev-obend/01a18fe9-771b-71b2-b01f-da7ed6517d48/scratchpad/kinds`.

Ember decided nominal kinds. Read `DESIGN.md` §4–§5, `review/GENERALIZATION-20261031.md` G3,
`lean/docs/REPORT-EXTENDS-20261031.md` (its decision and "not done"), `REPORT-LAWFINISH-20261031.md`
§2 (the checked `precedence` and what `linearize` lacks), `REPORT-VAULT-20261031.md` (`_kind.md`),
then `Spec/Ecosystem.lean`, `Spec/C4.lean`, `Law/Inherit.lean`, `Doc/Section.lean`, `Vault/*.lean`.

Deliver, one commit each: (1) the kind cell: a kind is a cell with its own law; every instance carries
its kind's identity; the kind's law is an ancestor of each instance's effective law
(`kind_law_inherited`); protocol dispatch is by kind, so two kinds with equal fields are distinguished
(the Extends decision's tooth); `create --from K` births under it; the vault's `_kind.md` becomes a
real kind. (2) `Obend/Intention.lean`: one structure for a named reference resolved against a World
(candidates are pins, the chooser is the name's owner, the support is "the record names v at p",
staleness is the blocked read), with `resolve`, `recite`, `renew` as one repair; re-base package
parents (`Spec/Ecosystem`) and cites (`Doc/Section`) onto it with their theorems kept (`stale_iff_blocked`,
`pinned_cite_stays`, `following_cite_behind`, `recite_holds` as instances), and add the kind reference
as the third instance; retire the duplicated resolution code. (3) C4 `linearize` rewritten structurally
and proved: monotonicity, local precedence (Barrett et al. 1996, `~/paperbin/barrett1996-…`), the
suffix property, and `c3_tree_is_chain` as a corollary; `precedence`'s runtime check becomes a theorem
and is retired; the 4000 seeded vectors stay as a test.

Conventions. Lean v4.35.0; every file a `module` (`lean/docs/REPORT-20261030.md` §2); the census in `Obend/Census.lean` is the only axiom check, add no `#assert_axioms` lines; one measurement build at the start and one at the end, targeted `lake build Obend.<Lib>` between; Mini's cohorts (`python3 lean/tests/run-obend-source.py`) and the receipt tests (`python3 lean/tests/run-receipts.py`) are the control. Named-file commits on `dev`, `git -c commit.gpgsign=false commit -F -`, trailer `Co-Authored-By: Claude Opus <noreply@anthropic.com>`, `git pull --rebase origin dev` before each push and resolve only your own files; five other lanes are live in their own worktrees, listed in `PLAN.md`. No sorry, no axiom; statements may be restructured for compositionality when every former theorem is kept or follows, named in the report; a theorem that could be vacuous gets a `#tooth` (`Obend/Tactic`). Report in `lean/docs/REPORT-<LANE>-20261101.md` in the lane-report style. The trees under `~/dev` other than `obend` are read-only. Ember: "Never kill by pattern. No `pkill -f <anything>`, no `pkill -x <bare word>`, no `killall`, no `kill -u`. A process you started is stopped by the PID in its PID file, and only that. Every detached job writes one (`nohup ... & echo $! > job.pid`). No PID file, no kill: tell me instead." When a disk is low: stop writing to it, tell Ember, wait. Reply with the commit range, what is fully proved, and the one decision for Ember.
