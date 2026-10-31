# Lane Parsimony: delete what nothing consumes; fold what duplicates; one class where two exist

Worktree: `/private/tmp/claude-501/-Users-ember-dev-obend/01a18fe9-771b-71b2-b01f-da7ed6517d48/scratchpad/kinds`.

The tree is quiet and this is the pass that needed it. Ground truth from a census on 11-01:
`Obend/Just.lean` and `Obend/Slot/PolySlot.lean` (485 lines, 48 theorems) have zero importers besides
the census; `Calculus` and `Graded` have one instance each; `Decides` is itself one of `Judge`'s
instances, so there are two classes for one idea; `Integrity` has three refuted floors proving one
point; the selection presets and descriptor (`Run/Control`) have one consumer. Read `PLAN.md` "How
we work" (a generalization is adopted only when it shortens proofs against a control), the
`parsimony-closeout` stance (adopt the alarmed view first, then re-justify calmly, delete only
through blind defense), `lean/docs/REPORT-JUST-20261031.md` §3 (why the semiring was refused),
`REPORT-JUDGE-20261031.md`, `Obend/Slot/Calculus.lean`, `Core/Graded.lean`, `Judge/Class.lean`.

Do, one commit each, each defended in the report by the consumers it had and the proofs it
shortened or lengthened: (1) delete `Just` and `PolySlot`; move the refutation's record (the gate
table) into `REPORT-JUST` if it is not already there; keep `Slot/Repair.lean`, which is consumed.
(2) Fold `Decides` into `Judge`: the typing judge is a `Judge` instance with its grade; `Graded` stays
only if `Judge`'s `mono` field and the improvement judge give it two real instances, else it becomes a
plain `Nat` grade; `Calculus` demoted to Core4's concrete definitions unless a second calculus is real
(it is not), with `calculus_typed_msubst` kept under its name. (3) `Integrity`'s three floors to one,
the strongest, with the other two as corollaries or deleted. (4) Look for duplicated folds and
resolutions across `Run`, `Law`, `Doc`, `Vault`, `Spec/Ecosystem` that the `Fold` and `Intention`
structures should subsume and have not yet (the Runner-2 report says projection still borrows from
each runner; the Kinds report says the vault's `resolveIn` stays): make them instances where that
shortens, and say where it does not. (5) Where a definition is written over a concrete type and a
second consumer wants the same shape, introduce the typeclass; where a typeclass has one instance
and no second in sight, remove it. The measure is the gate from PLAN: shorter against a control, or
not adopted. Record every deletion with its line count and every new class with its instance count.

Conventions. Worktree as named (warm; `git checkout dev && git pull --rebase origin dev`, then branch); Lean v4.35.0; every file a `module`; the census is the only axiom check; set `git config core.hooksPath lean/tools/hooks` in the worktree so tier 2 runs pre-push; one measurement build at the start and one at the end, targeted builds between; Mini's cohorts (`python3 lean/tests/run-obend-source.py`), receipts (`run-receipts.py`), workspaces (`run-workspace.py`) and the vault walkthrough are the control. Named-file commits on `dev`, `git -c commit.gpgsign=false commit -F -`, trailer `Co-Authored-By: Claude Opus <noreply@anthropic.com>`, rebase before each push; one other Lean lane is live. No sorry, no axiom; every former theorem kept or an instance, named in the report. Report in `lean/docs/REPORT-<LANE>-20261101.md`. Ember: "Never kill by pattern. No `pkill -f <anything>`, no `pkill -x <bare word>`, no `killall`, no `kill -u`. A process you started is stopped by the PID in its PID file, and only that. Every detached job writes one (`nohup ... & echo $! > job.pid`). No PID file, no kill: tell me instead." When a disk is low: stop writing to it, tell Ember, wait. Reply with the commit range, what changed in statement, and the one decision for Ember.
