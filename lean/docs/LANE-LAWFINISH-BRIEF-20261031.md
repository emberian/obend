# Lane LawFinish: what the Law lane left owed

From `lean/docs/REPORT-LAW-20261030.md` "not done" and `review/DECISIONS-20261031.md`. Read those,
`REPORT-LAWDOC-20261031.md`, then `Obend/Law/**` and the Core machine (`Obend/Core/Machine.lean`,
`Core/Proofs/Adequacy.lean` for what adequacy already covers).

1. **The machine judges what the relation says.** `Admits`/`Refuses` are over `Evaluates`; nothing
   connects `runBounded` to them, since adequacy covers ground values and a verdict is a sum. Prove
   it: running a law term on the machine with enough ticks yields exactly the verdict `Evaluates`
   gives, so a kernel that runs the machine enforces the law the theorem describes. If adequacy must
   be extended to sums of records to get there, do that in `Core/Proofs/` as a new file (the
   ProofEng lane is restructuring existing files there; add, do not edit, and rebase).
2. **`c3_tree_is_chain`** and the other linearization facts the inheritance theorems want:
   C4'"'"'s `linearize` (`Obend/Spec/C4.lean`, read-only for you since the Extends lane owns Spec; state
   your theorems over the list it produces, in `Obend/Law/Proofs/Inherit.lean`): on a tree the
   linearization is the chain to the root; monotonicity and local precedence (Barrett et al. 1996,
   `~/paperbin/barrett1996-monotonic-superclass-linearization-dylan.txt`) stated and proved for the
   produced list.
3. **`keeps` typing** and the remaining generator typing (`windowed`/`quorum` beyond scalar guarded
   fields), under `Bidirectional.checkAgainst`.
4. **Laws reach the runner.** A dispatched operation'"'"'s plan authority today comes only from the
   deployment-supplied spec (`REPORT-RUNNER` §10). Give the runner'"'"'s `admitOp` a Law-term judge: an
   operation is admitted when the object'"'"'s effective law (with parents) admits the write it
   performs, with the refusal naming the ancestor clause; theorem: `Legal` then implies every
   dispatched write was law-admitted. Coordinate with the SlotRun lane only through `origin/dev`;
   you own `Obend/Law/**` and may add one file under `Obend/Run/` named `LawJudge.lean`.

Work in your own worktree (`git worktree add /private/tmp/claude-501/-Users-ember-dev-obend/01a18fe9-771b-71b2-b01f-da7ed6517d48/scratchpad/<lane> dev`); Lean v4.35.0; `LEAN_NUM_THREADS=2 lake build 2>&1 | tee build.log`. Every file a `module` (`lean/docs/REPORT-20261030.md` §2). The census in `Obend/Census.lean` is the only axiom check; add no `#assert_axioms` lines. Mini's cohorts (`python3 lean/tests/run-obend-source.py`) are the control. Named-file commits on `dev`, `git -c commit.gpgsign=false commit -F -`, trailer `Co-Authored-By: Claude Opus <noreply@anthropic.com>`, rebase before each push; three other lanes are live (ProofEng under `Obend/Core/Proofs`, Extends under `Obend/Spec`, Vault under `Obend/Doc` and `Obend/Main.lean`); on conflicts in their files keep theirs. No sorry, no axiom; a theorem that could be vacuous gets a `#tooth`. Statements may be restructured when that makes them more compositional, provided every former theorem is kept or follows as an instance, named in the report. Report in `lean/docs/`. Ember: "Never kill by pattern. No `pkill -f <anything>`, no `pkill -x <bare word>`, no `killall`, no `kill -u`. A process you started is stopped by the PID in its PID file, and only that. Every detached job writes one (`nohup ... & echo \$! > job.pid`). No PID file, no kill: tell me instead." When a disk is low: stop writing to it, tell Ember, wait. Reply with the commit range, what is proved, and the one decision for Ember.
