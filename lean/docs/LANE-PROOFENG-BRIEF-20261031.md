# Lane ProofEng: drop the pin lists, make the proofs fast, try waterfall

Three things Ember asked for, in this order, each its own commit.

1. **Drop the per-theorem axiom lists.** There are 419 `#assert_axioms name name …` lines across
   131 files. `Obend/Census.lean` now crawls every constant in the library in the default build and
   fails on any stray axiom (`lean/docs/REPORT-CENSUS-20261031.md`), so the lists are maintenance
   with no information. Remove every `#assert_axioms` line and the "pins" prose in docstrings and
   `lean/README.md`; keep `#assert_axioms_tree` in `Census.lean`. The 27 `#assert_compiled` lines
   re-run a `native_decide` claim, which the census cannot; keep those only if you confirm they do
   that, otherwise drop them too, and say which. Delete `Obend/AxiomPin.lean`/`AssertAxioms.lean`
   machinery that nothing then uses. Commit this first and push, since other lanes will rebase over it.

2. **Make the proofs concretely efficient.** Measure once: a clean `LEAN_NUM_THREADS=2 lake build`
   records each module's time (Lake prints `(18s)` per job; `Core/Proofs/Adequacy` alone was 18 s at
   4.30). List the twenty slowest modules with times in the report, then for each of the top ten
   find what is slow (`set_option profiler true` on the file, `set_option trace.profiler.threshold`;
   typical causes here are `simp` with large sets, `decide` on big terms, `obend_cases` arms doing
   repeated `grind`, kernel reduction in teeth) and fix it without changing any statement: smaller
   simp sets, `simp only`, `decide := true` vs kernel, splitting a 5,000-line proof module along its
   section boundaries so Lake parallelizes it, `@[csimp]` or precomputation for decide-heavy
   teeth. Record before/after per module. The debt from the 4.35 bump belongs here too:
   `equirec_reduce` in `Core/DecisionReduction.lean` keeps `set_option backward.isDefEq.respectTransparency false`;
   replace it with a reduction that never unfolds a definition appearing in a type index
   (`lean/docs/REPORT-LEAN435-20261031.md` names what was tried).

3. **Try `waterfall`.** Sam Tobin-Hochstadt's ACL2-style proof search for inductive goals
   (https://github.com/samth/waterfall, v0.2.0, a clone is at
   `/private/tmp/claude-501/-Users-ember-dev-obend/01a18fe9-771b-71b2-b01f-da7ed6517d48/scratchpad/waterfall`
   with README and `docs/`; it is a `module` and works from module files; its toolchain is 4.33.1, we
   are at 4.35.0, so first check it builds as a `[[require]]`). Candidates where it should help:
   the structural lemmas over `Term` traversals (`Core/Traverse.lean` consumers), the list and row
   lemmas in `Core/Proofs/Collect*.lean`, `Settle.lean`, `Forcing/*.lean`, the Law meaning theorems'
   case splits, `Doc/Patch.lean`'s `apply_*`. Rewrite at least twenty existing proofs to `waterfall`
   (or `waterfall?`'s expansion where the search is slow at build time), keep each only if it is
   both shorter and not slower, and report the before/after lines and seconds honestly, including
   the ones it could not do. If it does not earn its place, say so and leave it out of the
   dependencies.

Work in your own worktree (`git worktree add /private/tmp/claude-501/-Users-ember-dev-obend/01a18fe9-771b-71b2-b01f-da7ed6517d48/scratchpad/proofeng dev`);
Lean v4.35.0. Full build is 207 jobs; Mini's cohorts are the control (`python3 lean/tests/run-obend-source.py`).
Named-file commits on `dev`, `git -c commit.gpgsign=false commit -F -`, trailer
`Co-Authored-By: Claude Opus <noreply@anthropic.com>`, rebase before each push. No sorry, no axiom,
no changed statement. Report at `lean/docs/REPORT-PROOFENG-20261031.md`. Ember: "Never kill by
pattern. No `pkill -f <anything>`, no `pkill -x <bare word>`, no `killall`, no `kill -u`. A process you
started is stopped by the PID in its PID file, and only that. Every detached job writes one
(`nohup ... & echo $! > job.pid`). No PID file, no kill: tell me instead." When a disk is low: stop
writing to it, tell Ember, wait. Reply with the commit range, the top-ten before/after times, and
the waterfall verdict.
