# Lane Elab: executable annotation preparation, and the front end converges on the checker

Full annotated completeness holds by `Classical.choose` (`lean/docs/REPORT-EQUIREC-20261031.md`;
`Core/Proofs/BidirectionalCompleteness.lean`, `annotateFromDerivation`). Astra showed a 72-annotation
search at one path already makes `checkAgainst` accept `(λx.x) 3` at `Nat` (`astra/ASTRA-EVAL-20261031.md`
line 75) and recommends executable preparation before any general inference (lines 59–81, 111). The
scholar's design for the eventual elaborator is `review/ALGEBRAIC-SUBTYPING-20261031.md` (read §3 and
§4; its first artefact is `Elab/Coerce.lean` with `coerce_checks`; Astra's corrections to its quantity
claims are at lines 55–57).

Build `Obend/Elab/` (root `Obend/Elab.lean`): (1) `Prepare.lean`, an executable annotation
preparation: given an erased term, a context and an expected type, produce annotations at the paths
`checkCovered` needs (lambdas in synthesis position, empty cases, injections) by local inference
from the expected type and the context, falling back to bounded search only where local inference
is silent, returning the annotated term or a refusal naming the path; the theorem `prepare_checks`:
if the term is `Typed` then preparation succeeds and `checkAgainst` accepts its output, which makes
`annotateFromDerivation` executable on the fragment preparation covers, with that fragment stated
syntactically. (2) `Coerce.lean` with `coerce_checks` as the scholar specified, honouring Astra's
measured η-wrapper matrix (line 55) and the record-coercion obstruction (line 57) as teeth. (3)
Convergence: `Obend/Spec`'s front end admits through `Check.check` today; make preparation plus
`Bidirectional.checkAgainst` the front end's gate, with Mini's cohorts (`python3 lean/tests/run-obend-source.py`)
unchanged as the control, and retire the annotation-directed route from the slot judge if the cohorts
and the completeness theorem allow it. Also: `termDepth` is 3 for a 1,000-field record (Astra line
83); replace the grant's measure with one that counts the work the checker does, and rename it.

Work in your own git worktree (`git worktree add /private/tmp/claude-501/-Users-ember-dev-obend/01a18fe9-771b-71b2-b01f-da7ed6517d48/scratchpad/<lane> dev`), since three other lanes build concurrently. Lean v4.35.0; `LEAN_NUM_THREADS=2 lake build 2>&1 | tee build.log` (177 jobs full; build your library by name while iterating). Every file a `module` (`lean/docs/REPORT-20261030.md` §2). Commit named files on `dev`, `git -c commit.gpgsign=false commit -F -`, trailer `Co-Authored-By: Claude Opus <noreply@anthropic.com>`, rebase on `origin/dev` before each push and resolve only your files. No sorry, no axiom, no weakened statement; every theorem that could be vacuous gets a `#tooth` (`Obend/Tactic`). Write a report in `lean/docs/` in the style of `REPORT-20261030.md`. The trees under `~/dev` other than `obend` are read-only. Ember: "Never kill by pattern. No `pkill -f <anything>`, no `pkill -x <bare word>`, no `killall`, no `kill -u`. A process you started is stopped by the PID in its PID file, and only that. Every detached job writes one (`nohup ... & echo $! > job.pid`). No PID file, no kill: tell me instead." When a disk is low: stop writing to it, tell Ember, wait. Reply with the commit range, what is fully proved, and the one decision for Ember.
