# Lane Just: provenance of eligibility, corrected, as the slot's one construction

`review/SYNTHESIS-20261031.md` proposed one semiring of justifications under the slot; Astra's
evaluation (`astra/ASTRA-EVAL-20261031.md` lines 11–27, 87, 109) refuted three of its claims by
countermodel and kept the core. Build the corrected version and run the experiment that decides it.

Corrections to honour: the algebra is a bounded distributive lattice with multiplicative idempotence
(absorption alone has a three-element countermodel), `Poly` carries a normalization to an antichain
of token sets with a decidable token equality (not a bare `List (List X)`), the dual (negative-token)
evaluation names refusals, and ordered observations (`Slot.dead`, `Slot.evidence`, selection order)
are *not* reconstructed from the monomial and must stay as they are. Repair is not "re-evaluation at
a later view" without a compatibility condition: find and state the condition under which repairing
one support does not retire another (Astra's pin-0/pin-1 countermodel at line 27 must be refused by
it), and prove repair soundness under that condition only.

The experiment, exactly as the synthesis stated it and Astra endorsed as the gate: `Obend/Just.lean`
(the lattice, `Poly`, normal form, Boolean and dual evaluation, `eval_congr`) and `Obend/Slot/PolySlot.lean`
redefining `usable`, `read` and `select`'s eligibility as evaluations of one polynomial, then re-proving
every theorem of `Slot.lean`, `Slot/World.lean` and `Slot/Integrity.lean` from the lattice lemmas,
under the original pins and `#tooth` mutations. The gate is that the proof text gets shorter; record
before/after line counts once, honestly. If it does not get shorter, say so and stop: that result is
worth as much as the other. Either way state `Integrity.repair` as the corollary of `contextual` it
is (Astra proved it; Kimi argued it) and replace B4′ in `Integrity.lean` with the operational transition
property over a stored selection that the runner lane (`Obend/Run/`) will use; coordinate only by
reading its commits on `origin/dev`.

Work in your own git worktree (`git worktree add /private/tmp/claude-501/-Users-ember-dev-obend/01a18fe9-771b-71b2-b01f-da7ed6517d48/scratchpad/<lane> dev`), since three other lanes build concurrently. Lean v4.35.0; `LEAN_NUM_THREADS=2 lake build 2>&1 | tee build.log` (177 jobs full; build your library by name while iterating). Every file a `module` (`lean/docs/REPORT-20261030.md` §2). Commit named files on `dev`, `git -c commit.gpgsign=false commit -F -`, trailer `Co-Authored-By: Claude Opus <noreply@anthropic.com>`, rebase on `origin/dev` before each push and resolve only your files. No sorry, no axiom, no weakened statement; every theorem that could be vacuous gets a `#tooth` (`Obend/Tactic`). Write a report in `lean/docs/` in the style of `REPORT-20261030.md`. The trees under `~/dev` other than `obend` are read-only. Ember: "Never kill by pattern. No `pkill -f <anything>`, no `pkill -x <bare word>`, no `killall`, no `kill -u`. A process you started is stopped by the PID in its PID file, and only that. Every detached job writes one (`nohup ... & echo $! > job.pid`). No PID file, no kill: tell me instead." When a disk is low: stop writing to it, tell Ember, wait. Reply with the commit range, what is fully proved, and the one decision for Ember.
