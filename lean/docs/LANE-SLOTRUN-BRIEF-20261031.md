# Lane SlotRun: the slot's open items, and the runner's

From `review/DECISIONS-20261031.md` "still open", the items that live in `Obend/Slot` and `Obend/Run`.
Read that ledger, `review/KIMI-REVIEW-20261030.md` §1–2, `astra/ASTRA-SELECTION-20261031.md` §7–8,
`lean/docs/REPORT-RUNNER-20261031.md` §8–10, `REPORT-JUST-20261031.md`, then the code.

1. **The version non-return law.** `Obend/Slot/World.lean` has `holds_congr`, `retired_dead`,
   `retired_step` and nothing about versions, so pins may alternate and a stale justification can come
   back true (Kimi §2). nano'"'"'s law is `stale_behind_forever` (`git -C /Users/ember/dev/nanodregg show
   origin/main:Kernel/Proofs/Versions.lean`, line 240 and the docstring at 21–30): a pin observed at
   w₀ and stale at w is stale at every later w', or the hash collides on the pin inputs. State the
   version order and the non-return law as World fields with the collision stance explicit (a
   `Digest`-class disjunct, or a lawful-order assumption as nano does), prove `dead_behind_forever`
   from it without the retirement special case, and give a toy World that violates it (a pin that
   returns) as the tooth. Keep every existing theorem.
2. **Names.** `slot_repair` is a bundle of reading and permanence lemmas: split or rename it so each
   name says what it proves, and rename `Integrity.transition` to what it is (a stored-selection
   transition law). Old names stay as deprecated aliases for one release.
3. **Runner authority.** Decision authority beyond the `.me` chooser (authenticated principals,
   decision revisions, an office change that does or does not void a prior choice, as a declared
   rule per slot); the per-slot selection-control descriptor Astra'"'"'s §8 specifies, with the presets
   first-usable, incumbent-first and chooser-required and each preset'"'"'s choice law proved; and the
   honest "nothing admissible" outcome with exact candidate diagnostics.
4. **Runner adapter.** Response typing against the declared response type (as `Spec.Preview` does);
   depth deepening mid-run instead of a `depth` stop; ticks exhausted within a turn resuming with
   more rather than ending; holes in emitted plans, so the selection machinery reaches Core4 plans
   (a plan with a choice point becomes a runner slot). Each with the `Legal` clause it adds and a
   fixture that the previous runner got wrong.

Work in your own worktree (`git worktree add /private/tmp/claude-501/-Users-ember-dev-obend/01a18fe9-771b-71b2-b01f-da7ed6517d48/scratchpad/<lane> dev`); Lean v4.35.0; `LEAN_NUM_THREADS=2 lake build 2>&1 | tee build.log`. Every file a `module` (`lean/docs/REPORT-20261030.md` §2). The census in `Obend/Census.lean` is the only axiom check; add no `#assert_axioms` lines. Mini's cohorts (`python3 lean/tests/run-obend-source.py`) are the control. Named-file commits on `dev`, `git -c commit.gpgsign=false commit -F -`, trailer `Co-Authored-By: Claude Opus <noreply@anthropic.com>`, rebase before each push; three other lanes are live (ProofEng under `Obend/Core/Proofs`, Extends under `Obend/Spec`, Vault under `Obend/Doc` and `Obend/Main.lean`); on conflicts in their files keep theirs. No sorry, no axiom; a theorem that could be vacuous gets a `#tooth`. Statements may be restructured when that makes them more compositional, provided every former theorem is kept or follows as an instance, named in the report. Report in `lean/docs/`. Ember: "Never kill by pattern. No `pkill -f <anything>`, no `pkill -x <bare word>`, no `killall`, no `kill -u`. A process you started is stopped by the PID in its PID file, and only that. Every detached job writes one (`nohup ... & echo \$! > job.pid`). No PID file, no kill: tell me instead." When a disk is low: stop writing to it, tell Ember, wait. Reply with the commit range, what is proved, and the one decision for Ember.
