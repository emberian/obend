# Lane Cost: `≈c`, ticks within a constant of clairvoyant cost, the improvement judge

Worktree: `/private/tmp/claude-501/-Users-ember-dev-obend/01a18fe9-771b-71b2-b01f-da7ed6517d48/scratchpad/cost`.

Read `review/EQUIV-PLAN-20261031.md` whole (definition 2, the `mix_assoc` constants, lanes 1–3),
`lean/Obend/Equiv/*.lean` (`Ahead`, `≈b`, `mix_assoc`, `mix_apply`), `Core/Machine.lean` and
`Core/Proofs/Adequacy.lean` (the machine-to-source relation, ticks), and the papers
`~/paperbin/hackett-hutton2019-call-by-need-is-clairvoyant-call-by-value.txt` (Theorems 4.1, 4.2)
and `moran-sands1999-improvement-in-a-lazy-context.txt` (Def. 3.3, 4.1; OCR text).

Deliver, one commit each: (1) yields under `Ahead`: `Yields` preserved, `≈b` over `Interaction`
traces (EQUIV-PLAN lane 1); (2) `⇓ᵏ_CV` for Core4 with Skip at its binding sites (β arguments, record
fields, inject and case payloads, the `self` of `fix`, `super` in `mixBody`), the cost measure, and
`≈c` (within a constant, Moran–Sands Def. 4.1), with `mix_assoc_cost : L ≈ᶜ R` with explicit constants
(the machine measured κ = 7 ticks at k = 0) and Faré's tests costed; (3) ticks within a constant factor
of CV cost on the existing machine-to-source relation (extend `Adequacy` to carry a tick bound, in a
new file under `Core/Proofs/`); (4) the improvement judge: a `Judge` instance (`Obend/Judge`) whose
certificate is a cost derivation, so an optimization is a candidate justified under `≈c` and a member's
charge difference is a theorem. Blackholes and ticks as EQUIV-PLAN states them.

Conventions. Lean v4.35.0; every file a `module` (`lean/docs/REPORT-20261030.md` §2); the census in `Obend/Census.lean` is the only axiom check, add no `#assert_axioms` lines; one measurement build at the start and one at the end, targeted `lake build Obend.<Lib>` between; Mini's cohorts (`python3 lean/tests/run-obend-source.py`) and the receipt tests (`python3 lean/tests/run-receipts.py`) are the control. Named-file commits on `dev`, `git -c commit.gpgsign=false commit -F -`, trailer `Co-Authored-By: Claude Opus <noreply@anthropic.com>`, `git pull --rebase origin dev` before each push and resolve only your own files; five other lanes are live in their own worktrees, listed in `PLAN.md`. No sorry, no axiom; statements may be restructured for compositionality when every former theorem is kept or follows, named in the report; a theorem that could be vacuous gets a `#tooth` (`Obend/Tactic`). Report in `lean/docs/REPORT-<LANE>-20261101.md` in the lane-report style. The trees under `~/dev` other than `obend` are read-only. Ember: "Never kill by pattern. No `pkill -f <anything>`, no `pkill -x <bare word>`, no `killall`, no `kill -u`. A process you started is stopped by the PID in its PID file, and only that. Every detached job writes one (`nohup ... & echo $! > job.pid`). No PID file, no kill: tell me instead." When a disk is low: stop writing to it, tell Ember, wait. Reply with the commit range, what is fully proved, and the one decision for Ember.
