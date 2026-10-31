# Lane Impact: `obend analyze impact`, the first world analysis

Worktree: `/private/tmp/claude-501/-Users-ember-dev-obend/01a18fe9-771b-71b2-b01f-da7ed6517d48/scratchpad/kinds` (warm; `git checkout dev && git pull --rebase origin dev`, branch `lane-impact`).

The design is `review/WORLD-ANALYSIS-20261101.md` (read whole; §on Impact and the `Obend/Analysis/`
layout), corrected by Gemini (`review/GEMINI-CHECKPOINT-20261101b.md` §3): a partial cell is its
*domain* of admissible pins (induced by its supports; non-empty catches contradictory constraints),
not a bare support list; three-valued reading is exact per cell (`.known true` iff every admissible
pin satisfies the fact); entailment is decidable for finite pins, equality/retirement constraints and
Presburger version facts, undecidable for unconstrained Core4 laws (report `uncovered`). Ground
truth: `Fold.lean` (`Admission`, `reads`, `step_of_pins`, `receipt_sufficient`), `Slot.lean`
(`read_blocked_exact`), `Slot/World.lean` (`holdsOfPin`, versions), `Intention.lean`,
`Spec/Ecosystem.lean`, `Doc/Section.lean`, `Receipt.lean`, `Journal/Journal.lean` (the `reads`
index built once for theorems: reuse its shape), `Vault/*.lean`.

Deliver: (1) `Obend/Analysis/Setup.lean`: `Setup` as per-cell admissible-pin domains with the
three-valued map as its degenerate instance; `read3` with `read3_sound` (a `.known` verdict holds in
every completion) and the contradiction refusal. (2) `Obend/Analysis/Impact.lean`: the `reads` index
over a world (every admission row to the cells it reads, by `Admission.reads`), `affected`: for a pin
move, the candidates that go `blocked`, the package turns that go `stale`, the cites that go
`behind`, the laws whose verdict could change, the receipts no longer current; theorems
`affected_reads` and `reads_affected` (exactness up to known blocks), each affected line carrying the
opening it rests on so `obend verify` checks it by `read_blocked_exact`. (3) The analysis as a
`Judge` instance whose certificate is the affected list with openings, with a planted bad
certificate. (4) `obend analyze impact CELL@PIN --world DIR` on a vault and on a workspace, with a
test in `lean/tests/analysis/` that moves a pin and checks every predicted line against the actual
re-judgment; a mutation tooth where a dropped read makes the prediction miss a blocked candidate. (5)
If time allows: `obend analyze replay` (counterfactual: re-run the fold with an amended law and list
the writes that would have been refused), which is the fold replayed and needs no new theorem.

Build on the box, not the Mac: lean/docs/BUILD-ON-BB2.md is the loop (edit in the named Mac worktree, `git push bb2 <branch>`, build and run tests over ssh under `swarm-build`; hbox at `~/obend/repo` user `hbox` is the alternative and is faster when up; read ~/swarm/MACHINES.md and RULES.md first). Tier 1 green is the bar for pushing `dev` (from the Mac, `--no-verify` is fine when the box built the identical commit); run tier 2 on the box afterwards and report its result; we revisit only if it is red. Lean v4.35.0; every file a `module`; the census is the only axiom check; named-file commits on `dev`, `git -c commit.gpgsign=false commit -F -`, trailer `Co-Authored-By: Claude Opus <noreply@anthropic.com>`, rebase before each push; other lanes are live, keep theirs on conflicts outside your files. No sorry, no axiom; every former theorem kept or an instance, named in the report. Report in `lean/docs/REPORT-<LANE>-20261101.md`. Ember: "Never kill by pattern. No `pkill -f <anything>`, no `pkill -x <bare word>`, no `killall`, no `kill -u`. A process you started is stopped by the PID in its PID file, and only that. Every detached job writes one (`nohup ... & echo $! > job.pid`). No PID file, no kill: tell me instead." When a disk is low: stop writing to it, tell Ember, wait. Reply with the commit range, what is proved, and the one decision for Ember.
