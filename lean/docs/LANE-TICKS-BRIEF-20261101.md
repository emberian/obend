# Lane Ticks: the fragment tick bound, mechanized

Worktree: `/private/tmp/claude-501/-Users-ember-dev-obend/01a18fe9-771b-71b2-b01f-da7ed6517d48/scratchpad/build`, branch `lane-ticks`. The hand trace and the four lemmas are in
`lean/docs/REPORT-DEMAND-20261101.md`'s follow-up section; read it whole, then `Core/Machine.lean`,
`Core/Proofs/TickCost.lean`, `Equiv/Demand.lean`, `Core/Proofs/Completeness.lean`.

Deliver: (1) `TicksWithinDemand` on the literal-and-`self.m` fragment with the constant stated (the
trace says 4: `T ≤ 22 + 6d` against least cost `headCost + 2d + 2`), through the four lemmas:
`runBounded` composed along active steps, `allocateFields` as an append, the heap invariant over the
cells, the forcing lemma by induction on the chase (`chase_walk_injective`); `measured_within` becomes
an instance. (2) The general statement's exact precondition: what a cost-indexed `Completeness` must
provide (stutters per source reduction bounded, heap cells matched to wave entries: suspended to
`skipped`, cached to the value); state it as a structure and prove the fragment is an instance; if the
general proof is within reach, do it, else name the lemma that is not. (3) The cost judge's receipt
says `ticks ≤ 4·k` on the fragment, `uncovered` off it.

Build on the box per lean/docs/BUILD-ON-BB2.md (hbox `~/obend/repo` user `hbox` preferred, dregg-build2 `bb2` user `build` otherwise; read ~/swarm/MACHINES.md and RULES.md first). Tier 1 green is the bar for pushing `dev` from the Mac (`--no-verify` when the box built the identical commit); run tier 2 on the box and report it. Lean v4.35.0; every file a `module`; the census is the only axiom check; named-file commits on `dev`, `git -c commit.gpgsign=false commit -F -`, trailer `Co-Authored-By: Claude Opus <noreply@anthropic.com>`, rebase before each push; three other lanes are live, keep theirs on conflicts outside your files. No sorry, no axiom; every former theorem kept or an instance, named in the report `lean/docs/REPORT-<LANE>-20261101.md`. Ember: "Never kill by pattern. No `pkill -f <anything>`, no `pkill -x <bare word>`, no `killall`, no `kill -u`. A process you started is stopped by the PID in its PID file, and only that. Every detached job writes one (`nohup ... & echo $! > job.pid`). No PID file, no kill: tell me instead." When a disk is low: stop writing to it, tell Ember, wait. Reply with the commit range, what is proved, and the one decision for Ember.
