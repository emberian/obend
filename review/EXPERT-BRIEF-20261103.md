# The "sitting next to an expert" exercise (2026-11-03)

Ember asked, of the FPGA work: "I'm sitting next to a guy who has actually done FPGA versions of
things like this and I'm wondering what in our design he would immediately sus at." Then: make that
a lever on the whole system, one expert per category, wide remit.

You are one of those experts. Read the repository the way that person would, write down what you
are immediately suspicious of, then dig until each suspicion is confirmed or cleared. The report
is for Ember and for the agents who will act on it, so it has to be concrete enough to act on.

## The repository

`/Users/ember/dev/obend`. Lean library under `lean/Obend/` (about 480 modules, 230K lines);
`.obend` programs under `apps/*/`, `stdlib/`, `lean/tests/obend-source/`; Rust under `crates/`;
hardware simulation under `apps/*/verilator/` and `hardware/`; design documents at the root
(`AMBITION.md`, `THESIS.md`, `DESIGN.md`, `PLAN.md`, `PHYSICAL.md`, `SILICON-ELABORATOR.md`,
`NEXT-MATHEMATICA.md`, `DEOS-CONTRACTS-CONSENSUS.md`, `QUALIFICATION-AND-SILICON-LEAN.md`,
`METATHEORY.md`).

The working tree holds about 150 uncommitted files from a parallel swarm that was suspended
mid-wave. Treat the working tree, not HEAD, as the state. Do not clean it up.

Two things to read before the code, so you extend them rather than repeat them:
`review/FABLE-COUNCIL-20261101.md` §1 and §2 (the structural pattern found two days ago: theorem-
shaped tests, "two of everything", checkers with no bridge theorem, documents describing a system
that does not exist), and the original statement of intent, `git show 26f3ce8:AMBITION.md`, against
`AMBITION.md` as it stands.

## How to write it

- Tag every claim **READ** (you opened the file; cite `path:line`), **INFERRED** (deduced from READ
  facts), or **PROPOSED**. Where you give a number, give the command that produced it.
- For each suspicion: what made you suspicious, what evidence would clear it, whether you found that
  evidence, and the verdict. Rank by how much it would embarrass us in front of a real expert of
  your kind, not by how easy it is to fix.
- Finish with the three changes you would make first, what each costs, and the one question you
  would ask Ember.
- Write the report to `review/EXPERT-<your-slug>-20261103.md`. Return a summary of at most twelve
  lines: the verdict, the top three findings with paths, and your one question.

## What you may and may not do

Read anything. Edit nothing except your own report file. Run no Lean or Rust builds anywhere: the
Mac is at load 45 and hbox's root disk is at 96 percent. You may run the already-built CLI
`lean/.lake/build/bin/obend` and the Python conformance runners in `lean/tests/` (each finishes in
under a minute); you may run `verilator --lint-only` on a single `.sv` file. No ssh.

Stopping processes: PID file or nothing. Never kill by pattern. No `pkill -f <anything>`, no
`pkill -x <bare word>`, no `killall`, no `kill -u`. A process you started is stopped by the PID in
its PID file, and only that. Every detached job writes one (`nohup ... & echo $! > job.pid`). No
PID file, no kill: tell me instead. If you must look first, `pgrep -fl` and read the list; it is
never the argument to a kill. Never `git stash`; other agents share this working tree.
