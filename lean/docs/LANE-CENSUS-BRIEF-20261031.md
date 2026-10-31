# Lane Census: one whole-package axiom census, and pins where they are missing

`Obend/AssertAxioms.lean` defines `#assert_axioms_tree` (the census over every constant the
importing module can see) and nothing invokes it; and 14 proof files carry theorems with no
`#assert_axioms` at all: `Core/Proofs/{Force,Settle,Forcing/Run}.lean`, the six
`Core/Proofs/Preservation/Cases/*.lean`, `Slot/Proofs/{Protocol,Negotiation}.lean`,
`Spec/Proofs/{Law,C4Vectors}.lean`. The README's "every proof module ends with its pins" is false
until this is done, and the paper (`paper/objective-bend.md`, axioms paragraph) says so.

Do: (1) add a root census module `Obend/Census.lean` (a `module` that `import`s the whole library,
as `Obend.lean` does) ending in `#assert_axioms_tree` with the compiled-trust set it reports
separately (the `_native` axioms, per `lean/docs/REPORT-LEAN435-20261031.md`), and make it part of
`lake build`'s default target so a stray axiom anywhere fails the build; (2) in each of the 14
files, add the per-module `#assert_axioms` line naming its theorems, as the other proof modules do;
(3) whatever the tree census reveals (a constant resting on something other than the standard
three plus the declared compiled set) is a finding: report it, and fix it only if the fix is a
proof, never by widening the census. Record the census's totals once in `lean/docs/REPORT-CENSUS-20261031.md`
and correct the README line.

Work in your own worktree (`git worktree add /private/tmp/claude-501/-Users-ember-dev-obend/01a18fe9-771b-71b2-b01f-da7ed6517d48/scratchpad/census dev`);
another lane is committing under `Obend/Spec` and `Obend/Slot/Core4.lean`, so if a rebase conflicts
there, keep theirs. Lean v4.35.0; `LEAN_NUM_THREADS=2 lake build 2>&1 | tee build.log`. Named-file
commits on `dev`, `git -c commit.gpgsign=false commit -F -`, trailer `Co-Authored-By: Claude Opus
<noreply@anthropic.com>`, rebase before pushing. No sorry, no axiom. Ember: "Never kill by pattern.
No `pkill -f <anything>`, no `pkill -x <bare word>`, no `killall`, no `kill -u`. A process you
started is stopped by the PID in its PID file, and only that. Every detached job writes one
(`nohup ... & echo $! > job.pid`). No PID file, no kill: tell me instead." When a disk is low: stop
writing to it, tell Ember, wait. Reply with the commit hash, the census totals, and any finding.
