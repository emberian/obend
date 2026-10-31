# Lane LawDoc: the law fragment compiles to laws; wikilinks become identity cites

Two closed decisions to build out, disjoint from the checker and slot lanes.

(1) `Obend/Spec/Law.lean` parses the `.obend` law fragment (`REF == INT`, `monotone`, `writeOnce`,
…) and `Obend/Law/Std.lean` has the generators with meaning theorems (`lean/docs/REPORT-LAW-20261030.md`,
"not done" list). Write `Obend/Spec/LawCompile.lean`: the fragment compiled to closed Core4 law terms
built from the Law combinators, with the theorem that the compiled law's `Admits`/`Refuses` agree
with the fragment's `LawExpr.denote`, and the typing theorem the Law lane left owed: generated laws
check at `lawTy S` under `Bidirectional.checkAgainst`. Wire it so a package's `law NAME: EXPR`
becomes a Law term in the captured package, cohorts unchanged.

(2) `lean/docs/REPORT-DOC-20261030.md`'s decision: Ember chose (c): `[[Beta]]` cites only the page's
identity with no bytes; byte cites are `![[Beta]]` embeds and `[[Beta#^id]]` block references, and a
following byte cite stays current while the bytes it quotes are unchanged (rule (b)). Change `Cite`
and `Vault.read` in `Obend/Doc/{Section,Render}.lean` accordingly, keep every theorem's shape, extend
the two-page vault test with an embed and a block reference, and add backlinks (the authenticated
reverse index of cites the kernel maintains because a cite is a support it pins).

Work in your own git worktree (`git worktree add /private/tmp/claude-501/-Users-ember-dev-obend/01a18fe9-771b-71b2-b01f-da7ed6517d48/scratchpad/<lane> dev`), since three other lanes build concurrently. Lean v4.35.0; `LEAN_NUM_THREADS=2 lake build 2>&1 | tee build.log` (177 jobs full; build your library by name while iterating). Every file a `module` (`lean/docs/REPORT-20261030.md` §2). Commit named files on `dev`, `git -c commit.gpgsign=false commit -F -`, trailer `Co-Authored-By: Claude Opus <noreply@anthropic.com>`, rebase on `origin/dev` before each push and resolve only your files. No sorry, no axiom, no weakened statement; every theorem that could be vacuous gets a `#tooth` (`Obend/Tactic`). Write a report in `lean/docs/` in the style of `REPORT-20261030.md`. The trees under `~/dev` other than `obend` are read-only. Ember: "Never kill by pattern. No `pkill -f <anything>`, no `pkill -x <bare word>`, no `killall`, no `kill -u`. A process you started is stopped by the PID in its PID file, and only that. Every detached job writes one (`nohup ... & echo $! > job.pid`). No PID file, no kill: tell me instead." When a disk is low: stop writing to it, tell Ember, wait. Reply with the commit range, what is fully proved, and the one decision for Ember.
