You are Astra (GPT-6). Ember accepted the Just lane's choice of incumbent-first selection for a
stored slot choice and asks you to analyze the whole space of options there, so the choice is made
knowingly rather than by default. Read `lean/docs/REPORT-JUST-20261031.md` (§on `Integrity.transition`,
`Advance`, the refuted `churn` and `sticky` policies, `select_prefix`/`select_reuse`), the code
`lean/Obend/Slot/Integrity.lean`, `Slot/Repair.lean`, `Slot.lean` (`select`, `read`, `alternatives`),
and your own `astra/ASTRA-EVAL-20261031.md` lines 19–27 and 97–111 (the early/chosen countermodel
and the replanning theorem). The runner lane is building `Obend/Run/` on `Integrity.transition`
concurrently; read its commits on `origin/dev` if any have landed, and touch nothing under `lean/`.
Context that bears on the answer: in the delvetalk2 playtest, agents asked for "a line that sticks"
and "public correction kept in the record" (`/Users/ember/dev/delvetalk2/docs/METAPHYSICS.md` §7.3);
nanodregg's LANG-73 chose "the executed prefix blocks re-plan" for protocols; the document instance
(LANG-83 in `/Users/ember/dev/nanodregg/decisions/lang.md`) has an editor who selects.

The question: when a stored selection's world changes, what should happen to the choice? Lay out
the space: incumbent-first, first-usable (canonical replay), chooser-decides (a named party
re-selects), priority with hysteresis, lexicographic on (still-usable, order, recency), "sticky
until contradicted and then chooser", and anything from the literature on belief revision (AGM
minimal change, Doyle's foundations versus coherence), truth maintenance (ATMS environment
switching), leader election and lease renewal in distributed systems, and legal or editorial
precedent (incumbency, stare decisis) that maps onto it. For each: the theorem it satisfies and
the one it fails, what replay needs as evidence, how a refusal names what would pass, what a
stranger reading the receipt sees, and a concrete scenario where it is the wrong choice. Then say
which policies should be *selectable per slot* (a chooser field) versus fixed in the kernel, and
what the kernel must guarantee regardless of policy so the runner's replanning theorem holds. If
the right answer is "incumbent-first by default, chooser can override, and these two invariants
are policy-independent", say so and state the invariants precisely enough to write in Lean. Run
small Lean or Python checks where a claim needs one; `lake env lean` in a worktree of your own
(`git worktree add <dir> dev`) works.

Write `/Users/ember/dev/obend/astra/ASTRA-SELECTION-20261031.md`, claims tagged READ, RAN,
INFERRED, PROPOSED, as long as it needs to be. Commit it alone on `dev` with
`git -c commit.gpgsign=false commit -F -` and trailer `Co-Authored-By: Astra (GPT-6) via codex
<noreply@openai.com>`, rebase before pushing. Ember's safety paragraph, verbatim: "Never kill by
pattern. No `pkill -f <anything>`, no `pkill -x <bare word>`, no `killall`, no `kill -u`. A process
you started is stopped by the PID in its PID file, and only that. Every detached job writes one
(`nohup ... & echo $! > job.pid`). No PID file, no kill: tell me instead." When a disk is low: stop
writing to it, tell Ember, wait.
