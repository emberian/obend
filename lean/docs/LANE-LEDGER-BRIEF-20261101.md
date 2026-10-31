# Lane Ledger: the first platform, a business ledger a stranger opens

Worktree: `/private/tmp/claude-501/-Users-ember-dev-obend/01a18fe9-771b-71b2-b01f-da7ed6517d48/scratchpad/cost`, branch `lane-ledger`. `PLAN.md` workstream 8 is the gate: a stranger opens a
vault with a ledger kind, posts from a second machine offline, reconnects, sees a balance refusal name
its clause, corrects it, and prints a report an auditor recomputes. Read `AMBITION.md`, `DESIGN.md`
§6, `astra/ASTRA-VISION-20261031.md` §7 and §8.G (the 1C-shaped platform: catalogs, documents,
registers, posting as a turn, period closing as a version law, reports as judged folds with
non-omission), `review/VISION-CLAUDE-20261031.md` §7.2, then what exists: `Obend/Vault/*` (`obend
open`, members, laws, merge), `Obend/Kind.lean`, `Obend/Run/Fork.lean` (fork and stitch),
`Obend/Law/*`, `Obend/Receipt.lean`, `Obend/Fold.lean`, `Obend/Analysis/*`, the stranger walkthrough
`lean/tests/vault/WALKTHROUGH.md`.

Deliver, as kinds and laws in `.obend` and vault pages, with the kernel unchanged except where a
theorem is missing: (1) kinds `Account`, `Document` (an invoice, a payment), `Register` (postings
with `balanced` as a law: every posting's debits equal its credits; `conserved`: the register's total
is the sum of its postings; `monotone` on the period), `Report` (a trial balance as a judged fold with
a non-omission receipt: every posting in the period is included, proved by a coverage argument over
the fold); (2) posting as a turn through the runner (an admitted write with its receipt), period
closing as a version law (no posting into a closed period, refusal names the period), correction as
a reversing posting not an edit; (3) the offline story: a second vault copy posts while disconnected,
`obend merge` stitches through the fork with the ledger's laws re-judged at stitch (Sound's atomic
stitch), a double-posting of one invoice refused by name; (4) `obend report trial-balance PERIOD`
with a receipt `obend verify` re-checks, and `obend analyze impact` on a posting; (5) the walkthrough
in `lean/tests/ledger/WALKTHROUGH.md` executed by a script, as the vault's was, with every refusal's
text shown. Where the kernel lacks a theorem (the non-omission coverage argument is the likely one),
add it under `Obend/Fold` or `Obend/Analysis` with a tooth, naming it in the report.

Build on the box per lean/docs/BUILD-ON-BB2.md (hbox `~/obend/repo` user `hbox` preferred, dregg-build2 `bb2` user `build` otherwise; read ~/swarm/MACHINES.md and RULES.md first). Tier 1 green is the bar for pushing `dev` from the Mac (`--no-verify` when the box built the identical commit); run tier 2 on the box and report it. Lean v4.35.0; every file a `module`; the census is the only axiom check; named-file commits on `dev`, `git -c commit.gpgsign=false commit -F -`, trailer `Co-Authored-By: Claude Opus <noreply@anthropic.com>`, rebase before each push; three other lanes are live, keep theirs on conflicts outside your files. No sorry, no axiom; every former theorem kept or an instance, named in the report `lean/docs/REPORT-<LANE>-20261101.md`. Ember: "Never kill by pattern. No `pkill -f <anything>`, no `pkill -x <bare word>`, no `killall`, no `kill -u`. A process you started is stopped by the PID in its PID file, and only that. Every detached job writes one (`nohup ... & echo $! > job.pid`). No PID file, no kill: tell me instead." When a disk is low: stop writing to it, tell Ember, wait. Reply with the commit range, what is proved, and the one decision for Ember.
