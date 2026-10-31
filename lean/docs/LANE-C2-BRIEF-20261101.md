# Lane C2: ownership across aggregates and staging

Worktree: `/private/tmp/claude-501/-Users-ember-dev-obend/01a18fe9-771b-71b2-b01f-da7ed6517d48/scratchpad/runner2`, branch `lane-c2`. Contract C2 in `review/DECISIONS-20261031.md`,
`REPORT-SOUND-20261101.md` (§5–§6: the `case` rule, subject reduction, `custody_conserved`,
`RowRefines`), `review/GEMINI-CHECKPOINT-20261101.md` §4.2 (records as linear black holes),
`review/RECENT-20261101.md` on Abel–Danielsson–Eriksson 2023 (`prodrec`), Astra's decisions §3
"Exactly-once binders and records consumed whole".

Deliver: (1) the positive counterpart to the projection refusal: a consuming record destructor
(`prodrec`-shaped: `let {a, b} = r in body` consuming `r` once and binding each field at its own
quantity), typed in `PartialTyping` and the checker, stepped in `Step`, with subject reduction and
conservation re-established (the singleton round trip `{held = h}.held` becomes typable through it);
anonymous records stay `⊗`-introduced, and `get` stays the `&`-style eliminator for shareable fields.
(2) The stated aggregate contract: how a resourceful aggregate may be dropped, transferred, split and
returned, and what a terminal machine state owes, as theorems over `Step` and the machine, not prose.
(3) Transfer across a generated-code boundary and closure capture tested as teeth (Astra's list:
returning a resource, nesting it, matching it, capture, crossing a quotation/import). (4) The quantity-indexed `joinUses` revisited: whether unrestricted should stay max (term-only counts) is settled with a theorem about what the count may be read as (all-path usage, never demand or cost).
(5) T7 of the quote orientation (`review/QUOTE-ORIENTATION-20261101.md` §4): the usage-composed contextual substitution for `splice`, so a splice cannot launder a once-resource, with its tooth. Cohorts unchanged or deviations recorded.

Build on the box per lean/docs/BUILD-ON-BB2.md (hbox `~/obend/repo` user `hbox` preferred, dregg-build2 `bb2` user `build` otherwise; read ~/swarm/MACHINES.md and RULES.md first). Tier 1 green is the bar for pushing `dev` from the Mac (`--no-verify` when the box built the identical commit); run tier 2 on the box and report it. Lean v4.35.0; every file a `module`; the census is the only axiom check; named-file commits on `dev`, `git -c commit.gpgsign=false commit -F -`, trailer `Co-Authored-By: Claude Opus <noreply@anthropic.com>`, rebase before each push; three other lanes are live, keep theirs on conflicts outside your files. No sorry, no axiom; every former theorem kept or an instance, named in the report `lean/docs/REPORT-<LANE>-20261101.md`. Ember: "Never kill by pattern. No `pkill -f <anything>`, no `pkill -x <bare word>`, no `killall`, no `kill -u`. A process you started is stopped by the PID in its PID file, and only that. Every detached job writes one (`nohup ... & echo $! > job.pid`). No PID file, no kill: tell me instead." When a disk is low: stop writing to it, tell Ember, wait. Reply with the commit range, what is proved, and the one decision for Ember.
