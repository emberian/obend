# Lane C1: identity across kinds, checked code and upgrades

Worktree: `/private/tmp/claude-501/-Users-ember-dev-obend/01a18fe9-771b-71b2-b01f-da7ed6517d48/scratchpad/kinds`, branch `lane-c1`. Contract C1 in `review/DECISIONS-20261031.md` (read it and
its parenthetical findings), `astra/ASTRA-DECISIONS-20261101.md` §3 "Held-code quotation and nominal
checking", `REPORT-KINDS-20261101.md` (the kind cell; its decision), `REPORT-PARSIMONY-20261101.md`
(vault kinds as cells), `REPORT-QUOTE1-20261101.md`, Kimi A on `encodingVersion` and kind pins.

Deliver: (1) nominal type checking: a kind's identity on record types in `PTy`/`Ty` so the checker
refuses a Kilo as a Mile everywhere, not only at direct calls; anonymous structural records kept as a
separate facility; stable kind identity distinct from the pinned version of its layout, law and
methods; `Annotated` and `TermWire` carried through; a higher-order Kilo-to-Mile crossing refused by
name as the tooth. (2) The vault's `_kind.md` pages registered as kind cells (`Kind.effectiveOf`
replaces `kindChain`), several parents per page, staleness from `kind_stale_iff_blocked`. (3) The
portable checked-code artifact: `encodingVersion` covers the syntax schema, the typed-envelope codec
and the checker edition (all codec rules, not tag representatives); `Code Ψ A θ` defined through
`checkAgainst` so `import_complete` needs no re-synthesis; a quotation under two package revisions
tested; `importWith` under a work bound. (4) Mirrors as capabilities: a mirror descriptor checked
against principal, target, grant, view and permitted depth in the same admission route as other
actions, not a forgeable record. (5) Kind pins cover the ancestor versions `effectiveOf` uses, and
`create` rejects name clashes. Cohorts unchanged or deviations recorded.

Build on the box per lean/docs/BUILD-ON-BB2.md (hbox `~/obend/repo` user `hbox` preferred, dregg-build2 `bb2` user `build` otherwise; read ~/swarm/MACHINES.md and RULES.md first). Tier 1 green is the bar for pushing `dev` from the Mac (`--no-verify` when the box built the identical commit); run tier 2 on the box and report it. Lean v4.35.0; every file a `module`; the census is the only axiom check; named-file commits on `dev`, `git -c commit.gpgsign=false commit -F -`, trailer `Co-Authored-By: Claude Opus <noreply@anthropic.com>`, rebase before each push; three other lanes are live, keep theirs on conflicts outside your files. No sorry, no axiom; every former theorem kept or an instance, named in the report `lean/docs/REPORT-<LANE>-20261101.md`. Ember: "Never kill by pattern. No `pkill -f <anything>`, no `pkill -x <bare word>`, no `killall`, no `kill -u`. A process you started is stopped by the PID in its PID file, and only that. Every detached job writes one (`nohup ... & echo $! > job.pid`). No PID file, no kill: tell me instead." When a disk is low: stop writing to it, tell Ember, wait. Reply with the commit range, what is proved, and the one decision for Ember.
