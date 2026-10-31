# Lane Logic: the claim logic, late binding, and `ReviewMember` verified end to end

Worktree: `/private/tmp/claude-501/-Users-ember-dev-obend/01a18fe9-771b-71b2-b01f-da7ed6517d48/scratchpad/runner2` (warm; `git checkout dev && git pull --rebase origin dev`, then branch
`lane-logic`). The design is `review/PROGRAM-LOGIC-20261101.md`; read it whole, then §5 is your
specification and §5.6 your deliverable. Ground truth to read before writing: `Equiv/Behaviour.lean`
(`BEquiv`, `bequiv_of_steps`, `bequiv_of_ahead`, `mix_apply`), `Equiv/Quote.lean`
(`rewrite_sound_below`, `observes`), `Judge/Cost.lean` (the certificate replay shape,
`CostWithin.context`), `Judge/Instances.lean` 115–210 (`lawProbe`), `Law/Claim.lean` (`Keeps`,
`Chain`), `Spec/Elaborate.lean` 929–931, 1199–1244, 1486–1508 (layer and claim lowering),
`Core/Term.lean` (`Step`, `extendFields`, `mixBody`, `Interaction`), `Slot.lean` (`Slot`,
`read_blocked_exact`), `Core/Code.lean` (`quote`, `address`), `Receipt.lean`.

Deliver, one commit each: (1) `Obend/Logic/{Claim,LateBinding}.lean`: `Holds`, `Obligation`,
`instantiateClaim` computing `superAt j` from the chain, the lowered layer shapes matching
Elaborate, and T1 `late_binding` with `late_binding_bequiv` and its tooth (a later provider moves
the index). (2) `Logic/Rewrite.lean`: `RStep` (`run`, `lateBinding`, `assoc`, `congr` with the
census check, `trans`), the checker, T2 `rewrite_sound`, `holds_equal_of_rewrite`, the `Judge`
instance, the planted bad derivation refused `stepMismatch`. (3) `Logic/Ground.lean`: the ground
judge as `lawProbe`'s twin with `Meaning := Holds`, refuting on `false`. (4) `Logic/Frame.lean`: T3
`claim_frame`, certificate transport along compositions agreeing at the supports, with the tooth
that a re-provided member blocks the slot by name. (5) `Logic/Obligation.lean`: the claim slot
(candidates `(format, bytes)`, supports, judge, status as the slot's read: `unchecked | checked |
blocked | refuted | attested`), `address (quote c)` tying the certificate to its claim; `Spec/`
changes for `claim … given …`, `keeps INV by LAW`, status in `SpecMeta.claims` from the slot;
`obend check` listing open obligations, `obend prove NAME` running the producers in order and
installing the first accepted certificate, `obend verify` replaying a claim receipt from the receipt
and the quoted statement alone. (6) `ReviewMember.obend` verified as §5.4: the two-step derivation,
support `{twice ↦ Twice}`, the three teeth (ground at `7` with the `+ 2n` mutation refuting at `3`;
frame with `Override` re-providing `twice`; statement with a wrong `address` refused `malformed`),
the receipt in `lean/tests/logic/`. (7) Optional if time allows: T4, a `caseSplit` step for open
scrutinees in `RStep`, so derivations become proof trees; and `Logic/Turn.lean` for `Counter.obend`'s
`bump` per listed response.

Gate: the three teeth red under their mutations; the receipt re-checked by `obend verify` with no
producer state; cohorts (`python3 lean/tests/run-obend-source.py`), receipts (`run-receipts.py`),
workspaces and the walkthrough unchanged; census clean. Touch nothing under `Core/`, `Equiv/`,
`Law/`, `Judge/Class.lean`. Conventions: Lean v4.35.0; every file a `module`; set `git config
core.hooksPath lean/tools/hooks`; one measurement build at start and end; named-file commits on
`dev`, `git -c commit.gpgsign=false commit -F -`, trailer `Co-Authored-By: Claude Opus
<noreply@anthropic.com>`, rebase before each push (Sound and Expose are live under `Core`; keep
theirs on conflicts). No sorry, no axiom. Report `lean/docs/REPORT-LOGIC-20261101.md`. Ember: "Never
kill by pattern. No `pkill -f <anything>`, no `pkill -x <bare word>`, no `killall`, no `kill -u`. A
process you started is stopped by the PID in its PID file, and only that. Every detached job writes
one (`nohup ... & echo $! > job.pid`). No PID file, no kill: tell me instead." When a disk is low:
stop writing to it, tell Ember, wait. Reply with the commit range, which of T1–T3 are proved, and
the one decision for Ember.
