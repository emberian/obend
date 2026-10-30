# Lane Law: `Obend.Law`, laws by occasion over Core4

Goal: the law library for Objective Bend, as nanodregg built it for its own term language, ported
onto Core4 terms. A law is a closed Core4 term of type `State → State → Req → Verdict`, where
`Verdict = sum {ok: {}, refused: String}` and `Req` carries an `occasion` sum
`birth | adopt | relaw | retire | write | invoke`. Every law is built by a generator that states an
arm for every occasion, and what each generator means is a theorem over Core4's reference
semantics, never by evaluating the term.

Read first: `/Users/ember/dev/obend/METATHEORY.md` §2 (the Law row), `/Users/ember/dev/obend/lean/README.md`,
`lean/docs/REPORT-20261030.md` §2 (the module discipline; required before touching a `module` file),
then nanodregg's originals via `git -C /Users/ember/dev/nanodregg show origin/main:<path>`:
`Lang/Std.lean` (the `At` cursor, `okT`/`refusedT`/`guard`/`guards`/`allOf`, `lawOf S birth adopt
relaw retire change`, `ownerSigns`, `allowlist`, `bounded`, `quorum`, `windowed`, `machine`),
`Lang/Proofs/Std.lean` (the meaning theorems: `guard_ok`, `lawCase_*`, `bounded_spec`,
`quorum_adopt_fresh`, `machine_adopt`, …), `Lang/Claim.lean` and `Lang/Proofs/Claim.lean` (`keeps`,
`guardedBy`, `guardedBy_sound`, `chain_keeps`), and `decisions/lang.md` entries LANG-8, LANG-19,
LANG-20, LANG-24, LANG-92 for why each shape is what it is.

Ground truth here: `lean/Obend/Core/Term.lean` is the `Term` you target (`lam`, `app`, `record`,
`get`, `inject`, `case`, `ifBool`, `binary` with `equal/less/lessEqual/…`, `label`, `nat`,
`boolean`; no `ite` and no bytes: a refusal reason is a `label`); `Core/Ty.lean` has `Ty` with
records and sums; the reference semantics is `Steps`/`Evaluates` in `Term.lean` and the machine
`runBounded` in `Core/Machine.lean`; `Obend/AxiomPin.lean` has `#assert_axioms`. Build with
`cd /Users/ember/dev/obend/lean && LEAN_NUM_THREADS=2 lake build 2>&1 | tee build.log` (about 80 s).

Build, one commit each: (1) `Obend/Law/Syntax.lean`: `occasionTy`, `verdictTy`, `reqTy S`,
`lawTy S`, the `At` cursor and the combinators; (2) `Obend/Law/Std.lean`: the generators, each a
closed Core4 term; (3) `Obend/Law/Proofs/Std.lean`: the meaning theorems over `Evaluates`, with
`#assert_axioms` pins; (4) `Obend/Law/Claim.lean` + proofs: `keeps` and its certifying-shape checker
with `guardedBy_sound` and `chain_keeps`; (5) `Obend/Law/Inherit.lean` + proofs: laws with parents
combined by conjunction along a C4 precedence list (reuse `Obend.Spec.C4` if it has landed, else a
list), `effective_law_eval`, `inherited_never_widens`, and the refusal naming the ancestor clause.
Add `Obend.Law` to the root `Obend.lean`. Every theorem that could be vacuous ships with a `decide`
tooth beside it. Write `lean/docs/REPORT-LAW-20261030.md` in the style of `REPORT-20261030.md`.

You own `lean/Obend/Law.lean`, `lean/Obend/Law/**`, your report, and one line in `Obend.lean`.
Other lanes are live in `Obend/Spec`, `Obend/Core/Graded.lean`, `Core/Traverse.lean`, `Obend/Tactic`,
`Obend/Slot`; leave them be, and if the build is red in their files, build yours by name
(`lake build Obend.Law`). Commits: named files on `dev`, `git -c commit.gpgsign=false commit -F -`
with trailer `Co-Authored-By: Claude Opus <noreply@anthropic.com>`, `git pull --rebase origin dev`
before each push. The source trees are read-only. No sorry, no axiom, no weakened statement.

Ember's one safety paragraph, verbatim: "Never kill by pattern. No `pkill -f <anything>`, no
`pkill -x <bare word>`, no `killall`, no `kill -u`. A process you started is stopped by the PID in
its PID file, and only that. Every detached job writes one (`nohup ... & echo $! > job.pid`). No PID
file, no kill: tell me instead." And on disk: when a disk is low, stop writing to it, tell Ember, wait.

Reply with the commit range, which theorems are fully proved, and the one decision for Ember.
