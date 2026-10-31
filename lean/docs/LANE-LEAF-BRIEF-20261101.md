# Lane Leaf: the emitter, scoped as the compilation that `late_binding` justifies

Worktree: `/private/tmp/claude-501/-Users-ember-dev-obend/01a18fe9-771b-71b2-b01f-da7ed6517d48/scratchpad/runner2` (warm; `git checkout dev && git pull --rebase origin dev`, branch `lane-leaf`).

Scope from Gemini's efficiency argument (in the conversation record; summarized in `DESIGN.md` §1 and
§7 after this lane): rows are static so field names are slot indices; the `prototype spec value`
split and the observer ladder mean reflection touches only the cold spine; `late_binding`
(`Obend/Logic/LateBinding.lean`, proved) says every `self.m` of a known composition is a slot load and
every `super.p` has a statically known target, so the mix/extend chain vanishes at link time; method
fields are already values and need no thunks; computed fields are the lazy cells and take the
two-stage demand cost (the Demand lane). Read `DESIGN.md` §1, §7, §8, `PLAN.md` WS 5, `Core/Machine.lean`,
`Core/Data.lean`, `Logic/LateBinding.lean`, `Spec/Elaborate.lean` (the lowered shapes), and
`/Users/ember/dev/bend` read-only for the leaf language's surface (`bendtt.lean` is the leaf checker
at Lean 4.34; do not vendor it this lane).

Deliver: (1) `Obend/Leaf/Flatten.lean`: for a closed composition over a record target, the flattened
object: a vtable of method closures with `self` as the vtable and each `super.p` resolved to its
provider by `providesLast` on the prefix; theorem `flatten_sound`: `get (flatten layers seed) m ≈b
get (fix (compose layers) seed) m` for every member, by `late_binding` (this is the compilation
theorem). (2) `Obend/Leaf/Emit.lean`: emission of the flattened object to the leaf language's book
(strict, affine): acyclic method definitions, a dispatcher, the slot indices, with computed fields
emitted as explicit thunk cells; the typing side: every emitted definition's type is the row's
member type with `self` at the record type; the theorem that the emitted book's shape is a function
of `(layers, seed)`'s digest. (3) The specialization slot: the emitted book is a candidate whose
supports are the pins of the layers it flattened; the machine (the unflattened term) is the
always-usable candidate; incumbent-first prefers the book while its supports hold, and a moved pin
blocks it by name (`Integrity` theorems applied, no new slot theory). (4) `ReviewMember.obend`
flattened and emitted end to end, with `twiceOfThree` computed by the book equal to the machine's 7,
and a tooth where an `Override` layer added after emission blocks the book. (5) Say exactly what the
refinement against `bendtt.lean`'s `Eval` would need (the toolchain decision, 4.34 versus 4.35, and
whether an interaction-tree simulation through the runner's adapter is the right statement) without
doing it.

Build on the box, not the Mac: lean/docs/BUILD-ON-BB2.md is the loop (edit in the named Mac worktree, `git push bb2 <branch>`, build and run tests over ssh under `swarm-build`; hbox at `~/obend/repo` user `hbox` is the alternative and is faster when up; read ~/swarm/MACHINES.md and RULES.md first). Tier 1 green is the bar for pushing `dev` (from the Mac, `--no-verify` is fine when the box built the identical commit); run tier 2 on the box afterwards and report its result; we revisit only if it is red. Lean v4.35.0; every file a `module`; the census is the only axiom check; named-file commits on `dev`, `git -c commit.gpgsign=false commit -F -`, trailer `Co-Authored-By: Claude Opus <noreply@anthropic.com>`, rebase before each push; other lanes are live, keep theirs on conflicts outside your files. No sorry, no axiom; every former theorem kept or an instance, named in the report. Report in `lean/docs/REPORT-<LANE>-20261101.md`. Ember: "Never kill by pattern. No `pkill -f <anything>`, no `pkill -x <bare word>`, no `killall`, no `kill -u`. A process you started is stopped by the PID in its PID file, and only that. Every detached job writes one (`nohup ... & echo $! > job.pid`). No PID file, no kill: tell me instead." When a disk is low: stop writing to it, tell Ember, wait. Reply with the commit range, what is proved, and the one decision for Ember.
