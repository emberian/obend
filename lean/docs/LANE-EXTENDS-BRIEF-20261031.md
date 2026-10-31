# Lane Extends: a stranger extends my package

The design origin (Ember, 10-29): "I really want cross-package extension and laws and document type
thinking in a certain way that becomes natural." Faré's audit finding 1 and Mini's own open list say
no surface form names another package's root. Build it, per `DESIGN.md` §4 (read it first, then
`GROUNDING.md` §5 and the LTUO sections it cites at `astra/fareoo/.../ltuo-readable.txt` §7.3.5.2 and
§9.3.7, then `minidregg/docs/objective-bend/MODULAR-TYPING.md` read-only).

Ground truth: a package root is already a specification knot (`lean/Obend/Spec/Elaborate.lean`,
the package `fix(specification({package: …}, λ$globals λ$seed. extend $seed {…}), {})` lowering;
`Obend/Spec/C4.lean`; `Obend/Spec/Contract.lean` with `run_append`/`run_assoc`); laws with parents
along a C4 list are in `Obend/Law/Inherit.lean`; intentions-as-slots is `Obend/Slot` with
`Slot.World`; the kind cell is described in `review/KIMI-REVIEW-20261030.md` via the Faré audit's
K-KIND-CELL. Build, one commit each: (1) the surface form `package Garden extends commons/record@^2,
bells@0x9f…` parsed and lowered so a parent package's root is an ancestor layer of this package's
root, with C4 identity `(intention, declaration)` so a diamond through two routes applies a parent
once and `compose(E, E)` still twice; the parse and lowering checked by a three-package test
(`tests/obend-source/three-package/` exists in spirit in Mini's cohort; make the real one: a base,
two independent extensions, and a fourth that extends both); (2) a hash parent is an extension fixed
forever, a name parent is an intention: a slot whose candidates are versions, whose chooser is the
name's owner, whose justification is the record naming version v at pin p, resolved inside a
workspace's ecosystem root (DESIGN §4, Astra's §C), with the theorem that a turn pins every root it
resolved and a moved pin is `stale` by name; (3) laws inherit across the package boundary: the
parent's package law is an ancestor of the child's effective law, the refusal names the ancestor
package and clause, and the metarule holds (a child only narrows: `inherited_never_widens` across
packages); (4) orthogonal protocols: `protocol Render for commons/record: def render(self) -> Page`
in a third package attaches a method to a kind it is not an ancestor of, C4-ordered with the rest.
The stranger'"'"'s example: Astra'"'"'s report-extended-by-a-stranger (`astra/ASTRA-SYNTHESIS-20261029.md` §G),
run end to end through `obend run --package`.

Work in your own worktree (`git worktree add /private/tmp/claude-501/-Users-ember-dev-obend/01a18fe9-771b-71b2-b01f-da7ed6517d48/scratchpad/<lane> dev`); Lean v4.35.0; `LEAN_NUM_THREADS=2 lake build 2>&1 | tee build.log` (207 jobs). Every file a `module` (`lean/docs/REPORT-20261030.md` §2). The census in `Obend/Census.lean` is the only axiom check; do not add `#assert_axioms` lines. Mini's cohorts (`python3 lean/tests/run-obend-source.py`) are the control and must stay unchanged unless a change is recorded as a deviation. Named-file commits on `dev`, `git -c commit.gpgsign=false commit -F -`, trailer `Co-Authored-By: Claude Opus <noreply@anthropic.com>`, rebase before each push; a proof-engineering lane is restructuring proofs under `Obend/Core/Proofs` concurrently, so keep theirs on conflicts there. No sorry, no axiom; a theorem that could be vacuous gets a `#tooth`. Report in `lean/docs/`. Ember: "Never kill by pattern. No `pkill -f <anything>`, no `pkill -x <bare word>`, no `killall`, no `kill -u`. A process you started is stopped by the PID in its PID file, and only that. Every detached job writes one (`nohup ... & echo $! > job.pid`). No PID file, no kill: tell me instead." When a disk is low: stop writing to it, tell Ember, wait. Reply with the commit range, what is proved, and the one decision for Ember.
