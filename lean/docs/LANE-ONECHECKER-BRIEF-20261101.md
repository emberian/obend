# Lane OneChecker (gate 2): retire `Check.infer`; `Bidirectional.checkAgainst` is the checker

Worktree: `/private/tmp/claude-501/-Users-ember-dev-obend/01a18fe9-771b-71b2-b01f-da7ed6517d48/scratchpad/cost` (warm; `git checkout dev && git pull --rebase origin dev`, then branch).

Why now. Two executable checkers exist against one `PartialTyping`: the fuel-indexed
`Check.infer`/`check` and the structural `Bidirectional.checkAgainst` with `tree_complete`. Every
change to the typing rules is paid twice (`REPORT-LINEAR-20261101.md`, `REPORT-SOUND-20261101.md`
§5: the legacy checker cannot carry the new `case` quantity and is now the stricter one;
`review/GEMINI-CHECKPOINT-20261101.md` §6.2 and gate 2; `REPORT-EXPOSE2-20261101.md`: `infer`'s
`_unsafe_rec` body is what cascades on every edit). Read those, then `Core/Check.lean`,
`Core/Bidirectional.lean`, `Core/Proofs/{Substitution*,Completeness,BidirectionalCompleteness,
Conservation,Hole,Templates}.lean`, `Elab/*.lean`, `Slot/Core4.lean`, `Spec/Elaborate.lean` (the
open-template check still uses `Check.check` for `check_instantiate`), `Core/Packet.lean`.

Deliver, one commit each, every former theorem kept or an instance named in the report: (1) an
inventory: every consumer of `Check.infer`/`check`/`inferFields`/`inferArms` and every theorem
stated about them (`check_msubst`, `checked_msubst`, `check_mono`, `infer_mono`, `check_instantiate`,
`judge_iff_check`, the budget theorems, `routes_agree`), with the bidirectional counterpart each
has or lacks. (2) The counterparts that are missing, proved for `checkAgainst`: substitution
(`checkAgainst_msubst`, from `calculus_typed_msubst` and `complete`), the open-template
instantiation theorem (`check_instantiate` restated over `checkAgainst` with the annotation tree
instantiated alongside), and whatever the Elab, Slot and Spec consumers cite. (3) Consumers moved:
`Spec/Elaborate`'s template check, `Slot/Core4`'s judge, `Core/Packet`, the budget judge, each on
`checkAgainst` with `checkWork` as the grade; the annotation-directed route in the slot judge gone
if `full_annotated` and the cohorts allow it (it should: `annotateExecutable_checks` exists). (4)
`Check.infer`, `check`, `inferFields`, `inferArms` and their proofs deleted; `PartialTyping`,
`Checked`, the quantity rules, `sameType` and the row machinery stay in `Check.lean` as the
specification. (5) The measurement: a `checkAgainst` body edit, modules rebuilt and seconds, against
the twenty-module gate; and whether the `_unsafe_rec` body of `checkAgainst` (structural recursion
on `(Term, AnnotationTree)`) cascades the same way, with the one-`Nat`-recursion rewrite proposed
or refused on that evidence. Cohorts, receipts, workspaces and the walkthrough unchanged, or each
deviation recorded; the journal before and after.

Conventions: Lean v4.35.0; every file a `module`; `git config core.hooksPath lean/tools/hooks`;
named-file commits on `dev`, `git -c commit.gpgsign=false commit -F -`, trailer `Co-Authored-By:
Claude Opus <noreply@anthropic.com>`, rebase before each push (the Logic lane is live under
`Obend/Logic` and `Spec/`'s claim surface; keep theirs on conflicts in `Spec`). No sorry, no axiom.
Report `lean/docs/REPORT-ONECHECKER-20261101.md`. Ember: "Never kill by pattern. No `pkill -f
<anything>`, no `pkill -x <bare word>`, no `killall`, no `kill -u`. A process you started is
stopped by the PID in its PID file, and only that. Every detached job writes one (`nohup ... & echo
$! > job.pid`). No PID file, no kill: tell me instead." When a disk is low: stop writing to it,
tell Ember, wait. Reply with the commit range, which theorems lost their statement (there should be
none) and which gained a bidirectional counterpart, the measurement, and the one decision for Ember.
