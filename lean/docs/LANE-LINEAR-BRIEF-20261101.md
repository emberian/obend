# Lane Linear: `linear` separates from `affine` in the checker

Worktree: `/private/tmp/claude-501/-Users-ember-dev-obend/01a18fe9-771b-71b2-b01f-da7ed6517d48/scratchpad/linear`.

Ember decided: exact discharge of `linear` binders is enforced in the kernel. Today `safeQuantity`
treats `affine` and `linear` as "at most once" and `Quantity.fits` (exactly once) lives only in
`CheckTeeth` (`review/ALGEBRAIC-SUBTYPING-20261031.md` §5.1; `Core/Check.lean`, `Core/Ty.lean`). This
gates T7 of the quote orientation (a splice must not launder a once-resource) and the coercion
quantity table (`Elab/Coerce.lean`).

Deliver: (1) `PartialTyping` and `Bidirectional.checkAgainst` enforce exactly-once for `linear`
binders (a `linear` hypothesis used zero times is refused by name at the binder), with the uses
vector unchanged in shape; preservation, substitution (`check_msubst`, `calculus_typed_msubst`) and
completeness (`complete`, `full_annotated`, `prepare_checks`) re-established, the journal
(`lake exe journal`) run before and after with the repair set in the report; (2) the coercion
quantity table re-derived: the η-wrapper acceptance matrix the Elab report measured changes exactly
where the orientation predicts, as `#guard` probes, and `coerce` refuses relabelling `linear` as
`affine`; (3) teeth: a dropped `linear` custody refused; `open_filling_tooth` still bites; a
coercion that would launder a once-resource refused by name. Cohorts and receipts unchanged, or each
change recorded as a deviation with the before and after.

Conventions. Lean v4.35.0; every file a `module` (`lean/docs/REPORT-20261030.md` §2); the census in `Obend/Census.lean` is the only axiom check, add no `#assert_axioms` lines; one measurement build at the start and one at the end, targeted `lake build Obend.<Lib>` between; Mini's cohorts (`python3 lean/tests/run-obend-source.py`) and the receipt tests (`python3 lean/tests/run-receipts.py`) are the control. Named-file commits on `dev`, `git -c commit.gpgsign=false commit -F -`, trailer `Co-Authored-By: Claude Opus <noreply@anthropic.com>`, `git pull --rebase origin dev` before each push and resolve only your own files; five other lanes are live in their own worktrees, listed in `PLAN.md`. No sorry, no axiom; statements may be restructured for compositionality when every former theorem is kept or follows, named in the report; a theorem that could be vacuous gets a `#tooth` (`Obend/Tactic`). Report in `lean/docs/REPORT-<LANE>-20261101.md` in the lane-report style. The trees under `~/dev` other than `obend` are read-only. Ember: "Never kill by pattern. No `pkill -f <anything>`, no `pkill -x <bare word>`, no `killall`, no `kill -u`. A process you started is stopped by the PID in its PID file, and only that. Every detached job writes one (`nohup ... & echo $! > job.pid`). No PID file, no kill: tell me instead." When a disk is low: stop writing to it, tell Ember, wait. Reply with the commit range, what is fully proved, and the one decision for Ember.
