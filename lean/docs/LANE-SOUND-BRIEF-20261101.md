# Lane Sound: close the linear soundness holes and the receipt forgery

Gemini's review (`review/GEMINI-CHECKPOINT-20261101.md`, items 1–2) found holes that Linear's teeth
did not cover. Claude verified each against the code; they are real. This lane closes them with
theorems and teeth, in the warm worktree
`/private/tmp/claude-501/-Users-ember-dev-obend/01a18fe9-771b-71b2-b01f-da7ed6517d48/scratchpad/kinds`
(`git checkout dev && git pull --rebase origin dev`, then branch).

**1. Linear soundness (`Core/Check.lean`, `Core/Bidirectional.lean`, their proofs).** Four rules let
a linear hypothesis be dropped or duplicated by `Step`: `specification` (no `linearFree` on the
metadata uses `mu`; `applySpecification` discards the metadata), `case`/`ArmsTyping.cons` (a linear
scrutinee consumed once by `inject`, payload bound `.unrestricted`), `ifZero` and `ifBool` (no
`linearFree` on the scrutinee, predecessor `.unrestricted`), `extend` (no `linearFree` on
`targetUses`; `extendRecord` overwrites). For each: first write the counterexample as a `#guard` that
the current checker accepts and a tooth that `Step` drops the hypothesis; then add the premise
(`linearFree context mu`, `linearFree context scrutineeUses`, `linearFree context vu`/`cu`,
`linearFree context targetUses`, or the quantity-preserving binding where that is the honest rule),
re-establish substitution, preservation and completeness (`check_msubst`, `calculus_typed_msubst`,
`complete`, `full_annotated`, `prepare_checks`), and turn the counterexample into a named refusal.
Then the theorem Gemini says is missing and is right about: **linear resource conservation**, a
`Step` never drops a linear custody value without an explicit discharge (state it over the live
linear positions of a well-typed closed term and prove it by preservation; if it needs the machine,
say so and state the source-level version). Run the journal before and after; cohorts, receipts,
workspaces and the walkthrough are the control, with any deviation recorded beside Linear's.

**2. Receipt verification (`Receipt.lean`, `Receipt/Export.lean`).** (a) `recheck` must enforce
`R.openings.map Prod.fst == A.reads (w', rest) R.row`, so `dated_sound`'s hypothesis `hm` is computed,
not assumed; (b) `capOpening` fails closed: `| none => false`; (c) `verify` derives the trust
ceiling from `R.supports`' modes, never from a separate `R.trust` list, and refuses a receipt whose
attested support has no attested entry; (d) `accepts` in `.cited` mode runs `recheck` and
`datedOpens` and the supports' verdicts, skipping only certificate re-execution; `.bit` is the only
mode that trusts the producer's bit; (e) `verify` takes an explicit expected root and checks
`R.dated` against it, and checks `R.quantifier` against the law's mode rather than trusting the
label (Astra's two probes). Add each forgery as a test in `tests/run-receipts.py` that must now be
refused by name (the omitted-capability receipt, the empty-trust receipt, the clock-shifted
receipt, the relabelled quantifier).

**3. Fork stitch (`Run/Fork.lean`).** `stitch` replays each deferred step through `crun` against
main's current World, law and authority at stitch time, and is atomic on the ledger (if any escalated
step is refused, main's ledger is unchanged and every refusal is a conflict section). Keep
`stitch_is_commit`, `stitch_accounts`, `stitch_exclusive`, `stitch_double_spend`; add
`stitch_atomic` and a tooth where a two-step escalation with the second refused leaves the first
uncommitted. `propagate` returns `Except` rather than swallowing.

Conventions: Lean v4.35.0; every file a `module`; set `git config core.hooksPath lean/tools/hooks` in
the worktree; one measurement build at the start and end; named-file commits on `dev`,
`git -c commit.gpgsign=false commit -F -`, trailer `Co-Authored-By: Claude Opus <noreply@anthropic.com>`,
rebase before each push; one other lane (Expose) is live under `Core` definitional modules, keep
theirs on conflicts in `@[expose]` lines. No sorry, no axiom; every former theorem kept or an
instance, named in the report `lean/docs/REPORT-SOUND-20261101.md`. Ember: "Never kill by pattern.
No `pkill -f <anything>`, no `pkill -x <bare word>`, no `killall`, no `kill -u`. A process you started
is stopped by the PID in its PID file, and only that. Every detached job writes one (`nohup ... &
echo $! > job.pid`). No PID file, no kill: tell me instead." When a disk is low: stop writing to it,
tell Ember, wait. Reply with the commit range, the conservation theorem's statement, and anything in
Gemini's items 1–3 you found not to be a bug.
