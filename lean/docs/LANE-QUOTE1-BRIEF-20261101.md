# Lane Quote-1: `quote`, `Code`, the importer, mirrors, the observer ladder

Worktree: `/private/tmp/claude-501/-Users-ember-dev-obend/01a18fe9-771b-71b2-b01f-da7ed6517d48/scratchpad/slotrun` (warm; `git checkout dev && git pull --rebase origin dev`, then branch).

The design is `review/QUOTE-ORIENTATION-20261101.md` §3, §4 and §8; read it whole, and the papers
it cites at the load-bearing points if a statement needs them (`~/paperbin`). Ember decided the
shape: `quote` is a kernel function on terms the kernel holds, `splice` a turn, no new `Term`
constructor, program-level quote on values refused. This lane is the orientation's first lane:
theorems T1–T6 (not T6′), T8, T14, plus the two additions of §8 (the versioned encoding,
`holeInCode`), in `lean/Obend/Core/Code.lean` and `lean/Obend/Equiv/Quote.lean`, touching no `Term`
constructor, no machine step, no checker rule.

Ground truth: `encode_injective` (`Core/TermTraverse.lean`), `binds_or_collides` (`Core/Digest.lean`),
`BEquiv`/`bequiv_of_steps`/`mix_assoc` (`Equiv/Behaviour.lean`), `calculus_typed_msubst`
(`Slot/Core4.lean`), `Checked`/`Calculus.Typed` (`Core/Check.lean`, `Slot/Calculus.lean`), `Scoped`
(`Core/Invariant.lean`), `decodePacket_term` (`Spec/Proofs/TermWire.lean`), `SpecMeta` as the model of a
built-in sum. `≈r` needs REFLECTION's probes R01/R02 ported from minidregg's
`tests/objective-bend-source/ltuo/AssociationProvenance.obend` as Lean terms (read-only source).

Deliver, one commit each: (1) `quote`/`unquote`/`address`, `quote_roundtrip`, `digest_of_quote`,
the `Syntax` built-in sum with its encoding digest, `quote_versioned`; (2) `Code Ψ A θ`, `import`
with `import_sound`, `import_complete`, `import_scoped`, and refusals `escapedIndex`, `foreignEncoding`,
`holeInCode`, `assumptionsDiffer`, each with a tooth; (3) `QEquiv`, `REquiv`, `observer_ladder`,
`quote_not_congruent` (Barendregt's pair), `census`, `rewrite_sound_below` at the three levels with
REFLECTION's probe as the `k = b` tooth; (4) `Mirror` with depths, `mirror_attenuates`, `quote` taking a
mirror of depth `code`. If T5 at level `r` needs more of REFLECTION than the two probes, say what.

Conventions. Lean v4.35.0; every file a `module` (`lean/docs/REPORT-20261030.md` §2); the census in `Obend/Census.lean` is the only axiom check, add no `#assert_axioms` lines; one measurement build at the start and one at the end, targeted `lake build Obend.<Lib>` between; Mini's cohorts (`python3 lean/tests/run-obend-source.py`) and the receipt tests (`python3 lean/tests/run-receipts.py`) are the control. Named-file commits on `dev`, `git -c commit.gpgsign=false commit -F -`, trailer `Co-Authored-By: Claude Opus <noreply@anthropic.com>`, `git pull --rebase origin dev` before each push and resolve only your own files; five other lanes are live in their own worktrees, listed in `PLAN.md`. No sorry, no axiom; statements may be restructured for compositionality when every former theorem is kept or follows, named in the report; a theorem that could be vacuous gets a `#tooth` (`Obend/Tactic`). Report in `lean/docs/REPORT-<LANE>-20261101.md` in the lane-report style. The trees under `~/dev` other than `obend` are read-only. Ember: "Never kill by pattern. No `pkill -f <anything>`, no `pkill -x <bare word>`, no `killall`, no `kill -u`. A process you started is stopped by the PID in its PID file, and only that. Every detached job writes one (`nohup ... & echo $! > job.pid`). No PID file, no kill: tell me instead." When a disk is low: stop writing to it, tell Ember, wait. Reply with the commit range, what is fully proved, and the one decision for Ember.
