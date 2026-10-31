# Lane Demand (contract C4): the demand semantics for knots, and ticks within a constant

Worktree: `/private/tmp/claude-501/-Users-ember-dev-obend/01a18fe9-771b-71b2-b01f-da7ed6517d48/scratchpad/build` (warm; `git checkout dev && git pull --rebase origin dev`, branch `lane-demand`).

Decided (`review/DECISIONS-20261031.md` C4; `review/GEMINI-CHECKPOINT-20261101b.md` §4): the cost
semantics for objects is the two-stage demand semantics on approximation types, Xia, Israel, Kramarz,
Coltharp, Claessen, Weirich, Li, ICFP 2024, *Story of your lazy function's life*
(`~/paperbin`, read Thms 3.8–3.9 and §4), extended to recursive `let` (knots), which their calculus
lacks. Gemini's Experiment 2 (its Lean is in the conversation record; the root will paste it into
`lean/Obend/Equiv/Approximant.lean` for you as a starting module) proved: iterated approximants
(`fixApprox`) give `{a = 7, b = self.a}.b` a derivation at cost 16, the approximant chain is monotone
and stabilizes, `Within` factor 8 survives, all three measured programs agree with the machine; and
found that naive re-running of `selfBody` over-charges shared work outside the record by the
dependency depth. Read `lean/docs/REPORT-COST-20261101.md`, `Equiv/Clairvoyant.lean`,
`Core/Proofs/TickCost.lean`, `Equiv/Cost.lean`, `Judge/Cost.lean`.

Deliver: (1) the two-stage rule in `Equiv/Clairvoyant.lean` (or a sibling that `Clairvoyant`
re-exports): settle the template once with `self` free (`Settled (.bound 0)`), then iterate field
waves on the settled record (`V₀ = skipped`, `V_{m+1} ← Run .fields (V.substitute (single V_m))`),
so shared work outside the record is paid once; the determinism/totality theorem on approximation
types (Xia Thm 3.8 shape: the demand run is a function of the demand) and minimality (Thm 3.9 shape:
it computes the minimum over clairvoyant runs) for the Core4 fragment, with `fixApprox`'s
over-charge as the tooth. (2) `self_field_no_cv` retired and replaced by the positive derivation;
`mix_assoc_cost` and Faré's tests re-established under the new rule; `Within` unchanged. (3) The
tick theorem that `ticks_not_within_cv` refuted, now in its true form: machine ticks are within a
stated constant of the two-stage demand cost on every program for which the demand run exists
(the three measured programs as the first instances, then the general statement through the
machine-to-source relation in `Core/Proofs/Completeness`; if the general form needs source-level
completeness that is still open, state exactly what is missing and prove the bound on the
finite-signature fragment). (4) The improvement judge (`Judge/Cost.lean`) takes a demand derivation
as a certificate, so `cost t ≤ k` is a checkable upper bound (Gemini §1.5: provide `readyB` so the
checker is total), and `CostWithin`'s symmetric `8ⁿ` factor is replaced by a directional improvement
relation with a flat constant via parallel `Sim` per step. (5) `claim within(...)` lands in the
surface only if (4) is clean; otherwise leave it for the Logic lane and say so.

Build on the box, not the Mac: lean/docs/BUILD-ON-BB2.md is the loop (edit in the named Mac worktree, `git push bb2 <branch>`, build and run tests over ssh under `swarm-build`; hbox at `~/obend/repo` user `hbox` is the alternative and is faster when up; read ~/swarm/MACHINES.md and RULES.md first). Tier 1 green is the bar for pushing `dev` (from the Mac, `--no-verify` is fine when the box built the identical commit); run tier 2 on the box afterwards and report its result; we revisit only if it is red. Lean v4.35.0; every file a `module`; the census is the only axiom check; named-file commits on `dev`, `git -c commit.gpgsign=false commit -F -`, trailer `Co-Authored-By: Claude Opus <noreply@anthropic.com>`, rebase before each push; other lanes are live, keep theirs on conflicts outside your files. No sorry, no axiom; every former theorem kept or an instance, named in the report. Report in `lean/docs/REPORT-<LANE>-20261101.md`. Ember: "Never kill by pattern. No `pkill -f <anything>`, no `pkill -x <bare word>`, no `killall`, no `kill -u`. A process you started is stopped by the PID in its PID file, and only that. Every detached job writes one (`nohup ... & echo $! > job.pid`). No PID file, no kill: tell me instead." When a disk is low: stop writing to it, tell Ember, wait. Reply with the commit range, what is proved, and the one decision for Ember.
