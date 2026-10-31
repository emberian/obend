# Lane Judge: the judgment class and the receipt type

Both vision studies name this as the first build (`review/VISION-CLAUDE-20261031.md` §6.2, §8, §9.1;
`astra/ASTRA-VISION-20261031.md` §1, §4, §8.A), and `review/GENERALIZATION-20261031.md` G2 and G4 state
it. Read those sections first, then the existing judges you will make instances: the bidirectional
checker (`Core/Bidirectional.lean`, `Elab/Gate.lean`), the law machine probe (`Law/Machine.lean`,
`judge_sound`/`judge_complete`), `coerce` (`Elab/Coerce.lean`), the protocol envelope (`Slot/Protocol.lean`,
`HasProt`), C4's checked linearization (`Law/Proofs/Inherit.lean`, `precedence`), the typing judge
(`Slot/Calculus.lean`, `Decides`), and the fold (`Fold.lean`, `receipt_sufficient`).

Build, as a module with its laws as fields, no spikes:

1. `Obend/Judge.lean`: `class Judge (Obj Cert R) [Graded R]` with deterministic `check : R → Obj →
   Cert → Verdict` where `Verdict = ok | refused Clause Path | uncovered`, `sound` (ok implies the
   declared meaning), `complete` on a stated fragment, `mono` in the grade; a `Format` registration
   record (name, version, the certificate encoding with the theorem that decoded bytes denote the
   checked statement, the checker, its trust base stated: Lean kernel only, compiled trust, external),
   and the regime label `decidable | semidecidable | attestable` the study §6.1 defines. Make the five
   existing judges and `Decides` instances with their existing theorems as the `sound`/`complete` fields,
   so nothing is re-proved. One foreign format end to end, so the registry is not a typeclass in name
   only: LRAT (unsatisfiability proofs for SAT; the study names it as the cheapest with a verified
   checker in the literature) or VeriPB/PBLean pseudo-Boolean proofs (Astra's P17, P18 in `~/paperbin`);
   pick by what is implementable in Lean 4.35 without Mathlib, decode real certificates from a real
   solver run, and plant a bad certificate as a tooth.
2. `Obend/Receipt.lean`: the receipt type the inventory found missing (`review/GENERATED-20261031.md`
   §0, §2.4): `{pre post : Root; row; law : Digest; pins : List (Cell × Option Pin); verdict;
   quantifier : Shape; trust : checked | attested; dated : View}`, per-support trust, prev-hash
   chaining, the disclosure dial as three projections (full log, cited openings, one bit), and
   `receipt_sufficient` from `Fold` as its theorem. `holdsOfPin : Cell → Option Pin → Fact → Bool` with
   `holds_pin` so that `holds_congr` becomes definitional and a stranger computes the read from pins.
   Astra's refusal outcomes (`noAdmissible | awaitingChoice | preferenceKept | candidateRejected |
   staleEvidence | executionFrozen`) are verdict constructors where they apply.
3. Both exercised on one admitted World transition (the runner's negotiation) and one conditional
   algebraic identity checked through the foreign format, with the receipt exported and re-checked by
   a consumer that has no producer state (`obend verify RECEIPT`).

Conventions: work in the warm worktree `/private/tmp/claude-501/-Users-ember-dev-obend/01a18fe9-771b-71b2-b01f-da7ed6517d48/scratchpad/slotrun`
(already at `dev`; branch from it), Lean v4.35.0, every file a `module`, no `#assert_axioms` lines,
one measurement build at the start and one at the end, targeted `lake build Obend.Judge` between.
Named-file commits on `dev`, `git -c commit.gpgsign=false commit -F -`, trailer `Co-Authored-By: Claude
Opus <noreply@anthropic.com>`, rebase before each push. No sorry, no axiom; statements may be
restructured for compositionality if every former theorem is kept or follows, named in the report.
Report `lean/docs/REPORT-JUDGE-20261031.md`. The source trees under `~/dev` other than `obend` are
read-only. Ember: "Never kill by pattern. No `pkill -f <anything>`, no `pkill -x <bare word>`, no
`killall`, no `kill -u`. A process you started is stopped by the PID in its PID file, and only that.
Every detached job writes one (`nohup ... & echo $! > job.pid`). No PID file, no kill: tell me
instead." When a disk is low: stop writing to it, tell Ember, wait. Reply with the commit range, the
foreign format chosen and why, and the one decision for Ember.
