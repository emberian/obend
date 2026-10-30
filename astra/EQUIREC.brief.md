You are Astra (GPT-6), asked by Ember to make Objective Bend's type agreement equi-recursive:
option (c) of the checker lane's decision. Ember: "let's be ambitious; (c) is clearly the right thing."
You own this end to end, and you may spawn Sol workers (model `gpt-6.1-sol`) as codex subagents for
parallel pieces, each with a short brief naming the files it owns; you read their Lean, build, commit.

## Where things stand

`/Users/ember/dev/obend/lean`, Lean 4.30.0, 123 jobs green at `1b0600d` on `dev`. Read, in order:
`review/CHECKER-COMPLETENESS-REPORT-20261030.md`, `review/ARGON-RESPONSE-20261030.md`,
`lean/docs/REPORT-CHECKER-20261030.md` (all of it; §7 is the follow-up that found the corollary
false), `lean/docs/REPORT-20261030.md` §2 (the module discipline), then the code:
`Obend/Core/Check.lean` (`sameType` at ~91 and `sameType_equivalence` at ~620, `PartialTyping` at ~183,
the annotation-directed `infer`/`check`), `Obend/Core/Bidirectional.lean`, `Core/Proofs/BidirectionalCompleteness.lean`
(`complete`, `full_corollary_fails`, the fragment `checkCovered`), `Core/Proofs/CheckCompletenessObstruction.lean`,
`Obend/Slot/Calculus.lean`, `Obend/Slot/Core4.lean` (the two-route judge, `routes_agree`,
`annotation_presence_not_coverage`), and the machine side that depends on agreement:
`Core/MachineTyping.lean` (`HeadNormalizes`), the lookup-transport lemmas in `Core/Proofs/Preservation*.lean`.
Paper: `~/paperbin/amadio-cardelli1993-subtyping-recursive-types.txt` (the visited-set decision
procedure for equi-recursive equality; Brandt–Henglein's coinductive axiomatization is the other
reference, not in paperbin).

The situation in one paragraph. `sameType` is an equivalence (chaining of one-step alias unfolding
at the head) but it does not descend into arrows, rows or sums: `α → Bool` does not agree with
`Nat → Bool` when `α := Nat`. Because of that, a record or `extend` built where the checker must
synthesize cannot be typed, `extend` is outside the bidirectional fragment, and the full corollary
(every typed term has an annotated form the checker accepts) is provably false: the witness is a
repeated-label record whose field is a lambda converted to an alias of its arrow. The judge today
admits through two routes and its coverage predicate is not syntactic.

## The goal

Type agreement that descends structurally and treats alias variables equi-recursively, decided by
a visited-set procedure (Amadio–Cardelli), with rigid variables still nominal and looked up through
their lower bound. Then the consequences, each a coherent commit:

1. `sameType` redefined as the equi-recursive congruence; `Equivalence` and congruence lemmas
   (arrow, record, variant, computation); decidability without fuel, the visited set bounded by the
   finite variable set of `assumptions`; the proof that it extends the current relation (every old
   agreement is a new agreement).
2. The relation and the machine: `PartialTyping.conversion` over the new agreement; the machine
   invariants (`HeadNormalizes`, lookup transport, preservation cases) re-established. This is the
   expensive part; use the journal (`lake exe journal`, `lean/Journal/README.md`) before and after to
   get the exact repair set, and `obend_cases` (`Obend/Tactic`) for the case explosions.
3. The bidirectional checker: `extend`, records with repeated labels and `inject` enter the fragment
   because the expected row now agrees with the synthesized one structurally; `checkCovered` grows
   accordingly; `complete` re-proved on the larger fragment.
4. The corollary: `annotateFromDerivation` and the full completeness statement, which `full_corollary_fails`
   currently refutes; its witness must now be admitted and the refutation replaced by the theorem.
   If some residue remains outside, state it as a theorem with its witness, as the lane did.
5. The judge: one route, `Covered` syntactic, `routes_agree` and the annotation route retired if the
   corollary makes them redundant; `extend_filling_admitted` and the budget teeth rebuild; the
   `Slot.Calculus` laws unchanged or changed with the reason written.

Done means: full `lake build` green, no sorry, no axiom, every pin intact, Mini's cohorts in
`lean/tests` unchanged (run `lean/tests/run-obend-source.py`), the journal's repair sets recorded, and
`lean/docs/REPORT-EQUIREC-20261031.md` in the lane-report style with decisions, critique and
meta-critique, and what you did not do.

## Conventions

Named-file commits on `dev`, `git -c commit.gpgsign=false commit -F -`, trailer
`Co-Authored-By: Astra (GPT-6) via codex <noreply@openai.com>`, push after each step; nobody else is
working in the tree. Build with `LEAN_NUM_THREADS=2 lake build 2>&1 | tee lean/build.log`; one build
at a time. The source trees under `~/dev/minidregg`, `~/dev/nanodregg`, `~/dev/bend` are read-only.
Ember's safety paragraph, verbatim: "Never kill by pattern. No `pkill -f <anything>`, no `pkill -x
<bare word>`, no `killall`, no `kill -u`. A process you started is stopped by the PID in its PID
file, and only that. Every detached job writes one (`nohup ... & echo $! > job.pid`). No PID file,
no kill: tell me instead." When a disk is low: stop writing to it, tell Ember, wait.
