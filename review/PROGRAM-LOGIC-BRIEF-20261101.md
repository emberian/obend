# Scholar brief: verifying obend programs

Ember, 2026-11-01: "program logics / 'verify obend programs' as a question." The library proves
things about the kernel (the checker, the laws, the slot, the runner). Nobody has yet asked what a
person who writes an `.obend` program can prove about *their* program, in what logic, with what
automation, and how that proof becomes a certificate the kernel re-checks. This is a study for Ember
and Claude to evaluate; it lands nothing in `lean/`.

What exists. The calculus and its reference semantics (`lean/Obend/Core/Term.lean`: `Steps`,
`Evaluates`; the machine `Core/Machine.lean`; adequacy); the typing (`Core/Check.lean`,
`Core/Bidirectional.lean`; uses vectors; the new `Core/Proofs/Conservation.lean`); the behavioural
equivalences (`Equiv/Behaviour.lean` ≈b, `Equiv/Quote.lean` the ladder, `Equiv/Clairvoyant.lean` cost);
laws as closed terms judged per write (`Law/*`), `keeps` claims checked by shape (`Law/Claim.lean`);
protocols with obligations as upper bounds (`Slot/Protocol.lean`); the runner's `Legal` as a trace
predicate (`Run/Spec.lean`) and the audited fold (`Fold.lean`); the judgment class with certificates
(`Judge/*`) and one foreign format (LRAT); quotation of held terms (`Core/Code.lean`). Surface:
`Spec/*` and the examples under `lean/tests/obend-source/`. Read `AMBITION.md`, `DESIGN.md`,
`review/QUOTE-ORIENTATION-20261101.md` §3, `astra/ASTRA-EFFECT-LAWS-20261101.md` §2 (plan contracts)
and §6, `review/VISION-CLAUDE-20261031.md` §6 (automation as certificates), `review/GEMINI-CHECKPOINT-20261101.md`.

The question, in parts. (1) What are the *specifications* a program author wants: functional
correctness of a method against a pre/post pair; an invariant of an object's state across every
admitted write (which the law machinery already judges per write, but not as a proved invariant of
a program); a protocol property of an activity (every `commit` preceded by a `reserve`; obligations
discharged); equivalence of two layers under `mix` (`≈b`, with observers); cost bounds (`≈c`, ticks);
resource properties (a custody is discharged exactly once, which `Conservation` now states for one
step); and properties across a package's extensions (every descendant keeps the base's invariant,
which `keeps` approximates). (2) In what logic: a Hoare or separation logic over the demand machine
(Iris-Lean is usable from this tree: `review/EQUIV-PLAN-20261031.md`); a program logic for lazy
languages (Hackett–Hutton's clairvoyant semantics makes cost Hoare-triples possible; the
literature on lazy program logics is thin, say what exists); a refinement calculus where a
specification layer refines another (`mix` as refinement composition is Faré's own reading); an
equational theory over `≈r`/`≈b` with the ladder as the observer discipline; type-based (the
quantities and protocols already are a logic); and laws-as-specifications, where a `law` is a
Hoare-style postcondition judged at runtime and a *proved* law is one discharged statically for all
writes. (3) Automation and certificates: for each logic, what the producer side is (an SMT or ASP
encoding, a tactic, a rewriter, a model checker over the protocol automaton, proof search like
waterfall, an LLM-proposed invariant) and what the kernel re-checks (a `Judge` instance with its
`Format`), with the regime labeled decidable, semi-decidable-with-certificate, or attestable; which
of these the existing `Judge` can host without change. (4) The surface: what a person writes in
`.obend` (`ensures`, `invariant`, `keeps`, `refines`, `costs`), how a proof obligation is stated,
shown, discharged or left open as a slot (an undischarged obligation is a hole whose candidates are
proofs: the slot theory already has this shape), and what the receipt says. (5) The design: which
logic first and why, what module it is (`Obend/Logic/`?), the first three theorems, the first
example program verified end to end (the Review/Counter examples in `lean/tests/obend-source/`), and
what in the current kernel makes it hard (no source-level subject reduction; records as linear black
holes; two checkers). Fetch literature into `~/paperbin` (Kagi key in `~/dev/allgame/.env`, request
shape in `~/dev/allgame/claude_resident/tools/web_tools.py`; `~/.annas-key`): Iris and its program
logics for effects and sessions; lazy-language program logics and improvement theory; refinement
calculi (Back–von Wright, Morgan); Dafny/Verus/Why3 for the obligation surface and solver
integration; F*'s effect system and its SMT encoding; Lean's own `omega`/`grind` as in-kernel
automation; verified-compilation-style "certificate of a rewrite"; anything on verifying
object-oriented programs with open recursion (Parkinson–Bierman, Leino's dynamic frames, Cook's
specification inheritance, behavioural subtyping).

Write `/Users/ember/dev/obend/review/PROGRAM-LOGIC-20261101.md`, claims tagged READ, INFERRED,
PROPOSED, as long as it needs to be, precise enough to brief a lane from §5. Commit it alone on
`dev` with `git -c commit.gpgsign=false commit -F -` and trailer `Co-Authored-By: Claude Fable 5.1
<noreply@anthropic.com>`, rebase before pushing; two Lean lanes are live, touch nothing under
`lean/`. Ember: "Never kill by pattern. No `pkill -f <anything>`, no `pkill -x <bare word>`, no
`killall`, no `kill -u`. A process you started is stopped by the PID in its PID file, and only that.
Every detached job writes one (`nohup ... & echo $! > job.pid`). No PID file, no kill: tell me
instead." When a disk is low: stop writing to it, tell Ember, wait. Reply with the commit hash, the
logic you would build first, and the first program you would verify.
