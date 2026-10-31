# Checkpoint 2026-10-31, for outside review

Tag `checkpoint-20261031` on `dev` (`emberian/obend`). Everything below is committed; two lanes
(proof engineering; the shared-World composition layer) are mid-work and not in this checkpoint.

## What the system is

A language with a Lean-checked core for objects anyone can extend without forking, laws judged on
every write, and documents that remember why they say what they say, built to run Bend underneath.
It is close in kind to a theorem prover or an automated reasoning system: every admission is a
re-executed check of a certificate, every refusal names the clause that failed, and the metatheory
is mechanized (about 200 modules, 2,500 theorems, a whole-library axiom census in the build, mutation
teeth that fail a theorem under a planted fault). `README.md` is the entry.

## Read in this order

1. `THESIS.md`, `DESIGN.md`, `METATHEORY.md` (the claim, the design, what is mechanized).
2. `review/DECISIONS-20261031.md` (every decision, who took it, what is open).
3. `review/GENERALIZATION-20261031.md` (what the research converges on: the audited fold, the
   judgment class, intentions as slots, the receipt type, laws over declared domains).
4. The studies it rests on: `review/GENERATED-20261031.md` (what the generated objects are: HoTT,
   arithmetization and epistemic readings), `astra/ASTRA-EFFECT-LAWS-20261031.md` (laws over effects,
   composition, hyperproperties, oracle evidence, hybrid intelligence), `review/ALGEBRAIC-SUBTYPING-20261031.md`,
   `review/EQUIV-PLAN-20261031.md`, `astra/ASTRA-SELECTION-20261031.md`, `astra/ASTRA-EVAL-20261031.md`,
   `review/SYNTHESIS-20261031.md` (refuted in `lean/docs/REPORT-JUST-20261031.md`; kept for the refutation).
5. The lane reports in `lean/docs/REPORT-*.md`, one per module, each with decisions, critique and
   what is not proved; `review/KIMI-REVIEW-20261030.md` and `review/ARGON-RESPONSE-20261030.md` for the
   earlier outside reads and what was taken from them.
6. The Lean under `lean/Obend/` where a claim needs checking; `lean/README.md` says how to build.

## What to critique

- The checker: a bidirectional checker complete on a stated fragment, equi-recursive agreement by
  finite bisimulation, executable annotation preparation; full annotated completeness proved
  (`lean/docs/REPORT-EQUIREC-20261031.md`, `REPORT-ELAB-20261031.md`). Is the fragment the right one,
  and is "complete via `Classical.choose`, executable on a fragment" the honest split?
- The slot and runner: deferred decisions with withdrawable supports, repair under a stated
  compatibility condition, stored selection with incumbent-first default, a guarded runner with
  `refines` (every dispatched operation admitted at its view, no token spent twice, nothing in flight
  replanned), decision authority as a layer. Is `World`'s law set (pin congruence, retirement,
  version non-return with a collision stance) the right abstraction of a history?
- Laws: closed terms judged by re-executing a machine probe (`judge_sound`/`judge_complete`),
  inheriting along a checked linearization, compiled from the surface fragment. Is "a refusal names
  the request that would pass" a contribution or a convenience?
- The generalization: is the audited fold the right organizing structure, or is it the next
  over-reach after the semiring? Which of the five modules would you refuse?
- The design phase: what would a theorem prover's author insist on before building further?
