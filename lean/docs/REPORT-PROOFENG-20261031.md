# Lane ProofEng: pin lists dropped, proofs made faster, waterfall tried (Claude Opus, 2026-10-31)

Placed by the root session from the lane's closing report. Commits `393eb2b` (step 1), `6fb22c1`,
`3e1d7c8` (step 2). Cohorts unchanged; all 73 teeth bite at the same declarations.

## Step 1: the lists are gone
Removed 420 `#assert_axioms` commands across 131 files and 10 `#print axioms` pins of the standard
three; `AxiomPin.lean` deleted; the "pins" prose removed from the READMEs, METATHEORY and the paper.
Kept: 27 `#assert_compiled` (each re-runs a `native_decide` claim through the evaluator, which the
census cannot). Kept for Ember's call: 15 `#print axioms` pins in `MachineFast`, `Data`, `Fast` that
pin a *choice-free* set, stricter than the census.

## Step 2: speed, with the measurement
Two clean builds back to back under a load average of 60–100 from other sessions: total CPU 667 s to
410 s, wall 461 s to 321 s. The `respectTransparency` debt from the 4.35 bump is retired:
`equirec_reduce` no longer needs the option and it is gone from the tree.

| module | before s | after s | what |
|---|---:|---:|---|
| `TypingTeeth` | 53 | 4.8 | `#tooth` graph walk: skip earlier modules, compiled `getUsedConstantsAsSet` (6.5 s to 78 ms) |
| `LawCompileTeeth` | 51 | 5.9 | same |
| `CheckTeeth` | 43 | 14 | `decide +kernel` first |
| `Substitution` | 30 | 21 | tooth fix, shared equation lemma |
| `CheckCompletenessObstruction` | 24 | 3.0 | `cases` instead of `trivial` (which runs `contradiction`, 150 ms a goal) |
| `Adequacy` | 24 | 11 | `primitiveResult_value` 4.9 s to 0.07 s |
| `Invariant` | 21 | 15 | unchanged (load noise) |
| `Templates` | 10 | 9.3 | shared equation lemma |

Heuristics worth keeping: profile with `-DElab.async=false` (async traces charge waiting time to
the waiter); interpreted `meta` code in a module is slow per node; equation lemmas are regenerated in
every importer, so prove one genuine lemma by `eq_def` in the defining module (`elaborate_refuses_hole`,
`infer_zero`); `decide +kernel` beats `simp` evaluation for closed checker runs except through
well-founded recursion; split on the definition's own match rather than a product of `cases`; state
membership proofs over the folded structure, not an unfolded node list (`root_mem_presentation`,
`mem_mirrorSupport`).

## Step 3: waterfall, not worth it
v0.2.0 does not build at 4.35 as published (one API change in `Leaf.lean`, a one-line patch). Plain
`waterfall` proved 11 of 52 candidates, every one slower (0.06–3 s against 0.003–0.04 s);
`waterfall?` expansions were often shorter (11→1, 16→3, 10→5 lines) but still slower and some cite
auxiliary `match_1` constants. Failures: Traverse's nested `Tree` with its custom `inductionOn`, the
Forcing simulation lemmas, the Collect lemmas. No rewrite met "shorter and not slower"; none kept,
nothing added to the dependencies.

## Next, in the lane's judgment
1. Make the type-graph worklist kernel-evaluable (structural or fuel-bounded), so `decide +kernel`
   covers every checker tooth and `equirec_reduce` can be deleted outright: the largest simplification
   on offer.
2. `stepRaw_lexicalInvariant` as one lemma per transition (64 goals × 0.12 s of `grind` in an early
   module much of the tree waits on).
3. The 15 choice-free pins.
