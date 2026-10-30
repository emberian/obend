# Report: `Obend.Law` (lane Law, Claude Opus, 2026-10-30)

Placed by the root session from the lane's own closing report; the harness refused the lane the
write of this file. Commits `4340797..b347578` on `dev`; full `lake build` green at 121 jobs.

## What landed

| commit | module(s) |
|---|---|
| `4340797` | `Obend/Law/Syntax.lean`: `occasionTy`, `verdictTy`, `reqTy`, `lawTy S`, the `At` cursor, the combinators, the six-arm skeleton, `Admits`/`Refuses` over `Evaluates` |
| `cd27755` | `Obend/Law/Std.lean`: the generators `ownerSigns`, `allowlist`, `bounded`, `machine`, `quorum`, `windowed` |
| `c44bafb` | `Run.lean` (a certified one-step function, used for teeth), `Proofs/Run`, `Proofs/Eval`, `Proofs/Std` |
| `f6bfba3` | `Claim.lean`, `Proofs/Claim.lean`: `keeps`, the certifying-shape checker, `guardedBy_sound`, `chain_keeps` |
| `14fdc42` | `Inherit.lean`, `Proofs/Inherit.lean`, `Obend/Law.lean`, one line in `Obend.lean` |
| `b347578` | visibility by the tree's public/private rule; every theorem pinned |

167 theorems under `Obend/Law/Proofs/*`, all pinned by `#assert_axioms` to the standard three; no
`sorry`, no `axiom`, no `native_decide`. The `hole` constructor landed on `Term` (`fa669fe`) while
the lane ran; no Law file needed an edit.

## Fully proved

- Combinators and skeleton: `guard_ok`, `guards_ok`, `allOf_ok`, `anyOf_true`, `andT_true`,
  `notT_true`/`notT_false`, the comparison inversions, `eqAt_true`, `lawCase6_arm` and one lemma per occasion.
- Generators: `ownerSigns_spec`, `allowlist_spec`, `bounded_spec`; `machine_birth`, `machine_adopt`,
  `machine_invoke`, `machine_{write,relaw,retire}_refused`; `quorum_birth_empty`, `quorum_adopt_fresh`,
  `quorum_retire_refused`, `quorum_relaw_needs_k`, `quorum_change_needs_k`; `windowed_lands_in_epoch`,
  `windowed_fresh`, `windowed_limit`.
- Claims: `guardedBy_sound`, `keeps_step`, `chain_keeps`, `keeps_guarded`, `checkClaim_keeps`, `claim_chain_keeps`.
- Inheritance: `effective_law_eval` (for closed laws, the effective law admits exactly when every law
  on the list admits), `inherited_never_widens`, `inherited_refusal_kept`, `effective_refusal_names`
  (a refusal names the first refusing ancestor and every law before it admitted), its converse
  `effective_refuses_first`, `effectiveVia_eval` (the same through C4 linearization).
- Reference step: `step_iff`, `step_deterministic`, `run_sound`, `evaluates_unique`,
  `applyLaw_steps`, `admits_iff`, `refuses_not_admits`.

Teeth: every hypothesis that could be vacuous has one (`ownerSigns`, `allowlist`, `bounded`,
`machine`, `quorum` with nine runs, `windowed`, `keeps`, `inherit`, `c4`), each `decide +kernel` on a
concrete run read back through `run_sound`, each pairing an admission with a refusal naming its reason.

## Decisions

- **Semantics.** Meaning theorems are over Core4's substitution-based small-step `Evaluates`, not
  nano's big-step environments; none needs the data closed. *Critique:* this is the tree's reference
  and keeps Law free of the machine, at the price that nothing yet connects the machine to `Admits`
  (adequacy covers ground values only, and a verdict is not one). *Meta-critique:* the honest
  statement of what a kernel runs is still owed.
- **Deviations from nano.** `reqTy` not `reqTy S` (the request does not depend on the state type);
  ids, members and refusal reasons are labels (Core4 has no bytes); equality is typed through
  `eqAt`; no packages, so `pkgOf`, `methodOf`, `stepTo` are not ported.
- **Inherited verdicts (the decision for Ember).** Core4 cannot join two labels into one, so the
  effective law has its own verdict type `inheritedVerdictTy` with `refused : {by : label, reason :
  label}`; that is what makes "the refusal names the ancestor" a fact about the value a kernel sees.
  Cost: an effective law is not a `verdictTy` law, so a kernel judging by effective laws must accept
  the richer verdict. Alternatives: keep `verdictTy` and pass the reason unnamed, with the naming
  living only in the Lean theorem; or add a label-concatenation primitive to Core4, a Core change
  touching every `Primitive` case.
- **Visibility.** 102 of 167 theorems public: cited by another module, `@[simp]`, the headline
  results, and the combinator toolkit (a judgment, not a token scan).

## Not done

- No theorem that the generated laws type-check at `lawTy S` (Core4 lambdas carry no annotations;
  the type is documentation for now).
- No theorem connecting the machine to `Admits`.
- `c3_tree_is_chain` not stated (C4's `linearize` has no theorems to build on yet).
- Compiling the `.obend` law fragment (`Obend.Spec.Law`) down to Law terms: the natural next step.
