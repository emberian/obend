# Gemini's second review (checkpoint-20261101b), pasted by Ember 2026-11-01

Full text held in the conversation; this file records what it found and what was done with it.

1. **Program logic (`review/PROGRAM-LOGIC-20261101.md`): a soundness bug in the judgment/regime
   bridge.** `Holds c d := Evaluates (c d) true` is total; the rewrite regime proves `lhs ≈b rhs`, a
   Kleene equivalence. If `review` diverges, `rewriteCheck` accepts `repeated` with supports `{twice}`
   while `Holds` is false (`binary equal` must evaluate both sides). Fix taken (option A): the equation
   judgment is partial, `HoldsEq lhs rhs d := ∀ o, Halts (lhs d) o ↔ Halts (rhs d) o`, which rewrite
   proves with that footprint; ground and Lean certificates prove total convergence; the receipt names
   which. Four elaborator mismatches: `composeStep` wraps each step in two beta redexes (simplify the
   elaborator to emit `specification m (mix l u)` directly); layers over recursive record types emit a
   flat delegating `record`, not `extend` (T1 must cover both shapes); T1's de Bruijn order needs a
   parallel substitution or closedness of `superAt`; `claim_frame` must not equate raw list indices,
   needs `late_binding_prefix` for `super.p`, and must substitute the `$globals` knot before replay.
   `==` on `Bool` elaborates to a beta-redex, so the recognizer matches three shapes. T2 must state
   `BEquivAt .b` under an observer-free substitution when `composeAssoc` is used.
2. **A CV derivation as a cost upper-bound certificate: correct** (H&H Thm 4.1(ii)), given a computable
   `readyB` for the negative premises.
3. **World analysis and Experiment 1, kernel-verified.** Monotone core proved (`usable`, `fillable`,
   fixed-incumbent retention, every policy-independent invariant); selected-candidate monotonicity
   refuted for first-usable and for incumbent-first from `none`; incumbent-first idempotent at a fixed
   store but path-dependent across stores, so not a closure operator. The invariants are the exact
   monotone envelope; policies are history-dependent choice functions inside it. The support-set
   generalization is sound only as the induced *domain* of admissible pins per cell (non-emptiness
   catches contradictory constraints; Kleene membership is incomplete for same-cell entailment);
   entailment decidable for finite pins, equality/retirement constraints, Presburger version facts;
   undecidable for unconstrained Core4 laws.
4. **Experiment 2, kernel-verified.** Iterated approximants give `{a = 7, b = self.a}.b` a derivation
   at cost 16; the approximant chain is monotone and stabilizes; `Within` factor 8 preserved; all
   three measured programs agree with the machine. Divergence: naive re-running of `selfBody`
   over-charges shared work outside the record by the dependency depth; the exact construction is
   two-stage (settle the template once with `self` free, then iterate field waves), which is Xia et
   al. ICFP 2024's demand semantics extended to knots. Contract C4 decided on this evidence.
5. **Sound, Expose, Parsimony closures audited: no new holes.**
6. **Run-length linear conservation without heap counts:** source-level subject reduction is cheap
   (~150 lines in `Conservation.lean`): custody is parametric, every `Step` rule but `primitive` is
   call-by-name, and every usage constraint is exact-one, at-most-one or zero, each already
   preserved by `step_conserves_linear` and the substitution lemma; `TypedChain` is then discharged.
