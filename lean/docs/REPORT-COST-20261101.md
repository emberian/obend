# Report: `≈c`, ticks against clairvoyant cost, the improvement judge (lane Cost, Claude Opus, 2026-11-01)

Brief: `lean/docs/LANE-COST-BRIEF-20261101.md`. Start measurement build: 251 jobs, 95 s; the census
(31184 constants, 27 on the compiler trust) failed only on this lane's first new file not yet
imported. End: see the last section. Every new file is a `module`; no `sorry`, no axiom, no
`native_decide`.

## What landed

**1. Yields under `Ahead`; `≈b` over `Interaction` traces** (`Obend/Equiv/Yields.lean`, EQUIV-PLAN
lane 1). `yields_behind` (a term ahead of a yielding term yields at once, with a related plan and a
related context, frames pointwise `Ahead`) and `yields_ahead` (a term behind reaches a related yield
by reduction). `interaction_ahead_of_behind` / `interaction_behind_of_ahead` transfer every turn of
an `Interaction`, responses equal and plans `Ahead`-related. `IEquiv`: under every substitution and
context the same traces (same responses, `≈b` plans, same final observation or convergence);
`refl`/`symm`/`trans`, `iequiv_of_ahead`, `IEquiv.bequiv` (the trace with no turns),
`mix_assoc_interaction`. Tooth: `perform_plans_distinguished` (two programs differing only in the
plan they yield are not `IEquiv`).

**2. Clairvoyant call-by-value for Core4, `≈c`, `mix_assoc_cost`, Faré costed.**

`Obend/Equiv/Clairvoyant.lean`: one relation `Run : Mode → Term → Term → Nat → Prop` (evaluation,
one binding, a field list). Every binding site has Let′ (evaluate first, +1) and Skip (cost 1,
leaving `skipped`, which has no derivation); a binding keeps a term already settled (cost 0). The
sites: β arguments, record and extension fields, specification and prototype components, an
injection's payload (which `case` binds), the `self` of `fix`, and `super` in `mixBody` (a β
argument). `fix s i` is H&H's recursive `let`: its body is evaluated with `self` the open index 0 (a
pointer that may be passed, never entered), and the value `V` is tied by a `knot` (Let′) or
`skipped` (Skip). A knot, `fix (λλ V) {}` with `V` a value, is entered at cost 3 (`knot_unfold`),
the source analogue of `Var′`. `CValue` is the weak-head value whose lazy parts are settled;
`Settled` adds knots, pointers and `skipped`. `run_produced`, `cv_of_value` (a value evaluates only
to itself at cost 0), `hoist_arg`/`hoist_fun` and `unhoist_arg`/`unhoist_fun` (when an argument is
bound does not change its cost), `cv_mix_app_app`.

`Obend/Equiv/Improvement.lean`: `Sim`, congruence plus the two associations (`assocLR`, `assocRL`)
and their bodies applied to a settled `self` and any `super` (`bodyLR`, `bodyRL`). Closed under
renaming, under settled substitution (`Sim.subst`), and any substitution into a context
(`Sim.substRefl`); preserves `Ready` both ways (`Sim.ready_iff`).

`Obend/Equiv/Cost.lean`: **`sim_cv`**: a derivation of cost `k` on one side is matched on the other
by one of cost `k' ≤ 8k` (and `k' + 7 ≤ 8k` when `k > 0`), with related results. The two association
cases (`bodyLR_case`, `bodyRL_case`) are the work: one body binds `self` three times, the other twice;
each binding is hoisted, matched and moved back. `CostWithin A t t'` is Moran–Sands Def. 4.1 for
clairvoyant cost (every `ρ`, every context `C`: a cost-`k` derivation of `C[tρ]` gives one of
`C[t'ρ]` of cost `≤ A·k`, same literal result); `t ≈c t'` is `∃ A`, both ways. **`mix_assoc_cost a b
c`**: `CostWithin 8` in both directions; `mix_assoc_cequiv`.

`Obend/Equiv/CostTests.lean`: `keep_cost` (`keep(7, y)` costs 3 for every `y`, `loop` included);
`good_cost` (`{good = 7, bad = self.bad}.good` costs 8); `bad_field_no_cv` (`.bad` has no
derivation, as need blackholes it); `self_field_no_cv` and `self_field_evaluates` (the decision
below); `assoc_left_runs`/`assoc_right_runs` (`mix_assoc_cost`'s hypothesis is inhabited: the left
runs at 6, so the right runs within 48). Tier-2 tooth `Obend/Teeth/Equiv/CostTeeth.lean`: mutating
the self-reading field into a constant rejects the stored proof of `self_field_no_cv`.

**3. Ticks against clairvoyant cost** (`Obend/Core/Proofs/TickCost.lean`). Not proved, because it
is false as posed (the decision). **`ticks_not_within_cv`**: for no constants `c d` does every
finished machine run of `T` ticks have a derivation of cost `≤ c·T + d`. The witness:
`self_field_machine`, the machine finishes `{a = 7, b = self.a}.b` with 7 in 25 ticks (not in 24),
and it has no clairvoyant derivation. Where they agree, measured exactly on the real `runBounded` by
`simp`: `good_machine` (`.good` in 16 ticks, cost 8), `bad_machine` (`.bad` at the blackhole in 21
ticks), `fare_agreement`. These are EQUIV-PLAN's probe numbers, now theorems.

**4. The improvement judge** (`Obend/Judge/Cost.lean`). `instance improvement : Judge (Term × Term)
(List Step) Nat`. A certificate is a cost derivation: steps, each re-associating one `mix` in a
context, either way round. `check` runs the steps from the original and accepts when it reaches the
candidate; the grade bounds the derivation's length. `Meaning` is `CostWithin (8 ^ n)` both ways;
**`charge_bound`** is the brief's "a member's charge difference is a theorem". `CostWithin.trans`
(factors multiply), `CostWithin.context`, `termBeq_sound` (term equality decided through the
traversal encoding; `Term` has no `DecidableEq`). `refutes` is constantly false: a rejected
derivation says nothing about the pair. Checked: a two-step certificate accepted
(`twoSteps_accepted`, so `original_candidate` within 64 both ways); a planted wrong-way step refused
`stepMismatch`.

## Decisions, with critique

- **`≈c` is a factor, not an additive constant.** EQUIV-PLAN wrote `k + κ`; that is false in
  context (a context that applies the association `n` times pays the per-application difference `n`
  times). Moran–Sands Def. 4.1 is a factor, and it is what is proved. Critique: 8 is the proof's
  constant, not the semantics'; the real gap per application is a few rules. A sharper proof would
  carry `k' ≤ k + κ·(applications)`; the factor is the honest statement of what `sim_cv` gives.
- **A binding keeps what is settled; Let′ only evaluates what is not.** A knot is kept and entered
  only where demanded, as need enters a cell. With Let′ on knots, a `self` bound once on one side and
  twice on the other could not be matched within any constant. Forbidding re-binding of values
  (`¬ CValue` premises on the construction rules) makes a value evaluate only to itself, which is
  what lets `Sim` preserve settledness both ways with no "less defined" ordering.
- **`self` is open during its own body.** That is H&H's Let′, and the decision below.
- **Which relation each theorem refines** (Quote-1's note): `IEquiv` and `CostWithin` quantify over
  every context like `BEquiv`, so they refine `BEquiv` (Quote's ≈r, `metadata` observers included).
  Stated at that strength they imply their `Observed .b` forms; I did not restate them over census-b
  contexts (a one-lemma follow-up once the rename lands).
- **The judge's certificate plugs capture-avoidingly**: a step rewrites under a binder only an
  association whose parts do not mention it. `mix_assoc_cost` holds in every context; the restriction
  is the certificate language's. A congruence-tree certificate (a checked `Sim` derivation) would
  lift it, at about 24 cases of checker soundness.
- **Meta-critique.** The first hour went to designing the semantics before writing it. That paid:
  the dead ends (by-name `self`, the knot table, Let′ on knots, the "less defined" relation) were
  found on paper, and `Cost.lean` compiled at its first full build. What I under-weighted was (3):
  the brief reads as "prove it", and the lane's most important output is that it cannot be proved for
  this semantics.

## Not done, said plainly

- No positive tick bound. The CV→machine direction (a cost-`k` derivation bounds the ticks of a
  finished run) needs source-to-machine completeness, which `Adequacy` leaves open; machine→CV is
  refuted.
- H&H Thm 4.1 is not mechanized: it is false for recursive `let` with self-reading lazy fields
  (below); the fix-free fragment, where it should hold, is not attempted.
- Heap cells and stack depth are not priced (`Limits.heap`), as EQUIV-PLAN said of definition 2.
- The judge is not a `Format` (no byte decoder, not in `registry`).

## The one decision for Ember

**Hackett–Hutton's clairvoyant semantics is not call-by-need for `fix` with lazy fields that read
`self`.** `{a = 7, b = self.a}.b` is 7 by reduction and in 25 machine ticks, and it has no
clairvoyant derivation (`self_field_no_cv`): Let′ at a recursive binding evaluates the body before
`self` is bound, while need forces `b` only after `self` is updated, so a clairvoyant run must
evaluate `b` early (stuck) or skip it (missing). That is the shape of every Core4 object (`fix` of
extensions whose fields read `self`), and it is a gap in H&H's own proof of Thm 4.1(i) (the "splice
the subproof into Let′" step moves a self-reading thunk before the update). Which repair does `≈c`
get?

- **(a) A by-name binding**: complete, but it overcounts a self-reading field demanded `n` times by a
  factor of `n`, unboundedly.
- **(b) A clairvoyant cell table**: the clairvoyant heap chosen up front, each cell with its value
  and a rank, a cell's derivation reading only lower-ranked cells (the forcing order). Faithful to
  need; definition 3's heap in clairvoyant form.
- **(c) Keep H&H as is**, and `≈c` says nothing about any program that reads a lazy self-field, that
  is, about objects.

`mix_assoc_cost`, the Faré costs and the judge do not depend on the choice: `Sim` is the relation,
and `sim_cv` should carry over to (b) at the knot cases. I recommend (b).

## End measurement and control

After rebasing onto `dev` (Linear, Quote-1, Runner-2, the build tiers):
- `lake build` (tier 1): 284 jobs, 109 s, green.
- `lake build Obend.Census Teeth` (tier 2): 305 jobs, 35 s, green.
- `#assert_axioms_tree`: 34657 package constants, 27 on the compiler trust as before, none on
  `sorryAx` or a declared axiom.

Controls, run with `lake build obend` first (the worktree's `.lake` came with a stale executable):
- Mini's cohorts (`python3 tests/run-obend-source.py`): probes 30/30, tutorial 71/71, preview cohort
  161 items with 0 failures.
- Receipts (`python3 tests/run-receipts.py`): 22/22.
