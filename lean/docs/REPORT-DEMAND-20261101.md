# Report: the demand semantics for knots, ticks within a constant (lane Demand, C4, Claude Opus, 2026-11-01)

Brief: `lean/docs/LANE-DEMAND-BRIEF-20261101.md`. Every file a `module`; no `sorry`, no axiom, no
`native_decide`; the census is the axiom check. Tier 1 green on the Mac (pre-push hook, 294 jobs);
tier 2 on hbox green (318 jobs; census 38220 package constants, 27 on the compiler trust as before, none on `sorryAx` or a declared axiom).

## What landed

**1. The two-stage rule** (`Obend/Equiv/Clairvoyant.lean`). `fixLet`/`fixSkip` are gone; `fix` is
`Run .head (selfBody s i) T k₁ → Run .knot (.app T skipped) V k₂ → CV (.fix s i) V (k₁+k₂+1)`.
- *Template* (`Mode.head`): evaluation with `self` the open index 0 that leaves the head record's
  fields unbound (`headRecord`, `headExtend`, `headEval`), so work outside the record (β arguments)
  is paid once. The tail rules (`apply`, `applySpec`, `get`, `case`, the conditionals, `reflect`,
  `metadata`, `project`, `done`) are shared by both tail modes (`Mode.tail : Tail → Mode`, with
  `Mode.eval`/`Mode.head` as match patterns), so one rule set serves evaluation and settling.
- *Waves* (`Mode.cell`, `Mode.wave`, `Mode.knot`): `V₀ = skipped` (`knotFirst`, previous fields
  `pending`, Xia's ⊥ of a record), then `V_{m+1}` from the template's fields read against `V_m`
  (`knotWave`). Per field: settled after substitution → taken (`cellValue`, 0); evaluated before →
  kept (`cellKeep`, 0); not yet → waits (`cellWait`, 0) or is evaluated (`cellEval`, Let′, cost+1).
  A value template (a recursive function) unrolls at no cost (`knotUnroll`); the waves stop at a
  value (`knotDone`).
- **Departure from the brief's formula, and why**: the brief wrote `V_{m+1} ← Run .fields
  (V.substitute (single V_m))`. Re-binding every field each wave re-pays every field per wave (the
  same over-charge by dependency depth that `fixApprox` has, moved from the template to the
  fields), and charging only the last wave is unsound (a lambda field reads an earlier approximant
  whose evaluated data the last wave may skip: `{a = expensive, f = λx. self.a}.f 0` would never
  pay `expensive`). The cell rules make each field paid once, in the wave where it is first
  evaluated, and keep it after: that is need's cell, with the wave number as its rank.

**2. Faré, `mix_assoc_cost`, `Within`.** `sim_cv` re-proved for both tail modes (`SimBelow` over
`Tail`; `knot_sim`, `wave_sim`, `cell_sim`, `sim_skipped_left/right`, `Within.add`);
`mix_assoc_cost` (factor 8 both ways) and `Within` unchanged. CostTests: **`self_field_cost`**
(`{a = 7, b = self.a}.b` costs 7: template 3, `b` in the second wave 2, knot 1, selection 1)
replaces `self_field_no_cv`; `good_cost` is now 5 (was 8); `bad_field_no_cv` re-proved through
`selfObject_loop_no_cv` (a field reading itself stays `skipped` in every wave, any template);
`keep_cost`, `self_field_evaluates`, `assoc_left_runs`/`assoc_right_runs` unchanged;
`knot_unfold` kept at cost 3 (result now `V[skipped]`), plus `knot_unfold_twice`. Tier-2 teeth
(`Teeth/Equiv/CostTeeth.lean`): mutating `selfLam` so `bad` is constant rejects `bad_field_no_cv`;
so `b` reads itself rejects `self_field_cost`.

**3. The demand semantics, Xia Thms 3.8/3.9 shape** (`Obend/Equiv/Demand.lean`), on the object
fragment: `obj fs = fix (λself.λsuper. {nᵢ = eᵢ}) {}` with `eᵢ` a literal or `self.m`, distinct
names. `demand fs x` is a total, computable function (follow the chase to a literal; `headCost +
2·links + 2`). **`demand_exists`** (a derivation of exactly that cost, with that value),
**`demand_minimal`** (every derivation has a defined demand, the same value, and costs at least it:
minimality with totality), **`demand_is_least`** (iff). The proof reads any derivation:
`head_template` (every template settling costs ≥ `headCost`, three template shapes), `knot_invariant`
= `knot_inv`/`wave_inv`/`cell_inv` (each evaluated selection paid 2 once, kept after, its value the
chase's, the evaluated set closed under reading), `chase_walk_injective`/`chase_short` (a successful
chase visits distinct fields, so the fuel `|fs|` suffices). `measured_least`: `.good` least 5, `.b`
least 7, `.bad` no derivation.

**4. Ticks** (`Core/Proofs/TickCost.lean`). `ticks_not_within_cv` retired (its witness now has a
derivation: `self_field_within`). **`measured_within`**: each measured program's ticks are ≥ its
least demand cost and ≤ 4× it (`.good` 5/16, `.b` 7/25), `.bad` none/blackhole at 21; `measured_agree`
records the derivations. `TicksWithinDemand c d` states the general bound; it is **not proved**:
`Completeness` proves finite completion by a lexicographic descent on source cost and a stutter
rank, with no tick count per source step and no relation between heap cells and approximants. The
missing piece is a cost-indexed `GraphRepresentsBy`: a machine heap cell that is updated ↔ the
approximant entry it holds, a suspended cell ↔ `skipped`, with ticks per source reduction bounded
by a constant (the stutter rank bounded by the demand cost). I did not prove the bound on the
fragment either: it needs the same machine-side analysis over arbitrary field lists.

**5. The judges** (`Judge/Cost.lean`).
- *Improvement*: certificates are rounds; a `Round` is a context whose holes `0…n-1` are each
  re-associated, all at once. `Round.sound`: **flat 8 per round** however many associations, by
  `Sim.substRefl` (no decision procedure needed). Meaning is directional, `Improves (8^rounds)
  original candidate`. `pair_flat`: two independent re-associations in one round, factor 8 (two
  sequential steps gave 64). `charge_bound` kept with the new meaning; `Step`, `runSteps_sound`
  (the symmetric sequential lemma), `original_candidate`, `twoSteps_accepted` (now `runSteps … =
  some candidate`), `badSteps_refused` (now `= none`) kept; `twoRounds_accepted`, `original_improves`,
  `badRound_refused` added.
- *Cost*: `instance cost : Judge (Term × Nat) DemandCert`: the certificate names the object's
  fields and the field; the checker runs `demand` (total, so no `readyB` is needed on this
  fragment); `ok` means `CostAtMost t k`; `noDemand` and `overBudget` **refute** (by minimality);
  complete on the fragment. `selfField_cost_checked`: ≤ 7 accepted, ≤ 6 refuted. A general
  derivation checker for all of Core4 (Gemini §1.5's `readyB`) is not built.

**6. `claim within(...)` in the surface: not landed.** (4) is clean on the fragment and for
re-association, but a surface claim would want the cost judge beyond the object fragment; I leave
it for the Logic lane.

**`RunA`/`fixApprox` retired.** Gemini's `Approximant.lean` (placed uncommitted by the root) no
longer builds once `fixLet` leaves `Run` (`toRunA`); the two-stage rule supersedes it, and
`within_fixApprox` is arithmetic that `Within.add` covers. Kept outside the tree at the lane's
scratchpad. The over-charge as a *theorem about RunA* (every `RunA` derivation of a program with
shared work outside the record pays it per pass) is not proved; the tooth that is proved is the
other side: `demand_minimal` pins the least cost, and the mutation teeth bite.

## Limits, said plainly

- **`super` loses self-reading fields.** The template stage binds a β argument with the ordinary
  rules, so the inner layer of `mix l u` (`l self super`, a β argument to `u`) is evaluated with
  `self` open and its self-reading fields are skipped. Objects whose self-reading fields come
  through `super` have no derivation; the measured programs and the fragment are single-layer.
  Lifting this needs a head-mode binding that leaves a raw record, which `Sim.subst` (settled
  substitutions only, because `bodyLR` shares `self`) does not admit.
- The fragment has literals and selections only; primitives over fields (a DAG of reads, not a
  chain) need the evaluated set as a closure and a sum, not a path.

## The one decision for Ember

**How should `super` carry a layer's self-reading fields?** Today `mix` objects lose the inner
layer's `self.x` fields at the template stage. Either (a) the template stage gets a head-mode
binding that passes a raw record as `super` (complete for layered objects; `Sim`'s settledness
discipline must be generalized to "settled or a raw template under the current knot", reworking
`bodyLR`/`bodyRL`), or (b) the elaborator flattens layers into one head `extend` chain before
`fix` (no semantic change; layered objects become single-layer), or (c) `≈c` and the cost judge
stay silent on layered objects. I recommend (b) if the elaborator can emit it, else (a).

## Follow-up (2), after the coordinator's decision on `super`

**Layered objects, through their flattening** (`Obend/Judge/LayeredCost.lean`). `LayeredCost C m k`:
the flattening's member costs at most `k` (a clairvoyant derivation exists) and is `≈b` the object's
(`flatten_sound`). The judge `layeredCost` takes a demand run of `C.flatten` as the certificate;
`layered_refuted` (a demand above `k`, or none, refutes); complete where the flattening is in the
object fragment. `layered_b`: `fix (compose {b = self.a, c = super.a} {a = 7}) {}` flattens to
`{b = self.a, c = 7, a = 7}` (`layered_flatten`, by kernel computation) and `.b` is costed at 7.
No `Sim` rule and no elaborator change were needed. What this does not claim, plainly: a clairvoyant
derivation of `C.object` itself (the rule still has none for an inner layer's `self` reads), nor
that `≈b` preserves cost. The cost is the compiled program's, and the compilation is proved
observationally faithful. "`≈c` respects `≈b`" is not a fact of this development: `≈c` is proved
of `Sim`-related terms, and an object and its flattening are not `Sim`-related.

**The fragment tick bound: not proved.** What it needs is a symbolic machine trace over arbitrary
field lists, which I worked out but did not mechanize. For `get (obj fs) x` with `fs` distinct
and `|fs| ≤ 40` (so the fixed limits `⟨100, 100⟩` are never hit):
- 12 transitions take the machine to `enter (3 + i_x)`: `get`, `fix` (cell 0), the two β steps
  (cells 1 = `self`'s argument `bound 0`, 2 = `super`), the record (`allocateFields`: cells
  `3 … 2+|fs|`, suspended `eᵢ.at (bound 1)` in `[2, 1, 0]`), the update of cell 0, the selection.
- Forcing a field along a chase of `d` selections takes `t ≤ 3 + 6d + 3` transitions: a literal is
  3 (enter, value, update); each selection is 6 (`get`, `bound 1`, enter cell 1, selection, enter,
  update), plus 3 the first time cell 1 is forced. A cached cell costs 1.
- One more transition completes. So `T = 13 + t ≤ 22 + 6d`, against the least demand
  `headCost + 2d + 2`. The constant is 4: `T ≤ 4·k` for `d = 0` (16 ≤ 16 or 20) and for `d ≥ 1`
  (22 + 6d ≤ 8d + 20). The measured programs sit exactly on it: 16 at cost 5, 25 at cost 7.

The proof needs:
1. `runBounded (n + j) s = runBounded j s'` along `n` active transitions within limits.
2. `allocateFields` as an append, with addresses `3 + i`.
3. A heap invariant: cell 0 is the cached record; cell 1 is suspended or cached at it; each field
   cell is suspended, evaluating exactly when its name is an ancestor on the forcing stack, or
   cached at its chase value.
4. A forcing lemma by induction on the chase. Its ancestors are disjoint from its path by
   `chase_walk_injective`.

A cycle or a missing field has no demand run (`demand_minimal`), so `TicksWithinDemand` is vacuous
there.

For the general statement, `Completeness` would need to provide a cost-indexed
`GraphRepresentsBy`. Each raw transition is a source reduction or a stutter (as now), and the
stutters between two reductions are bounded by a constant. Under it, a heap cell's state
corresponds to the wave approximant's entry: suspended to `skipped`, cached to the value. The
present proof measures termination by a lexicographic descent with an unbounded stutter rank,
which gives completion but no tick count.
