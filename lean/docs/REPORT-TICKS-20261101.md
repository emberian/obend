# Report: the fragment tick bound, mechanized (lane Ticks, Claude Opus, 2026-11-01)

Brief: `lean/docs/LANE-TICKS-BRIEF-20261101.md`. Every file a `module`; no `sorry`, no axiom, no
`native_decide`. Built on hbox in its own worktree (`~/obend/ticks`, so the shared `~/obend/repo` was
not switched under the other lanes): `lake build Obend Obend.Census Teeth` green, 331 jobs; census
39053 package constants, 27 on the compiler trust as before, none on `sorryAx` or a declared axiom.

## What landed

**1. The trace** (`Obend/Core/Proofs/TickTrace.lean`, new). The machine's run on `get (obj fs) x`,
symbolic in the field list, through the four lemmas the Demand report named:
- `Trace L s n s'` (n active transitions within the limits) and **`runBounded_trace`**:
  `runBounded L (n + j) s = runBounded L j s'`; `runBounded_complete`, `runBounded_short` (fewer
  ticks than the trace leave the run suspended), `Trace.trans`.
- **`allocateFields_toArray`**: allocation is an append; the fields' addresses are `|heap| + i`.
- **`prefix_trace`**: twelve transitions take `initial (get (obj fs) x)` to the template heap
  (`templateHeap`: the knot cached at the record, `self` and `super` suspended, every field
  suspended) entering the selected cell `3 + pos fs x`.
- **`force_trace`**, the forcing lemma by induction on the chase, with the heap invariant as its
  hypotheses and conclusions: from a field whose chase reaches `u` in `d` selections, the machine
  returns `u` in `3 + 6d` transitions, plus 3 when `self`'s cell is first forced; every cell on the
  path ends cached at `u`, `self`'s cell cached, every other cell untouched. The path's cells are
  distinct by `chase_walk_injective` (and `pos_inj`), so a cell is never re-entered while forcing.
- **`fragment_run`**: exactly `fragmentTicks d` (16 for a literal, `19 + 6d` for `d ≥ 1`) ticks to
  finish, with the chase's value; fewer leave it running. The hand trace's `≤ 22 + 6d` was loose by 3.

**2. The bound** (`Obend/Core/Proofs/TickCost.lean`).
- `TicksWithinDemandOn P c d`; `TicksWithinDemand c d` is now its instance at `P = True` (same
  statement as before). `InFragment`: `get (obj fs) x` with distinct names and `|fs| ≤ 97` (the
  limits `⟨100, 100⟩`: heap `3 + |fs|`, stack at most `d + 3`).
- `fragment_ticks`: `headCost + 2d + 2 ≤ fragmentTicks d ≤ 4 · (headCost + 2d + 2)`.
  `fragment_machine`: the machine finishes with the demand's value at exactly `fragmentTicks d`.
- **`ticks_within_fragment : TicksWithinDemandOn InFragment 4 0`**, proved through the ledger below.
- `measured_within` (statement unchanged) is now an instance: `good_machine` and
  `self_field_machine` are proved from `fragment_machine` (no kernel unrolling), and their `≤ 4·k`
  parts come from `ticks_within_fragment`. `bad_machine` stays a computation (no demand run, so no
  trace to instantiate). `self_field_within` kept.

**3. The general bound's precondition, as a structure** (`TickCost`, same file).
- `CellFor cell entry`: a suspended or forcing cell stands for `skipped`; a suspended literal for its
  value (the knot settles a literal at no cost; the machine forces it on demand, 3 transitions, which
  is why the accounting is per segment and not per transition); a cached cell for its value.
  `HeapFor heap cells wave`: the `i`-th named cell stands for the `i`-th entry.
- `Ledger L c cells Approximant s T K`: the run from `s` cut into segments, each at most `c`
  transitions per clairvoyant unit charged to it (the stutters per source reduction bounded), each
  ending where the heap stands for an approximant.
- **`CostIndexedRun L c t`**: the cost charged (a real derivation's, `charged_real`, and no derivation
  cheaper, `charged_least`), the knot's cells, its approximants, and a ledger from `initial t`.
- **`ticks_within_of_runs`**: ledgers for every finishing program in `P` give
  `TicksWithinDemandOn P c 0`. **`fragment_cost_indexed`**: the fragment has one at `c = 4`, two
  segments: the template (12 transitions, charged 3) ending where the heap stands for the first wave
  (`heapFor_template`: `approxL [] fs`), and the chase plus completion (charged the rest) ending where
  it stands for the last (`heapFor_final`: `approxL κ fs`, `κ` the chase's fields at its value,
  `Good` by `chase_suffix`). `ticks_within_fragment` is proved from these two.
- **Not proved, and named**: `CostIndexedCompleteness c` (every program the machine finishes, with a
  derivation, has a `CostIndexedRun` at `c`); `ticks_within_of_completeness` turns it into
  `TicksWithinDemand c 0`. It is not within reach: it needs `Core/Proofs/Completeness`'s simulation
  (`machine_simulation`) re-proved with (i) the stutter branch bounded by a constant per source
  reduction instead of a decreasing `stutterRank`, and (ii) an `AddressMeaning` that maps each field
  cell to a wave entry rather than to the source term it denotes, so that a cache hit is charged
  nothing. The lemma that is not proved is that cost-indexed `graph_stepRaw_whole`. I did not fix
  the general `c` either: β, `get` and the primitives cost the machine different constant numbers of
  transitions per clairvoyant unit, and a literal's forcing is free in the knot.

**4. The cost judge's receipt** (`Obend/Judge/Cost.lean`). `Meaning` is now `CostMeaning o`:
`CostAtMost t k ∧ TicksAtMost t (4·k)` (the machine finishes within `4·k` ticks; `cost_sound`, via
`fragment_within`). Off the fragment (not the certificate's selection, a repeated name, more than 97
fields) the verdict is `uncovered`; the clauses `notTheProgram` and `duplicateField` are gone, and
both remaining clauses (`noDemand`, `overBudget`) refute (`cost_refuted`, the old argument).
`Fragment` gained `|fs| ≤ 97`. `selfField_cost_checked` kept; `selfField_receipt` added (cost ≤ 7,
finished within 28 ticks); `costCheck_off` states the `uncovered` side. `LayeredCost` follows (its
soundness takes the cost half; its `Fragment` gained `|fs| ≤ 97`; `layered_b_cost` unchanged).

Former theorems: all kept with their statements (`self_field_machine`, `good_machine`,
`bad_machine`, `measured_within`, `self_field_within`, `selfField_cost_checked`, `layered_*`);
`TicksWithinDemand` is the same proposition, stated through `TicksWithinDemandOn`.

## The one decision for Ember

**Should the tick bound be stated against the fixed limits `⟨100, 100⟩`?** The fragment needs
`|fs| ≤ 97` only because `runBounded` is run under `limits`; the trace itself holds under any limits
large enough (`fragment_run` takes `L`). Either (a) keep `limits` in `TicksWithinDemand` and the
judge (programs past the limits are `uncovered`, as now), or (b) restate both over the unbounded
`rawRun` (or limits as a parameter), which drops the 97 and makes `CostIndexedCompleteness` a
statement about Core4 rather than about one capacity. I recommend (b) before the general lemma is
attempted, since `Completeness` already works over `rawRun`.

## Follow-up: (b), the bound over the raw machine (coordinator's decision)

- The bound is now stated over `rawRun` (`Obend.Core.Proofs.Adequacy`), with no limits:
  `Finishes t T n`, `FirstFinish t T n` (the first completion), and `TicksWithinDemandOn P c d` over
  them. `TicksWithinDemand c d` is its instance at `P = True`.
- The limits are a parameter: `TicksWithinDemandUnder L P c d` is the old `runBounded` shape, and
  **`ticks_within_under`** proves it from the raw bound for every `L` (limits only remove programs;
  through `runBounded_finished_trace`, `rawRun_trace`, `rawRun_short`). `ticks_within_fragment_under`
  is its fragment instance.
- The cap is gone: `InFragment` is a selection from an object with distinct names, nothing more.
  The size condition is the hypothesis `FragmentFits L fs` (`3 + |fs|` cells and frames) of
  `fragment_machine`, which `measured_within` discharges for `limits = ⟨100, 100⟩`, now only the default
  the measured programs run with. `fragment_first`: the raw machine first completes at exactly
  `fragmentTicks d`.
- `CostIndexedRun c t` no longer takes limits; it carries its own (`bound`; a finite run has some).
  `CostIndexedCompleteness c` is a statement about Core4: every program the raw machine completes,
  with a derivation, has a ledger. The fragment's instance uses `fragmentLimits fs`.
- The judge: `TicksAtMost t T` is `∃ n, Finishes t T n` (the raw machine has completed within `T`);
  the 97-field check and `Fragment`'s cap are gone, in `Cost` and `LayeredCost`. `rawRun_stays` gives
  completion at every larger count.
