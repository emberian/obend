# Lane Build: tiers, splits, the kernel-evaluable type graph (Claude Opus, 2026-11-01)

Commits on `dev`: `9450dc4` (tiers), `9c2e291` (splits), `fdf6fc4` (per-transition lexical lemmas),
`cb16f6d` (kernel-evaluable worklist), and this report with `tools/measure.sh` and
`docs/MEASURE-20261101.log`. Nothing new is axiomatized, and there is no `sorry`. Cohorts: probes
30/30, tutorial 71/71, preview 161 items with 0 failures. Receipts: 22/22. The census reports none
on `sorryAx` or a declared axiom, and the same 27 compiled-trust theorems.

## 1. Two tiers
`lake build` builds the `Obend` library: every definition and proof. `lake build Obend.Census Teeth`
builds the new `Teeth` library and the census. The `Teeth` library is `Obend/Teeth/`: sixteen tooth
modules moved there with their basenames (`Core/CheckTeeth`, `EquiRecursiveTeeth`, `DataBudget`, the
six evaluation leaves, `Law/{LawJudge,Typing,Machine}Teeth`, `Spec/{LawCompileTeeth,TermWire}`,
`Vault`, `Tactic/ToothChecks`). The C4 lane has since added `Spec/C4Teeth`. Nothing in tier 1
imports tier 2.

Lake globs cannot exclude, so the `Obend` library names each top-level module and directory except
`Teeth` and `Census`. The census now also refuses a module under `Obend/` that neither tier builds. I
checked that it bites: with the `Vault` glob removed, it refused the six Vault modules by name.
`tools/hooks/pre-push` runs tier 2; the build section of the README says how to install it. After a
clean tier 1, tier 2 takes 40 s.

## 2. Splits
Each file is now an aggregator at its old module name that `public import`s its pieces. Every
declaration name is kept: 322, 80, 131 and 128 declarations, the same names in the same namespaces,
checked textually against `HEAD`.

| file | pieces | made public |
|---|---|---:|
| `Adequacy` (4,939) | `Defs` (every definition, hoisted), `Source`, `Scoped`, `Meaning`, `Graph`, `Origins`, `CasesEval`, `CasesReturn`, `CasesControl`, `StepRaw`, `Run`, `Examples`, `Reach`, `Birth`, `Safety`, `SafetyRaw`, `Progress`, `Sound` | 104 |
| `Substitution` (2,072) | `Defs`, `Uses`, `Transport`, `Mono`, `Msubst`; the three corners with their `#tooth`s go to tier 2 as `Teeth/Core/SubstitutionTeeth` | 26 |
| `Collect` (1,958) | `Mark`, `Compact`, `Rename`, `Lockstep`, `Runs`, `Extract`, `Segment`, `Typing`, `Statements` (its section headers) | 18 |
| `Preservation.Base` (1,765) | `Weaken`, `Heads`, `Values`, `Insert`, `Reusable`, `Focus` | 2 |

- **Parallel pieces.** Hoisting the definitions lets the three Adequacy `Cases*` pieces, `Run`,
  `Birth` and `Examples` build side by side. Fourteen theorems that need `graph_stepRaw` moved from
  `Run` to `Sound`, so `Run` no longer waits on the step proofs.
- **Narrowed imports.** Direct importers now import only the pieces they cite. For example,
  `Preservation.Base` needs only `Adequacy.Defs`, and `TypedSubstitution` only `Msubst`.
- **`import all`.** An `import all` of an aggregator does not expose its pieces' private parts, so
  `GroundExecution` and `TypedSubstitution` now `import all` every piece.
- **Small fixes.** One proof changed (`fillTerm_zero`): a `match` in its statement now elaborates in
  a different module from `fillTerm`'s, so `simp` met two matchers; it is now `cases … <;> simp`.
- **The tool.** `tools/split.py` does the cutting.

## 3. `stepRaw_lexicalInvariant`
It is now 39 lemmas:
- 24 `lexical_evaluate_*`, one per term constructor;
- 12 `lexical_return_*`, one per frame;
- `lexical_enter`, `lexical_return_complete` and `lexical_terminal`.

Each lemma runs the old discharge on one transition (`lexical_unfold`, `simp only` at its control and
frame, `lexical_discharge`). The theorem dispatches on the control and the top frame, and its
statement is unchanged. `lake env lean Obend/Core/Invariant.lean` took 14.1–14.3 s before and
10.0–10.9 s after (two runs each, load average 40–160).

## 4. The kernel-evaluable worklist
- **Why it was stuck.** `FiniteBisimulation.worklist` recursed on a lexicographic pair, and
  `WellFounded.fix` does not reduce in the kernel. The other recursions on the checker's path
  (`exposeWalk`, `scan*`) already had `Nat` measures, so Lean 4.35 compiled them through
  `WellFounded.Nat.fix`, which reduces on closed terms.
- **The change.** The worklist now recurses on `(n*n − visited) * (successorBound g + 1) + pending`.
  The bound is a theorem: `successorBound` (structural over the nodes) dominates every successor
  list (`successors_length_le`), and `worklist_advance_lt` is the decrease when a fresh pair is
  visited. The body, its equations and every theorem about it are unchanged.
- **Effect on the checker teeth.** Every `CheckTeeth` tooth passes with
  `check_reduce := decide +kernel`. The module now builds in 10 s (14 s in the ProofEng report).
- **What is deleted.** `equirec_reduce`, its field equations, the worklist's Boolean step equations
  and all of `Core/DecisionReduction.lean`.
- **Where the probes went.** The five probes keep their names as `decide +kernel` theorems in
  `Teeth/Core/EquiRecursiveTeeth`, with three more: an alias cycle, a row permutation, and a custody
  shadow.
- **Before and after.** Five of the six closed comparisons I tried failed with "decide failed to
  reduce" before the change; all six pass after.

## Gate: the one-edit measurement, repeated
`tools/measure.sh`, updated for the pieces, the tiers and the `⚠` lines: `docs/MEASURE-20261101.log`
(`LEAN_NUM_THREADS=2`, under a load average of 55–200 from the sibling lanes on 12 cores).

| step | edit | rebuilt (tier 1, 277 modules) | wall | 10-30 |
|---|---|---|---:|---:|
| 0 | nothing | nothing | 1 s | 0 s |
| 1 | a private theorem appended to `Adequacy/Safety` (the largest piece) | `Adequacy.Safety` (3.2 s) and `GroundExecution` (its `import all`) | 5 s | 32 s |
| 2 | an exposed `def` appended to `Core.Term` | 177 modules: all of tier 1 downstream of `Term` | 198 s | 78 s |
| 3 | both reverted | the same 177 | 210 s | 78 s |

Reading the table:
- **Step 1** meets workstream 11's "a leaf proof edit under 10 s".
- **Step 2** is a larger tree (277 against about 50 modules) on a loaded machine. Teeth no longer
  rebuild. What makes it smaller is the `@[expose]` confinement pass, which was out of this lane's
  scope.

**Clean builds:**
- **Before** (tiers 1 and 2, 251 jobs): 427 s, load 87–208; summed module time 816 s; longest import
  chain 108 s, through `Substitution` (39 s).
- **After** (tier 1 only, 279 jobs, a tree that has meanwhile gained `Code`, `Quote`, `Durable`, …):
  399 s, load 160–200; summed module time 783 s; longest chain 83 s. That chain now runs through
  `Substitution.Transport` (8 s) and `Msubst` (10 s) into the new `Core.Code` (17 s).

Neither clean build is evidence for "under two minutes": at these loads, wall time measures the
siblings.

## Decisions, with critique
1. **The teeth moved into `Obend/Teeth/` rather than being listed in place.**
   - Critique: it renames sixteen modules under the feet of five live lanes.
   - Meta-critique: the alternative, enumerating every tier-1 module in `lakefile.toml`, silently
     drops any new file from `lake build`. The rename cost one rebase each (C4 and Linear absorbed
     it), and the census now catches the remaining case.
2. **Definitions hoisted into a `Defs` piece rather than kept in place.**
   - Critique: a reader of `Adequacy/Graph` no longer sees `GraphRepresents` beside its lemmas.
   - Meta-critique: without the hoist, the pieces form a chain (critical path 4,747 of 4,921 lines);
     with it, the per-transition pieces run in parallel. A file-local reading order is the price.
3. **`Substitution`'s corners went to tier 2.**
   - Critique: they are teeth of `check_msubst` and used to sit beside it.
   - Meta-critique: they are exactly what tier 2 is for, and their `#tooth`s only ever mutate their
     own file's definitions, so nothing needs `import all`.
4. **The worklist's measure, rather than a fuel argument.**
   - Critique: evaluating the bound computes every successor list once more in the kernel.
   - Meta-critique: there is no fuel parameter and no `Option`, and the statement and equations are
     untouched. The teeth got faster, not slower.

## Not done
- **The splits' parallel gain was not measured on an idle machine.** Within a file, Lean already
  elaborates proofs asynchronously, and `Substitution`'s two big proofs are now a chain of modules
  (`Msubst` cites `infer_transport`). The `Defs` hoist is what buys width.
- **`GroundExecution` still rebuilds on a private Adequacy edit.** Its `import all` should name only
  the pieces whose private declarations it uses.

## The one decision for Ember
Should tier 2 run before every push for every lane? The hook would be enabled once per clone with
`git config core.hooksPath lean/tools/hooks`, which is a repository setting this lane did not change.
Right now nothing forces it, and a lane that only runs `lake build` never sees a broken tooth or a
census refusal.
