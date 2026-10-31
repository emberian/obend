# `≈b` for the lazy heap: three definitions, a spike, and the Iris-Lean question

2026-10-31, answering `review/EQUIV-BRIEF-20261031.md`. Spike in `lean/Obend/Equiv/` (six new
files, plus their six import lines in `Obend/Census.lean`, which refuses a file under `Obend/` it
does not import).

## 0. Answers

- **The spike uses definition 1**, completed-run equality under all contexts and substitutions
  (`Obend.Equiv.BEquiv`, written `≈b`). `mix_assoc : mix (mix a b) c ≈b mix a (mix b c)` is
  proved for arbitrary open `a b c`, together with Faré's two tests and proofs that the discarded
  parts diverge. Axioms: `propext`, `Classical.choice`, `Quot.sound`.
- **The brief's shortcut does not hold, and the reason shaped the spike.** Under Core4's
  weak-head `Steps`, each association is a value after one step (`mix_assoc_not_weak_head`), and
  the two values differ. Applied to `s u`, the left side reaches `c s ((mix a b) s u)` with the
  inner `mix` in argument position, which weak-head reduction never touches unless `c` demands it.
  Both sides meet at `λself. λsuper. c self (b self (a self super))` only by reducing under
  binders. So the theorem needs a congruence result: reduction anywhere in a term preserves
  completed runs. That is `Ahead` (§3), and it is most of the spike. No heap is needed.
- **Iris-Lean can be used from this tree**: toolchain `v4.35.0` (bumped 2026-10-19), every file a
  `module`, core dependencies batteries and Qq only (no Mathlib), and the adequacy layer has
  landed: `Iris/ProgramLogic/Adequacy.lean` (`wp_adequacy_gen`, `wp_strong_adequacy_gen`) and
  `HeapLang.heap_adequacy`, both resting on the three standard axioms. A probe project
  (`module` file importing `Iris.ProgramLogic.Adequacy` and `Iris.HeapLang`, iris-lean master
  `fb21a8a`) built in about 5 minutes, with 570 MB of `.lake`. PR #394 (the adequacy
  interface) merged on 2026-05-22. **What `≈b` needs is not there**: no binary relational
  logic (ReLoC), no time credits, and the paper (§2.1) lists generalized step indices as still open.
  Master has since added `local stepindex` (#729). Iris-Lean is a sound base to build the heap relation on. Nothing ready-made gives
  you `≈b`.

## 1. Ground truth the plan rests on

- `Term.Step` is weak-head call-by-name with no reduction under `lam` and no argument evaluation.
  It is deterministic (`Adequacy.sourceStep_deterministic`, module-private; the spike re-proves it
  as `Equiv.step_deterministic`). `mix l u ⟶ mixBody l u = λself.λsuper. u self (l self super)`
  and `fix s i ⟶ s (fix s i) i`.
- The demand machine (`Core/Machine.lean`) is call-by-need. It has cells
  `suspended | evaluating | cached`, update frames, one tied address per `fix`, and the outcome
  `divergent address` when a cell is re-entered while it is evaluating (blackholing).
  `Core/Proofs/Adequacy.lean` proves one direction only: a finished machine run has a source
  evaluation to the same ground observation. `Representation` is not inhabited:
  source-to-machine completeness and administrative progress remain open. The Forcing, Collect
  and Settle proofs give the heap-renaming infrastructure (`HeapAgree`, `StateAgree`, `ForcesBy`,
  `BackSim`, settle-erasure commuting with a transition). A heap relation would reuse it. It
  relates two heaps of the same program, not a heap to a term.
- Measured on the machine, as a check on the analysis below and not as evidence for it
  (throwaway probe, not committed). `{good = 7, bad = self.bad}.good` finishes in 16 ticks.
  `.bad` ends `divergent (blackhole)` after 21 ticks, where `Steps` diverges.

## 2. The three candidates

Write `L = mix (mix a b) c` and `R = mix a (mix b c)`. Let `k` be the number of times `c` demands
`super`.

### Definition 1: completed-run equality (`≈b`, the spike)

`t ≈b t'` iff for every substitution `ρ` and context `C` (a term with the hole at variable 0),
`C[tρ]` and `C[t'ρ]` have the same ground observations (`Halts`) and converge alike
(`Converges`). Plugging is capture-avoiding. Real binding contexts are handled by `Ahead` being a
congruence through binders, so `Ahead L T` puts `L` and `T` in any context.

- *mix:* proved (`mix_assoc`).
- *Faré:* proved. `keep(7, fix(identity)) ≈b 7`. `keep(7, loop) ≈b 7` with `¬ Converges loop`.
  `{good = 7, bad = self.bad}.good ≈b 7` with `.bad` proved divergent (it returns to itself after
  four steps).
- *Pricing:* blind. On the reference semantics the two associations differ by `3(k − 1)` steps.
  `L` re-unfolds `(mix a b) s u` at every demand of `super`, so the difference is unbounded in `k`.
  Definition 1 also cannot see yields (`perform` stops `Steps`) or blackholing. A refusal the
  machine reports in 21 ticks counts the same as a run that burns the whole fuel budget.

### Definition 2: clairvoyant call-by-value cost equivalence

Hackett–Hutton's Theorem 4.2: contextual improvement under call-by-need coincides with contextual
improvement under clairvoyant CBV. That is a big-step `⇓ᵏ_CV` with a nondeterministic Skip at
every binding, and call-by-need cost is the minimum over derivations (Thm 4.1). It is
Moran–Sands' improvement (Def. 3.3) with the heap replaced by nondeterminism. Moran–Sands
identify blackholes with divergence (§3.1) and count every machine step. For `≈b`, take the
symmetric version within a constant (their Def. 4.1): `t ≈ᶜ t'` iff there is a `κ` such that
`C[t] ⇓ᵏ_CV` implies `C[t'] ⇓^{≤k+κ}_CV` and conversely.

- *Core4 shape:* Core4 has no `let`. Its binding sites are β arguments, record fields, inject and
  case payloads, the `self` of `fix`, and `super` inside `mixBody`. Each gets a Let′/Skip pair.
  `fix` is H&H's singly-recursive let, which their core language has. A non-value recursive
  binding (`bad = self.bad`) has no CV derivation, which agrees with need and with the
  blackhole.
- *mix:* under need, `R` always pays both unfoldings, and `L` pays the inner one only if
  `super` is demanded. So `cost L ≤ cost R ≤ cost L + κ` with a constant `κ` (the
  `mixBody`/β/β of one unfolding). The machine shows `κ = 7` ticks: `(15, 22)` at `k = 0` and
  equal for `k ≥ 1`. The statement to prove is `L ≈ᶜ R` with explicit constants. Exact cost
  equivalence is false, and the `k = 0` case is the counterexample.
- *Faré:* `keep(7, x)` costs the same for every `x` (Skip); `.good` costs a constant.
- *Pricing:* the right time measure at the source level. It is the cost of the machine the world
  runs, provided one more theorem holds: machine ticks are within a constant factor of CV cost.
  The existing adequacy relation preserves results, not costs, so that is new work. It does not
  price heap cells (`Limits.heap`) or stack depth.

### Definition 3: step-indexed relation over machine configurations with heap

A binary logical relation on `Machine.State` that relates heaps, control and frames. Cells
correspond by state: `suspended` to a term, `cached` to a value, `evaluating` to "under an
update frame". The observation set is the machine's `Outcome`: finished, divergent (blackhole),
refused, yielded, suspended (ticks or capacity). The relation is indexed by ticks and heap.

- *mix:* the same constant-bound statement as definition 2, plus space: `L` allocates the
  inner thunk and never forces it when `k = 0`.
- *Faré:* distinguishes what definitions 1 and 2 identify. `.bad` is a blackhole outcome, a
  cheap detected refusal, and a run that genuinely loops exhausts its ticks.
- *Pricing:* the only candidate that speaks the world's units (ticks, heap cells, the
  `sharedEffect` refusal, yields as turns). It is required for the sharing-identity test in
  DESIGN §6 ("a shared expensive field selected twice keeps one thunk's identity") and for the
  effect rule (a `perform` under an update frame is refused).

**Compatibility with resource pricing:** definition 1 is incompatible. Definition 2 is
compatible for time, once the tick/CV constant-factor theorem holds. Definition 3 is what the
world actually charges. The order to build them is 1 (done), then 2, then 3. Each refines the
previous one, and the earlier ones stay useful: `Ahead` is the pure-step layer of 2 and 3.

## 3. The spike (`lean/Obend/Equiv/`)

| file | content |
|---|---|
| `Reduction.lean` | renaming as substitution, `substitute_bound`, `instantiate_substitute`, `mixBody_substitute`, `step_substitute`, `steps_substitute`, `step_deterministic` |
| `Fields.lean` | field, arm and hole lists related pointwise with equal names; `find?` and `extendFields` respect the relation |
| `Ahead.lean` | `Ahead t t'`: `t'` is `t` with any subterms (under binders included) run ahead by `Steps`. `Ahead.refl`, `ahead_rename`, `ahead_substitute` (related substitutions), `ahead_instantiate`, `ahead_mixBody` |
| `Simulation.lean` | value-head inversions both ways; `step_ahead` (a step ahead is matched by reduction behind); `step_behind` (a step behind is matched by reduction ahead; determinism lets the term behind catch up); `evaluates_ahead`, `evaluates_behind` |
| `Behaviour.lean` | `Halts`, `Converges`, `SameRuns`, `sameRuns_of_ahead`, `BEquiv` (`≈b`, an equivalence), `bequiv_of_ahead`, `bequiv_of_steps`, `mix_apply` (an applied `mix` unfolds in three steps), `mix_assoc_ahead`, **`mix_assoc`**, `mix_assoc_not_weak_head` |
| `FareTests.lean` | `keep_fix_identity`, `keep_loop` (+ `loop_diverges`), `good_field`, `bad_field_diverges`, `diverges_of_closed` |

`Ahead` is Takahashi's parallel reduction with weak-head runs as the only contraction. The two
simulations are what a standardization theorem would otherwise provide, and the language's
determinism keeps them first-order. Adding a `Term` constructor costs one `Ahead` constructor and
one arm in each of `refl`, `ahead_rename`, `ahead_substitute`, `step_ahead` and `step_behind`.

Not in the spike:

- the cost statement of definition 2;
- yields: `Interaction`-level equivalence needs `Ahead` to preserve `Yields`, which is one more
  simulation lemma in the same shape;
- a context datatype with capture: the law holds there through `Ahead`'s congruence, but
  `≈b` is stated with capture-avoiding plugging.

## 4. What the heap-indexed version needs that the spike does not have

1. **A relation from heap to term, or from heap to heap.** Either inhabit `Representation`
   (source-to-machine completeness is the open half) and transfer, or relate two machine runs
   directly. The second is the ReLoC shape: `L` runs on the machine against a ghost copy of `R`.
2. **Guarded recursion for cyclic heaps.** A `fix` cell's relation mentions itself through the
   tied address and through record fields that point back at `self`, so the relation is a guarded
   fixpoint: Iris's `▷` and `BI/Lib/Fixpoint`, or Appel–McAllester indices by hand. By hand
   brings back the `n + m` arithmetic that D12 removed from typing.
3. **Cell-state invariants** across update frames: `evaluating` exactly when an update frame for
   it is on the stack, `cached` only after its update. Forcing and Settle prove these for one
   machine. A relation needs them for two machines in lockstep.
4. **Cost.** Ticks as a resource in the relation. Iris time credits (Mével–Jourdan–Pottier) are
   not ported. A tick counter in the machine state is the cheap substitute, at the price of
   explicit arithmetic. Heap cells are priced the same way, against `Limits.heap`.
5. **A binary program logic.** Iris-Lean has unary WP, lifting and adequacy. A refinement
   judgment (spec-thread ghost state, `refines` rules) has to be built on top. Rocq's ReLoC is the
   model; nothing of it is in the Lean port.
6. **A `Language` instance for the machine.** The machine is a state machine with explicit
   frames and no evaluation contexts, so `EctxLanguage` does not fit. Take `Expr := Control ×
   List Frame`, `State := Array Cell`, `toVal` on `complete`, and lift with
   `ProgramLogic/Lifting.lean` by hand.
7. **A dependency decision.** obend has no dependencies today. Iris brings batteries and Qq. The
   census (`#assert_axioms_tree`) walks library constants, so Iris's constants sit outside it,
   and their axioms were checked separately here (standard three).

## 5. Lanes this suggests

1. *Yields under `Ahead`* (small, same shape as `step_ahead`): `≈b` over `Interaction`.
2. *Definition 2 for Core4*: `⇓ᵏ_CV` with Skip at Core4's binding sites. Then H&H Thm 4.1 against
   a cost-counted call-by-need relation, `L ≈ᶜ R` with explicit constants, and Faré costs.
   Ordinary induction, no new tooling. Breitner's Isabelle work is the warning about scale:
   Launchbury's correctness proof failed when mechanized, and adequacy was still unpublished in
   2014. Budget for the heap-to-CV correspondence being where the work is.
3. *Ticks ↔ CV cost* on the existing machine-to-source relation in `Core/Proofs/Adequacy.lean`:
   extend it to carry a tick bound.
4. *Definition 3 in Iris-Lean*, only when a statement needs sharing identity, effects under
   update frames, or space. Start unary: re-derive the machine's existing soundness through WP as
   a calibration of cost against the hand proof. Then build the binary layer.
