# Lane Expose: `@[expose]` confined to what reduction needs (Claude Opus, 2026-11-01)

Placed by the root from the lane's closing report. Commits `c2d8024..c4edba9`, one per library
(Core first, then Slot, Law, Run, Doc, Judge, Receipt/Fold/Intention/Kind, Spec, measurement).
Both tiers green at every commit; cohorts, receipts (32/32), workspaces, walkthrough unchanged;
census unchanged at 27 compiled-trust constants. No theorem removed or restated.

## What changed
79 modules lost the section-wide expose; 536 of their 1,509 definitions carry `@[expose]` plus 19
derived `DecidableEq` instances. Core: `Term` 12/13, `Ty` 25/29, `Check` 20/25, `Machine` 9/10,
`Data` 14/21, `Invariant` 14/14, `TypeGraph` 11/11, `Code` 5/71. Elsewhere, e.g. `Spec/Elaborate`
0/106, `Spec/Parse` 0/97, `Receipt/Export` 0/38, `Run/Runner` 2/25. 38 exported `:= rfl` theorems
became `:= by rfl` (an `rfl` over the module's own unexposed body is refused). `GroundExecution`'s
`import all` went from 19 lines to 2. Named `import all` that remain: `Receipt/Negotiation` over
`Run.{Runner,Control,Fold,Negotiation}` (replays the session; the alternative was exposing ~55
runner definitions); the tier-2 teeth over `Ty`, `Check`, `TypeGraph`.

## Measurement (12 cores, load 130–210 from sibling lanes, `LEAN_NUM_THREADS=2`, tier 1 = 283 jobs)
| edit | rebuilt | wall |
|---|---|---:|
| private theorem appended to `Adequacy/Safety` | 1 module (before: 2, 5 s) | 1 s |
| `@[expose] def` appended to `Term` | 188 modules (before: 177, 198 s) | 190 s |
| body edit of unexposed `Check.checkExtension` | 1 module | 7 s |

## Gates (workstream 11)
Clean build under two minutes on an idle machine: **open**, not measured (never idle); exposure
decides what rebuilds, not what elaborates. A `Check` edit within twenty modules: **met only for an
unexposed definition**; an edit to `infer`, `check`, `isRowW` still rebuilds `Check`'s 111 tier-1
importers because ~30 proof modules and the checker teeth unfold those bodies.

## A Lean 4.35 behaviour the gate depends on
If a module does `simp [f]` or `rw [f]` on its own unexposed `f`, Lean writes `f`'s equation, body
included, into the public `.olean`, even from a private theorem; editing `f`'s body then rebuilds
every importer. `unfold`, `delta` and `decide` do not trigger it. Verified in a scratch project.

## Not done
No one-at-a-time pruning of the 536 exposures (two suspects tested, both needed). Exposed sections
remain in the other `Core/*`, `Equiv`, `Digest`, `Vault`, `Elab`. Known slip: the Law commit message
names `lawAdmission_run_write`; the restructured proof is `lawAdmission_run_cons`.

## Decision for Ember
Should the modules that unfold the checker (`Core/Proofs/Hole`, the `Substitution` pieces,
`MachineTyping`, `Bidirectional`'s proofs, `Slot/Core4`) take `import all Obend.Core.Check` (or move
into `Check`) so `infer` and `check` can be unexposed? It is the only route to the Check gate for the
definitions the Sound lane edits; those consumers rebuild on every `Check` body edit regardless,
since they read the bodies; `Check` must also stop rewriting `infer` by its own equations
(`infer_zero` does `rw [infer.eq_def]`) or the behaviour above puts the body back.
