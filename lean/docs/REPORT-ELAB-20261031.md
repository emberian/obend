# REPORT 2026-10-31 — `Obend.Elab`: executable preparation, coercions, and the front end on `checkAgainst`

Lane Elab (Claude Opus), on `lean/docs/LANE-ELAB-BRIEF-20261031.md`, in a worktree of `dev` at
`d37888a`, rebased onto `ae50958` before pushing. Tags as in the trees: **PROVED** (a Lean theorem,
checked, with its `#assert_axioms` pin), **MEASURED** (a command run here, output read), **READ**,
**INFERRED**. No `sorry`, no axiom, no `native_decide` added. Nothing outside `lean/` touched.

## 1. What landed

| commit | what |
|---|---|
| `9adb551` | `Obend.Elab.Prepare` (executable preparation), `Obend.Elab.Work`, `Obend.Elab.Gate`; the front end admits through the gate; the checker's injection rule reads an alias-named sum (`injectionHead`). |
| `8c7448b` | `Slot.Core4`'s grant measures `checkWork`; the historical annotation-directed API leaves Core4; `Obend.Elab.Proofs.AliasFree`. |
| `acb90f5` | `Obend.Elab.Proofs.{Refines, PrepareChecks, PrepareProbes}`: `prepare_checks`. |
| `f4a9779` | `Obend.Elab.Coerce`, `Obend.Elab.Proofs.CoerceProbes`. |
| (this commit) | this report. |

**MEASURED:** after the rebase, `LEAN_NUM_THREADS=2 lake build` green, **206 jobs**,
and `python3 tests/run-obend-source.py` against the rebuilt `obend`: **probes 30/30, tutorial 71/71,
preview 161 items and 4 request mutations, 0 failures**, the one stale pin
(`Structured-neverFinishing-no-partial-value`) held exactly as before. The cohort log is
byte-identical to the pre-lane baseline apart from temporary paths. Cohort files unchanged.

## 2. Preparation (`Obend/Elab/Prepare.lean`)

`prepare a hints Γ path t mode` walks the term in the checker's own two modes and returns an
`AnnotationTree` and, in synthesis, the type it predicts the checker will synthesize. It annotates
only what `elaborate` cannot recover from an expected type:

- a **let-redex** `(λx.b) e`: `e` is synthesized, its type is the parameter's, the parameter is
  `unrestricted` when that type and `e`'s captures are shareable and `affine` otherwise, reuse `once`;
- an **application** whose function type is callable as written is annotated with it, so the checker
  reads that representative and ascribes the written codomain (this is what keeps the front end's
  reported types byte-identical; without it the tutorial printed sorted rows, MEASURED: 66/71);
  deeper exposure through specification extensions only when the weak head is not yet an arrow;
- an **introduction form in synthesis** (record, `if`, `ifZero`, `case`, specification, prototype)
  is annotated with its own predicted type, so its synthesis tree also checks at any agreeing type
  (the invariant that removes every re-preparation);
- a **distinct-label record in checking** gets the positional row of the expected type's lookups,
  so members behind an alias or a row tail are found;
- a `fix` whose specification is a bare lambda gets `target → inherited → target`.

`hints` are annotations in the checker's convention (the packet's); a hint at a lambda, injection,
`perform` or `done` is kept. Preparation is untrusted: `prepareChecked`/`prepareInferred` run
`checkAgainst` on the result. Where local inference is silent (a lambda, injection, `perform`,
`done` or empty `case` in synthesis with no hint) the refusal is `.silent path what`, and
`prepareSearch depth` tries candidates there: for a lambda every scalar or context domain and
codomain at every quantity and reuse (72 with an empty context, Astra's set), each rechecked.
Exhaustion is `.searchExhausted path tried`.

**PROVED — `Obend.Elab.Proofs.PrepareChecks.prepare_checks`:**

```lean
theorem prepare_checks {source : AnnotatedTerm} {context : Context}
    (noAliases : source.assumptions.bounds = []) (fragment : Checkable source.term)
    (certificate : Checked source context) :
    ∃ annotations checked,
      prepareAnnotations { source with annotations := noHints } context certificate.type = .ok annotations ∧
      checkAgainst { source with annotations := annotations } context certificate.type = .ok checked ∧
      checked.uses = certificate.uses
```

The fragment is syntactic: `Checkable` / `Synthable` / `FieldsCheckable` (mutual inductives in the
same file). Synthesizable: variables, literals, applications of a synthesizable function to a
checkable argument, lets with synthesizable body and argument, projections, primitives. Checkable:
those, lambdas, lets with checkable body, `if`, distinct-label records, injections, `case` over a
synthesizable scrutinee (variant and activity scrutinees both, empty arms included). The type side is
`bounds = []`: no aliases and no rigid bounds. The certificate is any `Checked`, i.e. any
`PartialTyping` derivation with any conversions. `annotateExecutable` and
`annotateExecutable_checks` are `annotateFromDerivation` and its theorem on that fragment, reading
only the erased term, context, assumptions and type. `appliedLambda_prepared` instantiates both
premises with Astra's probe (non-vacuity).

The proof is one induction over `PartialTyping` (with `FieldsTyping`, `ArmsTyping`) whose motive
holds for every **refinement** of the context (`Obend.Elab.Proofs.Refines`): agreeing binder types,
and a quantity that is the derivation's, `affine` where the derivation's was not `unrestricted`, or
`unrestricted` at a shareable type. That is what lets the let parameter's chosen quantity and the
checker's chosen representatives differ from the derivation's. Its foundation is
`Obend.Elab.Proofs.AliasFree`: without bounds the weak head is the canonical form, agreement keeps
heads and relates components (`arrow_inv`, `variant_inv`, `computation_inv`, `callable_transport`),
lookup transports (`lookupV_transport`), and **the nominal `shareableUnder` equals the semantic
shareability and is agreement-invariant** (`shareable_semantic`, `shareable_congr`). That last fact
is false with unlisted aliases (`EquiRecursiveBoundary.lean:42–49`), which is why the fragment's
type side is what it is (§5, decision).

**MEASURED (`#guard`, `Obend.Elab.Proofs.PrepareProbes`):** the bare checker refuses `(λx.x) 3` with
`missingLambdaAnnotation [0]`; preparation accepts it; a let using its variable twice gets an
unrestricted parameter and checks; a lambda stored in a record and projected is `.silent [0,0,0]
"lambda"`, and `prepareSearch 1` accepts it; with a record parameter the search tries all 72 scalar
candidates and refuses `.searchExhausted [0,0,0] 72`.

## 3. Coercions (`Obend/Elab/Coerce.lean`)

`emit a fuel A B` builds a closed annotated lambda `A → B` or names the obstruction: identity on
agreement; records (target an explicit closed row of distinct labels, each found in the source by
lookup and coerced in place — width and depth); sums (source an explicit closed sum, every label
re-injected into the target, payload coerced inside its arm); functions (the η-wrapper
`λf. λy. c (f (d y))`, reuse fixed, quantities gated by `wrapperAllowed`); everything else refused
(`notCoercible`, `recursive` for aliases whose unfoldings differ). Refusals: `needsSharing` (two or
more kept fields of a non-shareable source), `payloadNotShareable`, `activityField`,
`quantityNotWrappable`, `reuseChanged`, `missingLabel`.

**PROVED:** `coerce_checks` — every coercion `coerce` returns is accepted by `checkAgainst` at
`arrow reusable q A B`. This is by construction (`coerce` emits, then checks, and keeps the
acceptance), so it is a soundness statement, not the emitability claim. The emitability claims are
proved for the two constructors that carry the first edition: `emit_identity_checks` (agreeing
types) and `width_checks` (a record of projections at agreeing members, with a shareable source
when two or more fields are kept), both without running the checker. Depth, sums and η-wrappers
are emitted and rechecked; their emitability is not proved.

**MEASURED, as teeth (`#guard` on the actual checker, `Obend.Elab.Proofs.CoerceProbes`):**
- Astra's η-wrapper matrix (line 55) re-measured cell by cell: `[[F,T,T,T],[F,T,T,T],[F,T,T,T],[F,F,F,T]]`,
  and equal to `wrapperAllowed` in all 16 cells.
- Astra's line 57: on `{handle : Custody 0, tag : Nat, extra : once affine Nat→Nat}`, `λx.{handle =
  x.handle}` and `λx.{tag = x.tag}` check with an affine binder; `λx.{handle, tag}` is refused at all
  four quantities. `coerce` emits the first and refuses the second with `needsSharing`.
- The shareable seed `{x : Nat, extra : Bool}` coerces to `{x : Nat}` and to a reordered row; a nested
  record member is coerced in place; a sum widens and refuses to narrow (`missingLabel "b"`); the
  η-wrapper `affine → linear` is emitted, `unrestricted → affine` and `affine → erased` are
  `quantityNotWrappable`, `once → reusable` is `reuseChanged`; a coercion into an alias of a
  different sum is `recursive`.

Not done from Astra's line 67: the extra-seed example through the actual front end (`chainFix`
still refuses `seedExtra`; nothing in `Spec` calls `Coerce`), and the observation/cost theorems.

## 4. Convergence

**The gate (`Obend.Elab.Gate.admit`):** `prepareInferred` with the packet's annotations as hints,
`checkAgainst` at the predicted type, then the prepared term's `checkWork` within the packet's grant (§5).
It now admits for `FrontEnd.accept`, `Preview.preview`, `obend run` on a packet, and
`obend check-core`. Refusals keep their three sentences (budget / ownership / typing), classified by
re-running the gate on the same two variations as before; the cohorts pin those prefixes.
`FrontEnd.Accepted` carries the gate's `Admitted` and its equation instead of `checkedExact`;
`accepted_typed`, `accepted_never_refused` (now through the new
`Preservation.checked_runBounded_no_refusal`, which needs only a `Checked`),
`accepted_execution_semantics`, `Accepted.sound` and `accept_inhabited` rebuild.

**One checker change was needed:** the front end names a recursive sum by its alias in an
injection's annotation (the legacy rule unfolded one alias step); `elaborate` read the annotation
raw and refused (`shapeMismatch … "sum" (variable 2)`, MEASURED: 104 preview failures). The rule now
reads `injectionHead`: the raw annotated sum, or the weak head of a non-sum, then converts back to
the annotation's type, so the synthesized type stays the alias. `completes_inject`, the
`obstruction_check` macro and, after the rebase, the Law lane's `chk_inject`
(`Law/Proofs/Typing.lean`, a three-line restatement of its head fact through `injectionHead`)
took the new name; nothing else moved. The first attempt did this in
preparation instead (unfold the hint), which made later comparisons unfold too: one Market program
then spent over ten minutes and 1.7 GB in the full bisimulation (MEASURED, `sample`: `TypeGraph.candidate`
and `Ty.decEq`), where the checker takes 27 ms once types keep their aliases.

**Not converged: the open-template check** (`FrontEnd.checkTemplate`) still uses `Check.check` with
rigid variables (given the work grant as its fuel), because what it buys is `Templates.Discharges.check_instantiate`, a theorem about
that checker; moving it would cut the theorem off. That is the one remaining second acceptance
route in the front end.

**The slot judge:** it already called only `checkAgainst`. The annotation-directed API still in
`Slot.Core4` (`gradedCheck`, `gradedCheck_iff`, `calculus_check_iff`, `calculus_check_msubst`,
`calculus_check_msubst_within`, `checkFuel`, `wronglyAnnotated_check_refused`) had no caller in the
tree (READ, `git grep`) and is retired. `Core.Proofs.Substitution`'s `check_msubst` laws stay where
they are; the substitution law the slot uses is `calculus_typed_msubst` (meaning, not a checker).

**The grant's measure:** `termDepth` is replaced by `Obend.Elab.Work.checkWork` (`Core4.checkWork`):
one per node plus the constructors of every annotation the checker reads.
`wide_record_work` pins Astra's line 83: a 1,000-field record of literals has nesting 3 and work
1,001; `wide_record_refused_at_depth_grant` shows a grant of 3 now refuses it.
`typed_iff_preparable_at_depth` becomes `typed_iff_preparable_within_work`. The toy budget in
`Slot/Budget.lean` was repriced (the filling costs 4: two nodes and the two types of its lambda's
annotation); the budget tooth still refuses at the short grant by name. `checkWork` does not meter
`sameType`, whose visited-pair search is quadratic in the type graph's support (§3 of the Work
module's header says so).

| retired or revised | replacement and reason |
|---|---|
| `Core4.termDepth`, `fieldsDepth` | `checkWork`; the old measure survives as `Elab.Work.nestingDepth`, only to pin what it missed |
| front end `limits.typeFuel` (default 4096, ceiling 16384) | `limits.checkWork` (default 65536, ceiling 1048576); cohort pin 43237 |
| `typed_iff_preparable_at_depth` | `typed_iff_preparable_within_work` |
| `gradedCheck`, `gradedCheck_iff`, `calculus_check_iff`, `calculus_check_msubst`, `calculus_check_msubst_within`, `checkFuel` | none: no caller; the single judge never used them |
| `wronglyAnnotated_check_refused` | `wronglyAnnotated_judge_refused` (kept) states the judge's refusal |
| `FrontEnd.Accepted.checkedExact` | `admitted`, `admittedExact` (the gate's equation) |
| `Accepted.sound`, `Accepted.source_eq_packet` | same names, about the gate and the prepared annotations |
| `budget_filling_admitted` at grant 2 | at grant 4 (`checkWork`) |

## 5. The front end's grant (decided: work)

`typeFuel` bounded the historical checker's recursion; keeping it under that name would leave Astra's
line-83 criticism standing for the front end. It is retired: the grant is `limits.checkWork`, the
same measure and word as `Slot.Core4.checkWork`, checked on the prepared term after preparation.
The cohorts' limits were re-pinned to what their programs need (the Market program the preview
cohort runs has `checkWork` up to 43,237 against the old `typeFuel 4096`); the before/after values
are recorded as a deviation from Mini in `REPORT-SPEC-20261030.md` §2. `nestingDepth` survives only
to state what the old measures missed.

Open points for Ember: whether the fragment of `prepare_checks` should
be extended to aliases by making the resource premises semantic in the checker (the D3 route of
REPORT-EQUIREC §3, which would make `shareable_congr` hold everywhere), or by requiring every alias
with a shareable unfolding to be listed (a decidable condition on assumptions under which the same
proof would go through after proving head-exposure for aliases); and whether the template check
should move to the gate once `check_instantiate` has a bidirectional counterpart.

## 6. Validation

**MEASURED:** full `LEAN_NUM_THREADS=2 lake build` after the rebase onto `ae50958`, green, 206 jobs;
cohorts as in §1; `#assert_axioms` on every new theorem (standard three only). The `#tooth`
command could not be used on `prepare_checks`: its dependency walk reaches the compiler-generated
`AliasExposure.exposeWalk.match_3.splitter._sparseCasesOn_2`, which `import all` does not expose
(MEASURED). Its non-vacuity is carried instead by `appliedLambda_prepared`, a kernel-checked
instance of both premises, and by the executable probes. Teeth that do run: `extend_filling_admitted`
and `extend_filling_budget_refused` under the new measure (`Slot.Core4`), the 16-cell matrix and the
line-57 projections (`CoerceProbes`).
