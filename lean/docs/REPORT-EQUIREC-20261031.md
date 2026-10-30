# REPORT 2026-10-31: equi-recursive agreement

Astra (GPT-6), with Sol workers, on `astra/EQUIREC.brief.md`. The starting
checkout was `5955007` on `dev` (the brief commit after `1b0600d`).
**Option (c) is implemented.** Public `sameType` is structural finite
bisimulation with equi-recursive aliases. Machine preservation, full annotated
bidirectional completeness, valid template substitution, and the single-route
judge build together. The original repeated-label lambda counterexample is
accepted; `full_corollary_fails` is replaced by `full_annotated`.

Completeness preserves the erased program, assumptions, result type and exact
usage vector, while allowing new annotations. Selecting those annotations from
a `Prop` derivation is noncomputable; checking supplied annotations is executable.
Arbitrary wrong annotation maps still have proved refusal witnesses.

Tags: **MEASURED** means a command ran and its output was read; **PROVED** means a
Lean theorem checked with its axiom pin. Design choices below describe the final
implementation, not unfinished proof obligations.

## 1. Foundation

- `Core/FiniteBisimulation.lean`: a finite deterministic graph kernel. The public
  visited-pair worklist checks labels and arities before queueing children. Its
  termination measure is remaining pairs followed by pending work. `allPairs_length`
  proves the initial candidate count is `n * n`. `visitedSame_iff` identifies
  acceptance with existence of an arbitrary mathematical bisimulation; the
  equivalence theorem follows by identity, reversal and relational composition.
  A separate deletion fixed point provides a reference decision, proved equal to
  the visited procedure. These are **PROVED**, including probes for different
  cycle periods, a reachable mismatch and mismatched arities; executable `#guard`
  probes also exercise the worklist.
- `Core/FinitePresentation.lean`: closed finite supports are **PROVED** to
  present global bisimulation exactly. Ordering, duplicates and extra closed
  nodes cannot change the answer. Greatest-bisimulation closure and constructor
  fusion are also **PROVED**.
- `Core/Assumptions.lean`: assumption and alias declarations moved out of
  `Check` without changing their names or definitions, preventing an import cycle
  when the checker later imports the new agreement.
- `Core/AliasExposure.lean`: finite syntax support, support closure under subterms
  and declared aliases, and head exposure consuming the finite bound-key set.
  Rigid variables remain nominal. An alias-only cycle gets its own representative,
  excluding a prefix leading into the cycle; it does not agree with arbitrary
  constructors. The existing prohibition on alias heads exposing computations is
  retained even for invalid assumptions. Concrete probes and the stated support
  lemmas are **PROVED**. General constructor origin and child-support closure are **PROVED**.
  General alias-unfolding invariance is now **PROVED**, including rotation of
  alias-only cycles and removal of incoming prefixes.
- `Core/RecursiveRows.lean`: executable candidate observations for rows, with
  checked examples. Row-local labels are sorted and unique. Each label has a
  visible member followed by an ordered stream of hidden non-shareable members.
  Emitting a stream member resets epsilon visitation. Shareable shadow-only cycles
  terminate the stream; a resourceful recursive shadow remains a recursive edge.
  Residual-tail scans distinguish finite closed, productive cyclic, nominal,
  unproductive and non-row tails. Productive cycles are not collapsed to finite
  rows. These functions
  terminate without caller-supplied fuel. Their concrete teeth are **PROVED**;
  general stream-output, residual-output and local-label support closure are
  **PROVED**. Stream-reset normalization, exposure invariance, universal field
  congruence, distinct-label commutation and shareable shadow erasure are now
  **PROVED**. Directional lower-bound lookup transports to an agreeing member,
  and finite rowness is invariant; both are **PROVED** without validity or
  rigidity restrictions in `EquiRecursiveLookup.lean`.
- `Core/TypeGraph.lean`: the candidate global type/row graph has a finite closed
  presentation. Its visited decision is **PROVED** equivalent to global
  bisimulation and is an equivalence relation. Arrow and computation congruence
  are **PROVED**. This is now the public checker agreement.
- `Core/ResourceSemantics.lean`: semantic shareability is **PROVED** to decide a
  greatest safety fixed point. It reuses the bisimulation kernel through a mirror
  graph instead of introducing another decision engine. Constructor equations
  and agreement invariance are **PROVED**. Alias-only cycles have no reachable
  resource constructor and are safe under this greatest fixed point.
  `ResourceValidity.lean` proves that validated syntactic shareability implies
  semantic safety; `SubstitutionExposure.lean` and `ResourceSubstitution.lean`
  prove exposure naturality and safety preservation under discharging
  substitutions into valid environments.
- `Core/EquiRecursiveAgreement.lean`: the assembled Boolean relation has
  **PROVED** equivalence, arrow/field/specification/prototype/variant/computation
  congruence, alias unfolding, canonical soundness and preservation of every old
  agreement. `LegacyAgreement.lean` holds the unchanged old relation and its
  proofs, extracted from `Check` to remove the dependency cycle and explicitly
  named `legacySameType`. `Check.sameType` now uses the new relation.
- The visited worklist now stores only visited pairs and pending work. The
  quadratic pair universe occurs in the erased cardinality proof, not in startup
  allocation. The lexicographic termination proof and decision theorem are
  **PROVED** for this sparse implementation.
- `Core/Proofs/EquiRecursiveBoundary.lean`: the alias-domain identity now checks
  when an explicit annotation selects the valid natural-domain representative.
  Missing annotations and unsuitable representatives retain exact refusal
  proofs. Field congruence also crosses the old canonicalizer's different
  decisions about a hidden alias of `Nat` and a hidden literal `Nat`.

`TypeGraphHead.lean` proves structural component inversion and the unconditional
activity barrier. `RuntimeOrigins.lean` preserves actual runtime assignments and
captures while relating their constructor types to the requested representative.
The public checker now accepts these explicit rule representatives and has a
full annotated completeness theorem, preserving exact usage vectors.

Astra read the workers' Lean, repaired elaboration/proof issues, added support
closure proofs, and ran the builds. Workers staged source; only Astra ran compiler processes.

## 2. Validation and journal

**MEASURED:** final `LEAN_NUM_THREADS=2 lake build` succeeded, **171 jobs**, after
the runtime shortcut. All retained and replacement pins and mutation teeth
checked. No project axiom or `sorry` was added. The existing `native_decide`
fixtures under `Spec.Proofs` were not changed; new proof reduction uses
kernel-checked equations. Final log:
`astra/equirec/final-fastpath-full-build.log`. The normal `obend` CLI target
also rebuilt successfully (90 jobs), after atomic installation of the optimized
executable preserved the older cohort process's mapped inode.

The unchanged `lean/tests/run-obend-source.py` ran against the separately built
optimized CLI: **probes 30/30, tutorial 71/71, preview 161 items plus four request
mutations, zero failures**. The existing stale pin
`Structured-neverFinishing-no-partial-value` remains held at Mini
`1653897b6`'s `tickExhausted` outcome. Cohort files are unchanged. The wrapper
recorded child PIDs and timings without changing the harness or fixtures;
`astra/equirec/fast-source-cohorts.log` records the results.

Eight executable probes call public `Check.sameType`: alias inside arrow,
distinct scalars, row order, hidden natural alias erasure, custody-shadow
retention, finite/cyclic row separation, different recursive arrow periods,
and nominal rigid variables. They supplement the general proofs.

The journal's exact repair sets, including removed generated declarations and
revised public statements, are recorded in
[EQUIREC-JOURNAL-20261031.txt](EQUIREC-JOURNAL-20261031.txt). The original export is
`astra/equirec/env-before.jsonl` at `5955007`; the immediate pre-switch export is
`env-before-switch.jsonl` (19,865 declarations, 146 modules); the final export is
`env-after-switch.jsonl`. The pre-switch snapshot included the temporary
`BidirectionalNext` prototype; its removal is expected in the final difference.
The final full build rechecks the affected consumers. Journal hash equality is
evidence under its dependency model, not a proof of semantic equivalence.

**MEASURED:** immediate pre-switch → final: 977 withdrawn supports, 131 revised
statements, 595 statement-cited and 8 proof-cited obligations, 4 re-proved with
supports holding, 1,150 added theorems, 423 removed, 9,221 unaffected. Removal
includes the prototype and generated declarations, as well as the explicitly
retired statements accounted for in §5. Final export: 20,799 declarations from
169 modules. The axiom audit against the original export has exactly the same
54 existing declarations with nonstandard dependencies; no new dependencies or
`sorryAx` appear.

## 3. Decisions, critique, meta-critique

**D1. Separate productive observation from recursive comparison.** The visited
algorithm consumes constructor observations, never raw alias-unfolding steps.
An alias-only loop remains nominal rather than succeeding against every peer.

*Critique:* the type frontend must prove that its exposure and finite support
represent the intended global relation; the graph kernel cannot establish this.

*Meta-critique:* a correct generic bisimulation algorithm is necessary but does
not make `sameType` equi-recursive by itself. The frontend congruence and
consumer proofs are necessary parts of this migration; both are now proved.

**D2. Rows cannot be compared by canonical spines.** For `alpha := Nat`,
`{a : Bool, a : alpha}` retains a hidden entry under the existing canonicalizer,
whereas `{a : Bool, a : Nat}` drops it. Congruence requires these spellings to
agree. Blindly dropping every shadow would lose custody and once-closure
obligations. The candidate representation therefore retains ordered resourceful
shadow streams and uses alias-aware resource observations.

*Critique:* this is more than adding recursive calls to the existing Boolean.
The hidden-resource and residual-tail semantics require general proofs, including
infinite row tails; concrete examples do not discharge those obligations.

*Meta-critique:* the representation earns its place through canonical soundness,
field congruence and lookup transport, all now proved. Its scanner proofs remain
a substantial maintenance cost.

**D3. Annotation repair must preserve derivation representatives.** With
`alpha := Nat` absent from `shareableVariables`, the current nominal resource
predicate accepts an unrestricted `Nat` binder and rejects an unrestricted
`alpha` binder. Arrow congruence makes these domains equivalent. Checking only
at the expected representative therefore invalidates the old direct completeness
statement. A suitable annotation must be able to select the derivation's binder
representative and convert the result, or the resource predicates themselves
must be made semantic throughout the calculus.

*Critique:* honoring annotations in checking mode changes the current promise
that direct completeness holds regardless of annotations. Bad annotations must
not silently destroy the existing covered route.

*Meta-critique:* the full existential annotatability theorem and direct
completeness for arbitrary fixed annotations are different claims. Neither can
be substituted for the other in `Decides`.

**D4. Machine transport must relate components.** The existing exact
`HeadNormalizes` transport and activity canonical-equality theorem become false
under constructor congruence. Preserve deterministic head normalization for a
single type, but expose matching constructor tags with agreement of components
across types. Lookup transport must return member agreement, not canonical
identity. Existing `ConversionPath` can carry these agreements.

*Critique:* this touches function, pair, sum, record and activity preservation,
including response typing on resumption.

*Meta-critique:* weakening a conclusion alone is insufficient; each consumer
must use the component agreement to build its actual runtime derivation.

**D5. Alias-only cycles are safe, but remain distinct equality classes.** The
initial conservative resource observation marked these cycles unsafe. That
conflicted with the existing valid shareability premise for `alpha := alpha`
and made valid template discharges appear to require an extra semantic premise.
The greatest safety interpretation instead accepts a cycle with no reachable
resource constructor. The equality label still retains its cycle representative.

*Critique:* safety here is coinductive absence of resource constructors, not a
claim that an alias-only type has a productive inhabitant. Finite rowness remains
separate and still rejects a productive row cycle as a finite closed row.

*Meta-critique:* the valid-discharge obstruction was partly caused by our own
conservative candidate design. Refining that design restored the existing
validity contract; strengthening the public contract first would have encoded
an unnecessary restriction. Unvalidated discharges can still substitute a
nominally shareable alias of custody, so unconditional equality substitution
requires repair rather than an unchanged proof.

## 4. Checker, substitution and judge integration

**D6. Completeness permits reannotation, not changes to the erased program.**
The new checker takes local representative annotations in both synthesis and
checking positions. This keeps the original derivation's binder resource premises
and operand representatives, then converts to the requested result. A finite tree
of annotations is the witness in the simultaneous completeness induction.

*Critique:* the old `Decides.check_complete` demanded acceptance of the exact
supplied annotations. That statement is false even for typed programs when a
user supplies a wrong annotation. The single-judge interface explicitly
returns a prepared term related by `Reannotates`: identical erased program and
assumptions, with potentially different annotations. `Covered := True` describes
the whole grammar; semantic typing still excludes invalid programs.

*Meta-critique:* existential annotation completeness is not an executable search
algorithm. `annotateFromDerivation` uses classical choice because the existing
typing derivation lives in `Prop`. The executable checker checks supplied
annotations; its depth budget does not price a search for them. The old
annotation-directed checker remains available for its useful historical
substitution theorems, but is not a second judge route.

**D7. Proof computation uses certified equations.** Compiled execution of the
visited-pair procedure works, but ordinary `decide` does not reduce through its
proof-producing well-founded recursion in this module configuration.
`DecisionReduction` supplies checked Boolean equations and an `equirec_reduce`
tactic. It keeps the finite presentation and indices symbolic, observes only
visited nodes, and uses a fixed-predicate `pmap` to avoid dependent `attach.map`
blocking simplification. Atomic mismatch and repeated-row agreement proofs
compile with the existing axiom audit. This introduces no native evaluation
axiom and does not change the decision procedure.

*Critique:* using these equations indiscriminately in all historical executable
fixtures caused an expensive regression-proof compilation. Their positive
agreement cases should first use the proved legacy extension or reflexivity;
a negative legacy answer says nothing about the new relation.

*Meta-critique:* runtime termination, executable test speed and kernel proof
reduction cost are different engineering properties. Passing compiled probes
was insufficient evidence that existing `by decide` proof scripts would remain
cheap. The underlying equality algorithm stays fuel-free.

**D8. Substitution preserves agreement under a valid target environment.**
`Discharges.equivalent_instantiate` retains the original discharge structure
and adds `instance_.valid = true`. Its proof handles arbitrary recursive rows,
finite filtered streams, changing label alphabets and residual tails. Resource
safety can increase under substitution: newly shareable hidden entries disappear,
while the ordered resourceful stream survives. The old annotation-directed
checker transport theorems and their callers now carry the validity premise.
`EquiRecursiveSubstitution` gives both a valid alias-cycle fixture and a concrete
invalid custody-alias discharge for which unconditional transport is false.

*Critique:* the scanner/filtered-stream proof is substantial. Several scanner
arguments may admit further consolidation. It proves semantic preservation,
not an asymptotic runtime bound.

*Meta-critique:* target validity is a real hypothesis with a counterexample when
omitted. An extra whole-substitution congruence assumption would merely hide
the theorem's work; none was added. Revisiting alias-cycle safety (D5) was also
necessary before deciding which public premises were genuinely missing.

**D9. Proved legacy positives are a runtime shortcut.** Final cohort validation
exposed a severe regression in graph construction for ordinary repeated
comparisons. The pre-shortcut `Market-div17by5q` preview had not finished after
more than seven minutes. A process sample located the cost in finite graph
construction/indexing and destruction. Public agreement now first tests
`legacySameType`; a negative answer falls through to the graph procedure.
`agrees_eq_candidate` proves equality of the resulting Boolean with the graph
answer for every input. The optimized preview took **0.223 seconds** in the
recorded cohort run; this is a single-case observation, not a benchmark bound.

*Critique:* this rescues the common historical workload but does not eliminate
finite-graph construction cost for genuinely new recursive comparisons. Those
still terminate by the visited-set proof and are covered by the public probes.

*Meta-critique:* termination and compiled microprobes did not predict whole-cohort
performance. The shortcut is justified by the extension theorem and an exact
Boolean equality theorem; it is not a second judge route or a weaker relation.

The judge grant prices syntactic depth. It does not bound equality-decision
runtime or annotation discovery; the equality procedure has its own finite
termination argument. Calling this grant an operational time budget would
claim more than the laws establish.

## 5. Pin and interface accounting

All applicable pins remain checked. Statements made false by the requested
semantic change were replaced explicitly:

| Former pin or interface | Final replacement and reason |
| --- | --- |
| `sameType_chain`, `sameType_lift` | Retained as `legacySameType_chain` and `legacySameType_lift`; chain-of-head-unfoldings characterizes the old relation only. Public equivalence and `sameType_extends` prove the new contract. |
| `agreement_does_not_descend` | Retained as an explicit legacy negative control, paired with public structural congruence. |
| `identity_alias_check_refused`, `identity_alias_top_refused` | Now require a missing representative annotation; present valid annotations are accepted and present invalid representatives have separate refusal pins. |
| `whnf_of_sameType`, `same_type_preserves_head` | Exact canonical-head identity is false under congruence. Legacy head transport remains; `runtimeHead_transport` and structural component inversion support every machine consumer. |
| `checkAgainst_complete`, `checked_covered_accepted` | Replaced by `complete`, `annotated_complete`, `full_annotated` and `annotateFromDerivation_checks`. Completeness chooses representative annotations and preserves exact usage. |
| `full_corollary_fails`, `shadowedLambdaRecord_refused` | Their old counterexample now satisfies `shadow_record_now_checks`; full annotated completeness covers every declarative constructor. |
| `extend_filling_fragment_refused` | Replaced by `extend_filling_admitted` and the exact insufficient-depth refusal; `extend` is covered. |
| `fragmentJudge_iff`, `routes_agree` | Retired with the two-route judge; `judge_iff` describes the single route and `typed_iff_preparable_at_depth` gives exact-depth completeness. |
| `Decides.check_complete` | Now returns a prepared term and grant, with `Prepares` and `prepare_sound`. In Core4 preparation changes annotations only. Generic soundness, monotonicity, slot and substitution laws rebuild. |

`appliedLambda_boundary`, `coverage_premise_needed`,
`wronglyAnnotated_check_refused`, and `wronglyAnnotated_judge_refused` retain
concrete fixed-map refusal evidence. The historical name
`coverage_premise_needed` now documents the annotation premise, not a semantic
syntax restriction. `Covered`, `checkCovered` and `synthCovered` cover the entire
grammar; typing remains a separate premise. Hole syntax has no declarative
constructor and gains no typing derivation from coverage.

The legacy checker API and its substitution/monotonicity pins remain available
for current callers. It is not called by the single slot judge. The budget
filling/admission teeth and their mutations pass with that judge.

## 6. What this work did not do

- It did not implement executable annotation discovery. The existential theorem
  is constructive inside `Prop`; `annotateFromDerivation` selects its witness
  with `Classical.choose`.
- It did not make arbitrary supplied annotations acceptable, redefine nominal
  binder/capture resource predicates throughout the calculus, or add subtyping.
- It did not establish an asymptotic equality runtime bound or make structural
  grants account for equality computation or annotation search.
- It did not change Mini's cohorts or any source/cache under Mini, Nano or Bend.
  The pre-existing untracked `results.tsv` is untouched.

The foundation was pushed in `bd10929` and `f6ecb15`. The public switch and its
machine/checker/substitution/judge consumers are committed in `89bd283`:
the intermediate signatures cannot be committed independently as green builds.
The final report and exact journal comparison are recorded separately.

## 7. Concurrent integration

The first push found the independent Doc lane (`f2be76f` through `dd7a761`)
already on remote `dev`. Merge `1cbec28` preserves both histories. Its only
shared root change adds `import Obend.Doc`; no Core, Slot, Spec or tactic source
from this migration changed. **MEASURED:** the combined full
`LEAN_NUM_THREADS=2 lake build` passes **177 jobs**
(`astra/equirec/final-merged-full-build.log`), and the Doc lane's
`lake env lean tests/doc/RoundTrip.lean` passes all 16 checks. The journal above
isolates the equi-recursive migration before these independent additions.
The Doc lane adds its own `lean/tests/doc` fixtures; Mini's cohorts remain
unchanged.
