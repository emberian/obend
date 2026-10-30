# REPORT 2026-10-31: equi-recursive agreement — work in progress

Astra (GPT-6), with six Sol workers, on `astra/EQUIREC.brief.md`. The starting
checkout was `5955007` on `dev` (the brief commit after `1b0600d`).
**This is a foundation checkpoint, not completion of option (c).** `sameType`,
`PartialTyping`, preservation, the bidirectional checker and the slot judge have
not yet been switched. The old `full_corollary_fails` remains true and present.

Tags: **MEASURED** means a command ran and its output was read; **PROVED** means a
Lean theorem checked with its axiom pin; **DESIGN** means an integration decision
whose required general proofs remain outstanding.

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
  are **PROVED**. It is not yet the checker agreement.
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
  proofs, extracted from `Check` to remove the dependency cycle. `Check.sameType`
  still resolves to that legacy definition at this checkpoint.
- The visited worklist now stores only visited pairs and pending work. The
  quadratic pair universe occurs in the erased cardinality proof, not in startup
  allocation. The lexicographic termination proof and decision theorem are
  **PROVED** for this sparse implementation.
- `Core/Proofs/EquiRecursiveBoundary.lean`: two migration boundaries, **PROVED**
  without changing the existing relation. Arrow congruence forces agreement
  between an unrestricted `Nat -> Nat` arrow and its alias-domain spelling, while
  the existing checker rejects `lambda x. x` at the latter under every annotation.
  Field congruence crosses the current canonicalizer's different decisions about
  retaining a hidden alias of `Nat` and discarding a hidden literal `Nat`.

`TypeGraphHead.lean` proves structural component inversion and the unconditional
activity barrier. `RuntimeOrigins.lean` preserves actual runtime assignments and
captures while relating their constructor types to the requested representative.
A separate checker prototype accepts explicit rule representatives; its
soundness is checked, while full annotation completeness is still in progress.

Astra read the workers' Lean, repaired elaboration/proof issues, added support
closure proofs, and ran the builds. Workers staged source; only Astra ran compiler processes.

## 2. Validation and journal

**MEASURED:** full `LEAN_NUM_THREADS=2 lake build` succeeded, 148 jobs at the pre-switch working-tree checkpoint (including the
temporary checker prototype), with all
existing pins and the new pins checked. No project axiom or `sorry` was added.
Source cohorts: probes 30/30, tutorial 71/71, preview 161 items plus four
request mutations, zero failures. The existing stale pin
`Structured-neverFinishing-no-partial-value` remains held at Mini
`1653897b6`’s `tickExhausted` outcome. Cohort files are unchanged.

Journal: **MEASURED**, the earlier 130-job foundation comparison had zero withdrawn supports, revised
statements, statement-cited proofs, proof-cited proofs, or removed theorems;
9,092 unaffected, 574 added.
One generated `List.lookup.eq_def` proof changed after extracting assumptions;
its statement and supports are unchanged. Exact repair sets and local export
locations are in [EQUIREC-JOURNAL-20261031.txt](EQUIREC-JOURNAL-20261031.txt).
The full pre-switch export is `astra/equirec/env-before-switch.jsonl`: 19,865
declarations from 146 modules. This is still before the agreement switch; the
post-switch repair comparison is pending. The original-to-pre-switch journal
records 179 statement-cited and 15 proof-cited obligations, 59 withdrawn supports,
one revised generated equation, and 36 removed private generated theorems after
module extraction. The full build rechecked them; exact names and dependencies
are recorded in the journal file, rather than treating extraction as hash-neutral.

Eight executable candidate probes also pass: alias inside arrow, distinct
scalars, row order, hidden natural alias erasure, custody-shadow retention,
finite/cyclic row separation, different recursive arrow periods, and nominal
rigid variables. These probes do not establish the remaining general laws.

## 3. Decisions, critique, meta-critique

**D1. Separate productive observation from recursive comparison.** The visited
algorithm consumes constructor observations, never raw alias-unfolding steps.
An alias-only loop remains nominal rather than succeeding against every peer.

*Critique:* the type frontend must prove that its exposure and finite support
represent the intended global relation; the graph kernel cannot establish this.

*Meta-critique:* a correct generic bisimulation algorithm is necessary but does
not make `sameType` equi-recursive by itself. This checkpoint does not claim it does.

**D2. Rows cannot be compared by canonical spines.** For `alpha := Nat`,
`{a : Bool, a : alpha}` retains a hidden entry under the existing canonicalizer,
whereas `{a : Bool, a : Nat}` drops it. Congruence requires these spellings to
agree. Blindly dropping every shadow would lose custody and once-closure
obligations. The candidate representation therefore retains ordered resourceful
shadow streams and uses alias-aware resource observations.

*Critique:* this is more than adding recursive calls to the existing Boolean.
The hidden-resource and residual-tail semantics require general proofs, including
infinite row tails; concrete examples do not discharge those obligations.

*Meta-critique:* the added representation must simplify the eventual agreement
and its consumers. Until it supplies canonical soundness, field congruence and
lookup transport, it is an implementation candidate, not the language contract.

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

## 4. Outstanding work — the original objective remains open

1. Alias-exposure invariance, resource correctness, row semantic equations,
   canonical soundness, all constructor congruences and old-agreement extension
   are complete.
2. Productive component inversion, row recognition and lookup transport are
   complete. Finish full equality transport through template substitution;
   exposure and resource-safety transport are already proved.
3. Switch `sameType`; repair machine invariants and preservation with the
   journal's exact repair set recorded before and after that switch.
4. Repair the checker, enlarge its fragment, and prove direct completeness under
   the precise resource/annotation discipline chosen. Add annotation locality
   and derive the full existential annotated completeness theorem. Admit the
   old repeated-label lambda witness and replace its refutation.
5. Replace the two-route judge with the proved checker route. Reconcile syntactic
   `Covered` with `Decides.check_covered` explicitly: a sufficient fragment need
   not characterize every accepted annotated program. Rebuild budget teeth.
6. Repeat the full build and unchanged source cohorts at the integrated result;
   update this report with final decisions, exact journal sets and remaining
   limitations.

## 5. What this checkpoint did not do

It did not redefine `sameType`, change declarative conversion, repair preservation,
expand `checkCovered`, prove annotatability, or change admission. No source or
cache under Mini, Nano or Bend was changed; the pre-existing untracked
`results.tsv` was left alone. The gap between this foundation and the requested
finished migration is substantive.
