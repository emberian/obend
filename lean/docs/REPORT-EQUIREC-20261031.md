# REPORT 2026-10-31: equi-recursive agreement — work in progress

Astra (GPT-6), with three Sol workers, on `astra/EQUIREC.brief.md`. The starting
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
  Independence from the traversal history still
  needs proof before integration.
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
  **PROVED**. Resource fixed-point correctness, canonical soundness, congruence and
  lookup transport are **not yet proved**.
- `Core/TypeGraph.lean`: the candidate global type/row graph has a finite closed
  presentation. Its visited decision is **PROVED** equivalent to global
  bisimulation and is an equivalence relation. Arrow and computation congruence
  are **PROVED**. It is not yet the checker agreement.
- `Core/Proofs/EquiRecursiveBoundary.lean`: two migration boundaries, **PROVED**
  without changing the existing relation. Arrow congruence forces agreement
  between an unrestricted `Nat -> Nat` arrow and its alias-domain spelling, while
  the existing checker rejects `lambda x. x` at the latter under every annotation.
  Field congruence crosses the current canonicalizer's different decisions about
  retaining a hidden alias of `Nat` and discarding a hidden literal `Nat`.

Astra read the workers' Lean, repaired elaboration/proof issues, added support
closure proofs, and ran the builds. Neither worker ran concurrent builds.

## 2. Validation and journal

**MEASURED:** full `LEAN_NUM_THREADS=2 lake build` succeeded, 130 jobs, with all
existing pins and the new pins checked. No project axiom or `sorry` was added.
Source cohorts: probes 30/30, tutorial 71/71, preview 161 items plus four
request mutations, zero failures. The existing stale pin
`Structured-neverFinishing-no-partial-value` remains held at Mini
`1653897b6`’s `tickExhausted` outcome. Cohort files are unchanged.

Journal: **MEASURED**, zero withdrawn supports, revised statements, statement-
cited proofs, proof-cited proofs, or removed theorems; 9,092 unaffected, 574 added.
One generated `List.lookup.eq_def` proof changed after extracting assumptions;
its statement and supports are unchanged. Exact repair sets and local export
locations are in [EQUIREC-JOURNAL-20261031.txt](EQUIREC-JOURNAL-20261031.txt).
This is the foundation comparison; the agreement-switch comparison is pending.

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

## 4. Outstanding work — the original objective remains open

1. Complete alias-exposure invariance and the resource/row semantic equations.
   Finite presentation independence and closure are now proved.
2. Finish the type/row observation representation and prove resource correctness,
   canonical soundness, constructor congruence, old-agreement extension,
   productive head inversion, row recognition and lookup transport.
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
