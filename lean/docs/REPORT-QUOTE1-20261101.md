# Report: `quote`, `Code`, the importer, mirrors, the observer ladder (lane Quote-1, Claude Opus, 2026-11-01)

Brief: `lean/docs/LANE-QUOTE1-BRIEF-20261101.md`; design `review/QUOTE-ORIENTATION-20261101.md` §3, §4, §8.
Two new modules, `Obend/Core/Code.lean` and `Obend/Equiv/Quote.lean`; one import line each in
`Obend/Census.lean` and `Obend.lean`. No `Term` constructor, `Machine` step or `Check` rule touched.
No `sorry`, no axiom, no `native_decide`; the evaluation teeth are `decide +kernel` and cheap (each
module builds in under ten seconds). Measurement: the start build was a warm replay (251 jobs). End,
after rebasing on the other lanes: tier 1 `lake build` green, 276 jobs, 93 s; tier 2 `lake build
Obend.Census Teeth` green, 295 jobs, 39 s. `#assert_axioms_tree`: 33281 package constants, none on
`sorryAx` or a declared axiom, 27 on the compiler trust as before. Controls: receipts 17/17; Mini's
cohorts probes 30/30, tutorial 71/71, preview 161 items with 0 failures (one stale pin held, as
before).

## What landed

**T1 `quote_roundtrip`.** `quote : Term → Data` is `TermTraverse.encode` rendered as the built-in
sum `Syntax` (`var | bind | node{tag, children}`, children a `SyntaxList`, tags a `SyntaxTag`;
declared in `syntaxSource` like `SpecMeta`). `unquote` accepts only the encoding of a term (a
well-formed tree that `decode` would repair is refused), so `unquote (quote t) = some t` and
`unquote d = some t → shapeOf d = some (encode t)`. `#tooth quote_roundtrip by mutation tagData :=
lossyTagData` (`mix` rendered as `app`) is rejected at `tagOf_tagData`.

**T2 `digest_of_quote`.** The address is a Merkle digest of `Data` (`dataDigest H`), one
`digestWith` per node with a constructor code or a digest as first operand, so every node is in
`binds_or_collides`'s domain under any hash with outputs of at most 32 bytes (`Short`).
`dataDigest_binds`: equal digests are equal data or `Collision H`; `digest_of_quote : address t =
address t' → t = t' ∨ Collision deployed`. Tooth: `lengthHash_address_collapses` (`nat 1`, `nat 2`
share one address under the length hash). No proof evaluates cSHAKE256.
*Restructured:* the orientation had `digest (bytesOf (quote t)) 0`. A byte string needs a proved
injective serialization and the first operand would need `Admissible`; the Merkle form gets both from
`binds_or_collides` alone.

**Versioned encoding (§8.1).** `encodingVersion := dataDigest deployed syntaxSchema`, where the
schema is `tagData` applied to one representative per tag. A different rendering has another version
or collides (`encodingVersion_binds`, `lossy_schema_differs`). `quote_versioned`: a reader of
encoding `e` refuses a quotation stamped `f ≠ e` as `foreignEncoding f e`.

**T6 `Code Ψ A θ` and the importer.** `Code Ψ A θ := {t : AnnotatedTerm // t.assumptions = θ ∧ ∃ c :
Checked t Ψ, c.type = A}`, which is `Calculus.Typed` (`Code.typed`). A held term is
`Held = {term, tree : AnnotationTree, assumptions}`, with the finite tree that full annotated
completeness produces. A quotation is `versioned v {term, annotations, assumptions}`, with codecs and
round trips for `Ty`, quantities, reuse, annotations, trees and `Assumptions`.
`importWith v Ψ A θ`:
1. read the version;
2. read the body;
3. compare the theory (`assumptionsDiffer found expected`);
4. run `checkAgainst`.

On a refusal it names an escaped index (`escapedIndex i`, counted at the root), then a hole
(`holeInCode position identity`), then the checker's own refusal. `import_sound` and
`import_roundtrip` (the quotation of an accepted held term imports to exactly it) are proved.
`import_complete`: every `Code` has a quotation that imports back to its term. It goes through
`tree_complete`, which is `annotated_complete` with the tree in view. It is existential in the tree by
necessity: `empty_tree_refused` and `identity_tree_accepted` give one term refused under the empty
tree and accepted under the witness. The refusals are theorems with reachable instances:
- `import_foreignEncoding`;
- `import_assumptionsDiffer`;
- `import_escapedIndex`, with `escaped_import_tooth`, which refuses `bound 0` at `[]` naming 0;
- `import_holeInCode`, with `hole_import_tooth`, which refuses `λ.hole 3` at position `[0]`.

**Holes (§8.2).** `typed_noHole`: `PartialTyping` has no hole rule, so `code_noHole` (no `Code` holds
a hole) and the importer never accepts one. This is not left to the checker happening to refuse.

**T8.** `code_scoped`/`import_scoped` (`Scoped Ψ.length`, from `MachineTyping.source_scoped`),
`splice_scoped` (substitution by `Scoped |Ψ′|` fillings, via `scoped_substitute`).

**T3–T5 (`Equiv/Quote.lean`).**
- `Blind`: equal up to specification metadata, with no `metadata` node outside a metadata field. It
  is a weak-head simulation (`step_blind`), so `sameRuns_of_blind`.
- `census : Term → Level` is a fold (`observes`); its meaning is `census_le_b → ObsFree`.
- `Observer = run C | quote C` (the kernel quotes what is plugged and hands it to `C` as `Data`;
  census `q`).
- `≈[q]` is `encode` equality, `≈[r]` is `Observed .r`, `≈[b]` is `Observed .b` (census-`b` contexts
  and closing substitutions).

The theorems:
- `observer_ladder`: `≈q ⊆ ≈r ⊆ ≈b`.
- `quote_not_congruent` (T4): Barendregt's pair is `≈r` by one β step, is not `≈q`, and
  `headReader` (a `case` on the quotation's head) separates the quotations of the two terms at `≈b`.
- `rewrite_sound_below k : a ≈[k] b → O.census ≤ k → O.plug a ≈[k] O.plug b` at all three levels
  (T5).

T5's teeth show its premise is necessary at both lower levels:
- `metadata_frame_breaks_b`: REFLECTION's probe separates two `≈b` specifications.
- `quote_breaks_r`: a `quote` separates two `≈r` terms.

**REFLECTION R01/R02**, ported as Core4 terms (`specA/B/C`, `compose`, `provenanceProbe`), run:
`probe_R01` evaluates to `true` and `probe_R02` to `false`, as minidregg's cohort records.
`compose_assoc_b` holds for any observer-free operands; it goes through `Ahead` to `mixAssocBody`
under the specification and then `Blind` across the two metadata. `compose_not_assoc_r` refutes it at
`≈r`. Raw `mix` stays associative at `≈r` (`mix_assoc_r`; it carries no metadata) and not at `≈q`
(`mix_not_assoc_q`). T5 at level `r` needed nothing of REFLECTION beyond the two probes.

**T14 mirrors.** `Mirror {over, depth}` is `Data` (codec, round trip), with
`Depth = structure ⊑ metadata ⊑ code`.
- `mirror_attenuates`: a derived mirror names the same target and is no deeper than its parent or
  than what was asked.
- `derive_chain`: no chain of derivations amplifies.
- `quoteVia store v m` answers only depth `code` (`quoteVia_ok`, `quoteVia_code`). It refuses
  `unknown` and `shallow over depth` by name.
- Tooth `metadata_mirror_cannot_quote`: a `metadata` mirror cannot quote, through any chain.

## Restructurings, named

- **≈r is the existing `BEquiv`** (`observed_r_iff`). `Equiv/Behaviour`'s `BEquiv` quantifies over
  every context, `metadata` included, so it separates specifications by their metadata: it is
  REFLECTION's reflective equivalence, not its ≈b. REFLECTION's ≈b, contexts that only run what they
  are given, is the new `Observed .b`, coarser. The orientation's ladder is kept with `≈b`
  re-pointed. The claim "mix_assoc fails under ≈r" is corrected: raw `mix` is associative at `≈r`;
  `compose`, which records provenance, is not.
- **`reflect` counts as census `b`**. The orientation put `metadata`/`reflect` frames at `r`.
  `reflect` returns the stored specification, whose metadata is again reachable only through
  `metadata`. `Blind` relates it congruently, so admitting `reflect` at `b` makes T5 strictly
  stronger.
- **The census is conservative**: any `metadata` node outside a metadata field, not only one whose
  operand is the hole, gives `r`. A frame-on-the-hole census is unsound under substitution contexts
  (`(λx. metadata x) [·]`).
- **The quotation carries an `AnnotationTree` and a theory**, so T6 is stated on `Held`. The
  orientation's `import (quote c.val.term)` holds with the tree as an existential witness, and it
  cannot hold for supplied annotations.
- **Diagnosis after refusal**: the importer runs the checker first and names the escaped index or
  hole when it refuses. `import_escapedIndex`/`import_holeInCode` prove the names are exact, because
  an accepted term is scoped and hole-free.
- The address is Merkle (T2 above). `encodingVersion` is a schema digest, not part of `address`; the
  versioned stamp travels in the quotation.

## Not done, or for the next lane

- `Syntax` is not registered in the front end's `builtinTypeNames` (`Spec/Elaborate.lean`, another
  lane's file); `syntaxSource` is the declaration to add.
- The JSON packet (`decodePacket_term`) is not on this path: it is a legacy non-`module` leaf, and
  the importer reads `Data`.
- T6′, T7, T9–T13, T15, T16 are outside this lane's scope.

## Decision for Ember

`Equiv/Behaviour`'s `≈b` (`BEquiv`) is, by its own definition, the *reflective* equivalence. Should
it be renamed `≈r`, with `≈b` given to the census-`b` relation (`Observed .b`), so that "a rewrite
justified by ≈b" means what REFLECTION means? The alternative is to keep the names and record that
Core4's `≈b` sees metadata. Every theorem now citing `BEquiv` (`mix_assoc`, Faré's tests,
`bequiv_of_steps`) stays true either way; only what a `RewriteJudge` may cite changes.
