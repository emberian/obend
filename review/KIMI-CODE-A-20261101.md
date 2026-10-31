# KIMI code review A, 2026-11-01

[READ] The reviewed source set was the nine requested modules plus `Obend/Kind/Proofs.lean` for the intended dispatch and staleness contracts.
[READ] Paths below are relative to `/Users/ember/dev/obend/lean`.
[READ] No Lean execution was completed, so no claim is tagged RAN.
[READ] `joinUses` is used but not defined in `Obend/Core/Check.lean`, so its implementation was outside the permitted source set.

## 1. Correctness

### Quotation, versioning, and import

[READ] `encodingVersion` does not cover the whole quotation codec, because `syntaxSchema` hashes only `tagRepresentatives.map tagData` at `Obend/Core/Code.lean:443-476`, while `shapeData` and `childrenData` are separate at `Obend/Core/Code.lean:116-126`.
[READ] Changes to the renderings of `var`, `bind`, `node`, `nil`, or `cons` can therefore leave the advertised encoding version unchanged.
[READ] The docstring of `encodingVersion_binds` at `Obend/Core/Code.lean:472-476` claims that equal versions make two encodings render every tag alike, but the theorem compares only their finite representative lists.
[READ] A renderer changed only at `.hole 1`, `.nat 1`, a nonempty label, or `.binary .multiply` is invisible to that theorem because the representatives are `.hole 0`, `.nat 0`, the empty label, and `.binary .add`.
[READ] `syntaxSource` at `Obend/Core/Code.lean:517-523` is not connected by any theorem to the executable codec whose version it purports to describe.
[READ] `import_scoped` at `Obend/Core/Code.lean:975-977` ignores its import-success hypothesis and simply applies `code_scoped` to the already-typed `Code` value.
[READ] Consequently `import_scoped` states no importer-specific fact beyond the invariant already packaged by `Code`.

### Quantity rules and refusals

[READ] For a `.linear` parameter, `argumentAllowed` at `Obend/Core/Check.lean:399-403` can fail only its `!type.isComputation` conjunct, because the other two conjuncts are automatically true.
[READ] `argumentRefusal` at `Obend/Core/Bidirectional.lean:100-104` nevertheless returns `.notShareable` for every `.linear` parameter, so every failure in that case is mislabeled and `.activityMisplaced` is never selected.
[READ] For an unrestricted argument with no linear use, a `reusableCaptures` failure also becomes `.notShareable` because `argumentRefusal` never examines the capture premise.
[READ] The `fix` rule at `Obend/Core/Bidirectional.lean:406-407` collapses every `argumentAllowed` failure to `.notShareable`, including activity failures and linear-argument failures.
[READ] The empty-field case of `checkFields` at `Obend/Core/Bidirectional.lean:703-715` reports `.typeMismatch path .emptyRow row`, reversing the expected row and the actual empty row used elsewhere in the checker.
[READ] `overuse` at `Obend/Core/Bidirectional.lean:70-78` names every detected `safeQuantity` failure `.affineBinderOverused` without inspecting the binding's quantity, so the refusal name is narrower than its implementation.
[READ] The annotated `extend` branch at `Obend/Core/Bidirectional.lean:539-554` checks `sameType prior.type annotation.domain` even though `prior` was just checked against `annotation.domain` and packed by `checkedSynth`.
[READ] That `sameType` premise is reflexively true on the branch, and its `.typeMismatch` refusal is unreachable.

### Kind identity and creation

[READ] `create` at `Obend/Kind.lean:122-125` does not check whether the new instance's name is already a kind name.
[READ] `effectiveOf` rejects exactly that condition at `Obend/Kind.lean:157-160`, so `create` can succeed and immediately produce an instance whose effective law is refused with `.clash`.
[READ] `dispatch` at `Obend/Kind.lean:188-192` never checks `kindRefs.current` and never reads `i.kind.version`.
[READ] A stale instance can therefore dispatch successfully while `effectiveOf` refuses the same instance with `.stale`.
[READ] `effectiveOf` checks only the instance's direct kind pin before recomputing precedence and reading the current registry laws at `Obend/Kind.lean:157-165`.
[READ] Revising an ancestor therefore changes the laws available to a descendant without making the descendant's direct pin stale.
[READ] `Obend/Kind/Proofs.lean:332-342` explicitly confirms that revising `Mile` leaves a `Trip` pin current, so a `KindPin` does not pin the effective law computed beneath that kind.
[READ] `holds` at `Obend/Kind.lean:68-72` compares only name and version, while `Kinds` has no invariant preventing law, layout, initial state, or parents from changing at the same name and version.
[READ] Such an in-place revision remains current under every theorem in the reviewed model.

### Observer and cost models

[READ] The header of `Obend/Equiv/Quote.lean:3-17` describes all three equivalences as observer-induced, but `LEquiv .q` is defined directly as `QEquiv` at `Obend/Equiv/Quote.lean:486-493` and no theorem connects `QEquiv` with `Observed .q`.
[READ] `Admits .q` and `Observed .q` therefore do not establish the claimed observer characterization of syntactic equality.
[READ] The docstring of `quote_not_congruent` at `Obend/Equiv/Quote.lean:672-689` generalizes its counterexample to every equivalence coarser than `≈q`, while the theorem proves failure only for the stated reflective and blind equivalences.
[READ] The opening of `Obend/Equiv/Clairvoyant.lean:2-22` presents least-cost call-by-need adequacy for the Core4 adaptation, but this module contains no theorem relating `Run` to the machine's `Steps` or proving that adequacy.
[READ] `CostAtMost` at `Obend/Equiv/Clairvoyant.lean:214-216` is only an existential bound over clairvoyant derivations, not a least-cost theorem.

## 2. Performance

[READ] Unannotated case synthesis elaborates the first arm at `Obend/Core/Bidirectional.lean:683-687` and then calls `against`, whose `checkArms` elaborates that same arm again at `Obend/Core/Bidirectional.lean:732-747`.
[INFERRED] Nesting cases in successive first arms can double elaboration at every level and produce exponential checking time.
[READ] `kindPrecedence` at `Obend/Kind.lean:129-142` recursively recomputes every parent's complete precedence list without memoization.
[INFERRED] A diamond-shaped acyclic hierarchy can therefore take exponential time despite having only linearly many kind cells.
[READ] `TypeGraph.nodes` at `Obend/Core/TypeGraph.lean:81-85` places `RR.fieldLabels types` inside the outer `flatMap` and adds two stream nodes for every pair of a supported type and a global field label.
[INFERRED] With `T` supported types and `L` distinct labels, the presentation contains `2*T*L` stream nodes before agreement starts, which becomes quadratic when `L` grows with `T`.
[READ] `rowObservation` at `Obend/Core/TypeGraph.lean:54-60` computes `RR.labels` and `RR.residual` once for its label and again through `rowChildren` for its successors.
[INFERRED] Repeated graph observation can multiply those duplicate row traversals during finite agreement.
[INFERRED] Appending one component with `path ++ [n]` throughout `elaborate` at `Obend/Core/Bidirectional.lean:263-749` copies the whole root path at each descent and costs quadratic time along a deep term.
[INFERRED] `checkArms` performs a linear `rowMember` search for every arm at `Obend/Core/Bidirectional.lean:732-748`, giving quadratic behavior when arm and row widths grow together.
[INFERRED] `labelsDistinct` at `Obend/Core/Check.lean:417-422` adds another quadratic scan over case arms.
[INFERRED] Each `lookupV` or `isRowV` call recomputes `unvisited` using a filter and linear membership tests at `Obend/Core/Check.lean:51-53,125-131`, making repeated alias walks quadratic in the number of bounds and visited variables.
[READ] The accepted branch of `unquote` at `Obend/Core/Code.lean:184-189` calls `decode s` once to validate the encoding and again to construct its result.
[INFERRED] `C4.mergeN` repeats the full candidate-tail scan in `nextHead` for every emitted name at `Obend/Spec/C4.lean:95-124`, while `nodupB` at `Obend/Spec/C4.lean:58-61` is independently quadratic.

## 3. Engineering quality

[READ] Every reviewed module applies `@[expose]` to its entire public section rather than to selected definitions whose bodies clients must reduce.
[INFERRED] This unnecessarily exposes large proof-helper bodies, mutation fixtures, and test terms to downstream modules and can increase interface and kernel-processing costs.
[READ] `lossyTagData` at `Obend/Core/Code.lean:212-239` duplicates every case of `tagData` solely to change the `.mix` case, so a new tag requires synchronized edits in a mutation fixture.
[READ] `syntaxSource` is a third hand-written enumeration of the same syntax schema and can drift without failing any proof.
[READ] `NoHole` at `Obend/Core/Code.lean:774-800` introduces a second full enumeration of `Term` even though `holeOf (encode t) = none` already defines the intended predicate operationally.
[READ] The 29-case `typed_noHole` elimination at `Obend/Core/Code.lean:802-846` then couples that duplicate enumeration to every typing constructor.
[READ] `treeEq_sound`, `treesEq_sound`, `treeEq_refl`, and `treesEq_refl` at `Obend/Core/Code.lean:152-179` are re-proved because the original laws are private, which preserves duplication instead of exposing a small reusable equality API.
[READ] `lookupW_sound` and `lookupW_complete_aux` at `Obend/Core/Check.lean:138-239` closely duplicate `isRowW_sound` and `isRowW_complete_aux` at `Obend/Core/Check.lean:241-338`, including their strong-induction cycle arguments.
[READ] `Check.infer` and `Bidirectional.elaborate` provide two large overlapping executable implementations of the typing rules with different conversion and annotation policies.
[READ] Every typing-rule change consequently requires two implementation audits even where both checkers construct the same `PartialTyping` relation.
[READ] `reusable_lambda_capture_rule` at `Obend/Core/Check.lean:948-959` carries typed, safe, and valid hypotheses that its proof never uses.
[READ] That theorem is only a rewrite of `reusableAllowed` under `annotation.reuse = .reusable`, not a theorem that needs a lambda derivation.
[READ] `agree_never_manufactures_shareability` at `Obend/Core/Check.lean:969-974` is a second name for the immediately preceding `agree_shareable` proof with no additional content.
[READ] `Obend/Core/Code.lean` combines syntax codecs, Merkle hashing, checked import, annotation serialization, diagnostics, and mirrors in one 1,263-line public module.
[INFERRED] That concentration makes the version-skew and duplicated-schema defects easier to miss and forces consumers of one facility to depend on all the others.

## 4. The first ten changes

1. [READ] Replace the representative-only schema at `Obend/Core/Code.lean:443-476` with a version covering every shape, list, tag, and payload encoding rule, and strengthen `encodingVersion_binds` to quantify over the complete codec.
2. [READ] Make `argumentAllowed` at `Obend/Core/Check.lean:399-403` return a typed failure reason consumed by both call sites at `Obend/Core/Bidirectional.lean:311-312,406-407`, so activity, capture, sharing, and linear-use refusals cannot diverge from the Boolean rule.
3. [READ] Correct the expected and actual operands in the empty-row refusal at `Obend/Core/Bidirectional.lean:706-707` and add a kernel-checked diagnostic example.
4. [READ] Make `create` at `Obend/Kind.lean:122-125` reject kind-name clashes before returning an instance, matching the invariant enforced by `effectiveOf` at `Obend/Kind.lean:157-160`.
5. [READ] Make kind pins cover the ancestor versions used by `effectiveOf` and reject stale pins in `dispatch` at `Obend/Kind.lean:157-165,188-192`, so one accepted pin identifies one effective law and one dispatch decision.
6. [READ] Replace the first-arm preview and subsequent full `checkArms` pass at `Obend/Core/Bidirectional.lean:675-689` with one incremental arm derivation that reuses the synthesized first result.
7. [READ] Replace fuel-only recursive recomputation in `kindPrecedence` at `Obend/Kind.lean:129-145` with memoized graph traversal carrying explicit visiting and completed states.
8. [READ] Construct only reachable stream nodes and hoist shared label and residual computations at `Obend/Core/TypeGraph.lean:54-60,81-85` before invoking finite agreement.
9. [READ] Carry source positions in reverse inside `elaborate` and reverse them only at annotation lookup or refusal boundaries, eliminating the repeated `path ++ [n]` copies at `Obend/Core/Bidirectional.lean:263-749`.
10. [READ] Narrow the blanket `@[expose] public section` usage beginning at `Obend/Core/Code.lean:31`, `Obend/Core/Bidirectional.lean:25`, `Obend/Core/Check.lean:4`, and the other reviewed modules to a deliberate public API with private test fixtures and proof internals.
