# Hostile review of the Objective Bend Lean library

## Scope

READ: I read the requested Obend documentation and the statements in `Obend/Slot.lean`, `Obend/Slot/World.lean`, `Obend/Slot/Integrity.lean`, `Obend/Core/Proofs/Substitution.lean`, and `Journal/Journal.lean`.

READ: I also read `Journal/Export.lean`, the journal report, the Core4 slot instance, and the extraction-evidence definitions needed to assess D5.

READ: I treated `Obend/Spec`, `Obend/Core/Graded.lean`, `Obend/Core/Traverse.lean`, and `Obend/Tactic` as in flight.

INFERRED: The nanodregg comparison is limited to the theorem shapes quoted in `World.lean` and `REPORT-20261031.md` D15 because this session was denied direct access to the sibling checkout.

## 1. The weight-bearing statements

### `slot_repair`

READ: `slot_repair` at `lean/Obend/Slot.lean:131` quantifies over every view type, support type, candidate type, slot, support predicate, view relation, current view, and candidate.

READ: Its first conjunct says that reading a candidate as usable is equivalent to passing the judge and having every cited support hold.

READ: Its second conjunct says that a blocked reading supplies a nonempty list containing exactly the cited supports that do not hold.

READ: Its third conjunct says that a support already false and satisfying `Permanent` remains a named blocker at every later view, provided the candidate still passes the judge.

READ: Its fourth conjunct says that any candidate already computed as usable reads as usable with the evidence computed by `Slot.evidence`.

INFERRED: The first, second, and fourth conjuncts are unfoldings of `read`, `usable`, `dead`, and `evidence`, while `Permanent` and the judge hypothesis do the work in the third.

INFERRED: A slot with no supports and a constantly true judge satisfies the first and fourth conjuncts trivially and makes the blocked-reading conjuncts vacuous.

INFERRED: An empty `later` relation discharges every cross-view content of the third conjunct.

INFERRED: The theorem has no stored-selection transition, no persistent slot state, and no repair operation, since the fourth conjunct merely passes a candidate to `read` under `some`.

INFERRED: The name `slot_repair` therefore denotes a collection of reading and permanence lemmas rather than a theorem that a stored object repairs across a history.

### `read_blocked_names`

READ: `read_blocked_names` at `lean/Obend/Slot.lean:106` assumes that `S.read holds (some c)` is already `.blocked c' d` and concludes that `c' = c`, that `d` is nonempty, and that membership in `d` is exactly membership in the candidate's dead supports.

INFERRED: The equality hypothesis does all the work by exposing the branch of `read` that produced `.blocked`.

INFERRED: A candidate with no supports or with every support live cannot satisfy the blocked-reading premise, so the theorem is vacuous for that candidate.

INFERRED: A constantly true judge removes only the `.rejected` alternative and does not by itself make a blocked reading with dead supports trivial.

INFERRED: This is a constructor-inversion lemma and supplies no independent existence, completeness, or repair result beyond the definition of `read`.

### `check_msubst`

READ: `check_msubst` at `lean/Obend/Core/Proofs/Substitution.lean:1898` quantifies over an annotated template, a context, two fuel amounts, a checking certificate, and an arbitrary partial substitution from hypothesis indices to annotated terms.

READ: The template premise requires `check t Ψ n = some c`.

READ: The substitution premise requires every filling to be closed and to check at fuel `m` under the template's assumptions at exactly the type assigned to its hypothesis by `Ψ`.

READ: The conclusion produces a certificate for `msubst σ t` at fuel `n + m`, preserves the template's checked type, and bounds the resulting use vector pointwise by the template's use vector.

INFERRED: Closedness prevents a filling from capturing or duplicating the template's free hypotheses, shared assumptions prevent a change of type-variable interpretation, exact hypothesis typing prevents an unchecked conversion at the join, and the added fuel pays for both checking runs.

INFERRED: Taking `σ` to be constantly `none` makes the filling premise vacuous and reduces the conclusion to checking the unchanged template, but `fuel_tooth` also supplies an actual filled term that is accepted at fuel 3.

INFERRED: The statement is therefore not satisfied only by the empty substitution or by a constantly successful judge.

READ: `fuel_tooth`, `open_filling_tooth`, and `assumptions_tooth` at `lean/Obend/Core/Proofs/Substitution.lean:1961`, `:1983`, and `:2006` respectively rule out dropping the fuel, closedness, and assumptions conditions.

INFERRED: This is a substitution theorem for a fuelled algorithm rather than a fuel-free substitution theorem for meaning.

READ: The separate `calculus_typed_msubst` at `lean/Obend/Slot/Core4.lean:100` now states the fuel-free law over `Calculus.Typed`.

INFERRED: `UsesLE c'.uses c.uses` is sufficient to reuse the template's safety checks but does not provide exact linear-use accounting after substitution.

### `slotFiller_integrity` and the collapse of B4′

READ: `Integrity.contextual` at `lean/Obend/Slot/Integrity.lean:59` quantifies over every slot, view, and candidate order.

READ: Its success clause requires the selected candidate to be in the order, pass the judge, have all supports live, and be the head of the filtered usable order.

READ: Its refusal clause requires every candidate in the order to have some entry in the refusal whose listed facts are dead cited supports, with an empty list permitted only when the judge rejects the candidate.

READ: `Integrity.repair` at `lean/Obend/Slot/Integrity.lean:68` separately requires retired-support exclusion at later views and requires some successful filling whenever a usable candidate is in the order.

READ: `slotFiller_integrity` at `lean/Obend/Slot/Integrity.lean:106` proves both predicates for the filler that selects the first usable candidate.

INFERRED: The first repair clause already follows from `Integrity.contextual`, because a successful fill would have every support live at the later view while `dead_behind_forever` makes the retired support false there.

INFERRED: The second repair clause also follows from `Integrity.contextual`, because a usable candidate has a true judge and no dead supports, so every refusal witness `d` for that candidate must be empty and must simultaneously imply a false judge.

INFERRED: Since `F.fill` is either `.ok` or `.error`, ruling out `.error` for a view with a usable candidate already gives the required existential success.

INFERRED: `Integrity.repair F` is therefore a corollary of `Integrity.contextual F` for every `Filler` over every `World`, and `Integrity F` is logically equivalent to `Integrity.contextual F`.

INFERRED: The claimed conjunction B4 ∧ B4′ consequently adds no independent repair condition to B4.

INFERRED: The proof of `slotFiller_integrity` uses the definitions of selection and the retirement laws, but its separate repair conjuncts do not identify an additional property that a contextually correct filler could fail.

INFERRED: On an empty view type, every `Filler` satisfies `Integrity`, because all the view-indexed success, refusal, and repair obligations are empty.

INFERRED: A one-candidate world with no supports and a constantly true judge also satisfies the property without exercising withdrawal or refusal.

READ: `toy_repair` at `lean/Obend/Slot/Integrity.lean:203` is a conjunction of three decidable equalities about calls at heights 0 and 1.

INFERRED: That example observes an alternative selection after revocation but does not relate a persistent stored selection to an audited history transition.

### The three `¬ Integrity` floors

READ: `not_integrity_credulousHoles` at `lean/Obend/Slot/Integrity.lean:212` refutes the support-ignoring filler by selecting Alice at height 1 and contradicting the contextual success requirement that Alice's retired grant hold.

READ: `not_integrity_firstCandidate` at `lean/Obend/Slot/Integrity.lean:218` uses the same dead-support contradiction for the filler that ignores both supports and judge.

READ: `not_integrity_blindRefusal` at `lean/Obend/Slot/Integrity.lean:227` refutes an empty refusal for Alice alone at height 1 because the formal refusal clause requires either a nonempty dead-support list or a false judge.

INFERRED: The first two floors exercise only the support conjunct and do not test the judge conjunct or the first-usable conjunct.

READ: The toy slot's judge is constantly true at `lean/Obend/Slot/Integrity.lean:196`, so no floor can detect a filler that ignores judge failures.

INFERRED: No floor tests selection of the second usable candidate ahead of the first.

INFERRED: No floor exercises `Integrity.repair` as an independent condition, because that predicate is already implied by contextual integrity.

PROPOSED: Add a support-respecting but judge-ignoring filler and a second-usable-first filler as separate mutations.

PROPOSED: Prove `Integrity.repair F` from `Integrity.contextual F` as an explicit redundancy tooth before claiming that the floor distinguishes contextual integrity from repair.

### `verdict_unaffected_iff`

READ: `verdict_unaffected_iff` at `lean/Journal/Journal.lean:198` quantifies over an arbitrary new export and candidate and equates a `.unaffected` verdict with a usable slot reading.

READ: The journal slot's judge is constantly `true` at `lean/Journal/Journal.lean:164`.

INFERRED: Both sides of the equivalence reduce to `slot.dead (holdsIn new) c = []`, so the proof is a `P ↔ P` coherence result after unfolding.

INFERRED: A candidate with empty statement and proof support lists is `.unaffected` at every new export, including an empty export.

READ: The surrounding `report` handles a theorem's own changed or missing row separately at `lean/Journal/Journal.lean:265`, so the bridge theorem does not itself claim to classify revision or removal.

INFERRED: The theorem says nothing about whether `candidateOf` included every semantic dependency or whether equal hashes imply equal kernel meanings.

### `verdict_blocked`

READ: `verdict_blocked` at `lean/Journal/Journal.lean:207` assumes that the verdict is `.statementCited dead` or `.proofCited dead` and concludes that the slot read is `.blocked c dead`.

INFERRED: The verdict hypothesis supplies the same list that `verdict` selected from `slot.dead`, and the constantly true judge then makes the corresponding read blocked by definition.

INFERRED: The theorem is another coherence result between two presentations of the same computed list rather than a correctness theorem for dependency analysis.

INFERRED: In particular, it does not prove that every changed definition reachable from the theorem appears in `dead`.

### The journal closure omits reachable dependencies

READ: `closure` at `lean/Journal/Journal.lean:99` starts with fuel `E.size + seeds.length + 1` and decrements that fuel on every stack pop, including pops of names already in `seen`.

INFERRED: A convergent acyclic graph can therefore exhaust the fuel before visiting every reachable row even when every individual citation list is duplicate-free.

INFERRED: For an explicit counterexample, let `R` cite `[A,B,C,D,Z]`, let each of `A`, `B`, `C`, and `D` cite only `X`, and let `X` and `Z` cite nothing.

INFERRED: That export has seven rows and gives the single seed `R` a fuel of nine.

INFERRED: The walk visits `R`, `A`, `X`, `B`, duplicate `X`, `C`, duplicate `X`, `D`, and duplicate `X`, then returns with `Z` still on the stack.

INFERRED: `candidateOf` can consequently omit `Z` even though `Z` is reachable from the theorem through `R`'s meaning edges.

INFERRED: If only `Z` changes in the new export, every recorded support can still hold and the journal can report `.unaffected` for the exact transitive-dependency change its documentation claims to detect.

PROPOSED: Bound the walk by the number of seeds plus the total length of all citation lists, or replace the fuel scheme with a worklist whose termination measure tracks unvisited rows.

PROPOSED: Prove a closure-completeness theorem stating that every finite meaning-edge path ending at a row is represented in the computed support set.

PROPOSED: Add the graph above as a kernel-evaluated negative test for the current implementation and a positive test after the repair.

## 2. Whether `World` abstracts the kernels' guarantees

READ: `World` at `lean/Obend/Slot/World.lean:39` supplies cells, pins, a support's cell, per-view pins, per-view support truth, and an arbitrary step relation.

READ: `holds_congr` requires equal pins for a support's cell to determine equal support truth, `retired_dead` requires a `none` pin to make every support of that cell false, and `retired_step` preserves `none` across one step.

INFERRED: These laws are sufficient for the local theorems about support congruence and terminal retirement that `World.lean` actually states.

INFERRED: They are not an abstraction of forward-only version history, because no law orders non-retired pins or prevents an old pin from returning.

INFERRED: A world with views in `Nat`, steps from `n` to `n+1`, and a live pin alternating between two values on successive views satisfies all three laws while allowing a support for the first pin to become false and then true again.

INFERRED: `slotFiller_integrity` remains valid for that cyclic world because `Integrity.repair` speaks only about `none` pins, while the intended property that a stale justification stays stale fails.

READ: `REPORT-20261031.md` D15 explicitly says that nanodregg's non-return-up-to-collision version law was omitted.

INFERRED: The class therefore captures a retirement fragment of the quoted kernel guarantee rather than the full `stale_behind_forever` property described by the project documentation.

INFERRED: A nonempty constantly live model with one cell, one pin, one always-true fact, and arbitrary steps satisfies the class without exercising any history constraint.

INFERRED: The word `audited` has no formal content in `World`, since `Step` is an arbitrary relation with no log, authorization, provenance, or reachability hypothesis beyond the retirement law.

INFERRED: The empty view type is also admitted, making every view-indexed `Integrity` proposition vacuous there.

READ: D15 also records that a hash-backed instance would owe a collision disjunct that the exact-pin class does not express.

PROPOSED: Add a version order or behind relation with the kernel's actual non-return law, and state explicitly whether hash collisions are assumptions, disjuncts, or outside the model.

PROPOSED: Keep terminal retirement as a separate law rather than treating it as a substitute for stale-version permanence.

PROPOSED: Instantiate the strengthened interface with nanodregg's real history and minidregg's `ObjectHistory` before calling B4/B4′ a theorem about either kernel.

## 3. Module discipline and D5

READ: The discipline in `REPORT-20261030.md` §2 places every declaration in a definitional module under `@[expose] public section` and uses selective visibility mainly in modules classified as proof modules.

INFERRED: Expose-all is a defensible migration expedient for definitions that downstream proofs and kernel teeth must reduce, but it is not a precise interface discipline.

READ: Proof-heavy modules such as `Core.Check`, `Core.Invariant`, and `Digest.Cshake256.Fast` are themselves in exposed sections, so the definitional/proof distinction does not match the actual declaration contents.

INFERRED: Moving their general lemmas into ordinary proof modules would prevent proof-only edits from becoming part of the exposed computational interface.

INFERRED: The right unit for `@[expose]` is the individual definition whose body a downstream reduction needs, not the module as a whole.

PROPOSED: Keep public theorem statements available without exposing proof bodies, expose only computational API definitions, and keep implementation helpers private or unexposed unless a measured consumer needs their bodies.

PROPOSED: Use `public import` only for dependencies that occur in the public interface rather than re-exporting every implementation dependency by default.

READ: D5 makes the constructors of `ExtractionWith` and `ExecutionWith` public so exposed extraction functions can construct their results.

READ: `ExtractionWith` contains a proof that `completeWith` returns exactly its `result`, and `ExecutionWith` contains both a proof of its exact `forceWith` outcome and an `ExtractionWith` value at `lean/Obend/Core/Data.lean:144` and `:156`.

INFERRED: A downstream module can invoke those constructors only by supplying the same exact-run and exact-extraction proofs that the smart constructors would have supplied.

INFERRED: Public constructors therefore do not by themselves weaken the later soundness theorems, which consume those proof fields rather than an unrecorded promise of construction by `executeWith`.

INFERRED: The report's concern about forging an `ExecutionWith` is misplaced as a logical-soundness concern, although it remains valid if the intended object is an unforgeable provenance or authority token rather than semantic run evidence.

PROPOSED: Retain public constructors for proof-carrying semantic evidence, and use a separate opaque capability type only if construction provenance itself is a security property.

## 4. Ranked requirements before calling this a contribution

### 1. Repair the journal's dependency correctness

PROPOSED: Fix the deterministic closure under-approximation, prove reachability completeness, and make the two verdict bridge theorems secondary to a theorem connecting export changes with actual transitive kernel dependencies.

PROPOSED: Treat equal 64-bit noncryptographic hashes as probabilistic evidence rather than equality of meaning, since `Row.meaning` equality is the only test used by `holdsIn` and the current bridge theorems cannot detect collisions.

### 2. Give repair an independent statement

PROPOSED: Replace the redundant `Integrity.repair` with a property of an explicit stored selection and a history transition, including persistence while blocked, selection of an alternative after withdrawal, and the exact relation between the old and new stored states.

PROPOSED: Add a filler that satisfies the new contextual clause but fails the new repair clause so the conjunction has a demonstrated independent floor.

### 3. Prove the abstraction at real kernels

PROPOSED: Supply non-toy `World` instances for nanodregg and minidregg, including version non-return and any collision assumptions, and derive their integrity statements from the actual receive and history theorems rather than from a parallel toy model.

### 4. Connect selection integrity to executed programs

PROPOSED: State the top-level theorem over `Slot.resolve` and the `interp`/`RunsR` semantics so an executed hole is filled by the body of the first usable candidate and an executed refusal carries the required support coordinates.

PROPOSED: Include a persistent-object scenario in which an audited step withdraws a support and the next run uses the repaired stored selection, since the present `toy_repair` observes three independent function calls instead.

### 5. Separate algorithmic coverage from semantic claims in the contribution text

PROPOSED: Describe `check_msubst` as a fuel-bounded checker theorem and reserve the unqualified substitution claim for `calculus_typed_msubst`, with the recognized-fragment completeness premise explicit wherever admission is discussed.

PROPOSED: Do not present `UsesLE` as exact resource preservation, and add an exact use-vector theorem only if exact linear accounting is part of the claimed contribution.
