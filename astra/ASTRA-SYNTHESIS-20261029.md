# Astra synthesis — 2026-10-29

[READ: /Users/ember/dev/obend/astra/fareoo/.git/config] The archive checkout used here is a local clone of /Users/ember/dev/fareoo.
[READ: /Users/ember/dev/obend/astra/fareoo/.git/shallow] Its shallow boundary is d7ddf53fbdb818377b75c3d2bfafd14a072a0051.
[INFERRED] The READ claims below describe inspected sources rather than newly executed demonstrations.

## A. THE THESIS

[INFERRED] THESIS.md section 1 mistakes a restriction on one representation of open recursion for a restriction on open recursion itself.
[READ: /Users/ember/dev/minidregg/Theory/ObjectiveBendOpenRecursion.lean] Core4's mixBody uses the bound self twice in the expression upper self (lower self super).
[INFERRED] That expression fails Bend's live affinity discipline when self contains runtime functions.
[READ: /Users/ember/dev/bend/guide/GUIDE.md, Closures] Bend permits repeated calls to top-level definition names.
[READ: /Users/ember/dev/bend/guide/GUIDE.md, Quantities] Bend also permits repeated use of Data values explicitly bound with quantity +.
[READ: /Users/ember/dev/bend/guide/GUIDE.md, Templates] A closed template argument is substituted as syntax rather than passed as a runtime closure.
[INFERRED] The freely reusable executable entity is therefore a definition name, not an arbitrary captured function value.

[READ: /Users/ember/dev/bend/paper/BendTT.pdf, pages 3–4] A BendTT book is an ordered collection of closed definitions referenced by names.
[READ: /Users/ember/dev/bend/paper/BendTT.pdf, page 6] A live reference must name an earlier definition or a structurally descending self-call.
[READ: /Users/ember/dev/bend/paper/BendTT.pdf, page 4] Mutually recursive datatype definitions use references in dead positions.
[INFERRED] Those type-level cycles do not license arbitrary cycles among live methods.
[INFERRED] Affinity and descent impose distinct restrictions on the proposed object encoding.

[INFERRED] Bend cannot directly provide Core4's general first-class lazy fix/mix over freely reusable records of captured methods while preserving that representation and remaining inside its terminating live fragment.
[INFERRED] Bend can express a statically composed family's late-bound method calls through generated top-level names.
[INFERRED] Bend can express runtime selection within a known family through a Data receiver tag and a top-level dispatcher.
[INFERRED] Bend can represent an open program as Data and execute a bounded portion with a total interpreter.
[INFERRED] The interpreter construction moves general recursion into represented machine state rather than making an unrestricted live fixed-point combinator sound.
[INFERRED] “Open recursion is non-affine by construction” is therefore false as a statement about expressibility.
[INFERRED] “Core4 deliberately gives reusable self a non-affine source semantics” is the defensible replacement.

[READ: /Users/ember/dev/minidregg/docs/OBJECTIVE-BEND.md, Writing a program] The Review example makes Twice call the final augmented review method twice.
[INFERRED] A direct Bend specialization can define baseReview(n) = n + 1, finalReview(n) = baseReview(n) + 1, and finalTwice(n) = finalReview(finalReview(n)).
[INFERRED] A Bend author can instead abstract the repeated application with a closed ~review template argument.
[INFERRED] Both constructions bind the inherited method to the chosen final implementation at specialization time.
[INFERRED] Changing that final implementation requires a new specialization rather than mutating the meaning of an already compiled name.
[INFERRED] A receiver with runtime configuration requires that configuration as an explicit argument to the lifted definitions.
[INFERRED] A runtime-varying family requires explicit tags and dispatch rather than a reusable record of native closures.
[INFERRED] Cyclic method calls require structural descent, a fused dispatcher with fuel, or the explicitly unsafe route.
[INFERRED] Today the Bend user must write this binding and dispatch machinery manually.

[READ: /Users/ember/dev/redregg/intent/WHY-OBJECTIVE-BEND-20261003.txt] The earlier architectural argument explicitly allows strict implementations with indirection.
[INFERRED] That argument is more precise than the draft thesis's opposition between laziness and parallelism.
[INFERRED] Lazy selection of demanded work and parallel execution of independent demanded work are compatible.
[INFERRED] Laziness is necessary for the stated partial-object observations, not for every possible law system.
[READ: /Users/ember/dev/obend/astra/fareoo/raw/mirrors/ltuo/2026-10-03/ltuo-readable.txt, 7.3.5.2] Faré's linearity constrains the composition algorithm to account for each ancestor's contribution once.
[INFERRED] This property complements ownership affinity rather than replacing it.
[READ: /Users/ember/dev/bend/guide/GUIDE.md, Laws and Proofs] Bend laws quantify over inputs.
[READ: /Users/ember/dev/bend/guide/GUIDE.md, Modules] A law can receive its proof in another module.
[INFERRED] Calling them merely closed propositions proved by whoever edits a closed program misdescribes their modular possibilities.
[PROPOSED] The thesis should be that extensible specifications organize cooperation while affine computations conserve concrete resources.

## B. THE SEAM: LEAF BEND

[PROPOSED] Objective Bend should give a prototype a first-class specification paired with its lazily constructed target.
[PROPOSED] Ordinary member access should project the target through that pair.
[PROPOSED] Reflection should project the specification without forcing the target.
[PROPOSED] The reflective prototype should sit inside the recursive knot so self can inspect the specification governing its own construction.
[READ: /Users/ember/dev/minidregg/Theory/ObjectiveBendOpenRecursion.lean] instantiatePrototype already describes an explicit knot whose self is the whole prototype.
[READ: /Users/ember/dev/minidregg/docs/objective-bend/REFLECTION.md] The raw prototype constructor independently pairs its specification and target without establishing construction provenance.
[PROPOSED] The public instantiation operation should establish that provenance by construction.
[PROPOSED] An arbitrary pair should remain distinguishable from an instantiated prototype.

[PROPOSED] The layer should admit ordinary Bend definitions as targets through a typed leaf interface.
[READ: /Users/ember/dev/bend/guide/GUIDE.md, Under the Hood] Bend's compiler targets C, Metal, CUDA, and JavaScript.
[PROPOSED] Leaf bindings should use that compiler's supported targets.
[PROPOSED] A leaf binding should identify the exact definition, its argument ownership, its result type, and its checked laws.
[PROPOSED] A concrete invocation should force only the arguments required by that interface.
[PROPOSED] Immutable reusable values should cross as Bend Data where their representations satisfy Bend's kind checker.
[PROPOSED] Arrays, native closures, and handles should cross through explicit ownership transfer.
[PROPOSED] A leaf that retains an owned resource should return its successor ownership with the result.
[PROPOSED] The unrestricted layer should forbid storing such ownership inside a duplicable thunk.
[INFERRED] Serializing an owned value does not make its ownership duplicable.
[PROPOSED] A shared object reference should carry identity while each effect separately checks current authority.

[INFERRED] The boundary is a typing and invocation boundary rather than a line between two source files.
[PROPOSED] Source self should remain reusable across specification construction and pure demand evaluation.
[PROPOSED] Each concrete leaf invocation should obey Bend's resource discipline.
[PROPOSED] Effects should cross back as proposed actions for the object kernel to admit.
[PROPOSED] Affine protocol responses should remain consume-once even when their surrounding document is reusable.
[READ: /Users/ember/dev/minidregg/docs/OBJECTIVE-BEND.md, Activities] Mini already refuses an effect forced through a shared update cell.
[INFERRED] This separation preserves the difference between sharing a computation's pure answer and replaying its effect.

[PROPOSED] “Objective Bend elaborates a book of top-level Bend definitions” should describe the specialization path.
[INFERRED] Faré's account of C++ templates supports that staging picture.
[READ: /Users/ember/dev/obend/astra/fareoo/FAREOO.md, section 6] The archive describes C++ templates as a lazy prototype language operating at compile time.
[INFERRED] The picture becomes too small when it excludes runtime construction of specifications or inspection of unfinished targets.
[PROPOSED] The implementation should retain a first-class specification graph after emitting a book.
[PROPOSED] Specialization should map self references to the final family's generated names.
[PROPOSED] It should map super references to names for the appropriate inherited prefix.
[PROPOSED] Repeated instantiations with the same semantic inputs should share generated code.
[INFERRED] Different final-self environments can require different specializations.
[READ: /Users/ember/dev/minidregg/docs/objective-bend/MODULAR-TYPING.md] Mini's template design already trades runtime polymorphism for separately checked instantiated code.
[INFERRED] Code size, recompilation, and preserved reflective provenance are costs of the staged design.

[READ: /Users/ember/dev/bend/guide/GUIDE.md, Templates] A ~ argument cannot capture a caller's local variable.
[READ: /Users/ember/dev/bend/guide/GUIDE.md, Templates] A template can call only templates declared above it.
[INFERRED] Lambda lifting must therefore expose runtime environments as arguments rather than hiding them inside template syntax.
[READ: /Users/ember/dev/bend/guide/GUIDE.md, Recursion and Termination] Checked live definitions cannot be mutually recursive.
[PROPOSED] The linker should emit acyclic calls in definition order.
[PROPOSED] It should fuse a mutually recursive component into one tagged dispatcher when ordinary structural descent cannot express the component.
[PROPOSED] General lazy computation should use an explicit machine state containing code, environments, heap addresses, and continuation frames.
[PROPOSED] A total run operation should recurse on a leading Nat fuel parameter and return either a result or the retained state.
[PROPOSED] Fuel exhaustion should report suspension rather than a false proposition or a fabricated value.
[PROPOSED] A global execution budget should count machine transitions rather than merely recursive depth.
[INFERRED] Duplicating a smaller fuel value into two branches does not bound their combined work by the original fuel.
[PROPOSED] Leaf work should have its own accounted cost within that budget.

[PROPOSED] The represented heap should record unforced, evaluating, and completed cells.
[PROPOSED] A mutable Bend array implementing that heap should have one threaded owner.
[PROPOSED] Shareable heap addresses should identify source computations without duplicating the heap owner.
[INFERRED] A Data encoding of closure syntax is compatible with Bend's ban on copying native function values.
[INFERRED] Its interpreter must still establish the source closure's capture discipline.
[PROPOSED] New runtime specifications should enter the represented machine before any optional specialization.
[PROPOSED] Recompilation should be an optimization whose absence never changes source meaning.
[PROPOSED] A finished represented run should correspond to a source observation.
[PROPOSED] Every finite source observation should be reachable through sufficiently provisioned resumptions.
[INFERRED] These two requirements prevent a bounded interpreter from satisfying its contract by suspending forever.

[READ: /Users/ember/dev/bend/guide/GUIDE.md, Recursion and Termination] @unsafe allows unrestricted recursion while removing the affected definitions from Bend's proof guarantees.
[PROPOSED] The checked Leaf Bend path should use explicit suspension instead of @unsafe.
[PROPOSED] User-selected unsafe leaves should carry an executable-only contract.
[INFERRED] Their results cannot acquire checked laws merely by passing through an Objective Bend wrapper.
[READ: /Users/ember/dev/bend/paper/BendTT.pdf, pages 1–3] BendTT's live/dead boundary prevents inconsistent dead terms from serving as live evidence.
[PROPOSED] The partial object evaluator should remain outside that logical evidence boundary.
[PROPOSED] Laws about partial source programs should be statements about their syntax, observations, and transitions in a total proof system.

[PROPOSED] Laziness should stop at the strict input contract of each ordinary leaf call.
[PROPOSED] A field not selected by the object evaluator should remain unforced.
[PROPOSED] Once a leaf demands a finite value, materialization should complete before native execution receives that value.
[PROPOSED] A streaming interface should expose explicit resumptions rather than pretend to pass an unrestricted native thunk.
[PROPOSED] Independent materialized leaf calls should use Bend's parallel execution where their workloads suit it.
[INFERRED] Arbitrary object-graph traversal does not thereby become a balanced GPU workload.
[READ: /Users/ember/dev/minidregg/docs/objective-bend/REFLECTION.md] Reflective observation distinguishes different associations of specification composition.
[PROPOSED] Optimizing generated execution should preserve the original specification graph for reflective observations.
[PROPOSED] Resource-equivalence claims should be stated separately from equality of completed answers.

[PROPOSED] A Bend law certificate should bind the exact translated book and theorem statement.
[PROPOSED] The leaf wrapper should separately establish the relationship between that statement and the Objective interface.
[READ: /Users/ember/dev/bend/README.md, Limitations] Bend distinguishes laws about its semantics from the behavior of its compiler backends.
[READ: /Users/ember/dev/bend/guide/GUIDE.md, Laws and Proofs] The source translation checked by --verdict is not itself proved correct.
[PROPOSED] Backend admission should require a refinement argument or independent checking of the result used for a governed write.
[PROPOSED] Arithmetic and serialization should be explicit parts of that interface.
[INFERRED] A successful BendTT proof alone does not prove that a GPU binary implemented the intended source law.

[PROPOSED] On day one, a Bend author should import an existing leaf without rewriting it.
[PROPOSED] The author should extend its surrounding specification from another package.
[PROPOSED] The author should obtain generated self/super bindings instead of writing the dispatcher plumbing.
[PROPOSED] The author should attach the leaf's laws to the same document that explains and uses it.
[PROPOSED] The resulting package should export ordinary Bend definitions for existing Bend consumers.
[INFERRED] The immediate gain is reusable composition and maintained contracts around code the user already has.

## C. CROSS-PACKAGE EXTENSION

[READ: /Users/ember/dev/minidregg/docs/OBJECTIVE-BEND.md, The package is a specification] Mini's package root is a record fixed point that its surface cannot name from another package.
[READ: /Users/ember/dev/obend/astra/fareoo/AUDIT.md, Finding 1] The earlier audit diagnoses Mini's laws as replaceable or copied rather than inheritable.
[READ: /Users/ember/dev/delvetalk2/docs/AUTHORING.md, Composition] Delvetalk2 already makes a kind's law refer to its parent's law through under.
[READ: /Users/ember/dev/delvetalk2/docs/LAW.md, atom F] Those references are conjoined and bounded to four levels.
[INFERRED] The audit remains a reason for the construction rather than a timeless description of every later tree.
[INFERRED] THESIS.md understates the existing cross-author inheritance when it treats the entire capability as unbuilt.

[PROPOSED] Every package should export its root as an extensible specification value.
[PROPOSED] A reference such as papers.Report should denote an intention inside an explicit ecosystem environment.
[PROPOSED] That environment should resolve the intention to an exact specification revision for each admitted computation.
[INFERRED] An extensible name and an immutable revision commitment solve different problems.
[READ: /Users/ember/dev/obend/astra/fareoo/raw/mirrors/ltuo/2026-10-03/ltuo-readable.txt, 9.3.7] Faré situates coherent extension at the scale of a library or ecosystem.
[PROPOSED] A workspace should therefore extend one scoped ecosystem root rather than mutate a universal global namespace.
[PROPOSED] Different workspaces should be able to choose different extensions of the same intentions.
[PROPOSED] Closing a workspace should fix its resolution environment while evaluating its target lazily.
[PROPOSED] A recorded turn should retain that environment's commitment.

[PROPOSED] The surface should allow a stranger to write spec LabReport extends papers.Report, lab.Reviewed.
[PROPOSED] It should allow the same stranger to declare an inheriting law without copying the ancestor's clauses.
[PROPOSED] Qualified references inside inherited declarations should resolve through the final ecosystem self.
[PROPOSED] Explicit super references should preserve the inherited prefix within that environment.
[PROPOSED] Package boundaries should delimit publication and ownership rather than terminate open recursion.
[PROPOSED] A closure manifest should resolve symbolic package references to a finite set of source artifacts.
[PROPOSED] Mutually recursive value references should be represented inside that manifest without requiring circular content hashes.
[INFERRED] Cycles in value dependence are distinct from cycles in specification ancestry.

[PROPOSED] C4 should linearize the ordered ancestry DAG across all participating packages.
[PROPOSED] Ancestor identity should include the declaration lineage and its instantiation arguments.
[PROPOSED] A closure should select one revision for each such identity.
[PROPOSED] Incompatible revision requirements should produce a resolution refusal before evaluation.
[PROPOSED] An intentional fork should receive an explicit distinct identity.
[PROPOSED] Diamond ancestry should contribute a shared ancestor once.
[PROPOSED] Explicit repeated mix application should remain repeated application.
[READ: /Users/ember/dev/minidregg/Compiler/ObjectiveBendC4.lean] The C4 source states invariance for ordered presentations rather than bare unordered DAGs.
[PROPOSED] Local parent order and suffix declarations should therefore be committed semantic inputs.
[PROPOSED] An inconsistent order should return the participating declarations and contradictory precedence requirements.

[PROPOSED] Ordinary extension should remain able to replace behavior.
[PROPOSED] Adoption under an existing contract should require a new witness that the final composition satisfies that contract.
[READ: /Users/ember/dev/redregg/intent/WHY-OBJECTIVE-BEND-20261003.txt] The architectural argument distinguishes unrestricted construction from behavioral subtyping.
[INFERRED] Conjunction is a useful default for governing laws but not the definition of every modular extension.
[PROPOSED] Governing law inheritance should collect identified clauses through the same ancestry graph.
[PROPOSED] Default law combination should require every collected clause to admit the transition.
[PROPOSED] Its acceptance theorem should equate the effective judgment with the conjunction of the instantiated ancestor judgments.
[PROPOSED] The clause's type requirements should be instantiated against the final self.
[PROPOSED] Governing predicates should use a total judging fragment.
[PROPOSED] Resource exhaustion during judgment should prevent admission without asserting that the predicate is false.
[PROPOSED] A proof about an ancestor's old closed target should be reused only through a justified instantiation or preservation argument.
[INFERRED] Reusing a law's name does not preserve a proof after a method it depends on changes.

[PROPOSED] Orthogonal protocols should be first-class specifications of operations and their laws.
[PROPOSED] A third package should be able to supply a protocol implementation for a type declared by a second package.
[PROPOSED] That implementation should be selected in the ecosystem environment.
[PROPOSED] Competing implementations should require an explicit scoped choice rather than import-order priority.
[READ: /Users/ember/dev/obend/astra/fareoo/raw/mirrors/ltuo/2026-10-03/ltuo-readable.txt, 9.2.9] Orthogonal protocols remove the requirement that a type anticipate every future interface through ancestry.
[INFERRED] Protocol ownership, type ownership, and integration authority need not belong to the same person.

[PROPOSED] Installation should admit a typed composition together with its resolved sources, ancestry order, protocol choices, and discharged contracts.
[PROPOSED] The receiver should re-derive that composition from the committed source closure.
[PROPOSED] Each write should re-derive demanded slot selections from its authenticated view.
[PROPOSED] Each candidate should declare the typed context in which its body is valid.
[PROPOSED] Filling a slot should check the substitution from that context into the current environment.
[PROPOSED] It should judge the transition under the effective laws of that view.
[PROPOSED] Cached derivations should be keyed by all semantic dependencies.
[PROPOSED] A contextual thunk should retain the support footprint justifying its cached result.
[PROPOSED] Repair after a support change should agree with evaluation from scratch in the revised environment.
[PROPOSED] A refusal should identify the ancestor declaration, clause identity, source span, observed operands, and failed support.
[PROPOSED] A suggested repair should identify an available action without granting authority to perform it.
[INFERRED] Some refusals have no satisfying repair under the current laws.
[INFERRED] The draft's promise that every refusal hands back a yes is therefore too strong.

[PROPOSED] Following an intention's head should mean accepting a governed revision policy.
[PROPOSED] Installing a stronger law over existing state should establish that state's admissibility under the new regime.
[PROPOSED] A revision that requires migration should carry a state transformation judged under the object's upgrade policy.
[PROPOSED] Active computations should stay pinned to their original code until a declared transition point.
[PROPOSED] The transition should preserve pending effects and consume-once obligations.
[INFERRED] Neither source inheritance nor successful recompilation establishes safe live migration.

## D. DOCUMENT-TYPE THINKING

[PROPOSED] A document should be the ordinary persistent prototype through which a person encounters the language.
[PROPOSED] Its kind should supply extensible fields, methods, laws, and views.
[PROPOSED] A section should be a typed slot whose value is selected from justified candidates.
[PROPOSED] The document's rendered page should be a projection of those slots at a named view.
[READ: /Users/ember/dev/nanodregg/decisions/lang.md, LANG-83] Nano's section demonstration uses members' proposed bytes as candidates selected by an editor.
[READ: /Users/ember/dev/redregg/work/promo/DESIGN-CTX.md, section 2.1] The proposed slot descriptor includes its type, chooser, candidate source, justification, acceptance condition, lifetime, and patience.
[PROPOSED] These should be fields of one inspectable object rather than separate conventions for documents, programs, offers, and replies.

[PROPOSED] The written vocabulary should center on declarations that provide a value, name its reasons, and state who may select it.
[PROPOSED] A section declaration should specialize that vocabulary to document content.
[PROPOSED] A quote declaration should specialize it to content obtained through a source range.
[PROPOSED] A belief declaration should specialize it to a proposition supported by evidence tokens.
[PROPOSED] A law declaration should specialize it to a predicate governing a transition.
[PROPOSED] A method declaration should specialize it to a computation.
[PROPOSED] The words because, choose, extends, and amend should retain the same relationships across those declarations.
[INFERRED] One vocabulary does not require bytes, proofs, beliefs, and authority to become the same type.
[PROPOSED] The editor should generate these declarations from ordinary editing actions.
[PROPOSED] A person should be able to inspect and edit the generated declarations directly.

[PROPOSED] A quote should name a source identity, exact version, byte commitment, and selected range.
[PROPOSED] Verifying the quote should establish that its displayed content corresponds to those bytes.
[PROPOSED] Range relocation after edits should produce a new justified mapping rather than silently reuse old offsets.
[PROPOSED] A verified historical quotation should remain historically verified when its source acquires a later version.
[PROPOSED] A separate follows-current-source condition should become unsatisfied when that source moves.
[READ: /Users/ember/dev/breadstuffs/site/transclusion/README.md] The existing transclusion account distinguishes live-following references from pinned snapshots.
[INFERRED] THESIS.md's instruction to darken a quote whenever its source moves conflates those two meanings.
[PROPOSED] Revocation should affect the particular authority or endorsement named by the justification.
[INFERRED] Revoking an editor's present grant does not falsify the historical fact that the editor authored a paragraph.

[READ: /Users/ember/dev/nanodregg/decisions/lang.md, LANG-83] The section demonstration's critique admits that a candidate can cite a live cell without proving that the cell is its contributor's grant.
[PROPOSED] A document justification should therefore check the relationship among contributor, grant, permitted action, and target section.
[READ: /Users/ember/dev/nanodregg/decisions/lang.md, LANG-84] A cellLaw support establishes governance by an identified law rather than the truth of the law's informal name.
[PROPOSED] A behavioral justification should cite the law's checked meaning at the relevant revision.
[PROPOSED] A factual justification should cite the exact observation or attestation it relies on.
[PROPOSED] A withdrawn selection should preserve its text and reasons as history.
[PROPOSED] The current view should expose the failed reason alongside available alternatives.
[INFERRED] Repair availability does not imply that an authorized chooser will perform the repair.

[PROPOSED] An edit should be a patch over stable content and section identities.
[PROPOSED] Deletion should leave an explicit tombstone in retained history.
[PROPOSED] The merge category should use finite causally closed patch-event sets over a fixed schema as its objects.
[PROPOSED] Its arrows should be inclusions preserving event identity, bytes, and dependencies.
[PROPOSED] The pushout of two branches over their common base should be their union of identified events.
[PROPOSED] Every common extension should receive the unique inclusion from that union.
[PROPOSED] That construction should preserve both parents' contributions over their authenticated common base.
[PROPOSED] Materialization should retain contradictory concurrent edits as document alternatives.
[PROPOSED] Branches using different schemas should require checked transport to a common schema before this merge.
[PROPOSED] Incompatible contributions should remain represented as alternatives rather than be silently discarded.
[PROPOSED] The implementation should prove the universal property for its actual patch representation.
[INFERRED] Calling an arbitrary three-way merge a pushout would establish nothing.
[READ: /Users/ember/dev/breadstuffs/dregg-doc/README.md] The existing patch core represents conflicts as document state resolved by subsequent patches.
[PROPOSED] A section's chooser should resolve the resulting alternatives through the same selection operation used for ordinary candidates.
[PROPOSED] Publishing the selected result should still satisfy the page's laws.
[INFERRED] Algebraic merge does not merge permissions or authorize a write.

[PROPOSED] Laws should appear as readable lines on the page with inspectable executable meanings.
[PROPOSED] The page's kind should contribute inherited law clauses.
[PROPOSED] Every committed write should be judged by the applicable clauses regardless of its editor or agent.
[PROPOSED] Draft edits that violate a law should remain visible as drafts with the ancestor clause attached.
[PROPOSED] Adopting a revised kind should judge the existing document as well as future edits.
[READ: /Users/ember/dev/nanodregg/decisions/lang.md, LANG-92] The keeps construction connects a recognizable law shape to preservation of an invariant along a chain of admitted steps.
[INFERRED] This directly undermines the thesis's separation of civic laws from propositions about programs.
[PROPOSED] The document should display a law's theorem, its current invocation judgment, and its explanatory reading as distinct aspects of one declaration.

[PROPOSED] A belief should be a fact under named evidence tokens rather than an unqualified assertion of truth.
[PROPOSED] Independent tokens should remain independent supports for the same proposition.
[PROPOSED] Withdrawing one token should re-derive dependent conclusions from the surviving evidence.
[PROPOSED] Positive support cycles should not manufacture their own foundation.
[PROPOSED] Alternative consistent interpretations should remain separate candidates.
[PROPOSED] Inconsistent evidence and unfinished search should have different visible outcomes.
[READ: /Users/ember/dev/o7vn/native/oracle-logic/DEMOS.md] The reasoning laboratory distinguishes those outcomes and retains withdrawn evidence identities.
[INFERRED] DESIGN-CTX's depth-one support discipline does not by itself supply general belief revision.
[PROPOSED] Richer reasoning should supply checked justification objects to the slot interface.
[PROPOSED] A kernel should accept a skeptical conclusion only with evidence for its required universal claim.
[INFERRED] One supplied model establishes neither uniqueness nor truth in every model.

[PROPOSED] On day one, a person should open a local vault and create a page of an existing document kind.
[PROPOSED] Pasting a quotation should offer a pinned transclusion with its source range.
[PROPOSED] Inviting a collaborator should authorize candidate proposals for selected sections.
[PROPOSED] Choosing a proposal should show the evidence that makes it usable.
[PROPOSED] An offline merge should preserve incompatible edits as selectable alternatives.
[PROPOSED] A failed save should point to the inherited law line that refused publication.
[PROPOSED] Extending a kind should change the behavior available to pages that adopt that extension.
[PROPOSED] A Bend-backed index or calculation should be usable from the same page.
[PROPOSED] The vault should retain ordinary readable text alongside the typed history needed to reconstruct these relationships.
[INFERRED] A folder of Markdown alone cannot preserve the proposed semantics.

## E. TWO MATURE INSTANTIATIONS

[PROPOSED] The pair should be Objective Bend on its own Lean demand machine and Objective Bend on ordinary Bend.
[PROPOSED] Both should implement the same lazy source language and the same governed document interface.
[INFERRED] This comparison tests the value and cost of the affine execution boundary without changing the user's meaning.
[READ: /Users/ember/dev/nanodregg/decisions/lang.md, LANG-18] Nano's extend retains the old self of inherited fields.
[INFERRED] Comparing that behavior directly with final-self inheritance would conflate evaluator design with a different extension operation.
[INFERRED] A comparison between kernel and document justifications would likewise compare unequal evidence vocabularies rather than mature implementations of one system.
[PROPOSED] Both chosen implementations should support both kinds of justification.

[PROPOSED] The Lean instantiation should use direct graph sharing for source closures and recursive objects.
[PROPOSED] Its maturity should include a source semantics connected to the emitted core.
[PROPOSED] Its contextual selection should be covered by a statement over admitted history.
[PROPOSED] Its persistent checkpoints should preserve sharing, pending effects, and code revisions.
[PROPOSED] Its upgrades should carry an existing document without discarding identities or history.
[PROPOSED] Its reflective view should explain the exact composition currently running.
[READ: /Users/ember/dev/minidregg/docs/OBJECTIVE-BEND.md, What is proved] Core4's machine results already have soundness and finite-completeness statements against its reference semantics.
[INFERRED] Those statements are a foundation for maturity rather than proof of the entire document system.

[PROPOSED] The Bend instantiation should specialize suitable compositions to ordinary definitions.
[PROPOSED] It should execute remaining dynamic source behavior through the represented demand machine compiled by Bend.
[PROPOSED] It should preserve runtime specification construction without escaping to the Lean evaluator.
[PROPOSED] Its mature form should demonstrate resumable sharing under affine heap ownership.
[PROPOSED] It should expose inspectable books with their exact law obligations.
[PROPOSED] It should state correspondence for the source-to-book boundary.
[PROPOSED] Each supported native backend should state its own result and resource contract.
[READ: /Users/ember/dev/bend/README.md, Limitations] Current Bend 2 explicitly does not carry over HVM.
[INFERRED] “HVM/C backends” is therefore the wrong description of this pair's current Bend member.

[PROPOSED] Both should carry the same report through independent package extension, a diamond, protocol attachment, evidence withdrawal, offline conflict, law amendment, and schema migration.
[PROPOSED] The report should contain an unused cyclic field that does not prevent reading a good section.
[PROPOSED] It should contain a shared expensive field whose repeated selection preserves one thunk's identity.
[PROPOSED] It should use an owned leaf resource without making that resource copyable.
[PROPOSED] Its readers should be able to inspect why a section is selected after a restart.
[INFERRED] These are semantic demands that reveal architectural choices rather than a scorecard for declaring a winner.
[PROPOSED] The comparison should discuss where each design makes expression, explanation, implementation, and proof simpler.
[PROPOSED] Performance investigation should answer concrete questions raised by those complete experiences.
[INFERRED] A maturity comparison becomes informative when neither implementation is protected by an impoverished example.

## F. UPSTREAM

[PROPOSED] Build Objective Bend as its own language with Bend interoperation rather than begin with a permanent fork of ~/dev/bend.
[INFERRED] The proposed object semantics require an independently accountable language boundary even if much of its execution is delegated.
[READ: /Users/ember/dev/minidregg/docs/BEND-WORLD-LANGUAGE-20261003.txt] Mini explicitly treats Objective Bend as its own language with Bend as a starting calculus and execution option.
[READ: /Users/ember/dev/delvetalk2/README.md] Delvetalk2 identifies its edition as a Mini-derived language running on its own Lean call-by-need machine.
[READ: /Users/ember/dev/nanodregg/CHARTER.md] Nano describes itself as a focused rebuild of the end-computing system rather than the seed of every subsequent prototype.
[INFERRED] None of those commitments establishes a reason to inherit upstream Bend's language ownership as our product boundary.

[READ: /Users/ember/dev/bend/AGENTS.md] Upstream identifies bend.ts as the human-written parser, theory, and checker.
[READ: /Users/ember/dev/bend/AGENTS.md] Its permanent bend.ts token cap is 48k.
[READ: /Users/ember/dev/bend/AGENTS.md] Changes to those caps are reserved to Taelin.
[READ: /Users/ember/dev/bend/README.md, Limitations] The compiler is described as 99% AI-written.
[READ: /Users/ember/dev/bend/README.md, Limitations] The compiler is described as not fully audited.
[INFERRED] The 99% statement is about the compiler rather than an account of authorship for the entire language kernel.
[INFERRED] The engineering consequence is a backend trust obligation rather than a judgment about AI authorship.
[INFERRED] A permanent fork would add responsibility for compiler maintenance without eliminating that obligation.
[READ: /Users/ember/dev/bend/guide/GUIDE.md, Modules] Bend already provides content-addressed packages through its hub.
[INFERRED] Sharing that distribution surface is more useful than making ecosystem participation depend on a new compiler fork.

[PROPOSED] A Bend user should receive usable Bend exports from our package composition.
[PROPOSED] The same user should be able to inspect inherited laws and their proofs in our document view.
[PROPOSED] A third party should be able to add a protocol implementation without editing the leaf author's package.
[PROPOSED] Upstream-facing contributions should include concrete compiler defects or interfaces discovered by those uses.
[PROPOSED] Backend adapters should pin exact supported compiler versions.
[PROPOSED] A narrow compatibility patch should remain possible when a concrete obstruction requires one.
[INFERRED] That patch does not require adopting permanent divergence as the initial architecture.
[PROPOSED] Objective Bend should earn its name by making Bend programs easier to combine, govern, explain, and continue.

## G. WHAT TO BUILD FIRST

[PROPOSED] The construction should take the shape of a living library whose first public volume is an executable notebook.
[PROPOSED] Its central object should be a document kind extended by a package written by someone other than its original author.
[PROPOSED] The library's own explanatory pages should be instances of that kind.
[PROPOSED] Those pages should expose the specifications, inherited law clauses, leaf contracts, and repair histories they describe.
[INFERRED] This makes the document medium part of the language's construction rather than a demonstration bolted onto a calculus release.

[PROPOSED] Construction should begin by giving package roots, sections, laws, and protocol implementations the same scoped naming and revision discipline.
[PROPOSED] That discipline should feed one composition operation over open specifications.
[PROPOSED] The composition operation should retain its ancestry and reflection graph when it closes into a runnable snapshot.
[PROPOSED] Its first consumer should be a report kind with a cited section and an inherited publication law.
[PROPOSED] A separate package should extend the report with a review section.
[PROPOSED] A third package should attach an export protocol to the combined report.
[INFERRED] This arrangement forces cross-package extension to exist before a polished interface can conceal its absence.

[PROPOSED] The next construction should make a section's selection a justified write under that inherited law.
[PROPOSED] The same operation should admit a patch, retain its causal parents, and produce a refusal naming the exact failing clause.
[PROPOSED] Quote verification should be one source of section justification.
[PROPOSED] A collaborator's grant should be another source.
[PROPOSED] Evidence withdrawal should repair the current view while retaining the earlier text and receipt.
[PROPOSED] Offline merging should feed conflicts back into the section's candidate set.
[PROPOSED] Kind evolution should use a checked adoption that preserves the existing page's identity.
[INFERRED] The durable object lifecycle belongs in this first coherent construction because it determines what an authored document means over time.

[PROPOSED] Leaf Bend should enter through one ordinary published computation used by that report.
[PROPOSED] A useful first leaf is an ordering routine for the report's keyed entries with orderedness and permutation laws.
[PROPOSED] Its wrapper should preserve the association between each key and its provenance-bearing entry.
[PROPOSED] The notebook should expose the exact Bend theorem statements used by the wrapper.
[PROPOSED] Its generated Bend export should be usable without running the document editor.
[PROPOSED] Its governed publication should independently check any native result whose backend correspondence has not been established.
[INFERRED] This gives the ecosystem a practical composition tool while preserving the distinction between source proof and native execution.

[PROPOSED] The first stranger-usable artifact should be a local notebook kit containing the editor, the extension packages, and the Bend export path.
[PROPOSED] A stranger should be able to make a report, extend its kind, invite a second author, merge their edits, and inspect an ancestor-law refusal without constructing a town or a private deployment.
[PROPOSED] The kit should retain a portable history that another installation can re-derive.
[PROPOSED] The Lean demand machine should carry the first complete experience.
[PROPOSED] The Bend machine should mature against that same experience as the second implementation.
[INFERRED] Publishing only a Core4 preview would stop before the intended unit of cooperation becomes usable.
[INFERRED] Requiring a usage quota before elaborating this construction would substitute an early proxy for the design question Ember asked.
[PROPOSED] The public claim should be concrete: a stranger can extend another person's computing document while preserving the reasons that make its contents and actions admissible.
