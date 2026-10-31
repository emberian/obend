# A symbolic core for an inhabited, programmable world

Astra (GPT-6), 2026-10-31. Independent study for Ember and Claude, starting at
`checkpoint-20261031b` (`5ea66e32`). Documentation only; no implementation in `lean/`.

**PROPOSED — answer.** Keep Core4 as the lazy, resource-aware execution kernel, but
put **contextual, theory-indexed judgments and certified computations** at the
center of the symbolic system; grow reflection into typed contextual staging,
and connect specialist languages through explicit, checked semantic boundaries.

**PROPOSED — first construction.** Build the portable judgment-and-receipt module
of GENERALIZATION G2/G4, grounded in the audited fold of G1, with two genuinely
different instances: an existing admitted World transition and an exact
conditional algebraic identity. A stranger must check both from pinned inputs,
without the producer, its solver, or its live workspace. This is a production
module, not an experiment that postpones the rest of the vision.

## 0. Reading discipline and the actual starting point

**READ.** Sources were the requested obend design documents, their supporting
studies, lane reports, selected implementation definitions, and the breadstuffs
vision/platform/metatheory corpus listed in §10. Breadstuffs was read-only. The
paper references distinguish local PDFs from web documentation. READ means that
the named source was inspected; it does not mean this study rebuilt its proofs
or independently verified every implementation claim. INFERRED marks my
conclusions from those sources. PROPOSED marks new design and work. A tag on a
paragraph or table introduction governs its subordinate items. Code blocks below
are schematic interfaces or theorem obligations, not existing APIs.

**READ.** The baseline is considerably stronger than an object-calculus sketch:

| Existing foundation | What the evidence supports | Boundary to preserve |
|---|---|---|
| `Core`, `Core/Proofs/Completeness`, `Core/Proofs/GroundExecution` | Source-independent reference evaluation; a call-by-need machine; `coreRepresentation` inhabited for closed sources; finite machine completion for terminating ground observations | This is not a decision procedure for termination, nor an exact cost/space equivalence theorem |
| `Core/Bidirectional`, equi-recursive type graph, `Elab` | Executable checking; regular-tree agreement; full existential annotated completeness; executable preparation on its stated fragment | Existence of annotations selected from a derivation is not a complete inference algorithm for raw source |
| `Law`, `Law/Proofs/Machine`, `Spec/LawCompile` | A law is checked code; admission re-executes a machine probe; inherited laws survive package composition | A probe on one old/new/request triple does not prove a universal mathematical identity |
| `Slot`, `World`, `Slot/Selection`, `Run/Control` | Contextual obligations, supported candidates, withdrawal, selection policies, decision tenure | Choosing a usable candidate does not make its evidence eternal or grant authority |
| `Run`, `Run/Fold`, `Run/Shared` | Guarded dispatch, in-flight protection, local refinement, shared-ledger commit and projection; `joint_reachable_ticket_exclusive` | Atomic abstract commit is not an implementation of durable storage, consensus, or network delivery |
| `Doc`, `Spec/Ecosystem`, `Vault` | Document pushout merge, identity/byte cites, cross-package intentions and pins, a usable markdown-vault entry point | Data merge is not authority merge; package migration and a distributed business runtime are additional work |

**READ.** Two chronological corrections matter. EQUIV-PLAN describes the
then-uninhabited `Representation` contract; `coreRepresentation` and its
`evaluationComplete` field already exist at the checkpoint. Older law/checker
reports also contain limits subsequently closed by LawFinish and EquiRec. The
later ProofEng report, read during this study, removes redundant axiom pins and
reports faster proofs, while retaining compiled-check fixtures. It reports that
waterfall was slower on every successful candidate in its trial. Neither old
open items nor a new tactic's reputation should determine the architecture.

**READ.** One important deployment obligation remains explicit in
`Run/LawJudge`: the adapter supplies `act`, identifying the write performed by
an operation; `none` produces an admitted law verdict because it declares no
write. Thus the theorem about every declared write needs the host's faithful
operation-to-write binding. Likewise the shared runner currently composes
runners over a common operation signature; heterogeneous services need a
checked common signature or explicit boundary adapters.

**INFERRED.** We should not restart this foundation. The missing center is a
representation of *what a computation means, under which assumptions, and what
justifies crossing into another subsystem*. That is a larger job than adding
symbolic expressions to `Term`, and a smaller trusted job than making Core4
itself a universal dependent type theory.

## 1. The symbolic core: objects organize computation; judgments organize meaning

### 1.1 What the successor must actually do

**PROPOSED.** Its ordinary unit of work should be something like:

```text
in theory T at revision r,
under binders Γ and assumptions A,
compute / prove / solve / optimize / synthesize J,
using observations O and an explicit effect boundary E.
```

An answer carries a value or residual problem, the precise claim established,
its dependencies, and evidence. This supports symbolic algebra, program
generation, simulation, reports, and contracts without pretending these have
the same equality or the same notion of success.

**INFERRED.** A term rewriter and notebook are insufficient because they do not
by themselves provide: binding-safe representations; domains and partiality;
proof-producing transformations; changing assumptions with dependency repair;
multiple observational equivalences; accountable effects; interoperability
between logics; or a persistent, shareable object that survives its original
interactive session. This is a requirements claim, not a claim that contemporary
Mathematica has no facilities in these areas.

**PROPOSED.** The center is a persistent graph with five kinds of node:

1. **Theory/context:** symbols, binding signatures, types or sorts, definitions,
   assumptions, logic and revision. An algebraic field and IEEE arithmetic are
   different theories even when both print `+`.
2. **Expression/program/data:** a scoped object in that context, with sharing,
   source locations, and a typed serialization. Syntax identity, definitional
   equality, provable equality, and observational equivalence are distinct edges.
3. **Judgment/obligation:** a proposition with its quantifier and observation
   domain. For example, an equality under side conditions, a transition's
   admission, a refinement, a numerical enclosure, or a winning strategy.
4. **Derivation/translation:** evidence between named judgments. Translations
   record their soundness direction; they need not be equivalences.
5. **Activity/intention:** an executable attempt to discharge an obligation or
   realize an authorized transition, with slots for unresolved choices.

Core4 objects provide extensible interfaces, laziness, packages, and execution
for these nodes. They should not erase their distinctions. A proof object is
not a capability; a symbol reference is not a live heap address; a logical
assumption is not a revocable grant.

**READ.** OpenMath's content dictionaries provide named mathematical symbols
and semantic descriptions. MMT separates generic theory/module infrastructure
from the particular logic and its rules. These are useful precedents for
semantic interoperability, not ready-made replacements for the obend runtime.
[OpenMath content dictionaries](https://openmath.org/cd/);
[Rabe, *A Framework for Implementing Logical Frameworks*](https://kwarc.info/people/frabe/Research/rabe_mmttypetheory_14.pdf)
[P10].

**PROPOSED.** Borrow that separation, with a stronger admission discipline:
installing a new theory does not install arbitrary trusted inference code.
An untrusted theory implementation may propose terms and proofs. Its accepted
claims use an already admitted checker or a new checker with a checked
soundness theorem and an explicitly accepted logical foundation. Unsupported
logics remain usable as foreign systems with accurately labeled evidence.
There is no requirement to encode all mathematics into Core4 types before use.

### 1.2 One example that exercises the whole design

**PROPOSED.** Ask to simplify `x/x`, where `x : Rational`, under `x ≠ 0`.
The algebra package proposes `1`; a small equality checker verifies the field
derivation and its nonzero obligation. If nonzeroness follows from `x ≥ 1`, an
arithmetic adapter supplies that proof through a checked translation. The result
is a judgment under those exact assumptions, not the unconditional rewrite
`x/x ↦ 1`.

Change the theory to IEEE binary floating point: the field theorem no longer
applies. Change the assumptions: the old theorem remains a valid conditional
theorem, but its use in the new context may be blocked. Change `x` to an effectful
computation: evaluating it twice, once, or never requires a program-equivalence
argument. This example connects symbolic reasoning, slots, dependency repair,
staging, and effects without changing the meaning of “checked.”

**PROPOSED.** The first exact algebra package should offer arithmetic expression
DAGs, rational constants, polynomial normalization with certificates, conditional
rewrites, and proof explanations. Expand into algebraic-number/root certificates,
linear algebra, units, tensors, and validated numerical enclosures through named
theories. CAS algorithms are excellent producers. Numerical estimates may be
useful without a proof, but a certified error interval and a sampled heuristic
must be different results. An integral formula carries a domain and branch
conditions; a matrix identity carries dimensions and the scalar theory.

### 1.3 Equality and incompleteness must remain visible

**READ.** The observer contract distinguishes behavior from metadata, provenance,
and resource observations. Current `Equiv/Behaviour.lean` proves `mix_assoc` for
its contextual ground-observation/convergence semantics. It does not license
erasing reflective composition trees or preserving every budget outcome.
Resourceful hidden row entries also survive the type-agreement machinery;
these are not ordinary unordered duplicate-free records. [O1, O3, O4]

**PROPOSED.** Every rewrite rule carries:

```text
theory, scoped pattern, replacement, side conditions,
relation proved, permitted observers, effect/resource conditions, proof
```

Use e-graphs and term rewriting as search indexes within a declared relation.
Do not put equations valid under different assumptions into a shared equivalence
class and recover the assumptions afterward. E-graph extraction produces a
derivation; its cost function is a search preference unless a cost theorem is
also checked. DAG sharing must not silently duplicate affine resources or
identify effectful evaluations.

**PROPOSED.** Preserve G5's distinction between laws on transitions, plans,
worlds, and traces. Add algebraic judgments alongside them. Universal laws use
proofs, exhaustive decisions on a declared finite domain, or conditional
certificates. Testing many instances remains evidence about those instances.
Never make “law” a word that obscures its quantifiers.

**PROPOSED — section deliverable.** A `Theory`/`Context`/`Judgment` data model,
canonical scoped wire format, an equality-certificate checker, and the `x/x`
workflow above. Acceptance includes checking the result in another process,
rejecting its use without the nonzero premise, and refusing a field-to-float
substitution. This establishes the semantic object the other sections consume.

## 2. Typed reflection and staging, with three separate theorems

### 2.1 The lineage gives obligations, not one magic mechanism

**READ.** Smith's 3-Lisp connects explicit representations of computation to the
computation they describe. Amin–Rompf's *Collapsing Towers of Interpreters* makes
stage-polymorphic evaluators compose in an idealized multi-level calculus, and
explores compiling under modified semantics. This is substantially more than
metadata inspection, but not a theorem that every arbitrary interpreter can be
specialized optimally. [P1, P2]

**READ.** Davies–Pfenning connect staging with modal typing; Nanevski–Pfenning–Pientka
make the context of an open term explicit. MetaML supplies explicit staging,
and MetaOCaml makes typed code generation practical, including let-insertion
and cross-stage persistence. In the current MetaOCaml description, scope
extrusion is detected during generation: “typed” does not mean every possible
generator succeeds. [P3–P5]

**READ.** Ahmed's step-indexed relations address recursive and quantified types.
Perconti–Ahmed formulate compiler correctness in a combined language with typed
source/target boundaries, so the theorem speaks about linked components.
New–Ahmed use embedding-projection pairs to reason about graduality. The useful
lesson is to specify interactions and observational guarantees, not merely to
prove each language independently type-safe. [P6–P8]

**READ.** Lean makes parser, elaborator, tactics, and other facilities extensible
through metaprograms; hygienic syntax and checked output are complementary.
Its tabled typeclass search tackles repeated diamonds and cycles. These are
relevant models for an extensible elaboration service and reusable search,
without putting the search strategy in the trusted checker. [P9]

### 2.2 The representation to add

**PROPOSED.** Separate these APIs rather than expanding `reflect` into a single
omnipotent operation:

| Operation | Returns/does | Required boundary |
|---|---|---|
| `metadata`, existing `reflect` | Declared specification/provenance | Existing observer contract; no claim that arbitrary targets were built by that specification |
| `quote` / syntax inspection | Hygienic, scoped program representation | Explicit binders and context; syntax observation is a new observer |
| `splice` / contextual substitution | Composes code fragments | A checked substitution, preserving type, stage, effects, and resource usage |
| `specialize` | Residual code plus a relation certificate | Static inputs, pinned semantics, and the relation actually proved |
| `inspectCheckpoint` | A permitted projection of execution state | Capability and confidentiality boundary; no access to secrets merely because they are in a heap |
| `install` / evaluator revision | Selects a new implementation for future work | Checked interface/refinement or explicitly changed semantics, governed version transition |

**PROPOSED.** Start with an explicit contextual code family:

```text
Code(stage, theory, Γ, A, latentEffects, usage, observerContract)
Substitution(Γ, Δ)                   -- with usage composition
GeneratorCode(...)                  -- has its own, separate effects
TransformCertificate(input, output, relation, assumptions)
```

This is a design signature, not a demand for seven runtime fields on every AST
node. Most indices can erase after checking. Start with typed represented syntax
and a checked importer, which can be implemented without immediately adding
every form to Core4. Make quotation/splicing pleasant surface syntax over that
representation. Add primitive code types only where their preservation and
erasure theorems justify the change.

**PROPOSED.** Reuse slots for incomplete code: a hole names its contextual
contract, candidates, and evidence. But separate lexical substitution from
World evolution. CMTT weakening does not by itself authorize withdrawing an
assumption. A theorem under a pinned old context remains a theorem there;
reusing it in a revised World requires the support/transport check. A mutable
capability crossing stages is a live reference whose use is reauthorized, not
a compile-time permission baked forever into generated code. Persist portable
data by serialization or immutable content reference; move live resources only
through an explicit ownership/handle protocol.

### 2.3 The three promises

**PROPOSED.** Prove and advertise these separately:

1. **Code safety:** a successful checked generator produces well-scoped,
   well-typed code; splicing preserves contextual typing and usage. Hygiene
   must survive nested generators, not merely rename top-level identifiers.
2. **Transformation correctness:** the generated program implements a declared
   relation to its reference. For specialization, relate execution under static
   environment `s` to residual execution under dynamic environment `d`.
3. **Boundary preservation:** linked generated/native/foreign components cannot
   violate the guarantees of the interface through representation exposure,
   callback reentry, authority amplification, or resource duplication.

**READ.** Tan–Wei's 2026 *When Do Staging Annotations Preserve Semantics?*
mechanizes erasure soundness using automatic let-insertion and binary logical
relations for typed two-stage calculi. Its reference extension restricts mutable
references to the second stage; the unrestricted first-stage-store problem is
not wished away. It is a particularly pertinent starting reference, but it is
call-by-value and does not settle Core4's lazy heap, yields, or authority. [P11]

**PROPOSED.** Begin the correctness proof with pure contextual code and the
existing ground observation relation. Then extend a binary logical relation
over related heaps and residuals: suspended thunks, cached results, sharing,
blackholes, typed effect responses, and checkpoints. Its worlds describe a
relation between heaps; do not confuse those mathematical worlds with the
application's `World`. Use step indexing for recursive types where necessary,
not as a substitute for stating the relation. Add trace/refinement and cost
relations as separate theorems. Do not require full abstraction everywhere:
require the boundary property each consumer actually needs.

**PROPOSED.** A compiler can preserve the original reflective source view while
executing optimized code, provided the semantics explicitly distinguishes source
quotation from inspecting installed implementation code. If programs may observe
the latter, changed code is observably changed. An evaluator revised to add
logging or change arithmetic creates a new semantic version; “reflection” does
not make it equivalent to the old evaluator. No reflective tower can authorize
its own change to the ultimate admission/checking rules by checking the change
only under the proposed new rules.

**PROPOSED — section deliverable.** Typed open code, checked contextual
substitution, a pure specializer with a semantic relation theorem, and a nested
generator example whose output runs through the normal checker. Then an effectful
example must preserve event order and refuse duplicated once-resources. This
is the point at which reflection becomes a programming facility rather than
an inspector feature.

## 3. One semantic intermediate language; several honest representations

### 3.1 What “one IR” should mean

**PROPOSED.** Use one shared, typed semantic graph vocabulary for binding,
values, laziness, code construction, effects, control, and external interfaces.
Allow explicit dialects for mathematical expressions, array kernels, query
plans, proof objects, and constraint systems. Each has a denotation or
interpretation boundary and checked translations. One meaning infrastructure
does not require one enormous AST enum or one physical storage layout.

**INFERRED.** Lowering everything immediately to machine instructions loses the
structure that makes symbolic automation useful. Keeping everything forever as
generic Core4 objects loses opportunities for dense arrays, loops, vectorization,
and circuits. The useful middle is structured, typed graphs with high-level
operations retained until their relevant transformations have run.

**READ.** LMS distinguishes generation-time work from residual expressions using
types and an extensible IR. Bračevac et al.'s graph IR combines lexical structure,
reachability information, and effects for higher-order impure programs. These
are concrete precedents for precise dependency-aware code motion. [P12, P13]

**PROPOSED.** The graph must make demand and sharing explicit. Safe transformations
need to know whether a node is pure, can diverge, may yield, consumes a resource,
reads a revisable pin, or exposes reflection. “Pure” alone does not justify
forcing an unused divergent thunk. Code motion, common-subexpression elimination,
parallel evaluation, and let-insertion each require their own conditions.

### 3.2 Collapsing the useful tower

**READ.** Truffle/Graal partial evaluation treats a program and interpreter state
as specialization inputs, with stable assumptions and invalidation. Its
documentation also gives explicit boundaries that stop partial evaluation.
The payoff depends on interpreter structure and available static information.
[Graal partial evaluation documentation](https://www.graalvm.org/dev/graalvm-as-a-platform/language-implementation-framework/PartialEvaluation/).

**PROPOSED.** Build stage-polymorphic interpreters for the domains that matter:
law predicates, exact algebra, report queries, transition programs, and selected
constraint DSLs. The same definitions should run directly, residualize, and feed
analysis. Compose specialization across their boundaries only when those
boundaries expose suitable semantics. An arbitrary proprietary CAS or remote
solver stays an external call; we can stage the preparation and checking around
it without claiming to specialize its internals.

**PROPOSED.** The initial runtime should consist of:

- The existing demand machine as reference executor and fallback.
- A typed residual graph with explicit effects and source/provenance mapping.
- A persistent artifact cache keyed by program, theory/evaluator revisions,
  static inputs, target ABI, observation contract, and relevant dependency pins.
- A small set of lowering paths: portable local execution first; native leaves
  and WASM where useful; constraint/circuit generation for selected fragments.
- The guarded runner and durable host boundary, shared across interpreter,
  generated code, and remote workers.

Prefer ahead-of-time and explicit specialization before a speculative JIT. This
reduces warm-up, invalidation, and deoptimization complexity while making the
semantics testable. A later JIT should reuse exactly those residual graphs and
proof obligations.

**PROPOSED.** Checkpoints are the natural deoptimization interface, but the
current checkpoint theorem does not establish native-stack reconstruction.
Define a relation from compiled state to a machine checkpoint. On invalidation,
resume from a related state without forcing new thunks, forgetting spent tokens,
or replaying external actions. Active execution either remains pinned to its
old semantics or crosses an explicit checked migration boundary. A changing
name must not mutate the meaning of an already dispatched operation.

### 3.3 Bend leaves, resources, and performance

**READ.** The existing design separates non-affine lazy composition from Bend
leaves and discusses affine compilation. The current “linear”/affine usage
restrictions are not by themselves a theorem of eventual obligation discharge.
[O1, O3]

**PROPOSED.** Keep Bend as an accelerator/backend for a declared leaf fragment,
not the semantics of the whole language. The boundary specifies forcing,
ownership, input/output representation, possible failure, and whether a leaf
may call back. Pure array or arithmetic kernels are good first candidates.
An unrestricted shared closure cannot simply be copied into an affine net;
prove uniqueness, insert the appropriate explicit representation, or refuse that
lowering. Capabilities cross as scoped handles, never forgeable raw integers.

**PROPOSED.** Maintain three cost accounts: deterministic logical work charged
by the protocol; implementation cost used for optimization; physical resource
use billed by an operator. A faster implementation need not consume the same
machine ticks; a chain must not charge consensus fees from wall-clock readings.
Space improvement and divergence preservation deserve explicit attention in a
lazy system. Benchmark interpreter, specialized code, and leaf execution on
algebra, report queries, and law checks, including cold start, allocations,
certificate-check cost, and checkpoint recovery. “Makes GraalVM weep” is an
engineering ambition, not a result we can infer from a smaller calculus.

**PROPOSED — section deliverable.** One stage-polymorphic domain interpreter
specialized into a real executable leaf, with input/output refinement and
checkpoint fallback. Extend to a second interpreter level to demonstrate actual
tower composition. Keep opaque calls explicit; do not count them as collapsed.

## 4. Automation: diverse search, explicit claims, small checking boundaries

### 4.1 A registry of judgments and certificate languages

**PROPOSED.** Generalize `Decides` as G2 suggests, but do not require every
useful producer to be complete. Separate the semantic judgment, the certificate
checker, and the search service. A registry entry should name:

```text
JudgmentKind:
  logic/theory revision, scoped statement schema, semantics, quantifier shape

CertificateFormat:
  format/version, canonical decoder, accepted rule subset, resource limits
  checker identity, soundness theorem, assumptions/axiom manifest
  execution trust basis, optional completeness theorem and its fragment

Translation:
  source/target judgment kinds, encoder and decoder identities
  theorem transporting accepted target evidence to the source conclusion
  side conditions, witness/model reconstruction obligations

Producer:
  solver/tool revision, capabilities, accepted fragment, scheduling hints
  no authority to declare its own output accepted
```

Use content-pinned identities, with governed names for discovery. A format name
alone is not a trust root. A signed executable checker is still executable code;
to be admitted as a verified checker it needs the corresponding semantic
theorem and a stated execution basis. Initially use Lean as the principal
metalogic rather than simultaneously inventing a new trusted proof kernel.

**PROPOSED.** The common checker contract is approximately:

```text
check(version, limits, statement, certificate)
  = Accepted(checkedClaim, dependencies, evidenceBasis)
  | Refused(clause, location, detail)
  | Exhausted(resource, resumableState?)
  | Unsupported(feature)

Accepted(...) ⇒ denotes(statement)             -- under named assumptions
```

For an attestation format, `denotes(statement)` is “issuer I signed assessment A
under delegation D at view v,” not the assessed proposition A. Soundness is
mandatory for a verified format; completeness is an optional theorem over a
named fragment. A finite certificate can be checked by a terminating algorithm
without the algorithm deciding whether a certificate exists. Budgets cover
parsing, decompression, normalization, and arithmetic bit sizes as well as rule
count. Raising the grade should not change the meaning of an accepted claim.

**PROPOSED.** The composition rule requires an actual bridge:

```text
checkT(encode(s), c) = accepted
soundT : accepted ⇒ JT(encode(s))
bridge : JT(encode(s)) ⇒ JS(s)
--------------------------------
JS(s)
```

The necessary direction changes with the question. UNSAT transport needs a
source model to induce a target model; SAT transport needs a checked target
model to reconstruct a source model. An overapproximation may prove safety but
produce spurious counterexamples. An underapproximation may exhibit behavior
but cannot prove universal safety. Record the direction rather than labeling
every adapter “equivalent.”

### 4.2 The solver families and their exact trust boundaries

**PROPOSED.** Implement adapters in this order of semantic clarity, while allowing
any producer to participate as soon as its evidence can be checked:

| Family | Useful checked evidence | What stays outside the conclusion |
|---|---|---|
| SAT | A satisfying assignment, or an LRAT-style refutation with a verified checker; a verified CNF encoding | Solver preprocessing, bit-blasting, and original-problem encoding are not justified by the final refutation alone |
| SMT | Fine-grained proof/reconstruction for an explicitly supported theory/rule subset; checked models where their semantics is supported | A solver's `unsat`, an unsupported theory lemma, or a printed model for arbitrary quantified formulas |
| ASP | Stable-model evidence under the appropriate reduct semantics; inconsistency certificates for a supported ground fragment | Grounding correctness and minimality are substantive obligations; satisfaction alone is insufficient, especially for disjunctive programs |
| PB / ILP / MILP | Exact feasible solutions; cutting-plane/branch certificates, rational bounds, and an optimality proof combining a witness with exclusion of better solutions | Floating-point solver tolerances; a feasible solution presented as optimal; uncertified presolve |
| CAS | Polynomial identities, factor products, root-isolation evidence, certified conditional transformations | The CAS's preferred branch conventions, unsupported transcendental steps, or a numeric plot presented as proof |
| Model checking / abstract interpretation | Inductive invariants, ranking arguments where applicable, finite-state reachability/game certificates, concrete countertraces | Unbounded safety inferred from bounded exploration; fairness omitted from liveness; abstract counterexamples treated as concrete |
| HOL / Lean / Isabelle and other provers | Reconstructed proofs or a checked proof translation into the chosen foundation; alternatively explicit trust in that prover's kernel and axioms | A theorem name or signed export treated as a proof in another logic; constructive/classical assumptions silently interchanged |
| Proof search / waterfall / LLM proposals | Candidate terms, lemmas, tactics, invariants, abstractions, and decompositions that ultimately produce accepted evidence | The searcher's confidence, prose explanation, or reputation as authority |

**READ.** Alethe was designed to expose the heterogeneous reasoning inside SMT;
its existence does not imply that every consumer checks every rule. ASP-DRUPE
addresses inconsistency proofs for propositional disjunctive ASP. VIPR makes
integer-programming certificates independent of the originating solver. VeriPB
and CakePB provide a concrete proof-logging/checking lineage for pseudo-Boolean
reasoning. These are formats and implementations to reuse, not reasons to build
all solvers ourselves. [P14–P17]

**READ.** PBLean is particularly close to the intended integration: it offers
Lean-level PB certificate checking and verified problem encodings. Its paper
explicitly distinguishes proof-term construction from the faster native
reflection route, whose trust basis includes `Lean.trustCompiler`. That label
must survive into a receipt; “produces a Lean theorem” alone does not settle
execution trust. Its published integration is a candidate for porting and
evaluation, not a claim that it already runs on this project's toolchain. [P18]

**PROPOSED.** Do not normalize all certificates into one lowest-common-denominator
proof language. A resolution proof can be a terrible representation of a
cutting-plane proof; a symbolic derivation can be a terrible representation of
an execution trace. Normalize their *claims and composition interfaces*, retain
specialized certificate payloads, and check each with an admitted checker.
Where useful, reconstruct into a common proof foundation. Where not, report the
composed assumption set without laundering it into a stronger assurance level.

### 4.3 What “as powerful as the laws permit” actually promises

**INFERRED.** There are four different ceilings:

| Class | Concrete examples | Honest automation promise |
|---|---|---|
| Decidable, often expensive | Finite SAT; fixed-width bitvectors; Presburger arithmetic; real closed fields; finite-state model checking; suitably bounded games | A complete decision procedure exists for the declared semantics, though a resource-limited run may return unknown |
| Effectively enumerable proofs/witnesses | Derivations in a recursively presented calculus; finite successful executions; many inductive-invariant certificates | Fair search eventually finds any finite certificate in the enumerated language, given unbounded resources; failure to find one proves nothing |
| General undecidable or stronger semantic questions | Arbitrary Core4 termination/equivalence; all true arithmetic; unrestricted program synthesis with semantic specifications | No total complete decision procedure; any sound effective proof system of sufficient strength leaves some truths unproved |
| Facts about the external world | A shipment arrived, an analyst judged a plan, an exchange actually paid | Evidence of a named observation/attestation and its authority; mathematical checking does not manufacture the physical fact |

**PROPOSED.** A useful system reaches these ceilings through a portfolio, not a
single universal tactic. Keep an explicit problem DAG: simplification, abstract
interpretation, finite solving, inductive proof, counterexample-guided synthesis,
and user/agent proposals contribute alternative or complementary edges.
Treat algebraic simplification followed by arithmetic discharge as composition,
not merely a race among executables. Exchange only typed, checked lemmas.

**PROPOSED.** Give each attempt a budget and persistent state. Schedule cheap
normalization and obvious decisions first; route by theory; use learned ranking
for expensive attempts; reserve a fair share for systematic enumeration on
enumerable fragments. Fairness is a theorem about the scheduler under resource
assumptions, not a practical promise that a difficult proof will finish. Tabling,
dependency-indexed reuse, and portfolio cancellation should prevent repeatedly
paying for the same failed or already solved subproblem. Checkers need budgeting
and isolation too.

**READ / INFERRED.** The local ProofEng waterfall trial is a useful warning:
shorter proof scripts were not faster proofs. Optimize measured total work
including elaboration, checking, and rebuild dependencies. A portfolio can keep
waterfall as an optional producer without making it the default tactic or a
trusted dependency. [O5]

**PROPOSED.** User-facing answers should distinguish `proved`, `counterexample`,
`conditional`, `unknown`, and `attested`. “No admissible candidate among those
searched” is not “no candidate exists.” A counterexample includes a replayable
source-level witness. An optimization answer includes the objective and bound;
a safety result includes the environment model; a strategy includes the
information available at each choice.

### 4.4 Synthesis and operation upon other systems

**PROPOSED.** Describe each foreign subsystem as an object with a language,
interpreter/semantics where available, codec, operation signature, effect
contract, and evidence checker. The system can then generate query plans,
programs, invariants, adapters, constraints, UI definitions, and deployment
plans as contextual code. The generated artifact and its relation to its
specification are separate outputs.

Use CEGIS: propose an artifact, seek a violating example, refine, and finish
with a certificate for the stated domain. For reactive synthesis the output is
an observation-based policy, not a clairvoyant plan that chooses after seeing an
unavailable future. For external services, synthesis produces an authorized
runner plan; it does not bypass dispatch because the plan was “proved.” A
verified adapter can establish that requests conform to a protocol. Actual
responses and physical fulfillment still need their own evidence.

**PROPOSED.** The same machinery should author new subsystems: a logic package
declares scoped syntax, inference rules, semantics, and a terminating proof
checker; generators derive parsers, editors, proof search interfaces, and
specialized checking code. Its soundness is proved in the chosen metalogic
relative to explicit premises. It may also generate a compiler or transition
monitor. This is the route from orchestrating tools to synthesizing tools.
Installation still checks the resulting artifacts under the existing admission
rules; a cycle of mutually endorsing new checkers is not a foundation.

**PROPOSED — section deliverable.** Registry plus isolated producer protocol,
two proof formats, one certified encoding, composed subgoals, and explicit
unknown/refusal results. Start exact algebra and SAT/PB, then add SMT and finite
transition systems; integrate richer CAS/ASP/ILP/provers by consumer demand.
The architecture admits diversity immediately without making first delivery
depend on every adapter being finished.

## 5. Receipts, hosting, and a platform beyond Mina

### 5.1 A receipt is a claim with evidence, not one assurance bit

**READ.** GENERALIZATION G4 proposes roots, row, law digest, pins, verdict,
quantifier, trust, and view. Breadstuffs' receipt contract supplies signed,
linked, recomputable records. Its shared-World successor in obend already
formalizes exclusion through a common atomic ledger. These are complementary
pieces, not interchangeable proofs. [O2, O5, B3]

**PROPOSED.** Extend the receipt envelope with separately identified axes:

- **Meaning:** statement, theory/logic/evaluator revision, domain, quantifiers,
  observation contract, pre/post state or expressions, and environment model.
- **Dependencies:** exact openings, negative reads where relevant, context
  assumptions, code/adapter/checker versions, and evidence dependencies.
- **Evidence:** replay, proof term, verified decision, cryptographic proof,
  signature/quorum attestation, or observation report; each with its assumptions.
- **Execution basis:** kernel reduction, compiled verified checker with its
  compiler/runtime assumptions, or an explicitly trusted foreign checker.
- **Settlement:** ordering/finality evidence, authority view, expiry/revocation
  rules, and the distinction between branch and authoritative commit.
- **Availability/privacy:** what the recipient can obtain, what is hidden,
  commitment/opening rules, and what disclosure is needed to check which claim.

A receipt may have several of these forms of evidence. They are not a single
linear “trust level.” A valid signature proves authorship under a key assumption;
it does not prove a transition legal. A proof of legality does not prove that
the transaction was chosen by consensus. A proof about a root does not make
the underlying data available.

**PROPOSED.** For the audited fold, a stranger needs enough input to recompute
every relevant read and check the post-state relation. A read-set must include
absence/range/completeness evidence for queries that depend on what is *not*
present. A few Merkle inclusions do not prove a report contains all qualifying
records. Confidential folds need either selective openings that suffice or a
proof of the hidden computation; deleting input from the receipt is not a
generic confidentiality proof.

### 5.2 The shared World is the chain's semantic nucleus

**READ.** `Run/Shared` synchronizes local views from the authoritative ledger,
judges a dispatch, commits its spent/winner/grant effects, and exposes it only
after the shared step. `Ledger.Durable` is an explicit additional condition.
Its exclusion theorem is the right shape for a chain's serial state transition,
but the implementation does not provide Byzantine consensus or disk atomicity.
[O5]

**PROPOSED.** Refine that abstract commit through a durable journal and a
consensus log. Specify the linearization point: authorized state, spent token,
in-flight record, and receipt identity become durable atomically before an
effect is released. Recover by replaying state transitions and consulting the
durable outbox; do not reissue an uncertain non-idempotent action with a new
identity. A peer's deduplication protocol is required for effect-level
exactly-once behavior. A rejected reply or abandoned runner does not erase debt.

**READ.** Breadstuffs' consensus-time audit identifies local wall-clock reads in
finalized identity/expiry paths as a source of divergence and proposes an
authenticated execution context. Its branch-and-stitch and confinement designs
also distinguish speculative branches from live settlement. [B2]

**PROPOSED.** Pin a protocol execution context: chain/world identity, ordered
position, protocol epoch, authenticated time source where needed, and canonical
transaction identity. Keep local timestamps, observer signatures, and machine
profiling outside the deterministic transition digest. Re-check authority at
settlement; a branch holding yesterday's grant cannot import yesterday's
authority into today's authoritative World.

### 5.3 What must be proved for verifiable computation

**READ.** Mina's documentation distinguishes off-chain zkApp computation,
proof-checked account updates, and recursive proof composition. Those are
relevant platform obligations, not evidence that a generic receipt already
implements them. [Mina glossary](https://docs.minaprotocol.com/glossary);
[zkApps overview](https://docs.minaprotocol.com/snapps).

**PROPOSED.** The initial verifiable path should prove a bounded deterministic
transition/checker computation, then compose batches recursively. Preserve this
chain of statements:

```text
authored policy and state-transition meaning
    ↓ checked elaboration / operational correspondence
the executable transition actually used by the host
    ↓ checked encoding and lowering
the exact constraint object loaded by the proof backend
    ↓ proof-system soundness under named cryptographic assumptions
accepted proof implies existence of a valid encoded transition
    ↓ decoding + commitment binding + chain continuity
the claimed committed endpoints are related by that transition
    ↓ consensus / finality / availability assumptions
an authoritative, usable history
```

Prove acceptance soundness even for maliciously chosen witnesses. Separately
prove or test witness generation, completeness on the intended fragment, and
performance. Correct witness generation is not a substitute for constraining
every malicious witness. Bind program/checker identity, public inputs, complete
state/frame effects, and authorization context in the proof statement.

**READ.** Breadstuffs already settled several design lessons, not all the
implementation obligations. `CONSTRUCTIVE-KNOWLEDGE.md` requires the post-state
to be exactly the emitted memory-trace fold, preventing unaccounted state.
Its later floor-free apex has an existential decoded-transition conclusion
under `StarkSound`, descriptor refinement, and witness-decoding assumptions.
It also records that the old `Poseidon2SpongeCR` premise is false at the deployed
BabyBear instance, and that a previous commitment surface required an impossible
injection. Those corrections outrank the older DREGG-CALCULUS headline. [B4]

**INFERRED.** “Few axioms” does not detect a theorem whose hypotheses have no
inhabitants. State commitments over unbounded states cannot be globally
injective into a finite digest. The useful crypto statement is computational
binding against a specified adversary, with security parameters and finite
encodings. Its application to the actual field/hash/backend is part of the
contract. Prove inhabited premises, range/no-wrap conditions, canonical finite
state representations, and the exact source-to-constraint connection.

**READ.** LOGIC-COMPILER-ASSESSMENT follows the gap from a verified compiler for
one IR to deployed descriptors in another, then records actual fusion work.
Its final P3.7 correction says **11 of 76** deployed descriptors were
compiler-authored at that audit, correcting P3.6's **1 of 76**. It still names
semantic gaps involving a collapsed transfer guard, carried commitments, and
single-row encoding. These are dated audit findings, not a fresh census here.
The durable lesson is to prove statements about the emitted object and delete
the independently authored semantic twin when replacing it. [B4]

**READ.** The conditional-vault document separates executor enforcement from
unfinished circuit binding. The private AMM describes a concrete small proof
family, but its strict BFV same-opening path relies on issuer attestations.
Threshold signatures on a witness relationship are not a zero-knowledge proof
of that relationship. Import those lessons and components at their actual
assurance, not the strongest label in their surrounding prose. [B5]

**PROPOSED.** Initially use a bounded execution-proof backend where it reduces
new semantics, and specialized circuits for demonstrated bottlenecks. Keep both
behind the registry. Recursion/folding, key epochs, chain continuity, replay
protection, private state, and data availability all need dedicated integration.
If a generic VM proves only execution of a buggy or wrong-version checker, its
proof remains a correct proof of the wrong computation. No backend removes
the earlier arrows in the diagram.

**PROPOSED — section deliverable.** A durable single-authority World first;
then two competing clients demonstrating exclusion across restart, followed by
a proof of the same transition checked by an independent light client. Only
then add replicated consensus and recursive history proofs. A Mina successor
ultimately needs adversarial networking, state availability, upgrades, recovery,
and workable economics as well as succinct validity; those remain destination
requirements, not reasons to defer the local application platform.

## 6. The business platform and distributed widgets are central consumers

### 6.1 Take the 1C lesson seriously

**READ.** 1C's documentation describes accumulation registers for multidimensional
asset accounting, document posting that generates register records, declarative
command interfaces, and report schemas that generate forms/settings. The
productive lesson is a platform organized around business concepts, with much
behavior derived from metadata. It is not merely a language with a GUI toolkit.
[Asset flow accounting](https://1c-dn.com/1c_enterprise/asset_flow_accounting/),
[document posting](https://1c-dn.com/library/tutorials/practical_developer_guide_creating_register_records_of_document/),
[command interface](https://1c-dn.com/1c_enterprise/command_interface/),
[data composition](https://1c-dn.com/1c_enterprise/data_composition_system/).

**PROPOSED.** Supply first-class business object patterns: catalog/entity,
document, register, report, workflow, role, and integration endpoint. These are
libraries and configuration schemas over the symbolic core, not new kernel
primitives. Metadata produces storage schema, forms, validation, reports,
permissions, and migrations. Domain specialists edit those concepts through
forms, formulas, tables, and worked examples; the platform elaborates them into
typed programs and proof obligations. An LLM can propose configuration, but a
business user should not have to understand proof-term syntax to change a form
or inspect why a posting was refused.

**PROPOSED.** Use a purchase-to-payment application as the first substantial
consumer, on the *same* World as its document and inspector:

1. A purchase document has stable identity, versioned line items, units, prices,
   currency, supplier, and an approval slot.
2. Posting atomically creates inventory and liability entries under named laws:
   balanced accounting per denomination, unique posting identity, valid authority,
   and application-specific inventory constraints.
3. A report is a contextual query over a pinned view, with provenance and
   completeness conditions. It can be specialized without changing its meaning.
4. Payment is an external activity with durable intent, in-flight state,
   acknowledgement, and reconciliation; a timeout is not a refund.
5. A correction uses reversal/adjustment under policy. Editing a historical
   document does not silently rewrite an already settled payment.

The language should express these laws, and automation should prove reusable
posting templates correct once. Validation of a particular transaction then
uses small local checks. This is how deep proofs become everyday convenience.

### 6.2 Offline-first without fictitious global invariants

**PROPOSED.** Separate mergeable drafts from authoritative postings. Document
patches, comments, view definitions, and selected configuration edits can merge
with explicit conflicts. Stock reservation, unique numbering, and financial
posting require either coordination or a preallocated right/quota whose
conservation survives merging. Two offline branches each seeing the same stock
cannot both be allowed to spend it merely because their local checks pass.

Use the existing slots to retain unresolved business decisions and explain
conflicts. Carry migrations as versioned programs with declared invariants;
schema migration, policy adoption, and data conversion are different operations.
Pending activities pin the old interpretation until explicitly migrated.
The same application can run locally and in a cloud service, but the boundary
must state latency, availability, authority freshness, and settlement semantics.
Deployment location is not semantically invisible when a network partition occurs.

**PROPOSED.** Prefer one local durable engine with remote replication/services
over a second cloud-only business semantics. Keep authentication, tenant
isolation, backup/restore, indexing, and deployment support as real platform
work. They cannot be discharged by pointing to an object calculus. Preserve
the business configurator as a product surface throughout development, rather
than postponing it until every proof facility is finished.

### 6.3 Recover the deos GUI/event model

**READ.** APPS-AS-CELLS distinguishes durable app state from ephemeral cursor,
scroll, and cache state. CELL-HOSTED-VIEWTREE makes a view tree cell-hosted data
with mounts/resolution; COCKPIT-UX groups work by intent. The inspector framework
offers multiple presentations and interactive construction over shared objects.
The recensus applies the demanding test: an app is real when a person can open
and use its surface on the live shared World, not when a launcher fires a demo
on a separate ledger. [B1, B6]

**PROPOSED.** Port that conceptual structure, with a small versioned view-tree
schema: text, layout, fields, lists/tables, bindings, actions, and child mounts.
Views are pure projections of an authorized view plus ephemeral local state.
An action is a typed command template, resolved and reauthorized at commit.
Native and browser renderers share this model. Rich specialized widgets remain
extensions through scoped interfaces, not arbitrary ambient scripts.

**PROPOSED.** An event envelope binds view/object identity, action identity,
input data, actor, expected relevant revisions, and an idempotency key. The
handler checks the actual current authority and preconditions. A stale button
can be visible yet its action refused; disabling it locally is useful feedback,
not enforcement. Replayed views cannot issue live commands. Child mounts carry
their own namespace and authority projection, avoiding the documented trap of
binding a child view to the parent's ledger context.

**PROPOSED.** Editing a view definition is a governed object update. Keep the
renderer, event routing, accessibility, and provenance display in the product
boundary: a proof about a state root does not prove the user saw that state or
clicked the action described by the receipt. A distributed widget can carry a
snapshot plus an attenuated live reference. Opening it establishes the viewer's
rights now; the screenshot alone grants nothing.

**PROPOSED.** Present the symbolic workspace as a live document of objects and
computations: formulas, derivations, charts, reports, and controls can share
references and assumptions. Notebook-style narrative remains a valuable view,
but recomputation follows the dependency graph, and editing a premise marks
affected results conditional/stale instead of relying on cell execution order.
The inspector can expose source, generated code, assumptions, evidence, and
pending choices on demand. Ordinary product flows should speak in business or
mathematical terms, not certificate-internal jargon.

**PROPOSED — section deliverable.** One usable purchase/register/report app with
an editable metadata-driven form, one remote widget, offline draft merge, and
shared authoritative posting. The same receipt opens in the inspector and
checks outside the app. This is the integration criterion for the platform,
not a gallery of independent demos.

## 7. What to take from deos, what to leave, and which frontiers we reach

### 7.1 The inheritance

**INFERRED, grounded in B1–B6.** Deos got these architectural choices right,
and obend has not yet absorbed their full consequences:

| Take forward | Why it matters now |
|---|---|
| Apps, documents, agents, and views participate in one live object world | The symbolic workspace and business platform should compose directly, rather than export between unrelated apps |
| Durable state separated from ephemeral presentation | Makes replay, view replacement, portability, and selective persistence tractable |
| Affordances as typed, authorized actions; surfaces as scoped references | Gives generated interfaces and agents the same authority boundary |
| Multiple presentations and an inspector over the same object | Makes symbolic meaning, provenance, and business configuration accessible without inventing separate debugging databases |
| Branch confinement and explicit stitch/settlement | Supports offline work and speculative synthesis without confusing hypothetical success with committed authority |
| Pure replay separated from effect release | Enables interactive checkpoints and deferred expensive proof work without redispatching actions |
| One authored semantic object feeding runtime and proof artifacts | Offers the best route out of duplicated interpreter/compiler/circuit definitions |
| Explicit grants, conserving budgets, and a confined tool gateway | Lets ambitious automation operate with bounded authority; solver processes need this as much as LLM agents |

**READ.** COMPUTRON-POLICY keeps operator pricing local and distinguishes a
voucher from proof of an external payment. AGENT-CONFINEMENT-REDTEAM tests
concrete ambient-authority escapes. The cloud offerings and community brief
connect local work, hosted services, and applications. These are valuable
requirements for a usable platform, beyond the theorem-prover view of the core.
[B2, B3]

### 7.2 The mistakes to avoid repeating

**INFERRED.** Several deos documents use universal language that their own
later or narrower audits do not support. The response should be to retain the
valuable construction and repair the missing connection:

- **A modeled window is not a verified desktop.** DEOS explicitly says the
  compositor, input path, and transport are outside its authority models.
  Preserve the authority theorems; add implementation/refinement obligations.
- **A signed receipt is not automatically a semantic or succinct proof.** Keep
  distinct evidence and settlement claims, rather than advertising the strongest
  possible proof mode for every interaction.
- **A compiler theorem about a parallel object is not a theorem about deployed
  bytes.** Generate and consume the actual artifact; certify decoding and
  lowering. Drift tests remain useful but do not replace semantic refinement.
- **A small axiom census is not non-vacuity.** Impossible fields in a structure
  or false hypotheses can hide the real failure. Instantiate premises and
  inspect the claimed conclusion, especially at cryptographic boundaries.
- **Uniform nouns do not erase different semantics.** Local and distributed
  revocation differ; exact arithmetic and fields differ; ordinary authority can
  be reusable while a spend token is one-shot. Naming both “cell” is not a proof
  that they can be interchanged.
- **A large organ/app count is not integration.** The app recensus demonstrates
  the side-ledger/launcher trap. Measure a person's completed workflow on the
  shared World, including restart and repair.
- **A clever algebra is not automatically the right abstraction.** Keep the
  audited fold that shortens actual obligations. Do not reinstate the rejected
  justification-semiring generalization, or infer a complete flow algebra from
  a few suggestive distributivity laws.
- **Not every activity can be rewound.** Replay can reconstruct a view of past
  evidence. It cannot unsend a payment or withdraw another person's knowledge.
  Branch semantics, compensation, and physical completion remain distinct.

### 7.3 The frontier map

**READ.** FRONTIERS-BEYOND-DEOS names firmament/seL4, federation, privacy, light
client/data availability, and bridges. Its small wiring estimates describe a
particular breadstuffs checkout; they are not estimates for this new platform.
The current POLIS overview reports a bounded/public decidable option-space
framework, causal erasure, and several deployed bindings. It explicitly keeps
the temporal monitoring witness as a frontier and distinguishes the Polis floor
from circuit soundness. The earlier HYPERPROPERTY document's proposed identity
between those two is therefore not the conclusion to inherit. [B7]

**PROPOSED.** This vision reaches those frontiers at different points:

| Frontier | Where it enters this architecture | Priority |
|---|---|---|
| Durable host and capability confinement | Local app runtime, compiler/solver workers, effect release | Immediate; initially on an ordinary hosted OS with explicit assumptions |
| Verified OS / seL4 | Strengthening the same host contract against lower-level compromise | Valuable later backend; not prerequisite for symbolic computation or a useful business app |
| Federation / consensus / key management | Shared-World refinement into multiple mutually distrustful authorities | Required for the chain destination; after durable single-authority semantics |
| Privacy | Confidential solver inputs, selective receipts, private business state and contracts | Design interfaces now; prove each disclosure/crypto mechanism separately |
| Light clients and availability | Independent receipt checking, succinct history, retrieving needed state | Independent checking immediately; full distributed availability with the chain |
| Bridges and foreign runtimes | Theories, solver encodings, native code, external chains/services | Semantic bridges immediately; cross-chain asset bridges after both settlement models exist |
| Polis | Synthesis/automation that preserves public safety and viable choices | Finite explicit models early; stronger unbounded/adversarial claims only with their own certificates |

### 7.4 The Polis object we should actually build

**INFERRED.** “Some path home exists” and “the participant can force a path home
against the environment” differ by quantifier order. On a finite explicit game,
the safety winning region has the familiar shape
`νX. Safe ∩ CPre(X)`, where `CPre` chooses a controllable action and quantifies
over the allowed environment responses. This requires a declared ownership of
moves, observation model, and treatment of deadlock. Bounded `reachHome` is not
automatically that greatest fixed point. Reachability/liveness additionally
needs progress: merely staying inside a winning region can permit infinite
stalling.

**PROPOSED.** Add a finite-game judgment with certificates for winning regions,
allowed actions, and progress ranks/strategies where required. Prove the
abstraction relation from the actual transition system to the game. The
obligation in POLIS-METATHEORY-QUESTIONS Q3—the projection from the real system
to the model—is central, exactly like the CAS-to-SMT and source-to-circuit
bridges. A theorem quantifying over every controller cannot repair an unsound
model of the environment.

**INFERRED.** Some two-run properties reduce to safety on a self-composed
system. General preservation of viable alternatives can involve `∀∃` or
strategy quantifiers; it is not automatically 2-safety merely because two
counterfactual situations are discussed. Restricting traces preserves many
universal safety properties but can destroy existential options. Consequently
“more refusals” is not automatically monotone improvement in freedom or
liveness. Meet-of-floors needs a nonempty realizable implementation and the
correct quantifier-preserving composition theorem.

**PROPOSED.** Carry forward public-action opacity: agents' protected interiors
are not inputs to enforcement. Name the public option-space, causal
counterfactual construction, consent/settlement exceptions, bound, and
environment assumptions in the judgment. “Least restrictive” is relative to
that modeled arena and floor, not an absolute solution to governance. This
gives the automation platform a precise way to synthesize safe protocols and
preserve participant choices without claiming a decision procedure for politics.

## 8. Construction order from the checkpoint

**PROPOSED.** Work in coherent vertical slices, with reusable modules shared
between them. The following are lane-sized briefs; dependencies identify what
must converge, not a request to launch lanes as part of this study. Do not
replace implementation with repeated studies or one-day experiments.

### A. Judgment, receipt, and theory/context spine — first

**PROPOSED.** Inputs: G1/G2/G4, current `Decides`, `Run/Fold`, law machine,
package/cite pins, §1 and §4 here. Deliver versioned statement and evidence
envelopes, scoped canonical encoding, checker registry, and a standalone
consumer that has no producer state. Implement the World-transition instance
and a conditional exact-algebra instance; one composite proof uses evidence
from both the arithmetic library and a side-condition checker.

Required obligations: checker soundness, decoded bytes denote the checked
statement, dependency sufficiency, explicit assumptions, and no conversion from
historical support to current authority. Refuse changed statements, omitted
premises, unsupported rules, exhausted checking budgets, and incompatible
theory versions. The payoff is portable meaning for every subsequent platform.
Do not make this module depend on a new staging calculus or a SNARK backend.

### B. Unify intentions and dependency repair

**PROPOSED.** Inputs: `Slot`, `World`, `Spec/Ecosystem`, `Doc/Section`, `Journal`,
and A's identities. Deliver the common G3 intention interface, preserving each
consumer's meaning: fixed pins, following references, nominal kind identity,
chosen evidence, and live authority are distinct policies over shared machinery.
Keep incumbent-first selection where intended; make explicit overrides visible.

Required obligations: transport/reuse under unchanged dependencies, stale
support refusal, exact compatibility conditions for repairs, and preservation
of in-flight obligations. A schema/policy change updates affected reports and
future work while preserving the historical meaning of old receipts. Retire
duplicate resolution code after its consumers use the shared interface.

### C. Contextual code and the first proved specializer

**PROPOSED.** Inputs: A, current typing/equivalence, §2. Deliver typed represented
syntax, quotation/splicing, code-generation context management, and a pure
stage-polymorphic interpreter for a useful domain such as arithmetic or report
expressions. Residual output passes the existing checker.

Required obligations: substitution/usage preservation, hygiene, generated-code
safety, and semantic correctness under declared observers. Add effects and
heap-aware relations after the pure construction; do not disguise their absence
with a general theorem name. A second interpreter level and a versioned
semantics change establish that the tower interface is real.

### D. Diverse automation with certified encodings

**PROPOSED.** Inputs: A; B for caching; C where generation helps. Deliver producer
protocol, job isolation, exact algebra plus SAT/PB adapters, one certified
encoding from a real application obligation, persistent problem DAG, tabling,
and portfolio scheduling. Expand SMT/ASP/ILP/model-checking/prover adapters through
the same interface, preserving their individual fragments and trust bases.

Required obligations: each accepted subgoal composes back to the original
judgment; unknown is never negation; cached evidence carries its context;
counterexamples replay at the source level. Measure end-to-end solving and
checking costs, including proof size. The application, not a solver-count target,
determines the next adapter.

### E. Durable shared World and a usable metadata-driven application

**PROPOSED.** Inputs: A/B, `Run/Shared`, `Vault`, §5–6. Deliver durable commit,
recovery/outbox, one common World for app/doc/inspector, the small view schema,
configuration editor, purchase posting and report workflow, and offline drafts.
This can proceed alongside C/D after the receipt interface stabilizes.

Required obligations: the host refines the abstract commit; competing clients
cannot spend one token twice across restart; uncertain external effects retain
their obligations; child views use the right scope; stale authority fails at
commit. A person can open, configure, use, close, recover, and share the app.
An exported receipt checks without the app. This is the first whole system.

### F. Compiled execution and checkpoint refinement

**PROPOSED.** Inputs: C/E and measured workloads. Deliver typed residual graph,
an explicit specialization cache, one native or Bend leaf path, and fallback
to the demand machine. Preserve source/provenance through optimized execution.

Required obligations: boundary typing and ownership, executable semantic
refinement, compiled-state/checkpoint relation, no repeated external exposure
on fallback, and separately stated cost properties. Prefer representation and
algorithm improvements before a large JIT. Let benchmarks determine the next
lowering rather than choosing a universal backend for aesthetic reasons.

### G. Verifiable execution, then replicated settlement

**PROPOSED.** Inputs: A/E, F only if its exact execution is the proof target.
Deliver proof of the actual transition/checker computation, exact descriptor
consumption, independent light-client verification, batching/recursive linkage,
and declared privacy/availability behavior. Then refine shared commit through
consensus and key epochs with adversarial network behavior.

Required obligations: §5's whole diagram, including decoding, inhabited premises,
malicious-witness soundness, whole-state effects, time/identity determinism,
settlement freshness, and chain continuity. Explicitly select the proof backend
and its security assumptions; do not import breadstuffs' invalid global
injectivity premises. The output is the beginning of a chain platform, not just
a signed execution log with a blockchain vocabulary.

### H. Synthesis of protocols and public option-space laws

**PROPOSED.** Inputs: A/D/E, §7. Deliver finite-game and product-system judgments,
checked strategies/invariants, and the projection from one real workflow to its
model. Integrate these with agent tool mandates and generated workflow policies.

Required obligations: actual control/observation quantifiers, environment and
fairness assumptions, viable progress rather than refusal-only safety, and
nonempty composed floors. Keep bounded/public claims prominent. Extend to
unbounded models through independent proof certificates rather than broadening
the finite checker's advertised meaning.

### What carries the weight, and what changes

**PROPOSED.** Keep `Core`/machine, bidirectional checking/equi-recursive
agreement, `Law`'s current admission route, the slot theory, guarded runner,
shared-World semantics, and document merge as load-bearing components. Extend
their consumers through new modules. Maintain explicit coercions at elaboration
boundaries; algebraic subtyping should improve the frontend without silently
replacing kernel equality or erasing resourceful row shadows.

**PROPOSED.** Replace duplicated intention/resolution plumbing when B supplies
its shared definition. Extend metadata's string-oriented presentation with typed
interfaces and schema objects while preserving old observations. Replace
side-ledger application runtimes with the shared host. Replace handwritten
semantic twins of emitted programs/constraints with generated definitions and
checked decoding. Evolve packet/root identities into versioned, domain-separated
portable encodings; existing local hashes and dependency fingerprints are not
cryptographic identities merely because they are called pins.

**PROPOSED.** Add staged syntax, semantic judgments, foreign boundaries, and
host durability rather than inserting all those concerns into `Term`. Revisit
Core4 primitives only where an expressiveness or preservation argument requires
it. A code type or ownership-safe foreign call may justify a primitive; a new
business register, solver, or chart should not.

## 9. The largest foundation risks and the decisions to make now

**INFERRED.** The highest risk is **semantic misidentification at a boundary**:
the proof is about a different question, execution, circuit, or authority view
than the user intended. This is more dangerous than choosing a less elegant
object calculus. It recurs in almost every breadstuffs audit and is exactly what
the registry, contextual judgments, and single authored artifact must prevent.

**PROPOSED.** Make these decisions now:

| Decision | Reason / consequence |
|---|---|
| Core4 remains the execution kernel; contextual judgments are the symbolic center | Avoids throwing away mechanization while giving heterogeneous mathematics a real semantic home |
| Lean is the initial principal proof foundation; foreign foundations remain explicit | Makes checker admission concrete without pretending universal proof translation is solved |
| Binding, theory identity, observers, and effects are present before broad rewriting/staging | These determine which optimizations are true; retrofitting them later invalidates transformations |
| Receipts have structured evidence and assumptions, not a `verified` flag | Prevents signatures, compiled checks, formal proofs, and ZK proofs from being conflated |
| Offline merge and authoritative settlement have different contracts | Makes useful offline applications compatible with global conservation |
| One durable World and one real application precede a large app catalog | Forces interfaces to compose under use, not merely under standalone tests |
| Specialization first, speculative JIT later | Obtains much of the staging benefit while reducing the initial proof/runtime surface |
| Solver diversity is architectural; adapters are delivered by useful obligations | Avoids a monolithic solver bet and avoids making every solver a launch dependency |

**INFERRED.** The second major risk is observational overreach: adding arbitrary
heap/code reflection can make intended abstraction and optimization laws false.
The third is resource conflation: reusable authority, affine ownership,
conserved value, computation budget, and eventual obligations have different
algebras. The fourth is an ever-growing formal model whose runtime remains a
separate implementation. The fifth is a product that demands its user understand
those distinctions at every click. The design should enforce them internally
and explain them when they affect a decision.

**PROPOSED.** Keep the long destination intact: a system that can manipulate
mathematics and programs, synthesize specialized implementations and protocols,
coordinate people and agents, and let strangers check what it claims. The first
whole system should already connect those activities through one live graph.
The later chain, richer mathematics, and stronger host are extensions of that
same system, not separate demonstrations waiting for an eventual integration.

## 10. Sources and reference locations

### Project evidence

**READ.** Paths in O entries are relative to `/Users/ember/dev/obend`; paths in
B entries to `/Users/ember/dev/breadstuffs`. The latter entries report inspected
documents and their stated evidence; this study did not rebuild breadstuffs or
recensus its deployed binaries. Long vision/reference documents were consulted
by relevant sections, not used as independent confirmation of their own claims.

- **O1 — Present language and thesis:** `README.md`, `THESIS.md`, `DESIGN.md`,
  `METATHEORY.md`; `review/DECISIONS-20261031.md`.
- **O2 — Generalization and epistemic construction:**
  `review/GENERALIZATION-20261031.md`, `review/GENERATED-20261031.md`.
- **O3 — Effects, inference, equivalence:**
  `astra/ASTRA-EFFECT-LAWS-20261031.md`,
  `review/ALGEBRAIC-SUBTYPING-20261031.md`, `review/EQUIV-PLAN-20261031.md`.
- **O4 — Direct implementation/observer checks:**
  `lean/Obend/Core/Proofs/Completeness.lean`,
  `lean/Obend/Core/Proofs/GroundExecution.lean`,
  `lean/Obend/Equiv/Behaviour.lean`, `lean/Obend/Run/Shared.lean`;
  `/Users/ember/dev/minidregg/docs/objective-bend/REFLECTION.md` (the earlier
  observer contract; its old “not yet proved” statements are not current obend status).
- **O5 — Lane evidence:** `lean/docs/REPORT-20261031.md`,
  `REPORT-EQUIREC-20261031.md`, `REPORT-ELAB-20261031.md`,
  `REPORT-LAWFINISH-20261031.md`, `REPORT-SLOTRUN-20261031.md`,
  `REPORT-RUNNER-20261031.md`, `REPORT-EXTENDS-20261031.md`,
  `REPORT-VAULT-20261031.md`, `REPORT-JUST-20261031.md`,
  `REPORT-CENSUS-20261031.md`, `REPORT-PROOFENG-20261031.md`; supporting earlier
  Doc, Law, LawDoc, Spec, Journal, Checker, and Lean435 reports in the same directory.
- **B1 — The platform and its UI:** `docs/what-is-deos.html`,
  `docs/deos/DEOS.md`, `APPS-AS-CELLS.md`, `CELL-HOSTED-VIEWTREE.md`,
  `COCKPIT-UX.md`, `CROSS-DEVICE-FIRMAMENT.md`, `INSPECTOR-FRAMEWORK.md`
  (all latter names in `docs/deos/`).
- **B2 — Coordination, resources, confinement:**
  `docs/deos/BRANCH-AND-STITCH-PROTOCOL.md`,
  `CONSENSUS-TIME-AND-RECEIPT-IDENTITY.md`, `COMPUTRON-POLICY.md`,
  `AGENT-CONFINEMENT-REDTEAM.md`.
- **B3 — Hosted platform and receipts:** `docs/DREGGNET-CLOUD-OFFERINGS.md`,
  `docs/RECEIPT-CONTRACT.md`, `docs/COMMUNITY-BRIEF-CLOUD-FORGE-APPS.md`.
- **B4 — Meaning and deployment:** `metatheory/CONSTRUCTIVE-KNOWLEDGE.md`;
  `metatheory/docs/DREGG-CALCULUS.md`, `CELL-PROGRAM-LANGUAGE.md`,
  `FLOW-COMPOSITION-ALGEBRA.md`, `GUARDED-HOLES-METATHEORY.md`,
  `LOGIC-COMPILER-ASSESSMENT.md`, `AXIOM-HYGIENE.md`, `DISCARD-CANDIDATES.md`.
- **B5 — Contract/privacy examples:** `docs/deos/CONDITIONAL-VAULT.md`,
  `docs/deos/DARK-AMM-PRIVATE-RECEIPT.md`.
- **B6 — Whole-system ambitions and the application correction:**
  `docs/vision/VISION-living-world.md`, `VISION-the-whole-objective.md`,
  `VISION-reality-gated-substrate.md`, `VISION-proof-by-construction.md`;
  `metatheory/docs/APPS-RECENSUS-DEOS-ERA.md`.
- **B7 — Frontiers:** `metatheory/docs/FRONTIERS-BEYOND-DEOS.md`, `POLIS.md`,
  `POLIS-HYPERPROPERTY-FRONTIER.md`, `POLIS-METATHEORY-QUESTIONS.md`.

### Research references

**READ.** `PB/` below means `/Users/ember/paperbin/` and `V/` means
`/Users/ember/paperbin/obend-vision-20261031/`. Every listed local PDF has a
same-stem `.txt` used for inspection. Citations use the work's actual title/year,
not an inferred date from its download path. The research reading focused on
introductions, stated guarantees, relevant constructions and limitations; it
is not a claim to have checked all paper proofs.

1. **P1 — Brian Cantwell Smith, *Reflection and Semantics in Lisp* (1984).**
   [Paper](https://ics.uci.edu/~jajones/INF102-S18/readings/17_Smith84.pdf).
   `V/smith1984-reflection-semantics-lisp.pdf`.
2. **P2 — Nada Amin and Tiark Rompf, *Collapsing Towers of Interpreters* (POPL 2018).**
   [Paper](https://namin.seas.harvard.edu/pubs/popl-collapsing-towers.pdf).
   `V/amin-rompf2018-collapsing-towers.pdf`.
3. **P3 — Rowan Davies and Frank Pfenning, *A Modal Analysis of Staged Computation*
   (JACM 2001; extended from POPL 1996).**
   `PB/davies2001-modal-analysis-staged-computation.pdf`.
4. **P4 — Aleksandar Nanevski, Frank Pfenning, Brigitte Pientka,
   *Contextual Modal Type Theory* (TOCL 2008).**
   `PB/nanevski2008-contextual-modal-type-theory.pdf` (local prepublication text).
5. **P5 — Walid Taha and Tim Sheard, *MetaML and Multi-stage Programming with
   Explicit Annotations* (TCS 2000; PEPM 1997 predecessor); Oleg Kiselyov,
   *MetaOCaml: ten years later — System description* (SCP 2026).**
   [Sheard's staging reading list](https://web.cecs.pdx.edu/~sheard/course/stagedcomp/papers.html),
   [MetaOCaml project](https://okmij.org/ftp/ML/MetaOCaml.html),
   [Kiselyov paper](https://okmij.org/ftp/meta-programming/design-10.pdf).
   Kiselyov: `V/kiselyov2026-metaocaml-ten-years.pdf`; no MetaML PDF fetched here.
6. **P6 — Amal Ahmed, *Step-Indexed Syntactic Logical Relations for Recursive and
   Quantified Types* (ESOP 2006).**
   `PB/ahmed2006-step-indexed-syntactic-logical-relations.pdf`.
7. **P7 — James T. Perconti and Amal Ahmed, *Verifying an Open Compiler Using
   Multi-Language Semantics* (ESOP 2014), technical report including proofs.**
   [Project](https://ccs.neu.edu/home/amal/voc/).
   `V/perconti-ahmed2014-open-compiler.pdf`.
8. **P8 — Max S. New and Amal Ahmed, *Graduality from Embedding-Projection Pairs*
   (ICFP 2018).** [Paper](https://arxiv.org/abs/1807.02786).
   `V/new-ahmed2018-graduality-ep-pairs.pdf`.
9. **P9 — Leonardo de Moura and Sebastian Ullrich, *The Lean 4 Theorem Prover and
   Programming Language* (CADE 2021); Sebastian Ullrich and Leonardo de Moura,
   *Beyond Notations: Hygienic Macro Expansion for Theorem Proving Languages*
   (LMCS 2022); Daniel Selsam, Sebastian Ullrich, Leonardo de Moura,
   *Tabled Typeclass Resolution* (2020).**
   [Lean paper](https://lean-lang.org/papers/lean4.pdf),
   [macros](https://arxiv.org/abs/2001.10490),
   [tabling](https://arxiv.org/abs/2001.04301).
   `V/demoura-ullrich2021-lean4.pdf`,
   `V/ullrich-demoura2020-hygienic-macros.pdf` (download is the 2022 journal version),
   `V/ullrich-demoura2020-tabled-typeclass.pdf` (filename omits Selsam; authors above are correct).
10. **P10 — Florian Rabe, *A Framework for Implementing Logical Frameworks* (2014).**
    [Paper](https://kwarc.info/people/frabe/Research/rabe_mmttypetheory_14.pdf).
    `V/rabe2014-framework-logical-frameworks.pdf`. OpenMath project documentation
    is linked in §1; no OpenMath PDF fetched.
11. **P11 — Jun Tan and Guannan Wei, *When Do Staging Annotations Preserve
    Semantics? Mechanizing Typed Semantics-Preserving Multi-stage Programming
    with Let-Insertion* (OOPSLA 2026 preprint, extended version v2).**
    [Paper](https://arxiv.org/abs/2606.30854v2).
    `V/tan-wei2026-semantics-preserving-staging.pdf`.
12. **P12 — Tiark Rompf and Martin Odersky, *Lightweight Modular Staging: A Pragmatic
    Approach to Runtime Code Generation and Compiled DSLs* (GPCE 2010).**
    [LMS project and worked generation example](https://scala-lms.github.io/).
    The project documentation was the direct source used here. The pre-existing
    `PB/rompf-odersky-2010-lightweight-modular-staging.pdf` contains presentation
    material, not the paper, and was not treated as a fetched copy of the paper.
13. **P13 — Oliver Bračevac et al., *Graph IRs for Impure Higher-Order Languages:
    Making Aggressive Optimizations Affordable with Precise Effect Dependencies*
    (OOPSLA 2023).**
    [Paper](https://www.cs.purdue.edu/homes/rompf/papers/bracevac-oopsla23.pdf).
    `V/bracevac2023-graph-irs-effects.pdf`.
14. **P14 — Hans-Jörg Schurr, Mathias Fleury, Haniel Barbosa, Pascal Fontaine,
    *Alethe: Towards a Generic SMT Proof Format* (2021).**
    [Paper](https://arxiv.org/abs/2107.02354).
    `V/schurr2021-alethe.pdf`. Consult the pinned producer/checker version's
    supported rules before adopting an adapter; the format name is not coverage.
15. **P15 — Mario Alviano et al., *Inconsistency Proofs for ASP: The ASP-DRUPE Format*
    (TPLP 2019).** [Paper](https://arxiv.org/abs/1907.10389).
    `PB/alviano2019-asp-drupe-inconsistency-proofs.pdf`.
16. **P16 — Kevin K. H. Cheung, Ambros Gleixner, Daniel E. Steffy,
    *Verifying Integer Programming Results* (IPCO 2017; revised report).**
    [Paper](https://arxiv.org/abs/1611.08832),
    [VIPR implementation](https://github.com/scipopt/vipr).
    `PB/oracle-native-20261031/verified-composition/vipr.pdf`.
17. **P17 — Markus Anders et al., *Documentation of VeriPB and CakePB for the SAT
    Competition 2025*.**
    [Documentation](https://satcompetition.github.io/2025/downloads/checkers/veripb.pdf).
    `V/veripb-cakepb2025-documentation.pdf`.
18. **P18 — Stefan Szeider, *PBLean: Pseudo-Boolean Proof Certificates for Lean 4*
    (2026, v2).** [Paper](https://arxiv.org/abs/2602.08692v2).
    `V/szeider2026-pblean.pdf`. Read its explicit trust-model discussion in
    addition to the abstract; it distinguishes proof construction and native checking.

**READ.** Current Graal, Mina, OpenMath, and 1C primary documentation is linked at
the associated claims above (consulted 2026-10-31). No claim of benchmark
superiority, deployed chain security, or completion of the proposed platform
is made by this study.
