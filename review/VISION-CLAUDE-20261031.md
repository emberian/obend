# The symbolic core of what comes after: a Claude vision study

Claude (Fable 5.1), 2026-10-31, on `review/VISION-BRIEF-20261031.md`. Baseline `checkpoint-20261031b`.
Nothing here lands in `lean/`. Tags: **READ** (a file, report or paper I opened; cited by path or
paperbin name), **INFERRED** (my deduction from READ material), **PROPOSED** (a design, theorem target
or order I am putting forward). Two colleagues read the deos GUI cluster and the deos cloud/contract
cluster for me and reported with citations; where I use their findings I tag them READ (reader) and
give the file they cited. Papers fetched for this study are listed in §10 with their paperbin names.

## 0. Answers in brief

**(1) The center.** INFERRED. Core4 with reflection, laws and slots is the right kernel for symbolic
computation over heterogeneous subsystems, provided it gains one constructor family it does not have:
terms as content-addressed data under the observer ladder (`quote`), so that the symbolic core is
*objects whose expressions are data, whose rewrites are certificates, and whose answers are receipts*.
Nothing else needs to move to the center; the term rewriter becomes one judge among many and the
notebook one page among many.

**(2) Reflection.** INFERRED/PROPOSED. The typed, law-abiding reflection obend has (`reflect`,
`metadata`, the observer table) must grow into four things: an observer *ladder* (`≈q ⊂ ≈r ⊂ ≈b`, with
cost as a refinement of `≈b`) under which a rewrite is sound exactly below the observers that can see
it; reflection as an attenuable capability (Bracha's mirrors) rather than an ambient primitive; stages
as views of the World, so that CMTT's `□(Ψ ⊢ A)` and MetaML's code type are the slot and a pin, and the
reflective tower is the sequence of meta-Worlds whose turns are judged by meta-laws; and boundaries to
foreign systems typed by embedding–projection pairs, where the kernel's `checked`/`attested` trust modes
are the two ends of a gradual spectrum.

**(3) Runtime.** PROPOSED. One intermediate language, Core4 with pins; binding time is pinnedness;
specialization is re-elaboration at a view where more is pinned; a specialized artifact is a candidate
in a slot whose supports are the pins it assumed, so deoptimization is the withdrawal of a support and
the demand machine is the always-usable fallback candidate; the leaf refinement against BendTT and the
`Chain` theorem (machine against reference) are the two proofs Truffle never states.

**(4) Automation.** PROPOSED. Solver diversity under one rule: search outside, decidable checking
inside, attestation for the rest, each named in the receipt's trust field. "As powerful as the laws
permit" means concretely: turn every claim about a subsystem into a claim about a certificate, every
certificate into a decidable check with a budget, and every claim that has no certificate (liveness,
non-termination, prose) into a bounded or attested one. The registry is a typeclass of judges whose
registration includes the encoding, the refusal vocabulary and a planted-bad-certificate tooth.

**(5) Platforms.** PROPOSED. A contract is a package root with laws by occasion, a transaction is a
turn judged by the effective law, the chain is the shared-World ledger, a light client holds a receipt
at the openings position of the dial, and succinct proofs are a later position of the same dial. A 1C
successor is kinds as cells with laws, registers as objects with conservation laws, forms as view
methods, reports as judged folds with non-omission receipts, and vendor extension as intentions. A
widget is an object whose view is a method, whose events are plans, whose affordances are the requests
the judge says would pass.

**(6) Order.** PROPOSED. First build `Obend/Judge.lean` and `Obend/Receipt.lean` together (G2 and G4 of
`GENERALIZATION`, fused), instantiated by the five judges the library already has plus one foreign
certificate format (LRAT) with a planted-bad-certificate tooth, and `holdsOfPin` so `receipt_sufficient`
is computable. Then `quote`. Then the specialization slot. The highest risk of building on the wrong
foundation is the demand machine's missing half (`Representation` uninhabited, source-to-machine
completeness open), because every compiled path and every cost statement stands on it.

## 1. Where we are, read for this question

READ. `README.md`, `THESIS.md`, `DESIGN.md`, `METATHEORY.md`, `review/DECISIONS-20261031.md`,
`review/GENERALIZATION-20261031.md`, the six studies, and the lane reports under `lean/docs/`. What is
proved, by module, as the brief lists it, with the theorem names that bear weight for what follows:

- **Core4** (`Obend/Core/Term.lean`, 24 constructors including `hole n σ`, `reflect`, `metadata`,
  `perform`, `done`): weak-head call-by-name `Step`, deterministic; the call-by-need demand machine
  with cells `suspended | evaluating | cached`, blackholing, checkpoints as canonical token lists with a
  proved round trip; `Chain` relating machine states to the reference, one direction of adequacy only
  (`EQUIV-PLAN` §1: `Representation` is not inhabited; source-to-machine completeness open).
- **The checker**: bidirectional, structural, fuel-free, carrying its `PartialTyping` derivation; equi-
  recursive agreement by finite bisimulation (`REPORT-EQUIREC`: `visitedSame_iff`, option (c) landed);
  `full_annotated` completeness, noncomputable selection, executable preparation on the alias-free
  fragment (`REPORT-ELAB`: `prepare_checks`); coercions emitted by the elaborator, never in `Core`.
- **Laws** (`Obend/Law`): closed Core4 terms by occasion; the kernel judges by running a probe on the
  machine (`judge_sound` under every policy and budget, `judge_complete` with enough); inheritance along
  a validated C4 list with the ancestor named (`judgeEffective_names`, `child_never_widens`); the `.obend`
  fragment compiled with agreement to `denote`; package laws change only by upgrade.
- **The slot** (`Obend/Slot`): candidates, supports, a chooser, a judge; `World V Fact` with `holds_congr`,
  `retired_step`, `ver_step` and the collision stance; `read_congr` (two views agreeing on the pins of a
  candidate's supports read it the same); `Integrity.contextual` and `repair` for every World; stored
  selection incumbent-first; repair under `Compatible`.
- **The runner** (`Obend/Run`): `refines` and `reachable_legal` (every dispatched call admitted at its
  own view, no token spent twice, nothing in flight replanned); the Core4 adapter (`run_is_trace`,
  `trace_is_run`); mandatory selection control; the shared-World layer (`Run/Shared.lean`: `Ledger` with
  atomic commit laws, `joint_reachable_ticket_exclusive`, `loser_refused_names_winner_and_epoch`).
- **The audited fold** (`Obend/Fold.lean`): `Admission` with `keeps_world`, `step_of_reads`,
  `observe_ok`; `receipt_sufficient`, `step_of_pins`, `Family.step`, `project_run` under a per-row
  rely–guarantee; `Legal` and the law judge as instances.
- **Documents** (`Obend/Doc`, `Obend/Vault`): patches with `apply_compose`/`apply_invert`, merge as a
  pushout with `no_cocone`, sections as slots, identity and byte cites, backlinks, `obend open` on a
  markdown vault with laws in frontmatter.
- **Extension** (`Obend/Spec`): `package NAME extends REF`, intentions as slots (`stale_iff_blocked`),
  package laws inherited across packages, orthogonal protocols keyed by (generic, kind).
- **Not there**: a receipt type (`GENERATED` §0 found none); the Leaf emitter; `≈b` beyond definition 1
  (`Obend/Equiv`, `mix_assoc` proved, cost blind); the nominal-kinds decision; carry between versions;
  the judgment class and the intention module as modules (`GENERALIZATION` G2, G3).

Two facts from the trees shape every section below. INFERRED. First, the library is set-level on purpose
(`GENERATED` §0): every equation the admitter needs is definitional, and admission is a fold whose rows
read pinned facts; a receipt is the accumulator's roots plus the openings a row cites. Second, the
project's trust rule is already the one a symbolic system needs (`GENERALIZATION` §1.2): search belongs
to the producer, checking to every node, and the meaning/procedure/budget split of `Decides` is the
pattern. The vision below is those two facts carried to the center of a symbolic system.

## 2. What deos got right, what it got wrong, which frontiers this reaches

READ: `docs/what-is-deos.html`, `docs/deos/DEOS.md`, `APPS-AS-CELLS.md`, `CELL-HOSTED-VIEWTREE.md`,
`COCKPIT-UX.md`, `CROSS-DEVICE-FIRMAMENT.md`, `BRANCH-AND-STITCH-PROTOCOL.md`,
`CONSENSUS-TIME-AND-RECEIPT-IDENTITY.md`, `COMPUTRON-POLICY.md`, `AGENT-CONFINEMENT-REDTEAM.md`,
`CONDITIONAL-VAULT.md`, `DARK-AMM-PRIVATE-RECEIPT.md`; `metatheory/docs/DREGG-CALCULUS.md`,
`CELL-PROGRAM-LANGUAGE.md`, `FLOW-COMPOSITION-ALGEBRA.md`, `GUARDED-HOLES-METATHEORY.md`,
`FRONTIERS-BEYOND-DEOS.md`, `POLIS.md`, `POLIS-HYPERPROPERTY-FRONTIER.md`, `POLIS-METATHEORY-QUESTIONS.md`,
`LOGIC-COMPILER-ASSESSMENT.md` (TL;DR through §7), `AXIOM-HYGIENE.md`, `APPS-RECENSUS-DEOS-ERA.md`,
`DISCARD-CANDIDATES.md`; `metatheory/CONSTRUCTIVE-KNOWLEDGE.md`; `docs/vision/*.md`;
`docs/DREGGNET-CLOUD-OFFERINGS.md`, `docs/RECEIPT-CONTRACT.md`, `docs/COMMUNITY-BRIEF-CLOUD-FORGE-APPS.md`.
The GUI and cloud clusters were read by two colleagues (reports cited inline as "reader").

### 2.1 Right, and not yet taken by obend

1. **Authority is constructive knowledge, and affordances are the projection of the gate.** READ
   (`CONSTRUCTIVE-KNOWLEDGE.md` §0, §4; `DEOS.md`, `fire_authorized_iff_subset`): you hold a capability
   iff you can produce the witness the kernel accepts at the point of use; authority is not affine
   descent; a button is a cap-gated effect template and `project_for` returns the per-viewer affordance
   set; ungranted affordances are dim, never hidden (`HIG.md`, reader). INFERRED: obend has the
   first half (`requires` reusable, `consumes` affine; `admitOp`) and the law judge's "the request that
   would pass". It does not have the projection: the set of admissible requests for a member at a view,
   computed by the judge and handed to a surface. That projection is the whole GUI story (§7.3).
2. **Deferred witness, never a deferred decision.** READ (`APPS-AS-CELLS.md` §0, `collapse.rs`): a
   symbolic turn runs every admission gate identically and defers only the Merkle materialization;
   `collapse` reproduces byte-identical receipts. INFERRED: obend's disclosure dial (`GENERATED` §2.4) is
   the static form; the dynamic form (admit now, materialize the stranger-checkable receipt later, with
   a theorem that the two agree) is what an interactive notebook needs per keystroke.
3. **The modality price.** READ (`DREGG-CALCULUS.md` §4.1): each guard modality carries its
   coordination cost; a monotone guard runs coordination-free, a bounded one forces ordering, with a
   constructive clashing-pair witness; `guardKeepsConfluence` decides it. INFERRED: obend's
   `Family.step` has a per-row rely–guarantee premise and no classifier saying which laws make that
   premise vacuous. `GUARDED-HOLES` §5d states the theorem to take: `guardGluing_iff_iconfluent`.
4. **Consensus time.** READ (`CONSENSUS-TIME-AND-RECEIPT-IDENTITY.md`): finalized execution must be a
   pure function of consensus state and the finalized block; no local clock in the transitive input;
   a finalized receipt core separate from local signatures. READ (reader, `STANDING-OBLIGATION.md`,
   `RATE-LIMITED-ALLOWANCE.md`): at the capacity layer the clock was a caller-presented field
   (`Discharge.clock`, `Spend.at_block`). INFERRED: obend's `World` has pins and versions and no clock
   discipline; `Law.Syntax` reads `height` from the request (`REPORT-LAWDOC` §1). The law must be: time is
   a ledger fact the judge reads, never a request field.
5. **Branch-and-stitch: structurally imaginary until the one door.** READ
   (`BRANCH-AND-STITCH-PROTOCOL.md`, `DREGG-CALCULUS.md` §8): a branch holds no capability to main;
   its effects cannot leak; the only door is settlement under `settlement_soundness`; the I-confluent
   part merges by union and conflicts are objects with an explicit linear drop. INFERRED: obend has the
   document pushout and `no_cocone` per page, and the shared-World ledger; it has no World-level fork
   with confinement and one door. Offline-first (§7.2) needs it.
6. **The receipt contract.** READ (`RECEIPT-CONTRACT.md`): prev-hash chained, signed or QC-bearing,
   re-witnessable; anything else is a log. INFERRED: obend's receipt type (G4) should carry these three
   as fields, with `dated : View` the ledger's view.
7. **Determination eager, witness lazy.** READ (`GUARDED-HOLES-METATHEORY.md` §8.5): every hole dregg
   has is a lazy witness over an eager shape; a lazy δ is an outstanding imbalance, a lazy authority is
   off-circuit trust. INFERRED: obend's slot already satisfies this (the hole's type and the op's
   `consumes` are fixed at install; the fill is lazy). State it as an invariant on `Slot` and `Spec` so
   that no future "partial plan" feature breaks it.
8. **The reality gate.** READ (`VISION-reality-gated-substrate.md` §0): recompile one Lean file, the
   deployed verdict flips; revert, it flips back. INFERRED: obend's `#tooth` is the proof-side form of
   this. The deployment-side form (edit the law file in a vault, the next write is refused) is cheap in
   obend because Lean is the implementation; it should be a standing gate of `obend open`.
9. **Non-omission receipts for reads.** READ (reader, `DREGG-DATA-STORE.md` §3;
   `CONSTRUCTIVE-KNOWLEDGE.md` §8): a query answer ships with a range certificate against the receipt
   MMR; omission is a cryptographic impossibility. INFERRED: a report in a 1C successor is a judged fold
   whose receipt certifies completeness at a height (§7.2).
10. **Transclusion that confers no authority.** READ (`metatheory/docs/deos/TRANSCLUSION.md`, reader):
    `transclusion_grants_no_unheld_authority`, `_stable_under_source_advance`. obend's cites already have
    this shape; the theorem names are the ones to port.

### 2.2 Wrong, and not to be repeated

1. **Two rails.** READ (`LOGIC-COMPILER-ASSESSMENT.md` TL;DR): a real spec-first compiler spine whose
   emission targets a retired IR, and a deployed rail of 65 of 91 hand-written descriptors; "the spine
   exists; it is just wired to the wrong backend." Also three parallel predicate algebras, three
   executors with the proven one not live (reader, `RESEARCH-handler-executor.md`,
   `RESEARCH-predicate-language.md`). INFERRED: the regression signature is a second evaluator or a
   second ledger. obend's rule that Lean is the implementation and the kernel re-executes the core is
   the structural prevention; keep it, and refuse any "Rust twin for speed" until the leaf path has its
   refinement theorem.
2. **The mirror disease.** READ (`VISION-living-world.md` §0, `GAME-PROOF-LARP-AUDIT` as cited): a
   hand-authored Lean copy of the evaluator diverged from the Rust in two places, both real bugs.
   INFERRED: obend's trees have the same scar (`delvetalk` is a semantic fork, `ADOPTION-PLAN` §0); the
   cure is one library that the trees `require`, which is `SHIP.md`'s whole purpose.
3. **Floors false at deployed parameters, apexes over uninhabited types.** READ
   (`CONSTRUCTIVE-KNOWLEDGE.md` §6, ⚑ paragraph): `Poseidon2SpongeCR` is false at BabyBear; every apex
   over `CommitSurface` is vacuous; existence behind a root is proved, uniqueness open. INFERRED: the
   discipline obend already has (census, `#tooth`, "prove the floor false") must extend to any
   cryptographic instance it adopts: a `Digest` instance is registered with a refutation attempt at the
   deployed parameters, not a name.
4. **Breadth before one inhabited surface.** READ (`APPS-RECENSUS-DEOS-ERA.md`): 0 of 22 apps usable in
   the live image; registry apps on a side ledger; the app model superseded nine days after it shipped;
   250 docs and ~47 organs. READ (`VISION-the-whole-objective.md` §3): green on one laptop, nothing a
   stranger can touch. INFERRED: obend's `obend open ~/vault` is the right counter-move; the vision must
   keep one stranger-usable artifact ahead of every platform in §7.
5. **Untyped view IR with positional bindings.** READ (reader, `DEOS-VIEW-RICHNESS-EXPANSION.md` §0, §2):
   `Bind { slot: usize }`, `BindingId(n)` by pre-order walk, four hand-synchronized renderers; the fractal
   cell-hosts-cell with `MAX_MOUNT_DEPTH = 16` and a cycle cut (`CELL-HOSTED-VIEWTREE.md` §2). INFERRED:
   a lazy `fix` is the right treatment of a self-hosting view; a mount cycle is a knot, bounded by
   demand, not by a constant.
6. **Decision-bit certification.** READ (reader, `RESEARCH-predicate-language.md` §5): the circuit
   binds the aggregate decision bit, "the executor decided admit", not the policy's term. INFERRED: a
   receipt must bind the law's digest and the openings it read; obend's `GENERATED` §2.4 receipt does.
7. **Grand unifications that were shape identities.** READ (`VISION-the-whole-objective.md` §2,
   "non-domination ≡ light-client-unfoolability" retracted as a struct projection). INFERRED: obend has
   already paid this lesson once (`REPORT-JUST` §3: the semiring did not shorten the proofs). The test
   stays: a generalization is adopted only when it shortens proofs against a control.
8. **A verb catalog as a kernel.** READ (`DREGG-CALCULUS.md` §1.2–1.3): eight verbs, compressed to
   three, "ontology-relative"; 53 `EffectKind` constructors for conservation coloring, 30 live actions,
   routed by name. INFERRED: Core4 is a calculus with one `Step`; the business verbs of §7.2 must stay
   objects with laws, never kernel constructors.
9. **Four authority stories conjoined by `&&`.** READ (`CONSTRUCTIVE-KNOWLEDGE.md` §12): biscuit,
   macaroon, cap and zk narrow authority in separately-modeled lattices with no proven arrow between
   them. INFERRED: obend has one authority object, the slot's supports and the Spec's tokens; keep one.

### 2.3 The frontiers this vision reaches

READ (`FRONTIERS-BEYOND-DEOS.md`): the five ranked frontiers there (seL4 net-client, federation DKG,
`verify_stark` wiring, light-client DA, the Midnight bridge) are deployment welds of a Rust node; this
vision reaches none of them directly and should not try. The frontiers it does reach are the ones in
`POLIS-*`, `GUARDED-HOLES` and `FLOW-COMPOSITION-ALGEBRA`:

- **The interleaved multi-agent hyperproperty** (`POLIS-HYPERPROPERTY-FRONTIER.md` §2). INFERRED: the
  "unified trace over a shared state with projections" is the joint log of `Run/Shared.lean`; a
  `CaptureBar` with `loadBearing` and `leastRestrictive` is a judge instance with `sound` and
  `complete`; "decidable from the public trace" is the `checked` trust mode; Astra's two-run hyperlaw
  (`ASTRA-EFFECT-LAWS` §4) is its first fragment. The frontier's own hypothesis, that the polis object
  and the cross-cell whole-history confluence coincide, becomes in obend: both are `Family` theorems
  over the shared-World fold.
- **The governor as viability kernel** (`POLIS-METATHEORY-QUESTIONS.md` Q1–Q4). INFERRED: `Legal` is the
  governor; `child_never_widens` and `package_never_widens` are `combine_monotone`; the projection-
  soundness question (Q3) is exactly the runner's adapter theorems (`refines`, `trace_is_run`) restated
  for an external world. The "least-restrictive envelope" is "the refusal names what would pass".
- **`guardGluing_iff_iconfluent`** (`GUARDED-HOLES-METATHEORY.md` §6, §8.6): the one new theorem that
  document found worth proving. PROPOSED as an obend theorem over `Fold.Family`: a member's rely–
  guarantee premise is discharged for free iff its laws are monotone in the world component (§6.5).
- **The right skew** (`FLOW-COMPOSITION-ALGEBRA.md`). INFERRED: obend's plans are late-bound by
  construction (`Prot.call op k` with `k` a function of the reply), so the runner lives on the late side
  of `(P ⊔ Q) ⋆ R`; the decidable refinement of flows (`decideRefines`) is a judge instance for "does this
  protocol refine that one", and `Iface.accepts` is where it attaches.
- **The logic-arithmetization seam** (`LOGIC-COMPILER-ASSESSMENT.md` §6): quantifiers unrolled, two
  incomparable arithmetizations. INFERRED: obend's answer, already in `GENERATED` §2.3, is to
  arithmetize the machine (the law judge is VM-shaped, Cairo and Lurk's route) and never the logic.

## 3. The symbolic core

### 3.1 What a term rewriter and a notebook do not have

READ (Wolfram, "Everything Is an Expression" and "The Standard Evaluation Procedure", see §10):
Mathematica is one expression tree `f[a, b]`, evaluated to a fixed point by rewriting with rules held
in a global symbol table, with attributes (`Hold*`, `Flat`, `Orderless`) as ad hoc observer control, and
a notebook that is a list of cells with no provenance, no versioning, no second author and no certificate
behind any answer. INFERRED, the ten things the successor needs that this lacks:

1. certificates, not trust: every answer from a subsystem carries a checkable certificate or is labeled
   attested, and the receipt says which;
2. objects, not symbols: an expression is a partial object with laws, extended by strangers without
   forking (Faré's `fix`, intentions as slots);
3. documents with provenance: a notebook cell is a page section, a slot whose candidates are judged
   computations and whose cites lighten when the source verifies;
4. an observer ladder in place of `Hold` attributes: which rewrites are visible to which observers is a
   theorem, not a flag;
5. budgets as part of meaning: `TimeConstrained` becomes a graded judge with `uncovered` as a verdict;
6. heterogeneous subsystems as judges under one trust rule (§6);
7. versioned knowledge: `Entity` data and curated facts are pins in a World, dated and withdrawable;
8. members: an agent that proposes a simplification is refused like anyone, pays from a purse, and its
   proposal is a candidate with a justification;
9. three regimes labeled: decidable, semi-decidable, attestable, in the receipt;
10. deferred decisions: a cell whose result has two candidates ("`Simplify` gave X, `Reduce` gave Y") is a
    slot, with a chooser and a justification, not a silently picked one.

Maude is the closest existing symbolic core with reflection over many logics. READ (Clavel–Meseguer,
Meseguer 2012, §10): rewriting logic as a logical framework; reflection through a universal theory
(`META-LEVEL`, `metaReduce`); strategies as meta-level programs. INFERRED: its lesson is that a
reflective tower over a rewriting engine is expressive enough for a logical framework, and its cost is
that the meta level is the engine itself, trusted. obend's version keeps the meta level judged (§4.3).

### 3.2 Is Core4 the right center?

INFERRED. Three candidates for the object at the center of a symbolic system: a term rewriter (Maude,
Mathematica), an e-graph (equality saturation; READ Willsey et al. 2021, Tate et al. 2009, §10), or a
lazy object calculus with laws (Core4). The first two are *search structures*: a rewriter searches for a
normal form, an e-graph searches a space of equalities and extracts. Both belong to the producer. The
kernel of a symbolic system that never trusts search needs at its center a thing that *checks*: a
judged fold over a World whose rows cite pinned facts. That is what obend already has, and the lazy
object is the right *value* at the center because partial objects (a specification under construction,
a notebook half written) are values a law can be judged on. So the center is not a different object.

What Core4 lacks, and must gain, is terms as data. READ (`REFLECTION.md`, minidregg; `Core/Term.lean`):
the observers are `metadata` (a `SpecMeta` value), `reflect` (the specification in a prototype),
`targetOf`, application/`fix`/`mix`, and string equality on `SpecMeta` fields; there is no observer of a
closure's code or a law's code. For a symbolic core that is exactly backwards: the thing it manipulates
is code. PROPOSED, `quote`:

- a constructor `quote : Term → Term` whose value is a first-order `Data` representation of the quoted
  term up to α, content-addressed by `Core/Digest` (the Lurk lesson, READ `audit-inference-lurk.pdf`:
  a term's identity is a digest and substitution is pointer manipulation; the hashing-modulo-α
  construction is Maziarz et al. 2021, §10); `splice : Term → Term` its inverse on well-typed data, typed
  `Code A → A`;
- a new equivalence `≈q`: equality of quotations (syntactic up to α and content address), with the
  theorem `observer_ladder : ≈q ⊆ ≈r ⊆ ≈b` and cost (`≈c`, `EQUIV-PLAN` definition 2) as a refinement of
  `≈b` that `≈r` and `≈q` both imply;
- the congruence theorem a rewriter needs: `rewrite_sound_below : (a ≈k b) → (∀ C, observers(C) ≤ k →
  C[a] ≈k C[b])`, with `k` ranging over the ladder. This is `REFLECTION.md`'s rule ("a rewrite justified
  by `≈b` may be applied only where no `metadata` observer can reach") stated once for all levels, and
  it is the principled form of Mathematica's `Hold` attributes;
- a judge instance `RewriteJudge` (§6): a certificate is a sequence of rule applications from a declared
  rule set, each rule a law of the kind the term belongs to, each step checked by `≈q` on quotations;
  equality-saturation extraction is a producer whose output is such a certificate (egg produces proofs;
  READ Willsey et al. §10, proof production).

What this does not change: the kernel never rewrites; the law judge still re-executes a probe; a
symbolic simplification is a candidate in the section's slot with a `RewriteJudge` certificate as its
support. A `Simplify` whose result has no certificate is an `attested` candidate and the receipt says so.

### 3.3 The notebook as a document

INFERRED from `DESIGN.md` §5 and `REPORT-VAULT`. A notebook is a page of kind `Notebook`; an input cell
is a section whose candidate is a quoted term; an output cell is a section whose candidates are the
judged results (one per judge that answered) with their certificates as supports; a cell that depends
on another cites it by byte, so editing an input darkens every output that quoted it until re-judged;
a second author's edit is a candidate; a kernel restart is a World step; the whole notebook is a
`Vault` page on disk. "Evaluate" is `obend judge` over the section. The notebook needs nothing a page
does not have, which is the test that the Doc layer is the right one.

### 3.4 Lane-briefable targets for the core

PROPOSED, each additive in `Core` except the first.

| target | shape | tooth |
|---|---|---|
| `quote`/`splice` | two constructors, `Step.quoteValue`, `Step.spliceQuote`, typing `Code A`; `Data` representation content-addressed | a quoted term's digest changes under a non-α rename; equal under α |
| `≈q` and `observer_ladder` | `Obend/Equiv/Quote.lean`; the ladder as three inclusions | `mix_assoc` holds under `≈b`, fails under `≈r` (`REFLECTION.md` probes R01/R02), fails under `≈q` |
| `rewrite_sound_below` | over `Ahead`-style contexts with an observer census | a `metadata`-observing context separates two `≈b`-equal specs |
| `RewriteJudge` | an instance of `Judge` (§6.2); certificate = rule-application trace | a trace citing an undeclared rule is refused by name |

## 4. Staged reflective metaprogramming

### 4.1 The lineage, read against what obend has

READ (Smith 1984; Wand–Friedman 1988; Danvy–Malmkjær 1988, §10): 3-Lisp's tower is an infinite
sequence of interpreters each running the one below; Wand and Friedman show the tower is a single
non-reflective interpreter with a meta-continuation, and that reflective procedures are the ones that
receive the continuation and environment as data. READ (Amin–Rompf 2018): a tower of interpreters
collapses by staging, each level written with `lift` so that interpreting a program that is itself an
interpreter specializes it away; stage polymorphism lets one interpreter run or generate code. READ
(Rompf–Odersky 2010; Taha–Sheard 2000; Kiselyov 2014): LMS makes staging a type (`Rep[T]`) and
generates code by evaluating the generator; MetaML's brackets, escape and `run` are typed so that staged
code is well-typed before it runs; BER MetaOCaml's residual problem is scope extrusion, a variable
escaping the stage that bound it. READ (Nanevski–Pfenning–Pientka 2008, already in paperbin): a
metavariable `u :: (Ψ ⊢ A)` carries its context; `□(Ψ ⊢ A)` is code open in `Ψ`; substitution for a
metavariable is the one operation. READ (Kovács 2022; Xie et al. 2022): two-level type theory puts a
dependent meta level over an object level with `⇑`, quote and splice, and staging is evaluation of
the meta level; typeclass-directed generation is the practical form. READ (Ullrich–de Moura 2020;
Ebner et al. 2017; de Moura–Ullrich 2021 in paperbin): Lean's elaborator is a metaprogram in `MetaM`
producing kernel terms the kernel checks; macros are hygienic syntax transformers; the elaborator is
untrusted by construction. READ (Bracha–Ungar 2004): reflection should be mediated by mirrors, objects
that are handed out as capabilities and separate the reflected-on object from its meta-level
interface, so reflection is neither ambient nor tied to the object's representation.

INFERRED, what obend already is in this lineage, stated exactly:

- The slot *is* CMTT: `hole n σ` with its filling closed (`Scoped 0`, `open_filling_tooth`), the
  substitution law `calculus_check_msubst`, and the meaning/procedure split; a filling that passes the
  judge at its hypotheses' types keeps the filled term typed (`checked_msubst`). The `Scoped 0`
  discipline on fillings is, read as staging, the absence of scope extrusion by construction: a stage-n
  term cannot capture a stage-(n+1) binder because a filling may not be open.
- The template elaborator is a two-level type theory in practice: Lean above, Core4 below, open
  specifications checked once and instantiated per `fix` (`MODULAR-TYPING` D1), which is Faré's remark
  that C++ templates are a lazy prototype language at compile time (`DESIGN.md` §1) and Kovács's
  object/meta split with `⇑` as "the type a template's `Self` will have".
- The front end is Lean's elaborator pattern already: the parser and elaborator are trusted with no
  theorem (`SHIP.md` §2), admission re-runs the checker on the core, and `admitted_front_end` demands a
  byte-identical core.
- Reflection is read-only and first-order (`REFLECTION.md`): `metadata` returns data, never code; laws
  are hidden knot fields with a status; reflection cannot change behaviour. That is the law-abiding
  half; the missing half is that it is ambient (anyone holding a prototype may `reflect` it) and
  blind to code.

### 4.2 What the reflection must grow into

PROPOSED, four growths, each a lane.

**R1. The observer ladder** (§3.2): `≈q ⊆ ≈r ⊆ ≈b`, `rewrite_sound_below`. This is the law-abiding part
made exact: a meta-level rewrite is admitted at level `k` only in contexts that observe at most `k`.

**R2. Reflection as a mirror capability.** A `Mirror` is a `Data` value naming a prototype and a depth
in a lattice `structure ⊑ metadata ⊑ code ⊑ live` (READ reader: deos designed exactly this as
`Target::Mirror{over, depth}` with `MirrorDepth: Structure ⊑ ReadState ⊑ Live`, and never built it,
`FIRMAMENT-REFLEXIVE-SUBSTRATE.md`). `reflect`, `metadata` and `quote` take a mirror, and a package
declares which depths it grants and to whom, as a law on the `invoke` occasion. Consequence: hiding a
law's code is a disclosure choice stated in the package, which is the honest home of the tension
`GENERATED` §3.2 found between why-not completeness and confidential refusals. Theorem target:
`mirror_attenuates`: a mirror derived from a mirror observes no more.

**R3. Stages are views; the tower is a sequence of Worlds.** The reading that makes the tower collapse
without a partial evaluator: a stage is the view of the World at which a thing is decided. Elaboration
is the view where templates are instantiated and intentions resolved; adoption is the view where a
package's laws attach to an instance; dispatch is the view where a plan's supports are rechecked. A
quoted term with holes is code at a later stage; filling a hole is `splice`; `fix` at a view is `run`.
MetaML's three operators are, respectively, `quote`, a slot fill, and `fix` under pins. The tower:
`relaw`, `adopt` and `upgrade` are *meta-turns*, turns in a World whose cells are packages and whose laws
are the metarule (a law must admit its own amendment) and `package_never_widens`; a meta-turn's receipt
at level n+1 is a pin at level n. The collapse theorem, PROPOSED: `stage_collapse`: re-elaborating a
term at a view where every pin it cites is resolved yields a term `≈q` to the one elaborated at genesis
with those pins substituted. This is Amin–Rompf's collapse restated: the "interpreter" at each level is
the resolution of intentions, and it specializes away when the intentions are pinned. Wand–Friedman's
observation returns as a design fact: there is one kernel, and reflective operations are the ones that
receive the World view as data.

**R4. Boundaries as embedding–projection pairs.** READ (New–Ahmed 2018; New–Licata–Ahmed 2019;
Patterson–Mushtak–Wagner–Ahmed 2022; Patterson–Ahmed 2017; Matthews–Findler 2007, §10): a boundary
between languages is a pair of conversions that form an embedding–projection pair in a shared semantic
model; graduality is the statement that adding precision never changes behaviour except to introduce
errors; semantic soundness for interoperability is proved by interpreting each language's types into a
common model rather than by syntactic embedding; linking types let a program state what it expects of
the code it links against. INFERRED for obend: every foreign subsystem (a Bend leaf, an SMT solver, a
CAS, a prover) enters through a boundary with an EP pair between a Core4 type and the subsystem's input
and output types, and the subsystem's claims enter through the judge's `sound` theorem, which *is* the
semantic model of its certificate format in the kernel's logic. The gradual spectrum is the trust field:
`attested` is the dynamic end (the claim is an opinion under a name), `checked` the static end (the
claim is a certificate the kernel verified). PROPOSED theorem, the gradual guarantee for trust:
`trust_mono`: replacing an `attested` support by a `checked` certificate of the same statement changes
no verdict, only the receipt's trust field. The leaf boundary gets the same shape: `DESIGN.md` §3's
`leafProof (package, lawName, kernelHash)` is an EP pair between a Core4 law and a BendTT law, and
the leaf refinement theorem is its soundness.

### 4.3 The reflective tower, judged

INFERRED. 3-Lisp's danger is that a reflective procedure can do anything to the level below.
Kiczales's metaobject protocols (READ, §10) channel that power through a protocol; mirrors channel it
through capabilities. obend channels it through laws: a reflective change is an audited meta-turn
judged by meta-laws, so "what may the meta level do" is the same question as "what may a member do",
answered by the same judge, and a refusal at the meta level names the clause. There is no
intercession in the MOP sense except `relaw` and the slot fill, both audited. This is the one design
decision of this section I would defend against the whole lineage: the tower is not a stack of
interpreters and not a stack of protocols; it is a stack of Worlds with the same kernel.

### 4.4 Lane-briefable targets

| target | shape | tooth |
|---|---|---|
| `Mirror` and depths | `Obend/Core/Mirror.lean`; `reflect`/`metadata`/`quote` take a mirror; `invoke`-occasion law per package; `mirror_attenuates` | a `metadata` mirror cannot `quote` |
| `stage_collapse` | `Obend/Spec/Stage.lean` over `Ecosystem.close` and intention pins | moving a pin changes the collapsed term by name (`stale_iff_blocked`) |
| meta-World | `Obend/Law/Meta.lean`: packages as cells, the metarule as a law, `relaw`/`adopt`/`upgrade` as rows of a `Fold.Admission` | a relaw that does not admit its own amendment is refused naming the metarule |
| `trust_mono` | in `Obend/Receipt.lean` (§6.3) | an `attested` support with a wrong statement is not replaceable by any certificate |
| EP boundary class | `Obend/Boundary.lean`: `Boundary A B` with `embed`, `project`, `retract : project ∘ embed = id`, `sound` | a boundary whose `project` forges a shareable type is refused (`agree_never_manufactures_shareability`'s shape) |

## 5. The runtime: one intermediate language across the tower

### 5.1 What the tower looks like today

READ: Lean elaborator (meta) → Core4 (object, lazy, non-affine) → Bend book (leaf, strict, affine) →
C/Metal/CUDA/JS (`bend/AGENTS.md`: `bend2/comp.ts` emits the four backends; BendTT at Lean v4.34.0,
obend at v4.35.0). `DESIGN.md` §2 gives the emission rule: acyclic method graphs as plain defs, a
strongly connected component as a dispatcher with descending fuel, everything else on the represented
demand machine compiled by Bend. The demand machine is call-by-need with checkpoints
(`Core/Machine.lean`, `Core/Checkpoint.lean`), proved equal to the reference in one direction (`Chain`).

READ (Würthinger et al. 2013, 2017; Bolz et al. 2009; Futamura 1999; Jones–Gomard–Sestoft 1993, §10):
Truffle is an AST interpreter whose nodes self-specialize on profiles; Graal partially evaluates the
interpreter with respect to the AST (the first Futamura projection, at run time) under assumptions,
and deoptimizes to the interpreter when an assumption fails, carrying frame-state metadata to do it;
PyPy meta-traces the interpreter. None of these steps has a theorem; the deoptimization metadata is
large; polyglot interoperability is a dynamic message protocol. READ (Moran–Sands 1999; Hackett–Hutton
2019; `EQUIV-PLAN`): the cost-sensitive equivalence a lazy language needs is improvement, and
call-by-need cost is clairvoyant call-by-value cost; obend has `≈b` (definition 1) proved and
definitions 2 and 3 planned.

### 5.2 The trim design

PROPOSED. One intermediate language: Core4 with pins. Binding-time analysis is pinnedness: a subterm
all of whose intentions are resolved and whose supports are permanent is static; everything else is
dynamic. Specialization is re-elaboration at a view (`stage_collapse`, §4.2). Four consequences:

1. **A specialized artifact is a slot candidate.** The emitted Bend book for `fix(compose(...))` at a
   view is a candidate in a slot whose supports are the pins it assumed (the versions of the intentions
   it resolved, the laws it compiled in, the kernel hash of the BendTT verdict). The demand machine
   running the unspecialized term is the other candidate, always usable. Incumbent-first selection
   prefers the book while its supports hold. When a pin moves, the book's support is `blocked` by name
   (`stale_iff_blocked`) and the machine candidate is selected: **deoptimization is the withdrawal of a
   support**, and `Integrity.contextual` and `repair` are the JIT's policy theory, already proved.
   Truffle's assumption objects and invalidation are exactly this with no theorem.
2. **Checkpoints are the deoptimization frames.** A book that reaches an unpinned slot suspends with a
   canonical checkpoint (`Checkpoint`'s round trip) and the machine resumes it; the obligation is that
   the suspension point in the book corresponds to a machine state in a `Chain` with the reference.
   This is the frame-state correspondence Graal carries as metadata and never proves.
3. **An optimization is a candidate with a justification.** A rewrite the elaborator applies is admitted
   under `rewrite_sound_below` at the observer level of the context, and a *cost* rewrite (inlining,
   sharing) is admitted under improvement (`EQUIV-PLAN` definition 2, `L ≈ᶜ R` with explicit constants).
   The receipt for a run names the candidate that ran and its justification, so a member who paid ticks
   can see which specialization they paid for. This closes `ALGEBRAIC-SUBTYPING` §3.7's concern that
   coercions change what a member is charged.
4. **Leaves are affine and strict, and that is where parallelism lives.** Nothing in the lazy layer
   competes with Bend's leaves; Taelin's claim and Faré's claim stay in their own terms (`DESIGN.md` §1).
   The interaction-combinator runtime (READ Lafont 1997; HVM2, §10) is the leaf's business.

Trim means: one IL (Core4), one machine (demand), one proof per boundary (`Chain` for machine against
reference, the leaf refinement against `bendtt.lean`'s `Eval`, `stage_collapse` for specialization),
and no optimizer in the trusted base, because every optimization is a candidate under a judge. More
powerful means: the thing GraalVM cannot say, "this compiled code is equivalent to this program under
this cost measure, and here is who assumed what", is a receipt.

### 5.3 Where the foundation is thinnest

INFERRED. `EQUIV-PLAN` §1: `Representation` is not inhabited; source-to-machine completeness and
administrative progress are open; adequacy is one direction. Every statement in §5.2 that relates a
book or a checkpoint to the reference semantics passes through the machine, and the machine's
correspondence to the reference is half proved. Second, `≈b` definition 1 is cost-blind and the world
prices cost; until definition 2 and the ticks-to-CV constant-factor theorem (`EQUIV-PLAN` §5.3) exist,
an improvement certificate has no meaning the world charges. Third, the leaf refinement needs
`bendtt.lean` at 4.34 against obend at 4.35; the toolchain decision (vendor or wait) is a real fork.
These three are the order of §9.3.

### 5.4 Lane-briefable targets

| target | shape | tooth |
|---|---|---|
| `SpecializationSlot` | `Obend/Leaf/Slot.lean`: candidates `{machine, book}`, supports = pins and the BendTT verdict hash; incumbent-first | moving a cited pin selects the machine candidate; a forged verdict hash is blocked by name |
| checkpoint correspondence | `book_suspends_in_chain`: a book's suspension state is in `Chain` with the machine state at the same demand | a book that suspends one tick early has no chain partner |
| improvement judge | `Obend/Equiv/Improve.lean`: definition 2 with Skip at Core4's binding sites; `L ≈ᶜ R` with constants | `mix_assoc` has κ = 7 ticks at k = 0 (`EQUIV-PLAN` §2) |
| leaf refinement | `Obend/Leaf/Refine.lean`: `accepted_execution_semantics` against `Eval` of the emitted book | a book with one method renamed fails the refinement by name |

## 6. Automation as powerful as the laws permit

### 6.1 The one discipline, and what "as powerful as the laws permit" means

READ (`GENERALIZATION` §1.2; `ASTRA-EFFECT-LAWS` §7; `METATHEORY.md` §1): search belongs to the
producer, checking to every node; a judge is a certificate checker over a declared domain with a budget;
`uncovered` is not `false`. READ (Necula 1997; Appel 2001, §10): proof-carrying code is the archetype:
the producer searches, the consumer checks a certificate against a small checker; foundational PCC
reduces the checker's trusted base to a logic. READ (Filliâtre–Paskevich 2013; Blanchette–Böhme–Paulson
2013; Armand et al. 2011, §10): Why3 drives many provers from one verification condition with a proof
session; Sledgehammer sends goals to untrusted ATPs and *reconstructs* the found proof in Isabelle's
kernel; SMTCoq checks SMT proof witnesses in Coq. READ (Kaufmann–Moore 1997; Moore 2019, §10): ACL2's
waterfall is a strategy whose output is not a checkable proof object, so ACL2 is trusted as a prover.
READ (Torlak–Bodik 2014): Rosette symbolically executes a host language's programs to produce solver
queries, so synthesis and verification are host-level operations over an untrusted solver.

INFERRED, the three regimes, with what the kernel may say in each:

- **Decidable.** Everything the kernel does itself: `sameType` by finite bisimulation, C4 validation,
  reads over pins, the law probe at a budget, the fold, membership in a finite table, checking a
  certificate of any registered format. The verdict is `ok` or `refused <clause>`, or `uncovered` when
  the budget ran out, and `uncovered` is monotone in the grade (`check_mono`).
- **Semi-decidable.** Existence of a certificate: a proof, a satisfying assignment, a stable model, a
  program meeting a spec, a rewrite to a normal form. The producer may not halt; the kernel sees a
  certificate or nothing. A refusal in this regime must distinguish *refuted* (a counter-certificate:
  a countermodel, a `DRAT` proof of unsatisfiability, a failing test case for a synthesized program)
  from *unproved* (budget, timeout) from *attested* (a named party says so). READ (`ASTRA-EFFECT-LAWS`
  §5, the asymmetric certificate table for ASP): this is the pattern for every solver.
- **Attestable only.** Non-termination (`spin`), unbounded liveness, universal claims over infinite
  traces, prose claims, physical facts. The kernel can bound them (liveness within `B` steps becomes
  safety; READ `POLIS-METATHEORY-QUESTIONS.md` Q1, the `cwithin` trick) or attest them (Astra's third
  trust mode, `GENERALIZATION` §0). Rice's theorem is the law: a property of a black-box subsystem's
  behaviour is only attestable; a property of its certificate is decidable.

"As powerful as the laws of computer science permit" is therefore a design rule, not a slogan: *the
system is as automated as the set of certificate formats it can check, and every claim it makes is
labeled with the regime it was established in.* Power comes from the breadth of the registry and the
cheapness of its checkers, never from trusting a cleverer producer. The LLM-proposed invariant (READ
Si et al. 2018; Pei et al. 2023; First et al. 2023, §10) is the clearest case: the proposal is free,
the check is the judge, and nothing about the proposer enters the receipt except as a `producer` field.

### 6.2 The judgment class and the certificate registry

PROPOSED, `Obend/Judge.lean`, generalizing `Decides` (`GENERALIZATION` G2):

```
class Judge (Obj Cert R : Type) [Graded R] where
  check    : R → Obj → Cert → Verdict            -- deterministic; Verdict = ok | refused Clause Path | uncovered
  sound    : check r o c = ok → Meaning o c      -- the certificate format's semantic model
  complete : Covered o c → ∃ r, check r o c = ok -- on a stated fragment
  mono     : r ≤ r' → check r o c ≠ uncovered → check r' o c = check r o c
```

and a registration record, which is what a *format* is:

```
structure Format where
  name, version : String
  Obj Cert : Type;  judge : Judge Obj Cert R
  encode   : Domain → Obj                        -- the lowering from the kernel's object to the solver's
  encode_sound : Meaning (encode d) c → Claim d  -- the encoding is part of the trust boundary
  refusals : List Clause                         -- the format's refusal vocabulary: refuted | unknown | malformed | budget
  tooth    : ∃ c, check ⊤ o c = refused _ _      -- a planted bad certificate is refused
  cost     : Obj → Cert → R                      -- the budget contract
```

INFERRED, the two lessons from breadstuffs that belong in the record: the encoding is a theorem, not a
convention (`LOGIC-COMPILER-ASSESSMENT` §6, and the reader's note on a SAT certificate for the wrong
encoding certifying the wrong question), and a format whose certificate is a decision bit is refused
registration (`RESEARCH-predicate-language.md` §5). The five existing judges instantiate the class with
no new proofs: the bidirectional checker (`Cert` = annotations, `sound` = `checkAgainst_sound`,
`complete` = `full_annotated`), the law machine probe (`judge_sound`/`judge_complete`), `coerce`
(`coerce_checks`), the protocol envelope (`HasProt`), C4's validated linearization (`precedence_ok`).

### 6.3 The solver roster, each with its trust boundary

PROPOSED, the registry's first rows. "Checker" says whether a verified checker exists in the literature;
"trusted" says what remains trusted after the certificate is checked. READ for the formats: Cruz-Filipe
et al. 2017, Heule et al. 2013 (DRAT/LRAT); Barbosa et al. 2022, Schurr et al. 2021 (cvc5, Alethe);
Gocht–Nordström 2021 (VeriPB); Alviano et al. 2019 (ASP-DRUPE, in paperbin); Assaf et al. 2016
(Dedukti); Harrison 2007 (sums of squares); Buchberger 1965/2006 (Gröbner cofactors), see §10.

| solver | object judged | certificate | checker | trusted after checking | regime |
|---|---|---|---|---|---|
| SAT | a CNF from `encode` | a satisfying assignment; LRAT for UNSAT | yes, verified LRAT checkers exist (ACL2, CakeML); ours is ~200 lines of Lean | `encode_sound` only | semi-decidable; UNSAT with LRAT is decidable to check |
| SMT | an SMT-LIB script | Alethe/LFSC proof; a model for SAT | partial: Alethe steps for QF theories; nonlinear arithmetic steps often `hole` | the unchecked steps, named per proof | `unknown` is a verdict, never `false` |
| pseudo-Boolean / ILP bounds | a PB or LP instance | VeriPB for PB; a dual-feasible solution for an LP bound (LP duality makes a bound checkable by one matrix product) | yes for PB; LP dual check is arithmetic | the encoding; integrality claims beyond the LP bound are attested unless branch certificates are given | feasibility semi-decidable; optimality via certified bounds |
| ASP | a finite grounded normal program | a stable model (GL reduct check); ASP-DRUPE for inconsistency | yes, the reduct check is a fixpoint | grounding (`encode`), the `complete_program` claim | credulous `q` decidable-to-check; skeptical needs countermodel exclusion |
| CAS identities | polynomial or elementary-function expressions | the *reverse operation*: cofactors `f = Σ cᵢ gᵢ` for ideal membership; a derivative for an antiderivative; a substitution for a root; SOS decomposition for nonnegativity; a rewrite trace (§3.2) for `Simplify` | yes: each check is evaluation or a `RewriteJudge` trace | nothing beyond the arithmetic; probabilistic identity tests (Schwartz–Zippel) are `attested` unless exact | decidable to check; the search is the CAS's |
| model checkers | a finite transition system from `encode` | an inductive invariant; a product invariant for 2-safety (`ASTRA-EFFECT-LAWS` §4); a ranking function for bounded liveness | yes: `Init ⊆ J`, `Step(J) ⊆ J`, `J ∩ Bad = ∅` by `decide` on finite systems | the abstraction's soundness (`ConcreteRefinesAbstract`), stated as a separate judge | unbounded safety decidable to check on finite abstractions; liveness bounded |
| Lean / HOL / Isabelle | a proposition in the kernel's logic | a proof term (Lean: re-checked by `lean4checker`-shaped replay; Dedukti as the lingua franca for HOL and Isabelle exports) | yes | the exporter for foreign provers; the kernel for Lean | decidable to check |
| proof search (waterfall, ATP) | a goal | *reconstructed* proof (Sledgehammer's architecture); an ACL2 verdict without a proof object is `attested` | reconstruction is the Lean judge | the hint is never trusted | semi-decidable |
| LLM proposals | an invariant, a lemma, a plan, a prose claim | whatever the target judge accepts; prose has none | by the target judge | nothing of the proposer | the proposer's regime is irrelevant; the claim's regime is the target's |
| the law judge, the checker, the fold | obend's own objects | the probe run, the annotations, the openings | the kernel | nothing | decidable, graded |

INFERRED: three roster-wide rules. (a) Every certificate format needs an `encode` from an obend object,
and `encode_sound` is where the real work is; a lane that adds a solver has not finished until the
encoding is a theorem. (b) Every format's refusal vocabulary must separate refuted from unproved; a
registry entry that cannot say "refuted" is a weaker judge, admitted but labeled. (c) The receipt's
`trust` field is per support, not per receipt: a verdict resting on three checked certificates and one
attestation is `attested` as a whole and names which support.

### 6.4 Synthesizing and operating upon other systems

INFERRED. "Operate upon" has two readings and both are covered: a foreign system's *artifacts* are
data (`quote` for terms, `Data` for certificates, pages for its documents), and its *claims* are
certificates under a format. "Synthesize" is search by construction: a synthesizer (Rosette-style
symbolic execution of Core4 on the demand machine, an LLM, a CEGIS loop) produces a candidate program
and a certificate that it meets its specification (a proof, a bounded-model-check invariant, a test
suite that is itself a judged fold); the candidate enters a slot; a chooser selects; the receipt names
the synthesizer only as producer. Why3's proof session and Sledgehammer's reconstruction are the two
producer-side tools worth building first, because they multiply every registered format by every goal
shape. PROPOSED: a `Session` object, a page of kind `ProofSession` whose sections are goals, whose
candidates are certificates from different formats, with incumbent-first selection, so that a goal
proved once by SMT and later by a Lean term keeps the stronger certificate and the receipt shows the
history. That is the symbolic core's "notebook" for proofs, and it is the same page type as §3.3.

### 6.5 Lane-briefable targets

| target | shape | tooth |
|---|---|---|
| `Judge` and `Format` | `Obend/Judge.lean`; the five instances; `Registry : List Format` | a `Format` with a trivially-true `check` has no `tooth` and is refused registration |
| LRAT judge | `Obend/Judge/Lrat.lean`: CNF as `Data`, LRAT steps, RUP check by unit propagation; `encode` from a finite-domain law | a planted deletion of a needed clause is refused naming the step |
| reduct judge | `Obend/Judge/Stable.lean`: the GL reduct as a fixpoint; Astra's six fixtures (`ASTRA-EFFECT-LAWS` §10) as `decide` probes | self-support `0 :- 1; 1 :- 0` has no stable model |
| product-invariant judge | `Obend/Judge/Product.lean`: `Init ⊆ J`, `Step J ⊆ J`, `J ∩ Bad = ∅` on finite systems; the two-run hyperlaw as its first client | the refined system of `ASTRA-EFFECT-LAWS` §4 (output = secret) is refused |
| `guardGluing_iff_iconfluent` | over `Fold.Family`: a member's `Guarantee` is discharged for every interleaving iff its laws are monotone in the world component | the ticket (bounded) needs the shared commit; a grow-only register does not |
| `ProofSession` page | a Doc kind with sections as goals, candidates as certificates | a withdrawn format version blocks every candidate citing it by name |

## 7. The platforms

### 7.1 Smart contracts, replacing Mina

READ (Bonneau et al. 2020; Chiesa–Tromer 2010; Kothapalli–Setty–Tzialla 2022; Bowe et al. 2020, §10):
Mina keeps the chain succinct by recursive proofs; a zkApp's logic runs off chain and a proof of the
state transition is posted, with preconditions on the account state the transaction assumed; proof-
carrying data and folding schemes (Nova) make "fold the history" a primitive. READ (`DREGG-VS-ETHEREUM`,
`VERIFIED-LIGHTCLIENT-FOLD-PATH`, `INTERCHAIN-MODEL`, reader): breadstuffs settled that rules fold and
crypto stays a named leaf, that the apex must take only what a light client has, that two trust rungs
in one artifact stream must be visible in the type, that the Mina leg was scoped and not built and its
predecessor relay was vacuous, and that a Groth16 apex with a single-party ceremony is the one thing a
Mina replacement must not inherit.

PROPOSED, the contract platform, in obend's own objects:

- **A contract is a package root.** Its state is a World cell; its laws are the package's laws by
  occasion; strangers extend it by `package X extends contract@^1` without forking, and the vendor's
  upgrade is a repair offered to each instance at its next write (`adopt` arm). Mina's permissions
  (`editState`, `send`, `setVerificationKey`) are laws on occasions; `setVerificationKey` is `upgrade`,
  which `REPORT-LAWDOC` already makes the only way a package law changes.
- **A transaction is a turn.** The member's plan yields operations; each is admitted at the dispatch
  view by `admitOp` and the effective law; Mina's preconditions are `DecisionsHeld` and `Authorized` at
  the view of dispatch, which the runner already proves (`refines`).
- **The chain is the shared-World ledger.** `Run/Shared.lean`'s `Ledger` with its atomic commit laws
  is the sequencer; `joint_reachable_ticket_exclusive` is no double-spend; validators are re-executing
  judges; `Ledger.Durable` is the persistence law; consensus time (§2.1 item 4) is a field of the ledger
  record that every law reads.
- **A receipt is a proof, at three positions of the dial.** With the log, a follower re-executes
  (`refines`); with the openings, a stranger recomputes the verdict from pins (`receipt_sufficient`,
  computable once `holdsOfPin` exists); with one bit, a light client needs a succinct proof of the fold.
  The third position is not built and the charters say not now; the design obligation is only that the
  fold stay IVC-shaped (`GENERATED` §2.3: `Legal` is `AtEach` over `foldl`, the nullifier set is
  `OnceSpent`, the machine's `Checkpoint` is the row encoding). The verifiable-computation story is
  therefore: build the receipt so that the one-bit position is a later *instance* of the same type, with
  the lessons of §2.2 items 3 and 6 as its registration conditions (a hash floor refuted at the deployed
  field, the law's digest bound, never a decision bit).
- **Privacy** is the dial plus Astra's two-run hyperlaw on public receipts, judged at install by the
  product-invariant judge (§6.3); confidential refusals trade names for a coarser reason, which `Poly`'s
  normal form specifies (`GENERATED` §3.2).
- **Cross-contract composition** is `Fold.Family` with rely–guarantee, and `guardGluing_iff_iconfluent`
  says which contracts need the shared commit and which may run coordination-free.

What differs from Mina, in one line each: contracts are lazy objects with a mechanized metatheory, not
circuits; laws inherit across packages and refusals name what would pass; proofs are a position of a
dial rather than the substance of the chain; and a document and a contract are the same object.

### 7.2 Hybrid desktop/cloud business software, replacing 1C

READ (the 1C:Enterprise Developer Network pages fetched for this study, `1c-dn-*.txt`, §10): 1C is a
metadata-driven platform: "a developer thinks in terms of metadata ('data that describes data'), or
configuration objects"; a base configuration is edited in the Designer and a database configuration is
what users run; an accumulation register holds records with dimensions and resources, "changes to the
accumulation register generally occur when a document is posted", and the platform derives balance and
turnover tables from the records; an accounting register is "tightly linked to a chart of accounts";
an information register sets a value per key (periodic or not). From memory, not in the fetched pages:
distributed infobases exchange changes offline with conflict resolution by priority, and *configuration
extensions* let a customer change a vendor's configuration without modifying it. READ (reader, the deos cloud
cluster): breadstuffs had registers with laws as Rust house capacities (escrow, obligation, allowance,
vault, derived cells), each with a Lean rung, and "no notion of a document type, posting, or report as
data a non-programmer configures; every register was a Rust module with a bespoke API."

PROPOSED, the business platform, in obend's objects:

- **Metadata objects are kinds, and kinds are cells.** The nominal-kinds decision (`REPORT-EXTENDS`
  "Decision for Ember", recommended nominal) is the gate for this platform: a catalog, a document type
  and a register are kinds with laws; an instance carries its kind's identity; the kind's law is an
  ancestor of each instance's effective law. The vendor's configuration is a package; the customer's
  extension is `package Ours extends vendor/erp@^12`; the vendor's upgrade is a repair offered, and the
  customer's instances keep their pins until adopted (`DESIGN.md` §4). This is 1C's configuration
  extension with a theorem (`package_never_widens`) instead of a priority rule.
- **Registers are objects with conservation laws.** An accumulation register is append-only movements
  with a derived balance; an accounting register adds the double-entry law `balanced : Σ debit = Σ credit`
  per transaction and `conserved` across accounts; an information register is latest-by-key, which is a
  slot with incumbent-first selection. The `Law.Std` generators (`REPORT-LAWFINISH` §4: `eqAt`,
  `windowed`, `quorum`) grow by `balanced`, `conserved` and `monotone` with meaning theorems over
  `Evaluates`. breadstuffs' design of a register as terms sealed in the commitment plus a cursor plus a
  law computable from commitment and clock, with a second independent witness such as `spent_total`
  (reader, `STANDING-OBLIGATION.md`, `RATE-LIMITED-ALLOWANCE.md`), is the right shape; the clock must be
  a ledger fact.
- **Posting is a turn.** A document's `post` method yields a plan whose operations write movements; the
  effective law of each register judges each write; a refusal names the register, the clause and the
  movement that would pass. Un-posting is a forward turn with the inverse patch, judged like any other
  (READ reader, `FIRST-CLASS-REVERSIBILITY.md`: the inverse turn is a turn through the same gate).
- **Period closing is a version law.** A closed period is a retired pin: `ver_behind_forever` says a
  closed period never reopens, and a write dated inside it is refused by name.
- **Reports are judged folds with non-omission receipts.** A report is `Fold.Admission.run` over the
  movements at a view; its receipt is the accumulator's roots plus the openings, and a stranger (an
  auditor) recomputes it from pins. Completeness ("every movement in the range is in the report") is a
  range certificate against the ledger (§2.1 item 9), stated as a judge instance.
- **Forms are view methods** (§7.3) bound to typed fields of the object, and the affordances a form
  shows are the requests the judge says would pass for this member.
- **Offline-first is a branch.** A desktop works in a fork of the World that holds no capability to the
  shared ledger; reconnecting is a stitch through one door, where monotone registers merge by union,
  bounded ones (balances, stock) escalate to the shared commit, and conflicts are sections with two
  candidates (`conflict_is_section`). `guardGluing_iff_iconfluent` decides, per register law, which
  regime it is in, so the platform can tell a non-programmer *why* a field needs the cloud.
- **Hybrid desktop/cloud** is `CROSS-DEVICE-FIRMAMENT`'s `n` read as the number of runners sharing a
  ledger: `n = 1` is the single-writer World of nanodregg's charter; `n > 1` is `Run/Shared`.
- **The 1C lesson for non-programmers** is kept where obend already keeps it: a law is a line in plain
  words in the kind's `_kind.md`, judged on every write, and the refusal says the line that would pass
  (`REPORT-VAULT`). The Designer is `obend open` on a folder.

The platform's test is `SHIP.md` §4 step 4's bar transposed: a stranger opens a vault with a `Ledger`
kind, posts a document from a second machine offline, reconnects, sees the movement merge and a
balance refusal name its clause, and prints a report an auditor recomputes.

### 7.3 Distributed widgets and the GUI

READ (reader, the deos GUI cluster): a widget is a cell read coalgebraically, `obs` is the render,
`next` the affordances; a view tree is a serializable `{kind, props, children}` IR hosted in the cell's
committed heap; a binding reads one slot positionally; the update loop is a dirty set from committed
turns to invalidated bindings; user input is `{turn, arg}` through one gate; a subscription is a one-shot
hole with a resolution condition; the cockpit's five modes are a layout card reshaped by a receipted
turn; predict-then-commit is the only write path; the self-cycle was cut by unit delay with an admitted
authority-staleness window; derived cells are writer-maintained claims, not demand-maintained views.

PROPOSED, in obend's objects:

- **A widget is an object; its view is a method.** `view(self) -> View` returns a `Data` value of a
  declared view type, bound by typed reference to the object's fields, not by position. The renderer is
  a leaf (a Bend program over `Data`), so renderer-independence is a theorem about one value, not four
  tree walkers.
- **Events are plans.** A user's gesture is a request; the widget's method yields a plan; the host
  (the cockpit, which is a runner) dispatches it under the effective law; the receipt is the UI
  feedback. A subscription is a slot whose support is withdrawable, exactly as the reader read
  `Promise/Notify/React`.
- **Affordances are the judge's "would pass".** The set of requests the effective law admits for this
  member at this view, computed by `judgeEffective` and its refusal-with-request theorem, is the
  affordance set; a dim button is a request the judge refused with its clause attached. This makes
  "the refusal names what would pass" a UI primitive, and it is the one thing deos designed and could
  not compute, because its gate returned a bare `Bool` (reader, `TEACHING-USABILITY-FRONTIER.md`).
- **The GUI is a document.** A screen is a page; a panel is a section; a widget's state is a candidate;
  layout is the page's order; the cockpit's modes are kinds. Distributed widgets are byte cites across
  packages that darken when the source moves; a transclusion that confers no authority is a widget
  from another package shown under the viewer's mirror depth (§4.2 R2). Cross-device is the shared
  ledger; conflicts are sections.
- **Self-hosting views are lazy knots.** A view that hosts a cell that hosts a view is `fix` over a
  specification; demand bounds it; there is no depth constant and no cycle cut.
- **Derived views re-derive on demand.** A derived value is a thunk in the demand machine whose supports
  are the pins of the cells it read; a moved pin blocks it and the next read re-derives; deletion is
  re-derivation, never a reference count (`THESIS.md` §2's demand-maintained views).
- **Predict-then-commit** is `refines` used as a UI primitive: simulate the turn in a fork, show the
  receipt, commit the identical turn.

What to leave: positional bindings and an untyped view IR; UI state as ledger cells with unit delay;
seven fixed presentation kinds; per-protocol host functions. The HIG's four words (cell, capability,
turn, receipt) translate to obend's five (page, section, cite, law, kind) plus one: receipt.

### 7.4 Lane-briefable targets

| target | shape | tooth |
|---|---|---|
| `Kind` cells, nominal | per `REPORT-EXTENDS`'s recommendation; every instance tagged; the kind's law an ancestor | two kinds with equal fields are distinguished by a protocol call |
| `Law.Std.{balanced, conserved, monotone}` | generators with meaning theorems over `Evaluates`; `EqTy` records | a transaction with debit ≠ credit is refused naming `balanced` |
| ledger time | `Ledger.Rec` carries `height`; `Law.Syntax`'s `height` is read from the ledger, not the request | a request claiming a future height is refused |
| World fork and stitch | `Obend/Run/Fork.lean`: a fork holds no token of the shared ledger; `stitch` is a commit through `jrun`; monotone rows merge by union | a fork's write to a shared token is refused `notMine`; a double-spent ticket across fork and main is refused naming the epoch |
| report receipt | `Obend/Doc/Report.lean`: a fold over movements with a range certificate | an omitted movement changes the root |
| affordance projection | `Obend/Law/Affordance.lean`: `wouldPass : View → Member → Object → List Request` from `judgeEffective` | a revoked grant removes exactly the requests citing it |
| `View` type and typed binding | `Obend/View.lean`: `View` as `Data`; `bind : Field → View` | a binding to an absent field is a checker refusal, not a runtime blank |

## 8. The one receipt type (where everything meets)

PROPOSED, `Obend/Receipt.lean`, the fusion of `GENERALIZATION` G4, `RECEIPT-CONTRACT.md` and
`CONSENSUS-TIME-AND-RECEIPT-IDENTITY.md`:

```
structure Receipt where
  pre post   : Root                      -- the accumulator's roots (Fold.Rest digested)
  row        : Digest                    -- the event
  law        : Digest                    -- the effective law's identity (Spec/Identity)
  openings   : List (Cell × Option Pin × Fact × Bool)   -- what the row read, by pin
  verdict    : Verdict                   -- ok | refused clause path (would-pass : Option Request) | uncovered
  shape      : Quantifier                -- ∃run | ∃plan∀M∀r | ∃policy∀M∀r | ∀M∃plan  (ASTRA §6)
  trust      : List (Support × Trust)    -- per support: checked format@version | attested principal@revision
  dated      : LedgerView                -- the shared ledger's view, never a local clock
  prev       : Digest                    -- the producer's previous receipt
  producer   : Principal                 -- who ran the fold (informational; never trusted)
```

with `receipt_sufficient` from `Fold` as its theorem once `holdsOfPin` makes `holds_congr` definitional,
`trust_mono` from §4.2, and the dial as three projections (the log, the openings, the roots). A
`Refusal` is a `Receipt` whose verdict names the clause and, where one exists, the request that would
pass. INFERRED: every section above produces or consumes this type: the rewrite certificate (§3), the
meta-turn (§4), the specialization candidate (§5), every solver verdict (§6), the transaction, the
posting, the report and the fired affordance (§7).

## 9. The order

### 9.1 What is built first and why

PROPOSED. First: `Obend/Judge.lean` and `Obend/Receipt.lean` together, with the five existing judges
as instances, the `Format` record, one foreign format (LRAT) end to end with a planted-bad-certificate
tooth, and `holdsOfPin` so that `receipt_sufficient` is computable. Why first: every one of the six
questions routes through it (the rewriter is a judge; EP boundaries carry a judge's `sound`; the
specialization candidate's support is a judge's verdict; solver diversity is the registry; the chain's
light client and the auditor's report are receipts; the affordance set is a judge's would-pass). It is
additive in `Core`, lands on modules that exist, and `GENERALIZATION` already ordered G1 → G4 → G2; I
pull G2 forward because without one *foreign* instance the registry is a typeclass in name only, and
LRAT is the cheapest format with a verified checker in the literature.

Second: `quote`, `≈q`, `observer_ladder`, `RewriteJudge` (§3.4). Third: `Mirror` and the meta-World
(§4.4). Fourth: the specialization slot and the improvement judge (§5.4), which wait on `EQUIV-PLAN`'s
definition 2. Fifth: the platform kinds (§7.4), gated on the nominal-kinds decision. The Leaf emitter
and its refinement run beside these as the lane `METATHEORY.md` §5 already names, because every runtime
claim in §5 is conditional on it.

### 9.2 Which modules carry the weight, and which must be replaced

INFERRED from the reports and the tree.

Carry the weight, unchanged in statement: `Core/Term`, `Core/Machine`, `Core/Checkpoint`,
`Core/Interaction`, the bidirectional checker and `FiniteBisimulation`, `Slot`/`World`/`Integrity`/
`Selection`/`Repair`, `Law/Machine` and `Law/Inherit`, `Run/Runner`, `Run/Spec`, `Run/Shared`, `Fold`,
`Doc/{Patch,Merge,Section}`, `Spec/Ecosystem` and the intention slot, `Vault`.

Must be replaced or completed, with the reason:

- `Spec/C4.linearize`: an imperative hash-map merge with no theorem, validated after the fact
  (`REPORT-LAWFINISH` §7); rewrite structurally and prove it, because the kind-cell platform (§7.2) puts
  every register's effective law on it.
- `Check.check` (the fuel path) beside `Bidirectional`: two checkers; retire the first once the open-
  template check moves (`REPORT-ELAB` leftovers).
- `Just`/`PolySlot`: keep as provenance for explanations only (`REPORT-JUST` §3).
- `Core/Digest`'s cSHAKE as the one digest: make the digest an instance registered with a refutation
  attempt at deployed parameters (§2.2 item 3), because the receipt's roots depend on it.
- `Host.allowed` as "whatever the host decides": the shared `Ledger` replaces it on every platform path;
  the bare runner stays for single-writer worlds.
- `Prot` as an inductive of finite depth: the reference tree (`Interaction.observe`, coinductive) must
  be composed into `trace_is_run` before any liveness statement is made (`REPORT-RUNNER` §9).
- `Law.Syntax`'s request-carried `height`: replaced by the ledger's time (§7.4).
- the JSON packet wire and the parser: trusted without a theorem; acceptable for the front end, not for
  a certificate format; `Format.encode` must be Lean, never a wire.

### 9.3 Where the risk of the wrong foundation is highest

INFERRED, ranked.

1. **The machine's missing half.** `Representation` uninhabited; source-to-machine completeness and
   administrative progress open (`EQUIV-PLAN` §1). Every compiled path, every checkpoint correspondence
   and every cost statement in §5 stands on it. If it cannot be proved for the machine as it is, the
   machine, not the reference, is what changes.
2. **Cost blindness.** `≈b` is what rewrites are justified by and ticks are what members pay; until
   definition 2 and the ticks-to-CV theorem exist, an optimization can change what a member is charged
   with no theorem saying by how much (`ALGEBRAIC-SUBTYPING` §3.7).
3. **The solver boundary of admission.** `METATHEORY.md` §6: solvers belong only in the elaborator. If a
   judge instance ever searches (a `check` that is not deterministic, or a format whose `encode` is
   Rust), admission becomes search and the trust rule is gone. The `Format` record's fields are the
   guard.
4. **Pins without a computable semantics.** `holds_congr` is propositional; until `holdsOfPin` exists a
   receipt is not stranger-computable and the contract platform has no light client (§7.1).
5. **The nominal-kinds decision.** Pending; every platform object in §7 is a kind.
6. **The toolchain fork for the leaf.** BendTT at 4.34, obend at 4.35; vendoring `bendtt.lean` or
   waiting is a decision that gates §5 entirely.
7. **Breadth.** The failure mode of §2.2 item 4. The vault is the one stranger-usable artifact; every
   platform section above should land as a kind in a vault before it lands as anything else.

## 10. References

Papers read from `~/paperbin` are cited by their paperbin names. Papers fetched for this study are
listed by the names the fetch lanes assigned; where a fetch failed the entry says so and the citation
above is from memory, as marked "(from memory)" below.

### Already in paperbin (READ)

- Ahmed 2006, step-indexed syntactic logical relations: `ahmed2006-step-indexed-syntactic-logical-relations.txt`
- Nanevski–Pfenning–Pientka 2008, CMTT: `nanevski2008-contextual-modal-type-theory.pdf`; Murase 2023 polymorphic contexts: `murase2023-cmtt-polymorphic-contexts.pdf`
- de Moura–Ullrich 2021, Lean 4: `demoura2021-lean4.pdf`
- Moran–Sands 1999: `moran-sands1999-improvement-in-a-lazy-context.txt`; Hackett–Hutton 2019: `hackett-hutton2019-call-by-need-is-clairvoyant-call-by-value.txt`; Launchbury 1993: `launchbury1993-natural-semantics-lazy-evaluation.txt`; Sestoft 1997: `sestoft1997-deriving-a-lazy-abstract-machine.pdf`; Ariola–Felleisen 1997: `ariola-felleisen1997-call-by-need-lambda-calculus.txt`; Breitner 2014: `breitner2014-adequacy-of-launchburys-natural-semantics.txt`
- Dolan 2016, Dolan–Mycroft 2017, Parreaux 2020/2022/2024: `dolan2016-algebraic-subtyping-thesis.pdf`, `dolan-mycroft2017-mlsub.pdf`, `parreaux2020-simple-essence-algebraic-subtyping.pdf`, `parreaux-chau2022-mlstruct.pdf`, `parreaux2024-superf-subtyping-constraints-liberate.pdf`
- Bracha–Cook 1990, Cook–Hill–Canning 1990, Cook–Palsberg 1994, Cook 2009, Flatt–Krishnamurthi–Felleisen 1998, Kamin 1988: `bracha-cook1990-mixin-based-inheritance.pdf`, `cook-hill-canning1990-inheritance-is-not-subtyping.pdf`, `cook-palsberg1994-denotational-semantics-of-inheritance.pdf`, `cook2009-on-understanding-data-abstraction-revisited.pdf`, `flatt-krishnamurthi-felleisen1998-classes-and-mixins.pdf`, `kamin1988-inheritance-in-smalltalk-80.txt`
- Plotkin–Pretnar 2009/2013, Pretnar 2015: `plotkin-pretnar2009-handlers-of-algebraic-effects.pdf`, `plotkin-pretnar2013-handling-algebraic-effects-lmcs.pdf`, `pretnar2015-introduction-algebraic-effects-handlers-tutorial.pdf`
- Jung et al. 2015/2018 Iris, Iris in Lean 2026: `jung2015-iris-monoids-invariants-orthogonal-basis.pdf`, `jung2018-iris-from-the-ground-up.pdf`, `iris-in-lean2026.pdf`
- Angiuli et al. 2014 patch theory: `angiuli-morehouse-licata-harper2014-homotopical-patch-theory.pdf`
- Avigad et al. 2022 Cairo: `avigad-verified-algebraic-representation-cairo-cpp2022-2109.14534.pdf`; Lurk audit: `audit-inference-lurk.pdf`; Jolt, Lasso: `jolt-2023-1217.txt`, `lasso-2023-1216.txt`
- Alviano et al. 2019 ASP-DRUPE: `alviano2019-asp-drupe-inconsistency-proofs.txt`; Green–Karvounarakis–Tannen 2007: `green-karvounarakis-tannen-provenance-semirings-pods2007.txt`
- Kaufmann–Moore ACL2 papers: `kaufmann-moore2011-how-can-i-do-that-acl2-defattach.pdf`, `kaufmann2020-acl2-iteration-loop.pdf`, `swords2018-acl2-incremental-sat-abstract-stobjs.pdf`, `peng2018-acl2-smtlink-2.pdf`; Leino 2010 Dafny: `leino2010-dafny-automatic-program-verifier.pdf`; Protzenko et al. 2017 Low*: `protzenko2017-lowstar-verified-low-level-programming-fstar.pdf`
- Omar et al. 2018/2019 Hazelnut Live: `omar2018-hazelnut-live.pdf`, `omar2019-hazelnut-live-live-functional-programming-typed-holes.pdf`; Blinn 2024 typed holes and LLMs: `blinn2024-statically-contextualizing-llms-typed-holes.txt`
- Mokhov–Mitchell–Peyton Jones 2018, build systems à la carte: `mokhov-mitchell-peytonjones2018-build-systems-a-la-carte.pdf`
- Belyakova 2020, world age in Julia: `belyakova2020-julia-world-age-in-julia.pdf`
- Garg–Pfenning 2010, PCFS; Morgenstern 2011 LPCFS; Abadi–Burrows–Lampson–Plotkin 1993; Appel–Felten 1999: `garg-pfenning2010-proof-carrying-file-system.txt`, `morgenstern2011-lpcfs.txt`, `abadi-burrows-lampson-plotkin1993-calculus-access-control-distributed-systems.txt`, `appel-felten1999-proof-carrying-authentication.txt`
- Clarkson–Schneider 2010, Clarkson et al. 2014, Finkbeiner et al. 2015/2021 (fetched by Astra's study): `clarkson-schneider2010-hyperproperties.txt`, `clarkson2014-temporal-logics-hyperproperties.txt`, `finkbeiner-rabe-sanchez2015-model-checking-hyperltl.txt`, `finkbeiner2021-model-checking-algorithms-hyperproperties.txt`
- Halpern–Moses 1990: `halpern-moses1990-knowledge-common-knowledge-distributed-environment.pdf`
- Xia et al. 2020 interaction trees: `xia2020-interaction-trees.txt`
- Mayer et al. 2018 Sketch-n-Sketch: `mayer2018-sketch-n-sketch-bidirectional-evaluation-direct-manipulation.pdf`

### Fetched for this study

Metaprogramming, reflection, staging, runtime (each with a `.txt` sibling unless noted):

- Amin–Rompf 2018: `amin-2018-collapsing-towers-of-interpreters.pdf`
- Rompf–Odersky 2010: `rompf-odersky-2010-lightweight-modular-staging.pdf`
- Kiselyov 2014: `kiselyov-2014-design-implementation-ber-metaocaml.pdf`; Taha–Sheard 2000 (fetch failed: ScienceDirect blocked, no open copy, Anna's Archive unreachable; cited from memory)
- Smith 1984: `smith-1984-reflection-and-semantics-in-lisp.pdf`; Wand–Friedman 1988: `wand-friedman-1988-mystery-of-the-tower-revealed.pdf` (the 1986 Indiana TR 196 scan behind the paper; OCR text); Danvy–Malmkjær 1988: `danvy-malmkjaer-1988-intensions-extensions-reflective-tower.pdf`
- New–Ahmed 2018: `new-ahmed-2018-graduality-from-embedding-projection-pairs.pdf`; New–Licata–Ahmed 2019: `new-licata-ahmed-2019-gradual-type-theory.pdf`; Patterson–Mushtak–Wagner–Ahmed 2022: `patterson-2022-semantic-soundness-language-interoperability.pdf`; Patterson–Ahmed 2017: `patterson-ahmed-2017-linking-types-multi-language-software.pdf`; Matthews–Findler 2007: `matthews-findler-2007-operational-semantics-multi-language-programs.pdf`; Siek–Taha 2006: `siek-taha-2006-gradual-typing-functional-languages.pdf`
- Würthinger et al. 2013, 2017: `wurthinger-2013-one-vm-to-rule-them-all.pdf`, `wurthinger-2017-practical-partial-evaluation-dynamic-language-runtimes.pdf`; Bolz et al. 2009: `bolz-2009-tracing-the-meta-level-pypy-tracing-jit.pdf`; Futamura 1999: `futamura-1999-partial-evaluation-computation-process-compiler-compiler.pdf`; Jones–Gomard–Sestoft 1993: `jones-gomard-sestoft-1993-partial-evaluation-automatic-program-generation.pdf`
- Willsey et al. 2021: `willsey-2021-egg-fast-extensible-equality-saturation.pdf`; Tate et al. 2009: `tate-2009-equality-saturation-new-approach-optimization.pdf`
- Meseguer 2012: `meseguer-2012-twenty-years-of-rewriting-logic.pdf`; Clavel–Meseguer 2002 (fetch failed, paywalled; cited from memory)
- Bracha–Ungar 2004: `bracha-ungar-2004-mirrors-design-principles-meta-level-facilities.pdf`; Kiczales 1993 (fetch failed, no open copy; cited from memory)
- Xie et al. 2022: `xie-2022-staging-with-class.pdf`; Kovács 2022: `kovacs-2022-staged-compilation-two-level-type-theory.pdf`; Stucki et al. 2018: `stucki-2018-practical-unification-multi-stage-programming-macros.pdf`
- Ullrich–de Moura 2020: `ullrich-demoura-2020-beyond-notations-ijcar.pdf` (and the LMCS extension `ullrich-demoura-2020-beyond-notations-hygienic-macro-expansion.pdf`); Ebner et al. 2017: `ebner-2017-metaprogramming-framework-formal-verification.pdf`
- Carette–Kiselyov–Shan 2009: `carette-2009-finally-tagless-partially-evaluated.pdf`; Elliott 2017: `elliott-2017-compiling-to-categories.pdf`; Reynolds 1972/1998: `reynolds-1998-definitional-interpreters-higher-order.pdf`
- Ingalls 1981: `ingalls-1981-design-principles-behind-smalltalk.pdf`; Dolstra et al. 2004: `dolstra-2004-nix-safe-policy-free-software-deployment.pdf`
- Lafont 1997: `lafont-1997-interaction-combinators.pdf`; Taelin 2024, HVM2: `taelin-2024-hvm2-parallel-evaluator-interaction-combinators.pdf`
- Wolfram Language documentation: `wolfram-ref-standard-evaluation-procedure.txt`, `wolfram-ref-everything-is-an-expression.txt`
- Rideau, Houyhnhnm Computing ch. 1–7: `rideau-houyhnhnm-ch1-the-way-houyhnhnms-compute.txt` … `rideau-houyhnhnm-ch7-platforms-not-applications.txt`
- Maziarz et al. 2021, hashing modulo α (from memory; not fetched)

Solvers, certificates, verifiable computation, platforms:

- Torlak–Bodik 2014: `torlak-2014-rosette-lightweight-symbolic-vm.pdf`; Filliâtre–Paskevich 2013: `filliatre-2013-why3-where-programs-meet-provers.pdf`; Blanchette–Böhme–Paulson 2013: `blanchette-2013-extending-sledgehammer-smt-solvers.pdf`; Armand et al. 2011: `armand-2011-smtcoq-modular-integration-sat-smt-coq.pdf`
- Cruz-Filipe et al. 2017: `cruz-filipe-2017-efficient-certified-rat-verification.pdf`; Heule–Hunt–Wetzler 2013: `heule-2013-trimming-while-checking-clausal-proofs.pdf`; Barbosa et al. 2022: `barbosa-2022-flexible-proof-production-cvc5.pdf` (the 71-page extended version); Schurr et al. 2021: `schurr-2021-alethe-generic-smt-proof-format.pdf`; Gocht–Nordström 2021: `gocht-2021-certifying-parity-reasoning-pseudo-boolean-proofs.pdf`; Assaf et al. 2016: `assaf-2016-dedukti-logical-framework-lambda-pi-modulo.pdf`
- Kothapalli–Setty–Tzialla 2022: `kothapalli-2022-nova-recursive-zk-folding-schemes-2021-370.pdf`; Bonneau et al. 2020: `bonneau-2020-mina-decentralized-cryptocurrency-at-scale.pdf`; Chiesa–Tromer 2010: `chiesa-2010-proof-carrying-data-hearsay-arguments.pdf`; Bowe et al. 2020: `bowe-2020-zexe-decentralized-private-computation-2018-962.pdf`
- Necula 1997: `necula-1997-proof-carrying-code.pdf` (scanned; `.txt` is OCR); Appel 2001: `appel-2001-foundational-proof-carrying-code.pdf`
- Gebser et al. 2014: `gebser-2014-clingo-asp-control-preliminary-report.pdf`; Nethercote et al. 2007: `nethercote-2007-minizinc-standard-cp-modelling-language.pdf`; Gulwani–Polozov–Singh 2017: `gulwani-2017-program-synthesis.pdf`
- Kaufmann–Moore 1997: `kaufmann-1997-industrial-strength-theorem-prover-acl2.pdf`; Moore 2019: `moore-2019-milestones-pure-lisp-theorem-prover-to-acl2.pdf`; Leino–Moskal 2010: `leino-2010-usable-auto-active-verification.pdf`; Martínez et al. 2019: `martinez-2019-meta-fstar-proof-automation-smt-tactics.pdf`
- Si et al. 2018: `si-2018-learning-loop-invariants-code2inv.pdf`; Pei et al. 2023: `pei-2023-can-llms-reason-about-program-invariants.pdf`; First et al. 2023: `first2023-baldur-whole-proof-generation-repair-llm.pdf`
- Harrison 2007: `harrison-2007-verifying-nonlinear-real-formulas-sums-of-squares.pdf`; Davenport 2010: `davenport-2010-challenges-of-multivalued-functions.pdf`; Buchberger 1965/2006 (fetch failed: paywalled and Anna's Archive unreachable; cited from memory)
- 1C:Enterprise Developer Network pages: `1c-dn-metadata-objects.txt` (the "Configuration objects" page), `1c-dn-accumulation-registers.txt`, `1c-dn-accounting-registers.txt`, `1c-dn-information-registers.txt`, `1c-dn-business-processes.txt`, `1c-dn-configuration-and-database.txt`
- Hoare 2003: `hoare-2003-verifying-compiler-grand-challenge.pdf`; Leroy 2009: `leroy-2009-formal-verification-realistic-compiler.pdf`; Backus 1978: `backus-1978-can-programming-be-liberated-von-neumann-style.pdf`
