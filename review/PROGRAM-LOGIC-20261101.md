# Verifying obend programs: the logic, the certificates, the surface

2026-11-01, answering `review/PROGRAM-LOGIC-BRIEF-20261101.md`. A study for Ember and Claude; nothing
lands in `lean/`. Baseline read: `dev` at `7a6d454`. Tags: READ (a file or paper opened, the claim is
what it says), INFERRED (my deduction from READ things), PROPOSED (new syntax, statements, modules,
recommendations). Formulas inside a tagged paragraph inherit its tag. Papers fetched for this study
are in `~/paperbin` (§7); the obend files are named with their paths.

## 0. Answers in brief

- **The question has a one-line answer the library already half-gives.** A program author's
  specification is a closed Core4 predicate judged over `Evaluates` (`Obend/Law/Syntax.lean`:
  `Admits law o n rq := ∃ w, Evaluates (applyLaw law o n rq) (inject "ok" w)`;
  `Obend/Law/Claim.lean`: `Keeps I n := Evaluates (app I n.term) (boolean true)`), and a `claim` in a
  `spec` is elaborated today to exactly such a predicate, closed over `self`, `super` and its
  parameters, typed `Bool`, status `unchecked`, never evaluated (`Obend/Spec/Elaborate.lean`
  `finishSpecification`, "LT6 owns discharge"). The program logic obend needs first is the one whose
  judgment is **`Holds c d⃗ := Evaluates (c d⃗) (boolean true)` for every data instance `d⃗`**, whose
  proof rules are the reduction and congruence facts `Obend/Equiv/` already proves (`Steps`, `Ahead`,
  `bequiv_of_steps`, `rewrite_sound_below`, `mix_assoc`), and whose one new rule is the OO one:
  **late binding**, that `get (fix S seed) m` reduces to the body of the *last* layer providing `m`
  with `self := fix S seed`. That rule is the frame rule of this logic, and the members a proof
  unfolds through it are the proof's supports. (§2.7, §5.3.)
- **Build first: an equational partial-correctness logic of claims over the reference semantics**,
  module `Obend/Logic/`, with three certificate formats by regime: a ground run (decidable, the law
  probe reused as a `Judge` instance, refuting), a rewrite derivation (semi-decidable with
  certificate, the improvement judge's shape over `Ahead`/`≈b`, never refuting), and a Lean proof in
  the library (decidable to check, trust `kernel`, exported later as a `Format`). Not first: a
  separation logic over the demand machine in Iris-Lean (needed only for sharing identity, effects
  under update frames and space: EQUIV-PLAN definition 3), and cost triples (gated on contract C4,
  because `ticks_not_within_cv` refuted the tick correspondence; `lean/docs/REPORT-COST-20261101.md`).
- **The first program to verify end to end: `lean/tests/obend-source/ReviewMember.obend`, claim
  `repeated`** (`self.twice(value) == self.review(self.review(value))` in layer `Twice`), proved of
  `fix(compose(Prior.Base, Twice, Augmented), seed)` by a two-step derivation (late binding at
  `twice`, then β), with support `{twice ↦ ReviewMember.Twice}` and no support on `review` (so the
  claim survives every later `review` override, which is Cook's and Shaner's point about open
  recursion), a ground tooth `twiceOfThree() == 7` (the cohort's expected value,
  `lean/tests/obend-source/preview-cohort.json` row `ImportedReview`), and a mutation tooth: a fourth
  layer re-providing `twice` withdraws the support, the claim's slot reads `blocked` naming
  `twice`, and the ground judge refutes the claim at `3`. Second: `examples/Counter.obend`'s `bump`,
  as an interaction-tree claim decided per response branch. (§5.4.)
- **What the literature says about lazy program logics is thin and the thinness is instructive.**
  Partial correctness of pure call-by-name terms is equational reasoning (Bird–Wadler, hs-to-coq's
  "Total Haskell is reasonable Coq"); the two places laziness bites are *binders that may diverge*
  (Liquid Haskell's stratified `Div`/`Wnf` types: READ Vazou et al. 2014 §2) and *cost* (Moran–Sands
  improvement, Hackett–Hutton's clairvoyant call-by-value, Danielsson's `Thunk n a`, Pottier et al.'s
  thunks-and-debits in Iris with time credits). obend's answer to the first is that claims quantify
  over `Data` (values), results are partial, and termination is a separate certificate; to the
  second, that **a cost upper bound for a lazy program is witnessed by one clairvoyant derivation**
  (the oracle's Skip/Let′ choices), which is a deterministic certificate the improvement judge
  already checks in shape. (§2.2.)
- **Laws are already a program logic judged at runtime**; a proved law is the same predicate
  discharged for all writes. The enforced `law` fragment (`Obend/Spec/Law.lean`, `LawExpr.denote`)
  is linear integer arithmetic over fields, so law entailment, law vacuity and "this activity's
  every plan satisfies this law" are Presburger questions `omega`/`grind` decide in the kernel with a
  Lean proof as the certificate. That is the cheapest new automation in the tree. (§2.6, §3.)

## 1. What a program author wants to prove, against what exists

READ, the examples: `ReviewMember.obend` (a claim about open recursion), `examples/Counter.obend` and
`tutorial/ch8-counter.obend` (`bump`, one turn; `serve`, a resident that never finishes),
`DeosCounter.obend` (`reset` needs a Proof credential: "the object's law, checked by the kernel; the
program cannot see or change it"), `three-package/*/*.obend` (`law capped: new.total <= 50 or
request.caller == 7`, `law monotone: monotone(total)`, `law bounded: new.total <= 100`),
`stranger/review/Review.obend` (`law reviewed: new.sections <= 9`), `world/market/*.obend` (a
settlement whose "Objective laws are retained, never checked; kept as a named property:
`chosen_book_exact`"). No `.obend` source in the tree writes `keeps`, `ensures`, `invariant`,
`refines` or `costs`.

| specification (brief (1)) | an example in the tree | what exists | the gap |
|---|---|---|---|
| functional correctness of a method against pre/post | `claim repeated` in `ReviewMember.obend` | the claim is elaborated to closed Core4 code `λself. λsuper. λvalue. …` typed `Bool`, kept as a hidden knot field `key#claim#name`, status `unchecked` in `SpecMeta.claims` (Elaborate 1490–1508) | no judgment says what the claim MEANS of an object; nothing discharges it; no precondition form |
| an invariant of an object's state across every admitted write | `law bounded: new.total <= 100` | judged per write by the machine probe (`Law/Machine.lean` `judge`, `judge_sound`/`judge_complete`); `keeps inv law` proved for all writes when the law is in certifying shape (`Law/Claim.lean` `guardedBy`, `Law/Proofs/Claim.lean` `chain_keeps`) | `keeps` has no `.obend` syntax; the certifying shape is one proof rule, not a logic; a `law` cannot be proved of a *program's* writes, only of all writes |
| a protocol property of an activity (every `commit` after a `reserve`; obligations discharged) | `Slot/Protocol.lean` `Negotiation` | `HasProt` as an envelope (tokens as a bag, facts, obligations as an upper bound, result post `Q`), decided on finite signatures (`Judge/Instances.lean` `checkProt`, sound and complete); `Legal` (`Run/Spec.lean`) with `Paired`, `OnceSpent`, `AfterAbandon` | ordering ("after a reserve") and discharge are not expressible in `Φ` (READ Astra §1.1: membership, not a count; no discharge operation); the envelope is over `Prot`, not over a Core4 activity term; the connection is the adapter |
| equivalence of two layers under `mix` | `mix_assoc`, `compose_assoc_b` | `≈b` (`Equiv/Behaviour.lean`), `≈r`, `≈q`, the ladder and `rewrite_sound_below` (`Equiv/Quote.lean`), `IEquiv` over turns (`Equiv/Yields.lean`) | no certificate format for an equivalence except the improvement judge's re-association steps; no `refines` preorder |
| cost bounds | `mix_assoc_cost` within a factor of 8 | `CostWithin`, `≈c` (`Equiv/Cost.lean`), the improvement judge (`Judge/Cost.lean`) | ticks are not within a constant of clairvoyant cost (`ticks_not_within_cv`); contract C4 open |
| resource properties (a custody discharged exactly once) | — | `step_conserves_linear` (`Core/Proofs/Conservation.lean`): one source `Step` keeps every `linear` count | no source subject reduction, so no run-length statement; records are `⊗`-constructed with neither `⊗` nor `&` eliminated (C2) |
| properties across a package's extensions (every descendant keeps the base's invariant) | `three-package` | `package_never_widens`, `chain_keeps`, `Spec/Contract.lean` rows (`assumes`/`consumes`/`provides`, `replaced`) | a claim proved of a layer has no stated frame: which later layers may be added without re-proof |

INFERRED. Two things are missing, and only two: a *judgment* for what a claim means of an object
(with its frame under composition), and *certificate formats* that discharge it in the three regimes.
Everything else in the table is a specialization of one or the other.

## 2. The logics

### 2.1 Hoare and separation logic over the demand machine (Iris-Lean)

READ (`review/EQUIV-PLAN-20261031.md` §0, §4): Iris-Lean builds from this tree (4.35, modules,
batteries and Qq only); it has unary WP, lifting and adequacy, no binary logic (ReLoC), no time
credits. READ (`iris-in-lean2026.txt`, abstract): "complete coverage of all of the non-experimental
features included in Iris", a proof mode, Diaframe-style automation, Mathlib integration. READ
(`frumin-krebbers-birkedal2021-reloc-reloaded.txt`): the refinement judgment `e ≾ e′ : τ` with
type-directed and symbolic-execution rules, built on Iris. READ
(`moine-chargueraud-pottier2024-thunks-debits-time-credits.txt` §1): thunks as a mutable memoization
structure; Okasaki's debits as ghost state; "a debit is associated also with future thunks"; verified
streams and three of Okasaki's queues in Iris with time credits. READ
(`mevel-jourdan-pottier2019-time-credits-time-receipts-iris.txt`): time credits as an affine
resource `$n`, receipts as the dual.

INFERRED. What this logic would give obend that nothing else gives: statements about **sharing
identity** ("a shared expensive field selected twice keeps one thunk", DESIGN §7's sharing-identity
test), **effects under update frames** (`perform_under_update_refused`, `Core/Machine.lean`:
`sharedEffect`), **space** (`Limits.heap`), and **blackholes as an observation** (`.bad` ends
`divergent` in 21 ticks; `Steps` diverges). Each is a definition-3 statement (EQUIV-PLAN §2). What it
costs: a `Language` instance for a machine with explicit frames and no evaluation contexts
(EQUIV-PLAN §4.6), guarded recursion for cyclic heaps (§4.2), cell-state invariants across update
frames in lockstep for two machines (§4.3), the dependency decision (§4.7). What it would not give:
anything about `fix`'s open recursion or about `claim` that the equational logic does not already
give more cheaply, because `Steps` is deterministic and has no state. PROPOSED: Iris-Lean enters
when a *statement* needs definition 3, as EQUIV-PLAN §5.4 already says; the first such statement is
the sharing-identity test, and it is not among the first three theorems of §5.

### 2.2 Program logics for lazy languages, and improvement theory

READ (`hackett-hutton2019-…`): Theorem 4.1 (moral equivalence of call-by-need and clairvoyant
call-by-value: a need-evaluation of cost `k` gives a CV derivation of cost `≤ k`, and every CV
derivation of cost `k` gives a need-evaluation of cost `≤ k`), Theorem 4.2 (contextual cost
equivalence of the two), improvement as Moran–Sands' relation with the heap replaced by
nondeterminism; §5 proves "common subexpression elimination is an improvement" and a bounded
slowdown for one rule. READ (`moran-sands1999-improvement-in-a-lazy-context.txt` Def. 3.3, §3.4):
improvement and strong improvement; the improvement theorem; improvement induction. READ
(`breitner2014-adequacy-of-launchburys-natural-semantics.txt`): Launchbury's semantics mechanized;
correctness and adequacy against a denotational semantics, with the warning that the original
adequacy proof did not go through as written. READ (`danielsson2008-…`): `Thunk n a` as a dependent
type, "a WHNF of type `a` can be obtained in `n` steps amortised time, no matter how the value is
used", a monad combining ticks, verified in Agda. READ
(`madhavan-kuncak2017-contract-based-resource-verification-memoization.txt`): resource contracts
for higher-order functions with memoization, discharged by SMT with a cache model. READ
(`vazou2014-refinement-types-for-haskell.txt` abstract, §2.4): "standard refinement systems
crucially rely on a property of eager languages: when analyzing any term, one can assume that all
the free variables appearing in the term are bound to values"; the fix is a stratification of binders
into `Div`, `Wnf`, `Fin` types with refinement-checked termination.

INFERRED, the honest state of "lazy program logics". There is no Hoare logic *of* call-by-need in
the literature in the sense of a proof system over thunks and demand; what exists is (a) equational
reasoning about pure programs, where laziness is invisible except through `⊥` and admissibility,
(b) refinement types with a divergence stratification (Liquid Haskell), (c) cost reasoning: Sands'
improvement, H&H's clairvoyant semantics, Danielsson's ticks in types, and Pottier et al.'s debits in
a separation logic *for a strict language with explicit thunks*. Nobody has a logic where the
thunks are implicit at every binding site and the heap is an implementation of a deterministic
weak-head relation, which is what Core4 is. The reason is that such a logic is mostly unnecessary
for correctness: with `Steps` deterministic and stateless, `{P} t {Q}` for partial correctness is
`∀ v, Evaluates t v → Q v` and every rule is a reduction fact. Laziness bites in two places only:

- *Binders may diverge.* A claim's parameter `value: Nat` is not a value under CBN; `twice(loop)`
  substitutes `loop` unevaluated. Vazou's lesson transfers exactly: a precondition on a binder is
  sound only if the binder is known to be a value. PROPOSED: claims quantify over `Data` (first-order
  values; `Ty.isData`, `Data.term` are weak-head literals or records of them) for their parameters,
  and over *terms* (with `≈b` as equality) for higher-order ones; results are partial
  ("whenever the left side has a ground observation"); a termination claim is a separate
  certificate (a ground run per instance, or a Lean proof). No stratified types are needed because
  the claim surface already separates data parameters (`Nat`, sums) from closures.
- *Cost.* READ (`REPORT-COST-20261101.md` §3): `ticks_not_within_cv` is a theorem: for no `c d`
  does every finished machine run of `T` ticks have a CV derivation of cost `≤ cT + d`; the witness
  is `{a = 7, b = self.a}.b` (25 ticks, no derivation), which Gemini reads as a `fixLet` staging
  artifact (`review/GEMINI-CHECKPOINT-20261101.md` item 4). INFERRED, the one new observation of
  this study about cost: **under the clairvoyant semantics, an upper bound on call-by-need cost is
  witnessed by a single derivation** (H&H Thm 4.1 part ii: a CV derivation of cost `k` gives a need
  run of cost `≤ k`). The nondeterminism is angelic for upper bounds, so the certificate of
  `cost t ≤ k` is the derivation itself: which bindings were Skipped, which were Let′'d. That is a
  deterministic check (`Equiv/Clairvoyant.lean` `Run` is an inductive relation; a checker walks a
  listed derivation), and it is the shape `Judge/Cost.lean` already has for re-association steps.
  Lower bounds and exact costs quantify over all derivations and need a Lean proof. Cost triples
  `{P} t {Q}≤k` are therefore available today *over CV cost*; over machine ticks they wait on C4.

### 2.3 Refinement calculi (Back–von Wright, Morgan), and `mix` as refinement composition

READ (`morgan1998-programming-from-specifications.txt`): the specification statement `w:[pre, post]`;
Law 1.1 strengthen postcondition, Law 1.2 weaken precondition; refinement `⊑` as "every
specification the right satisfies the left satisfies"; stepwise refinement to code. READ
(`shaner-leavens-naumann2007-…`): model programs as grey-box specifications of higher-order methods
with *mandatory calls* (`self.m()` that an override must make), with refinement-calculus semantics
("Remarkably, refinement style reasoning is not needed to use the grey-box approach"), and a
soundness proof against state transformers. Back–von Wright's book was not fetched (paywalled;
§7); its predicate-transformer lattice is what Morgan's laws instantiate.

INFERRED. Faré's reading of `mix` as refinement composition is exact in this tree in two senses.
(i) A layer whose method body is a `hole n σ` (`Core/Term.lean`: inert syntax, refused when
demanded, `Core/Proofs/Hole.lean`) together with a `claim` on that method *is* Morgan's
specification statement: the claim is `post`, the data-parameter types and a `given` are `pre`, and
the hole is `w`. Filling the hole is one refinement step; the slot's judge (`Obend/Slot.lean`:
candidates, supports, `judge`) is "the filling satisfies the specification statement"; Laws 1.1 and
1.2 are monotonicity of that judge in the claim. (ii) Refinement between layers is the preorder half
of `≈b` restricted to census-`b` observers, and `mix` is a congruence for it (`rewrite_sound_below b`),
so a composition is refined layer by layer. What does *not* transfer: Morgan's `w` is a frame of
variables; obend's frame is the set of *members a proof reads through late binding* (§2.7), which
is closer to Kassios's dynamic frames than to Morgan's. PROPOSED: no refinement calculus as a
separate logic; `refines` is a claim form judged by the equational logic (§4.1).

### 2.4 An equational theory over `≈r`/`≈b` with the ladder as the observer discipline

READ (`Equiv/Behaviour.lean`): `BEquiv t t′ := ∀ ρ C, SameRuns (C[tρ]) (C[t′ρ])`; `bequiv_of_ahead`,
`bequiv_of_steps`, `mix_assoc`. READ (`Equiv/Ahead.lean` per EQUIV-PLAN §3): `Ahead` is parallel
reduction with weak-head runs as the contraction, a congruence through binders. READ
(`Equiv/Quote.lean`): `≈q ⊆ ≈r ⊆ ≈b` strict at both steps; `rewrite_sound_below k`: an observer of
census at most `k` preserves `≈k`; `compose_assoc_b` and `compose_not_assoc_r`. READ
(`Equiv/Yields.lean`): `IEquiv` with turns counted, `mix_assoc_interaction`. READ (`Judge/Cost.lean`):
a certificate is a list of steps each re-associating one `mix` in a context; `check` runs them from
the original and accepts on reaching the candidate; `refutes` constantly false. READ
(`willsey-2021-egg-…`, `flatt2022-small-proofs-congruence-closure.txt`): equality saturation with
proof production; small proofs from congruence closure. READ (`necula2000-translation-validation…`):
the validator checks each pass's output against its input with a simulation relation and heuristics,
"without help from the optimizer".

INFERRED. This is the logic the tree has most of. Its judgment is `t ≈b t′` (and `t ≈c t′`,
`IEquiv`); its proof system is: reduction (`bequiv_of_steps`), parallel reduction (`bequiv_of_ahead`),
congruence with the census guard (`rewrite_sound_below`), the proved laws (`mix_assoc`, Faré's tests),
and transitivity. Its certificate language is a derivation; its checker is a rewriter that replays
the derivation; its producer is any rewriter (an e-graph, a simplifier, a language model) that
emits steps in that language, with translation validation as the discipline. What it lacks: a step
for `fix` (late binding, §2.7), and a step for `case`/`ifBool` on open scrutinees (a case split, which
is where derivations become proof trees). A `==`-claim is an equation whose sides are `Nat`-valued
terms; `l ≈b r` plus a ground observation of `l` gives `Evaluates (binary equal l r) (boolean true)`
by `SameRuns.halts` and `Step.primitive`. So the equational logic *is* the claim logic for the
partial-correctness reading, and every `≈b` proof is a claim proof.

### 2.5 Type-based: the quantities and the protocols are already a logic

READ (`Core/Ty.lean`): `Quantity = erased | affine | linear | unrestricted`; `computation plan
response result` ("only a direct position may hold it; it is not shareable"); `Core/Check.lean`
`PartialTyping` with uses vectors, the `perform`, `done`, `case`-on-computation rules (560–578).
READ (`Slot/Proofs/ProtocolTyping.lean` 45–61): `HasProt sp Ω Γ Q Φ Δ P` with `ret` requiring `Q`,
`call`/`spend` requiring facts in `Γ`, tokens in `Δ`, obligations in `Φ`, every response branch;
`hole` by its `Iface`. READ (`nanevski-morrisett-birkedal2006-hoare-type-theory.txt`): `{P}x:A{Q}` as
a type; "type-checking in HTT is carefully designed to split into two independent phases"
(decidable VC generation, then validity). READ (`swamy2016-…`, `rastogi2021-…`): Dijkstra monads
and indexed effects in F*: a computation type carries its WP or an index, layered effects refine
each other. READ (`das2019-nomos-…`): linear session types with amortized resource bounds for
contracts. READ (`devilhena-pottier2021-separation-logic-effect-handlers.txt`): "the specification
of a program fragment includes a protocol that describes the effects that the program may perform
as well as the replies that it can expect to receive", with a frame rule and a bind rule.

INFERRED. The typing is the decidable half of HTT's split: quantities decide custody, `HasProt`
decides the envelope, `checkProt` is sound and complete on finite signatures. The F*/HTT move of
putting the WP *in* the type (`computation plan response result` indexed by a `Prot`) is tempting
and is refused here for the AMBITION's reason ("everything rich sits beside it as judged subsystems,
never inside") and for a technical one: there is no source subject reduction
(`REPORT-SOUND-20261101.md` "What it does not say"), so a type-carried WP could not be preserved along
`Steps` by any theorem the tree has; the machine's preservation (`typed_stepRaw_preserved`) does not
track counts. Hazel's protocol is the right *reading* of `Iface` (`! plan {P} ? reply {Q}` is
`requires`/`establishes`/`post` with iProps instead of lists); it becomes the thing to port when
definition 3 arrives. PROPOSED: the envelope stays a judge beside the type, and an activity's
`claim` is judged over its interaction tree (§4.1).

### 2.6 Laws as specifications: a postcondition judged at runtime, a proved law discharged statically

READ (`findler-felleisen2002-…`): higher-order contracts checked at run time with blame.
READ (`nguyen-tobinhochstadt-vanhorn2014-soft-contract-verification.txt`): "statically prove either
complete or partial contract correctness" by symbolic execution with contracts as symbolic values;
what is not proved stays a runtime check. READ (`leavens-naumann2015-…`, Theorem 12 and Theorem 30):
supertype abstraction is valid iff behavioral subtyping holds; specification inheritance (JML's
conjunction of inherited specifications) forces behavioral subtyping. READ (`dhara-leavens1996-…`):
the original "forcing" construction. READ (`liskov-wing1994-…` 249–250): the constraint clause for
history properties. READ (`parkinson-bierman2005-separation-logic-and-abstraction.txt`): abstract
predicate families as the unit of information hiding in a separation logic for classes. READ
(`kassios2006-…` was a slide deck, replaced by nothing; the dynamic-frames idea is READ through
`leino2010-dafny-automatic-program-verifier` and `smans`' abstract in the search results):
frames as sets of locations named by specification functions, so framing is a proof obligation
rather than a syntactic restriction. READ (`cook-hill-canning1990-inheritance-is-not-subtyping`,
`cook-palsberg1994-…`, `bracha-cook1990-mixin-based-inheritance`): inheritance as a fixed point of
generators; a mixin is a function of `super`.

INFERRED. obend's `law` is a runtime contract in Findler–Felleisen's sense, judged on every write
by re-execution, with blame as the ancestor clause (`effective_refusal_names`,
`dispatch_refused_names`). A *proved* law is Nguyen's "complete contract correctness": the same
predicate shown to hold on every write the program can make, so the runtime check is redundant
(and may stay, as the receipt's re-execution). The tree has one such proof rule, `keeps` by
certifying shape, and it is a *syntactic* discharge. Three more are cheap:

- **Presburger for the enforced fragment.** `LawExpr.denote facts old new` (`Spec/Law.lean`) is a
  Boolean combination of linear comparisons over `Int` readings of top-level scalar fields and four
  request facts. "Law `L` entails law `M`", "law `L` admits some write" (vacuity: a law nobody can
  satisfy refuses everything and is a bug, cf. `static-coverage-deductive-verification-dafny-boogie-2025`
  in paperbin), and "every plan this activity yields satisfies `L`" when the plans' fields are
  linear in the activity's data parameters, are sentences of linear integer arithmetic. Lean's
  `omega` decides them, `grind` with its linear-arithmetic and case-analysis engines decides them
  with hypotheses (READ `lean2026-reference-grind-tactic.txt`: "congruence closure, constraint
  propagation, E-matching, guided case analysis", linear integer arithmetic; `bv_decide` for the
  SAT-shaped ones with "a compact, machine-checkable certificate"). The certificate is the Lean
  proof; the regime is decidable; the trust base is the kernel.
- **Specification inheritance is `package_never_widens` plus a frame.** Leavens–Naumann's theorem
  says the modular reasoning principle (reason about `E.m()` by the static type's spec) is valid
  exactly when every subtype satisfies the supertype's spec, and conjoining inherited specs forces
  it. obend already conjoins laws along the C4 list and proves narrowing; what it lacks is the
  *claim* side: a claim proved of a layer, inherited by the compositions that keep what the proof
  read. That is §2.7.
- **Dynamic frames are supports.** A certificate's frame is the set of members its derivation
  unfolded through late binding, each pinned to the layer that provided it. Re-providing one of
  them in a later layer moves that pin, the support is withdrawn by name, the claim's slot reads
  `blocked` (`Slot.read_blocked_exact`, `stale_blocked_forever`). This is Kassios's framing as a
  proof obligation, realized by the slot theory with no new machinery.

### 2.7 The synthesis: one judgment, and late binding as its frame rule

PROPOSED. The judgment:

```
Holds (c : Term) (d⃗ : List Data) : Prop := Evaluates (apps c (d⃗.map Data.term)) (.boolean true)
```

for a closed claim `c`. For a claim of layer `L_j` in `O = fix (compose L₁ … Lₙ) seed`, its
`self` is `O` and its `super` is the row beneath `L_j`, `superAt j := L_{j-1} O (… (L₁ O seed))`
(`mixBody`: `λself. λsuper. upper self (lower self super)`), so the obligation is
`∀ d⃗, Holds (c O (superAt j)) d⃗`. The frame rule:

```
late_binding : ∀ (layers : List Layer) (seed : Term) (m : String) (j : Nat),
  seed is a record value →
  providesLast layers m = some j →            -- L_j is the last layer whose `extend` lists m
  Steps (.get (fix (compose layers) seed) m)
        (instantiate₂ (body layers j m) (fix (compose layers) seed) (superAt layers seed j))
```

where `body layers j m` is the field `m` of `L_j`'s `extend super {…}` (Elaborate lowers a spec layer
to `λself. λsuper. extend super {defs}`, line 1223, under a `specification` wrapper whose
`applySpecification` step strips it, and `compose` to `specification (composed …) (mix l u)`,
`composeStep` 991–1004). The proof is a finite reduction: `Step.fix`, `applySpecification`,
`mix_apply` (three steps, `Equiv/Behaviour.lean`), β twice per layer, `extendTarget` until the
inherited row is a record, `extendRecord`, then `Step.field` through `extendFields`, whose first
entry of a name is the *outermost* layer's (`fields ++ inherited.filter …`). INFERRED: the
hypothesis "seed is a record value" is what makes the `extend` chain reduce under CBN (the
inherited target is forced to a record by `extendTarget`); a seed that is itself a `fix` reduces
first and the lemma composes. The members a proof unfolds through `late_binding` are its supports.

This is the whole OO content of the logic. Cook's "inheritance is not subtyping" is the fact that
`body layers j m` mentions `self`, so a claim of `L_j` is a claim about the *final* `O`; Shaner's
mandatory calls are the `self.m` occurrences the derivation leaves in place rather than unfolding;
Leavens–Naumann's specification inheritance is the corollary that the claim holds of every
composition whose `providesLast` agrees on the supports.

## 3. Automation and certificates, per logic

READ (`Judge/Class.lean`): `class Judge (Obj Cert)` with `Clause`, `Meaning`, `check : Nat → Obj →
Cert → Verdict`, `sound`, `refutes`/`refuted`, `Fragment`/`complete`, `mono`; `Format` with decoders,
`trust`, `regime`, a planted bad certificate; `Translation` with `encode_sound`. READ
(`Judge/Instances.lean`): the bidirectional checker, the law probe (`lawProbe : Judge LawProblem
Unit`, deepened along a resource ladder, refusal refutes), `coerce`, C4, the envelope. READ
(`Judge/Lrat.lean`, `Judge/Certified.lean`): LRAT end to end, CaDiCaL's refutation replayed by the
kernel (`decide +kernel`), trust `compiled` for the 32-bit instance. READ
(`review/VISION-CLAUDE-20261031.md` §6.1): the three regimes and the rule "the system is as
automated as the set of certificate formats it can check".

PROPOSED, the table. "Hosts" says what the existing `Judge` class hosts with no change to the class.

| logic (§2) | producer (search) | certificate | checker (kernel re-checks) | regime | refutes? | hosts |
|---|---|---|---|---|---|---|
| ground claim at listed data | none, or a fuzzer/LLM choosing instances | the data instances | the machine probe on `claim d⃗`, read as `true`/`false` | decidable | yes: `false` at an instance refutes the ∀-claim (counterexample) | `lawProbe` reused: a `ClaimProblem` instance with `Meaning := Holds c d⃗`, same proof as `lawProbe` |
| rewrite derivation (§2.4, §2.7) | a rewriter: e-graph with proof production (egg/Flatt), a simplifier, an LLM proposing steps; translation validation as the discipline | a list of steps: `run` (a `Steps` segment at a path), `lateBinding m j`, `assoc` either way, `congr path` with a census check, `trans` | replay the steps from the left side, reach the right side; each step's soundness is a library theorem | semi-decidable with certificate | no (a rejected derivation says nothing) | the improvement judge's shape (`Judge/Cost.lean`), generalized: new instance `rewrite : Judge (Term × Term) (List RStep)` with `Meaning := ∀ ρ, l ρ ≈b r ρ` |
| Lean proof in the library (§2.6, §2.7) | tactics: symbolic execution of `step?` (`simp` as `CostTests` does on `runBounded`), `omega`/`grind` for the arithmetic, `decide +kernel` for ground instances, proof search (waterfall-shaped, reconstructed as a term), LLM-proposed lemmas | a theorem name whose statement is the generated obligation, in the build; the census is the check | the Lean kernel, at build; the receipt cites the library digest | decidable to check | by a disproof theorem (`¬ Holds …` at a witness) | not a `Judge` instance: the obligation is a theorem; `Obend/Census.lean` is its registry (`#assert_axioms_tree`) |
| Lean proof exported as bytes | the same | a proof term for a statement, with the library digest and toolchain pinned | a replay checker (`lean4checker`-shaped) run as compiled code | decidable to check | — | a new `Format` with trust `external "lean4checker"` or `compiled`; not first (§3.2) |
| Presburger for the enforced `law` fragment (§2.6) | `omega`, `grind` | the Lean proof | the kernel | decidable | yes: a witness write is a countermodel, checked by `denote` | a `SatisfiableLaw` judge whose certificate is one state and whose check is `denote` (decidable, refuting), today; entailment as a library theorem |
| finite product invariant over the protocol automaton (`law L on plan P`, Astra A's monitor) | a model checker | an inductive invariant `J` of the monitor×tree product | `Init ⊆ J`, `Step J ⊆ J`, `J ∩ Bad = ∅` by `decide` on finite `Sig` with listed responses | decidable to check | yes, with a bad path as witness | new instance beside `envelope` (VISION §6.5 row 4) |
| SAT/LRAT for finite-domain claims | CaDiCaL | LRAT | `Judge/Lrat.lean` | decidable to check | yes (a model) | `Translation` from a bounded claim (`Nat < 2ⁿ`) through `Judge/Identity.lean`'s Tseitin encoding; `encode_sound` is the work |
| cost upper bound (§2.2) | the clairvoyant oracle's choices: a cost analyser, or the machine's own demand trace read back as Skip/Let′ | one CV derivation | replay `Run .eval t v k` as listed | decidable to check; the bound is semi-decidable to find | no | the improvement judge's shape; a new instance `cvBound : Judge (Term × Nat) Derivation` |
| attestation | a named party | a signature | the receipt's `trust` field per support | attestable | no | `Receipt.Trust.attested who` exists |

### 3.1 The three regimes applied to one claim

INFERRED, `claim repeated(value: Nat)` of `ReviewMember.Twice`:

- *ground*: `repeated 3`, `repeated 0`, `repeated 41` run to `true` in the machine: decided, each
  an existential fact about one instance; `false` at any would be a refutation of the ∀-claim.
- *derivation*: `[lateBinding "twice" Twice, beta]` turns the left side into the right side
  syntactically; the judge accepts; meaning `∀ ρ, (self.twice v)ρ ≈b (self.review (self.review v))ρ`;
  the ∀-claim holds wherever the left side has a ground observation. Semi-decidable: the derivation
  was found by someone; its check is a replay.
- *Lean proof*: `∀ n, Holds (repeated O (superAt 2)) [natural n]` including convergence
  (`O.review (O.review (nat n))` halts at `natural (n + 4)`): a theorem by symbolic execution, in
  the library, kernel-checked at build.

The receipt names which of the three was run (§4.3). The third is strongest and the first is cheapest;
the second is the one a stranger re-checks without a Lean build.

### 3.2 Lean proofs as certificates: two routes, and why the library route is first

PROPOSED. Route A, *obligations as theorems in the build*: the elaborator writes, for each claim
with a `proved` marker, the Lean statement of its obligation (the quoted claim term, by
`Core/Code.lean` `quote`, its `address` as the statement's digest) into a generated module
`Obend/Logic/Obligations/<package>.lean`; a person or a tactic proves it; the census is the check;
the receipt says `proved at library <digest>`. For a stranger this is `attested` unless they
rebuild, and the receipt says so. Route B, *a `Format` whose certificate is an exported proof term*:
honest only with a replay checker whose trust base is named (`external "lean4checker"`); the
`Judge.check` function would run the Lean kernel's typechecker as compiled code. Route A first,
because it is what the tree does today for every stdlib law (`Law/Proofs/Std.lean`: "what each law
MEANS is a theorem over `Evaluates`"), because `Law/Run.lean`'s `run_sound` already reads machine
runs back as `Evaluates` facts under `decide +kernel`, and because Route B's checker is a project of
its own. Route B when a consumer without a Lean build needs the strongest regime.

### 3.3 What the existing `Judge` hosts without change

INFERRED. The ground claim judge (a copy of `lawProbe` with `Meaning := Holds`), the rewrite judge (a
generalization of `improvement` with more step kinds), the cost-bound judge (same shape), the
satisfiable-law judge (a `decide` on `denote`), and the product-invariant judge are all `Judge`
instances with `Nat` grades; none needs a new field. The envelope judge already hosts the
activity's `ensures` on finite signatures. Nothing in the class needs to change for this study; the
`Format` for Route B is the only registration that would.

## 4. The surface

### 4.1 What a person writes

READ (`Spec/Syntax.lean`): a `Spec` has `methods` and `claims` (`Claim.mk name params body`); a
`Module` has `laws : List (String × Law.LawExpr)`; `requires` in a spec is a *row requirement* (a
member the layer reads from the final self), not a precondition. READ (DESIGN §2): "Laws, three
kinds, one word", by where the law is written.

PROPOSED, the same discipline: **`claim` is the one word**, and its domain is where it is written.

```
spec Twice for Review:
  requires review(value: Nat) -> Nat
  def twice(value: Nat) -> Nat:
    self.review(self.review(value))
  claim repeated(value: Nat):                     -- about the final self (open recursion)
    self.twice(value) == self.review(self.review(value))
  claim positive(value: Nat) given 0n < value:   -- a precondition: `given` is sugar for an implication
    0n < self.twice(value)

def bump(count: Nat) -> Activity<Plan, Response, Nat>:
  match perform(Plan.write({field: 0n, before: count, after: count + 1n})):
    case written(_): count + 1n
    case refused(_): count
claim bump_plan(count: Nat):                        -- about the interaction tree: the first yielded plan
  plan(bump(count)) == Plan.write({field: 0n, before: count, after: count + 1n})
claim bump_written(count: Nat):                     -- the result after one listed response
  after(bump(count), Response.written({})) == count + 1n

law bounded: new.total <= 100                        -- unchanged: judged on every write
keeps bounded by capped                              -- the existing Claim.keeps, given syntax

claim augmented_refines_base: Augmented refines Base  -- a `≈b`-preorder claim, census b
```

- `claim` in a `spec`: `self`/`super` abstracted as today; judged of the fixed object, framed by
  late binding. `given COND` lowers to `ifBool COND BODY true`: no new elaboration.
- `claim` at module level over an activity: `plan(e)` and `after(e, r)` are claim-only forms the
  elaborator lowers to the turn judge's object (the term, the response list); they are not terms of
  the language (a program cannot observe its own plan: `perform` yields it). A claim over a
  resident (`serve`) is bounded (`within n turns`) or refused as `attestable`.
- `keeps INV by LAW`: `Claim.keeps inv law` (`Law/Claim.lean`), checked by shape at install as today.
- `refines`: `t refines t′` is `∀ ρ C, census C ≤ b → observations of C[t′ρ] ⊆ observations of
  C[tρ]` (the preorder half of `Observed .b`); a derivation that reaches `t′` from `t` by
  `≈b` steps proves it both ways; the one-way form waits for an improvement-style preorder.
- `costs`: not in this surface until C4 (§2.2); when it comes, `claim within(value: Nat): cost(self.twice(value)) <= 3n * cost(self.review(value)) + 2n` over CV cost with a derivation certificate.
- `invariant`: not a word; `law` is the invariant, judged per write, and `keeps` is its proof.
- `ensures`: not a word; a `claim` on a method with `result` would be sugar for the same thing and
  the parsimony lane would delete it.

### 4.2 How an obligation is stated, shown, discharged, or left open

READ (`Obend/Slot.lean`): a slot is candidates with supports and a judge; `usable`, `blocked`
naming the dead supports, `alternatives`; `Slot.World` with `stale_blocked_forever`. READ
(`Obend/Doc/Section.lean`): a section is a slot over runs; a cite is a support. READ
(`Spec/Elaborate.lean` 1496–1499): `SpecMeta.claims` lists `{name, status: "unchecked", rest}`.

PROPOSED. **Every claim is a slot whose candidates are certificates.** Candidate = `(format,
bytes)`; its supports = the pins its derivation read (`(member, layer)` pairs from `lateBinding`
steps; the library digest for a Lean proof; the data instances for a ground run); its judge = the
format's checker on the quoted statement (`address (quote c)` ties the certificate to the claim it
proves, `Core/Code.lean` `digest_of_quote`). The status in `SpecMeta.claims` becomes the slot's read:

```
unchecked                      -- no candidate: the obligation is a hole
checked(format, trust, digest) -- the selected candidate is usable at this view
blocked(support)               -- the selected candidate's support was withdrawn: a re-provided member, a moved library pin
refuted(instance)              -- a ground run returned false; the claim is false of this object
attested(who)                  -- a named party's word, nothing re-checked
```

An unchecked claim is not an error at `fix`; it is a hole (the slot theory's shape, PLAN WS 2's "a
quotation is usable at a view only while those pins hold"). `obend check` lists the open obligations
by name; `obend prove NAME` runs the producers in order (ground instances, the rewriter, the
tactics) and installs the first certificate the judge accepts, incumbent-first thereafter; `obend
verify RECEIPT` replays the certificate from the receipt alone. A `ProofSession` page (VISION §6.4)
is this slot rendered as a section.

### 4.3 What the receipt says

READ (`Obend/Receipt.lean`): roots, row, law digest, pins, openings, verdict, `Shape`
(`existsRun | planForAll | policyForAll | forAllPlan | forAll`), `Trust` per support, `dated` view,
chained `prev`; `recheck` computes coverage; the disclosure dial.

PROPOSED, one row per claim, nothing new in the type:

```
claim ReviewMember.Twice.repeated
  statement  address(quote c) = 0x…            -- the quoted claim, so the certificate is of THIS claim
  object     fix(compose(ReviewBase.Base, ReviewMember.Twice, ReviewMember.Augmented), seed) at pins …
  verdict    ok
  format     rewrite/1, 2 steps                 -- or ground/1 at [3, 0, 41]; or lean/library@<digest> theorem <name>
  shape      forAll                             -- ground: existsRun per instance
  regime     semidecidable                      -- ground: decidable; lean: decidable
  supports   twice ↦ ReviewMember.Twice@<pin>   checked
  trust      kernel                             -- the rewrite checker ran in the kernel; compiled for big derivations
  dated      view V
```

A stranger with the receipt and the quoted statement re-runs the format's checker; the supports'
pins are openings against `dated` (`openings_checked`); a `blocked` row names the support, as a
refusal must (AMBITION: "every refusal names what would pass").

## 5. The design

### 5.1 Which logic first, and why

PROPOSED: the equational partial-correctness logic of claims over `Evaluates`/`Interaction` (§2.4,
§2.7), with the three certificate formats of §3.1. Reasons, in order of weight:

1. It is the logic whose proof rules exist: `bequiv_of_steps`, `bequiv_of_ahead`,
   `rewrite_sound_below`, `mix_assoc`, `IEquiv`, and the law machinery's `judge_sound`. The new
   theorem is `late_binding`, a finite reduction. The first useful artifact is days, not weeks.
2. It answers the question the examples ask. `claim repeated` is in the source; `twiceOfThree == 7`
   is in the cohort; `bump` is one turn with two listed responses. None needs a heap, a cost, or a
   type-carried WP.
3. Its OO content is the one thing the literature does not hand us ready-made for lazy mixins:
   late binding as the frame rule and supports as dynamic frames. Getting that right first makes
   every later logic (cost, heap, hyper) inherit the frame.
4. It is honest about laziness: data parameters, partial results, termination as a separate
   certificate (§2.2), which is Vazou's lesson without stratified types.
5. It needs none of the five gates (`PLAN.md` "Gates before building further") except that the
   claim's *typing* certificate should come from one checker (gate 2); the logic itself is untyped
   (`Steps` on terms), which is also why the lack of source subject reduction does not block it.

Not first, with the reason each waits: separation logic in Iris-Lean (definition-3 statements only,
§2.1); cost triples over ticks (C4, `ticks_not_within_cv`); a type-indexed WP (no subject reduction,
and AMBITION's "beside, never inside"); hyperlaws (Astra C: after B's shared step); a refinement
preorder as its own calculus (§2.3: it is a claim form).

### 5.2 The module

PROPOSED, `lean/Obend/Logic/`, tier 1, no new dependency, census-imported:

| file | content |
|---|---|
| `Logic/Claim.lean` | `Holds c d⃗`; `apps`; `Obligation := {claim : Term, object : Term, superAt : Term, params : List Ty}`; the instantiation of a layer's claim at an object; `Holds` of a `==`-claim from `SameRuns` and a ground observation (`holds_equal_of_bequiv`) |
| `Logic/LateBinding.lean` | the lowered layer shapes as Lean definitions matching Elaborate (`layerTerm`, `composeTerm`, `providesLast`, `superAt`); `late_binding` (T1); `late_binding_bequiv` |
| `Logic/Rewrite.lean` | `RStep := run path n | lateBinding m j | assoc path dir | congr path | trans`; `check`; `rewrite_sound` (T2); the `Judge (Term × Term) (List RStep)` instance; a planted bad derivation refused `stepMismatch` |
| `Logic/Ground.lean` | `ClaimProblem`; the ground judge as `lawProbe`'s twin (`Meaning := Holds`), `refutes` on `false`; `claim_ground_sound`, `claim_ground_refutes` |
| `Logic/Frame.lean` | supports of a derivation; `claim_frame` (T3): a derivation accepted for `O` is accepted for every composition agreeing on `providesLast` at its supports |
| `Logic/Obligation.lean` | the claim slot: candidates `(Format name, bytes)`, supports, judge; status as the slot's read; `obend check`/`prove`/`verify` surfaces |
| `Logic/Turn.lean` (second step) | the interaction-tree claim: run `step?` to `Yields`, read the plan as `Data` (`Core/Data.lean` `execute` extraction), resume with each listed response (`Term.plug`), to depth `n`; `turn_sound` against `Interaction` |
| `Teeth/Logic/*.lean` | the three teeth of §5.4 |

Surface changes, all in `Spec/`: `claim … given …` sugar in `Parse`/`Elaborate`; `keeps INV by LAW`
as a module line; `plan`/`after` claim forms; `SpecMeta.claims` status from the slot. No change to
`Core/`, `Equiv/`, `Law/`, `Judge/Class.lean`.

### 5.3 The first three theorems

PROPOSED, Lean-shaped, each with its tooth.

**T1 `late_binding`** (`Logic/LateBinding.lean`).

```
theorem late_binding (layers : List Layer) (seed : Term) (hseed : Value seed ∧ IsRecord seed)
    (m : String) (j : Nat) (hj : providesLast layers m = some j) :
    Steps (.get (.fix (composeTerm layers) seed) m)
      (instantiate (instantiate (body layers j m) (superAt layers seed j)) (.fix (composeTerm layers) seed))
```

with `body layers j m` the field of `L_j`'s `extend super {…}` under its two binders and the
instantiation order fixed by `mixBody`. Corollary `late_binding_bequiv` by `bequiv_of_steps`. Tooth:
a composition where a later layer also provides `m`; the stored proof with `j` the earlier layer is
rejected (`extendFields` puts the later field first).

**T2 `rewrite_sound`** (`Logic/Rewrite.lean`).

```
theorem rewrite_sound {l r : Term} {steps : List RStep} {k : Nat}
    (h : rewriteCheck k (l, r) steps = .ok) : ∀ ρ : Nat → Term, l.substitute ρ ≈b r.substitute ρ
```

by induction on `steps`: `run` is `bequiv_of_steps` under `Ahead`'s congruence at the path;
`lateBinding` is T1 under the path; `assoc` is `mix_assoc` under the path (`CostWithin.context`'s
shape, `Judge/Cost.lean`); `congr` is `rewrite_sound_below b` with the census of the path's frames
(`Equiv/Quote.lean` `observes`); `trans` is `BEquiv.trans`. Corollary `holds_equal_of_rewrite`: for
`c = binary .equal l r` and data `d⃗` with `Halts (l d⃗) (natural n)`, `Holds c d⃗`. Tooth: the
planted derivation whose `lateBinding` names the wrong layer is refused `stepMismatch` at its index
(the improvement judge's `stepMismatch` tooth, kept).

**T3 `claim_frame`** (`Logic/Frame.lean`).

```
theorem claim_frame {layers layers' : List Layer} {seed : Term} {c : Term} {steps : List RStep} {k : Nat}
    (h : rewriteCheck k (instantiateClaim c layers seed, rhs) steps = .ok)
    (hsup : ∀ s ∈ supports steps, providesLast layers' s.member = providesLast layers s.member ∧
                                  body layers' s.layer s.member = body layers s.layer s.member)
    (hseed : Value seed ∧ IsRecord seed) :
    rewriteCheck k (instantiateClaim c layers' seed, rhs') steps' = .ok
```

where `steps'` is `steps` with its `lateBinding` indices re-pointed by `hsup` and `rhs'` the same
rewrite of `rhs`: the certificate transports along any change of composition that keeps what it
read. INFERRED: this is specification inheritance (Leavens–Naumann Thm 30's direction "inherited
specs are kept") stated as a certificate transport rather than a semantic subtyping, which is what
a slot needs: the supports *are* `hsup`. Tooth: `layers'` re-provides a support's member with a
different body; `hsup` fails on it; the stored proof is rejected; and the claim's slot reads
`blocked` naming the member (a `#tooth` on `read_blocked_exact`).

The three together are `verify ReviewMember` (§5.4). After them, in order: `turn_sound` for
activities; the satisfiable-law judge (a `decide` over `denote`, with `omega` entailment as library
theorems); then the cost-bound judge once C4 settles the semantics.

### 5.4 The first program verified end to end

PROPOSED. `lean/tests/obend-source/ReviewMember.obend`, unchanged source. Elaborated (READ
Elaborate: layers as `λself. λsuper. extend super {…}` under `specification`; `compose` as nested
`specification (composed …) (mix l u)`):

```
O     := fix (compose [Base, Twice, Augmented]) seed      -- seed := {review: λv. v, twice: λv. v} in twiceOfThree
claim := λself. λsuper. λvalue. (self.twice value) == (self.review (self.review value))
obligation : ∀ n, Holds (claim O (superAt 2)) [natural n]
```

The certificate, format `rewrite/1`:

```
[ lateBinding "twice" Twice      -- O.twice v  ⟶*  (λvalue. self.review (self.review value))[self := O, super := superAt 2] v
, run [] 1 ]                      -- β: O.review (O.review v)
```

after which the two sides of `==` are syntactically equal, so `rewriteCheck` accepts with the right
side reached. Supports: `{twice ↦ ReviewMember.Twice}`. `review` is never unfolded: the derivation
is the same for every composition whose last provider of `twice` is `Twice`, which `claim_frame`
states. Meaning by `holds_equal_of_rewrite`: `Holds` at every `n` where `O.review (O.review (nat n))`
halts at a natural, which for this composition is every `n` (`n + 4`, by `Augmented` over `Base`:
`v + 1` then `+ 1` twice).

Three teeth, as the tree cuts them:

1. *Ground.* `twiceOfThree() == 7` by the ground judge (`lawProbe`'s twin on the closed claim
   `twiceOfThree () == 7`); the cohort's expected `7`. Mutate `Augmented` to `super.review(value) +
   2n`: the ground judge returns `false` at `3` and the verdict is `refused`, refuting.
2. *Frame.* Add `spec Override for Prior.Review: def twice(value: Nat) -> Nat: value` after
   `Augmented`. `providesLast "twice"` moves; the support `twice ↦ Twice` is withdrawn; the claim's
   slot reads `blocked twice`; the ground judge at `3` returns `3 == 7 = false`: refuted of the new
   object, and the receipt names both.
3. *Statement.* The certificate presented with a claim of a different `address` is refused
   `malformed` before any step runs (`Format.checkBytes`).

Second program, `examples/Counter.obend` `bump`, by `Logic/Turn.lean`: `claim bump_plan(count)` and
`claim bump_written(count)` decided per listed response at ground `count` (the turn judge), and
proved for all `count` by a Lean theorem whose proof is symbolic execution of `step?` to the yield,
`Data` extraction of the plan with `count` symbolic (`after = count + 1` as `binary add (nat n) (nat
1)` forced to `natural (n+1)`), `plug` of each response, and `simp` to the value. This is the
`Interaction` relation of `Core/Term.lean` made a judge. `serve` gets a `within 3 turns` claim and
the receipt says `bounded`.

### 5.5 What in the current kernel makes it hard

READ and INFERRED, each with the consequence for this design:

- **No source-level subject reduction** (`REPORT-SOUND-20261101.md`: "source subject reduction is
  not proved in the tree; the proved preservation is the machine's"). The logic is untyped
  (`Steps` on terms), so T1–T3 do not need it; what it blocks is any claim stated *through* a type
  (a type-carried WP, a `linear`-custody claim along a run). Those wait on the machine's typed
  relation or on `steps_conserve_linear` getting its hypothesis.
- **Records as linear black holes** (C2; `get` drops siblings, no `⊗`/`&` elimination). A claim
  cannot destructure a resourceful record; claims about custody must be stated at the machine
  (per-address counts, not done) or through `Conservation`'s single-step statement. Out of scope for
  the first logic; named in the receipt as `uncovered`.
- **Two checkers** (`Check.infer`, `Bidirectional.checkAgainst`; gate 2). The claim's code is typed
  at elaboration; the obligation's typing certificate (that `c` has type `Bool` under its binders)
  should be the bidirectional one. Until gate 2, the logic cites neither; it is a fact about `Steps`.
- **The `fix` staging in `Equiv/Clairvoyant.lean`** (`fixLet` settles `selfBody` before tying the
  knot, Gemini item 4). Affects only cost; the equational logic uses `Step.fix` directly.
- **`claim` is lowered with `self` and `super` as the layer's own binders** (Elaborate 929–931), so
  a claim's `super` at the object is `superAt j`, not the seed; §5.2's `instantiateClaim` must
  compute it from the chain. A claim that only mentions `self` has no such subtlety.
- **The plan a program yields is a term; the kernel sees data** (`Core/Machine.lean`: `perform`
  allocates the plan lazily; `Core/Data.lean` extraction forces it within a budget). Activity claims
  are over the extracted data, so the turn judge needs a budget and reports `uncovered` when
  extraction suspends, exactly like the law probe (`Judge.deepen`).
- **`==` is `Nat` equality only** (`Primitive.equal`; `labelEqual` separate; no record equality).
  Claims over records and closures are equations in `≈b`, not `==`; the surface should say
  `equivalent` for them, judged by the rewrite judge directly.

### 5.6 The lane, in one paragraph

PROPOSED. Deliverable: `Obend/Logic/{Claim,LateBinding,Rewrite,Ground,Frame,Obligation}.lean` with
T1–T3 and their three teeth; `Spec/` changes for `given`, `keeps … by …`, and claim status from the
slot; `obend check`/`prove`/`verify` for claims; `ReviewMember.obend` verified as §5.4 with its
receipt in `lean/tests/logic/`. Gate: the three teeth red under their mutations, the receipt
re-checked by `obend verify` from the receipt and the quoted statement alone, cohorts unchanged
(`python3 tests/run-obend-source.py`: probes 30/30, tutorial 71/71, preview 161 with 0 failures),
the census on the standard three. Ground truth to paste into the brief: `Equiv/Behaviour.lean`
(`BEquiv`, `bequiv_of_steps`, `bequiv_of_ahead`, `mix_apply`), `Equiv/Quote.lean`
(`rewrite_sound_below`, `observes`), `Judge/Cost.lean` (the certificate replay shape,
`CostWithin.context`), `Judge/Instances.lean` 115–210 (`lawProbe`), `Law/Claim.lean` (`Keeps`,
`Chain`), `Spec/Elaborate.lean` 929–931, 1199–1244, 1486–1508 (layer and claim lowering), `Core/Term.lean`
(`Step`, `extendFields`, `mixBody`, `Interaction`), `Slot.lean` (`Slot`, `read_blocked_exact`).
Depends on nothing in flight; touches nothing under `Core/`, `Equiv/`, `Law/`. Not in the lane:
Iris-Lean, cost over ticks, hyperlaws, the exported-proof `Format`.

## 6. What this study refuses, with reasons

- **A separation logic as the first logic.** The demand machine's statements that need it are not
  the examples' statements; EQUIV-PLAN §5.4 already orders it last; and a unary WP over
  `Machine.State` without a `Language` instance is a project before it is a logic.
- **A WP in the computation type.** HTT and F* do this well for strict languages with a typed
  semantics; here the typing has no subject reduction at the source and AMBITION refuses rich
  structure inside the calculus.
- **`ensures`, `invariant`, `costs` as new words now.** `claim` by place, `law` per write, `keeps`
  as the proof; parsimony (`REPORT-PARSIMONY-20261101.md`'s discipline) would delete synonyms.
- **An SMT `Format` before a Presburger need.** The enforced `law` fragment's questions are decided
  by `omega`/`grind` in the kernel with a Lean proof; an Alethe checker is a lane when a claim's
  arithmetic leaves Presburger.
- **Stratified divergence types.** The data/term split of claim parameters and partial results
  give Vazou's soundness without a type-system change; a termination claim is a certificate.
- **Trusting the producer.** A rewriter, an e-graph, a language model, a cost analyser: each emits
  a derivation the kernel replays; none appears in the receipt except as `producer`.

## 7. Papers

Fetched for this study into `~/paperbin` (READ as cited above): `parkinson-bierman2005-separation-logic-and-abstraction`,
`liskov-wing1994-behavioral-notion-of-subtyping`, `leavens-naumann2015-behavioral-subtyping-specification-inheritance`
(TR 06-20b) and `leavens-naumann2013-behavioral-subtyping-ucf-tr`, `dhara-leavens1996-forcing-behavioral-subtyping-specification-inheritance`,
`shaner-leavens-naumann2007-modular-verification-higher-order-methods-model-programs`,
`morgan1998-programming-from-specifications`, `vazou2014-refinement-types-for-haskell`,
`moine-chargueraud-pottier2024-thunks-debits-time-credits` (Pottier, Guéneau, Jourdan, Mével),
`mevel-jourdan-pottier2019-time-credits-time-receipts-iris`, `devilhena-pottier2021-separation-logic-effect-handlers`,
`frumin-krebbers-birkedal2021-reloc-reloaded`, `swamy2016-dependent-types-multi-monadic-effects-fstar`,
`rastogi2021-programming-proving-indexed-effects-fstar`, `findler-felleisen2002-contracts-higher-order-functions`,
`nguyen-tobinhochstadt-vanhorn2014-soft-contract-verification`, `danielsson2008-lightweight-semiformal-time-complexity`,
`madhavan-kuncak2017-contract-based-resource-verification-memoization`, `necula2000-translation-validation-optimizing-compiler`,
`spectorzabusky2018-total-haskell-reasonable-coq`, `nanevski-morrisett-birkedal2006-hoare-type-theory`,
`flatt2022-small-proofs-congruence-closure`, `chargueraud2011-cfml-characteristic-formulae`,
`lean2026-reference-grind-tactic` (the reference manual chapter as text).

Already present and read: `hackett-hutton2019-call-by-need-is-clairvoyant-call-by-value`,
`moran-sands1999-improvement-in-a-lazy-context`, `breitner2014-adequacy-of-launchburys-natural-semantics`,
`launchbury1993-natural-semantics-lazy-evaluation`, `iris-in-lean2026`, `jung2018-iris-from-the-ground-up`,
`dardinier-mueller-hyper-hoare-logic-pldi2024`, `kozen1997-kleene-algebra-with-tests`,
`leino2010-dafny-automatic-program-verifier`, `leino-2010-usable-auto-active-verification`,
`filliatre-2013-why3-where-programs-meet-provers`, `lattuada2023-verus-linear-ghost-types`,
`martinez-2019-meta-fstar-proof-automation-smt-tactics`, `cook-hill-canning1990-inheritance-is-not-subtyping`,
`cook-palsberg1994-denotational-semantics-of-inheritance`, `bracha-cook1990-mixin-based-inheritance`,
`das2019-nomos-resource-aware-session-types-digital-contracts`, `angelo2026-contextual-metaprogramming-session-types`,
`wang-dillig-lahiri-cook2018-verifying-equivalence-database-driven-applications`, `willsey-2021-egg-fast-extensible-equality-saturation`,
`necula-1997-proof-carrying-code`, `appel-2001-foundational-proof-carrying-code`, `cruz-filipe-2017-efficient-certified-rat-verification`,
`static-coverage-deductive-verification-dafny-boogie-2025`.

Missing (paywalled or not found as PDF; cited from memory and marked so): Back & von Wright,
*Refinement Calculus: A Systematic Introduction* (1998) and "Refinement calculus, part I" (1990);
Parkinson & Bierman, "Separation logic, abstraction and inheritance" (POPL 2008); Kassios, "Dynamic
frames" (FM 2006; the fetched file was a slide deck and was removed); Smans, Jacobs & Piessens,
"Implicit dynamic frames" (2008/2012); Sands, "Total correctness by local improvement" (TOPLAS
1996); de Moura et al., "grind: an SMT-inspired tactic for Lean 4" (2025, Springer). None of the
study's claims rests on a sentence of these; where their ideas are used (§2.3, §2.6) the fetched
descendants (Morgan, Leavens–Naumann, Leino's Dafny) carry them.
