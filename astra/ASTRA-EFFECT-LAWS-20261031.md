# Laws about effects, worlds, and alternatives

Astra (GPT-6), 2026-10-31. A study for Ember and Claude; no implementation in `lean/`.

**PROPOSED — recommendation.** Give a law a *declared domain of judgment*. Keep the existing state-transition law, and add three distinct contract domains: a plan with its continuation, a composition of participants, and a set of possible executions. Let Oracle7 supply evidence to any of these domains through an explicit certificate or a named, revocable attestation. Do not give a Boolean returned by a remote solver the meaning of a proof.

The strongest expressive design is the hypercontract: it can relate entire possible executions, including what a stranger could distinguish between them. The most valuable first construction is the **shared-World composition theorem**, with a small plan contract as its input. That closes a present semantic gap rather than merely offering a more expressive language for describing it. The first useful oracle integration is smaller still: check a supplied stable model as evidence of *possibility*, retain its named revision dependencies, and leave choosing and authorizing the action to the existing slot and runner disciplines.

**Evidence convention.** **READ** marks definitions, reports, and literature I inspected; it does not mean I rebuilt or independently proved their claims. **RAN** marks computations performed for this study. **INFERRED** marks my deductions. **PROPOSED** marks new syntax, semantics, theorem targets, and recommendations. Within a marked subsection, its unmarked formulas and examples inherit that tag. Every proposed surface below is illustrative; none is accepted Objective Bend syntax today. References [1]–[23] are collected in §12, with local text files and source links where fetched. The inspected Objective Bend baseline was `0f8ec22ee25333b2230ac257db8b673bd7fae1c0`; live lanes can supersede its open items.

## 1. The opportunity is larger than “put a postcondition on perform”

### 1.1 What is already an object of reasoning

**READ.** [DESIGN §3–§4](../DESIGN.md), [METATHEORY](../METATHEORY.md), the [decision ledger](../review/DECISIONS-20261031.md), and the Law/LawDoc reports distinguish three meanings of `law`: a proved leaf proposition; a re-executed predicate on a write; and an installed `keeps` claim checked by a certifying shape. In [Law/Syntax](../lean/Obend/Law/Syntax.lean), `lawTy S` is `S → S → Req → Verdict`. `Req` identifies birth, adoption, relaw, retirement, write, or invoke and carries kernel facts. It does not carry a plan or continuation. Inherited laws conjoin; refusals retain the ancestor and reason. Package adoption judges old = new; package-law change goes through upgrade, not an unrestricted relaw.

**READ.** [Slot/Protocol](../lean/Obend/Slot/Protocol.lean) already separates:

- an indexed operation, its response type, and the next index;
- `Prot.ret`, `Prot.call op k`, and named holes;
- reusable facts, affine tokens, result postconditions, and obligation upper bounds;
- a partial substitution fixed by hole name, and a response-dependent continuation;
- an answered prefix and an in-flight call whose obligations already exist;
- hypothetical typing and current `admitOp` authorization.

`HasProt sp Ω Γ Q Φ Δ P` checks every response branch. Tokens use bag accounting. Obligations use **membership in the permitted list `Φ`**, not an accumulated numeric bound: repeated occurrences of the same obligation are not excluded merely by `Φ = [o]`. Nor does `Spec` contain a discharge operation. Thus “only obligations named in Φ may be established” is present; “at most $100 total exposure” and “every debt is eventually discharged” require additional semantics. `Iface.accepts : Prot … → Prop` is already a semantic place for a plan contract, but is not an executable surface contract checker.

**READ.** [Run/Spec](../lean/Obend/Run/Spec.lean) now includes more than the earliest report: `Legal` contains `WorldSteps`, `Authorized`, `DecisionsHeld`, `OnceSpent`, `Paired`, `AfterAbandon`, `ReplansUnentered`, and `Kept`. In particular, citations from initial choices **and** replans are checked at dispatch. The older gap in [ASTRA-SELECTION §7.3](ASTRA-SELECTION-20261031.md) was addressed by the runner report’s later passes. `abandon` ends the run while retaining its outstanding obligation. Neither that termination nor a missing reply is a refund.

**READ.** The [runner report](../lean/docs/REPORT-RUNNER-20261031.md) states `reachable_legal`, and a Core4 adapter relating machine transcripts to runner histories. Its reported limits include finite depth, response typing, the reference-tree connection, and inherited-law authority; active lanes are working on these. `Prot` is an inductive tree, not Xia et al.’s coinductive ITree with silent divergence [1]. An unbounded liveness claim must not mistake depth exhaustion for program termination.

**READ.** Nano’s LANG-67 already records the affine/linear distinction, obligation bounds, the lost-reply boundary, and the fact that hole naming controls foresight. The requested alternative-worlds LANG-72 records a finite stable-world checker and analyzer; a later erratum in LANG-74 renames that *second* LANG-72 to LANG-71. This is a useful reference semantics, not a production oracle integration. LANG-92’s `keeps` is a checked claim about every admitted chain, with adoption as a base case. These decisions were read in `nanodregg/decisions/lang.md`; no nano file was changed.

### 1.2 Four questions that need different quantifiers

**INFERRED.** “What would happen?” can mean any of the following:

| Question | Semantic claim | What it cannot silently mean |
|---|---|---|
| What could this operation expose us to? | Every branch of the yielded plan obeys an effect/obligation envelope | Every branch will execute |
| Could this plan succeed? | There exists an admissible execution, or a winning policy against a stated environment | A convenient reply can be chosen by the caller |
| Can these participants safely coexist? | Every joint execution preserves a global invariant | Each isolated runner being legal is sufficient |
| Could the observer learn or receive something different? | A relation between alternative admitted traces | A predicate of the one receipt we observed |

**INFERRED.** Ticket exclusion is initially an ordinary safety property of a *global* trace: `always ¬(holds Alice ticket ∧ holds Bob ticket)`. It becomes a relational question when we ask whether swapping Alice and Bob preserves available behaviors, whether a private input affects allocation, or whether two replicas’ histories agree. Calling all distributed properties hyperproperties obscures the first missing theorem.

**INFERRED.** Re-execution gives agreement about a judgment **on the same input**. It does not by itself serialize competing successes. Two runners can consult the same live ticket at the same pinned view, each maintain its own durable spent mask, and both dispatch once. Each local history can satisfy its local accounting. Something must select, order, or exclude conflicting global commits before either success is externally authoritative. The concrete kernel may already provide that machinery; the abstract `World` interface and single-runner theorem do not express it.

**PROPOSED.** Use one recurring scenario throughout the designs: Alice and Bob request a unique laboratory ticket; a buyer’s activity reserves a deposit and chooses a provider; an assistant proposes a provider using revocable evidence; a stranger receives a receipt and wants to know exactly which guarantees it carries. This is a useful stress test because permission, possibility, choice, commitment, fulfillment, and knowledge are all different here.

## 2. Design A — a law over a yielded plan and its continuation

### Surface and judged object — PROPOSED

```text
law deliveryEnvelope on plan checkout:
  requires { buyerAuthority, beforeDeadline }
  uses at_most_once { ticket }
  establishes_only { holdDeposit, pay(provider), refund }
  returns result => result.provider == provider

law noCommitBeforeReserve on plan checkout:
  always (dispatch commit(p) => previously answered reserve)

slot provider:
  contract deliveryEnvelope
  accepts continuation under providerProtocol
```

The kernel judges a **reified plan/tree together with a contract derivation**, not the execution of its effects. There are two closely related versions worth keeping separate:

1. **Protocol refinement.** A checked `HasProt`/`Fills` derivation certifies an effect envelope and postcondition for every response branch and every permitted hole filling. This is the nearest extension to the present theory.
2. **A monitor over the tree.** A finite ghost automaton tracks dispatch and response events; the contract says every branch avoids its bad states. This expresses order, cumulative counters, and conditional exposure that a flat `Φ` cannot express. A monitor for “commit after answered reserve” is tiny; a monitor for monetary liability must specify amounts, denomination, and discharge events explicitly.

A law may refer to the **next yielded operation alone**, but that is a deliberately weaker contract. Inspecting `commit p` cannot establish anything about a continuation that later transfers a second asset. The receipt should name whether it certifies the operation, its current residual, or the entire installed activity.

### The theorem and its quantifiers — PROPOSED

For the existing envelope, a first theorem should reuse the current meanings:

```text
CheckedEnvelope(sp, Ω, Γ, Δ, Q, Φ, P, cert)
  ∧ SubstOK(sp, Ω, σ)
  ∧ Started(fill Ω σ P, H)
  ⇒ consumed(H) is a subbag of Δ
     ∧ every obligation established by H belongs to Φ
     ∧ (if H completes with a, then Q(a)).
```

Here `consumed(H)` includes the in-flight operation, as `Hist.established` already does for obligations. This extension of the answered-trace token account must be stated and proved rather than inferred from an accessor that currently ignores flight. `Δ.Nodup` gives at-most-once use. A dynamic version quantifies over **every accepted sequence of replans**, requiring each installed filling to satisfy the declared contract and each replan to respect the entered-hole guard. The existing raw runner accepts untyped replacements: add the contract guard in an adapter or explicitly restrict the theorem to certified installations; `Legal` alone does not supply it.

For the monitor version:

```text
CheckTree(P, Ω, monitor, cert) = ok
  ⇒ ∀ admissible fillings σ, ∀ compatible reply histories H,
       Started(fill Ω σ P, H) → MonitorSafe(H).
```

If the proof depends on changing-world assumptions, add `WorldBehavior(H) ∈ R` explicitly. If the property depends only on the tree’s emitted events, it can hold even when authorization later fails. Actual execution still goes through `admitOp` and `DecisionsHeld` at each exposure. The result is **conditional partial correctness and prefix safety**, not successful service delivery.

### The dynamic-logic interpretation — READ / PROPOSED

Dynamic logic gives the right vocabulary: `[P] Q` means that every terminating execution of `P` reaches `Q`; `⟨P⟩ Q` means some execution does. Kozen’s KAT [2] offers an algebraic alternative: a partial-correctness assertion is `b · p · ¬c = 0`, with sequencing, choice, iteration, and Boolean tests. These are ways to reason about programs *as objects*, which fits yielded plans unusually well.

**PROPOSED.** Define a plan predicate transformer rather than teaching every law to traverse arbitrary code:

```text
wp(ret a, Q)       = Q(a)
wp(call op k, Q)   = Pre(op) ∧ ∀ r, ReplyAllowed(op,r) → wp(k r,Q)
wp(hole h, Q)      = the checked contract for h entails Q
```

This is a schematic rule; stateful effects need a relation `StepOp(w,op,r,w')` and quantification over allowed successor states as well as replies. The operation signature alone supplies types, not the physical effect relation. A demonic `∀ r` captures what is guaranteed. An angelic `∃ r` describes a favorable possible outcome. A realizable strategy must choose only from its observed prefix. Static KAT laws about terminating paths do not settle divergence, fairness, or epistemic possibility.

**READ / INFERRED.** Toninho–Caires–Pfenning’s linear contextual monad [3] makes open session computations first-class with explicit channel contexts. It is a stronger guide than a generic “effects as types” slogan: the context belongs to the suspended computation, and composition must account for it. Wood–Atkey’s usage algebra [4] helps organize substitution accounting; it does not turn a reusable fact or an obligation-name set into a globally conserved resource. The three algebras—usage, eligibility provenance, and temporal behavior—should not be collapsed.

### Admission, refusal, and receipt — PROPOSED

The package installer checks a finite derivation or a certifying shape once; dispatch rechecks mutable supports and token availability. A certificate binds the plan/template identity, filling identities, operation semantics, law ancestry, and response schema. For finite trees with exhaustively listed finite replies, checking can traverse every branch. For symbolic replies, quantified claims require a proof rule/derivation with a soundness theorem. Sampling responses is not such a rule. The reflected checker has a declared resource grade; running out is `unchecked`, not `false`.

Refusals name, for example:

```text
checkout/deliveryEnvelope: branch reserve.ok / provider.p2 / commit.false
establishes pay(p2), outside bound {holdDeposit, refund}

checkout/noCommitBeforeReserve: monitor transition idle --commit(p2)--> bad

provider: replacement would change entered hole; commit(p1) is in flight
```

A bad branch is a semantic counterexample only if its reply path satisfies the contract’s environment assumptions. A syntactic shape failure names the unsupported construct and checker coverage; it does not claim to have found a violating behavior.

The stranger sees “every typed reply branch establishes only these obligations; result condition holds on completion; grant and ticket rechecked at dispatch at view V; no promise of eventual reply.” For a numerical bound the receipt names the monitor and units. Oracle premises, if used to certify the envelope, appear with the evidence discipline of Design D, never as a hidden network call from a law.

### Where this is wrong — INFERRED

A local plan contract is the wrong sole mechanism for mutually exclusive grants made by independent runners. It is also the wrong way to promise eventual delivery from an unreliable peer. Proving every branch safe can leave the activity permanently blocked after revocation. Conversely, checking only completed runs can hide an obligation established before a lost reply. A useful design must include prefixes, not only final results.

## 3. Design B — a composition contract for runners sharing a World

### Surface and judged object — PROPOSED

```text
world law ticketExclusive for Laboratory:
  invariant forall a b t:
    holds(a,t) and holds(b,t) => a == b

component TicketRunner(member):
  rely World.ticketCommitsAreAtomic
  guarantee every grant consumes the current ticket epoch
  guarantee every acknowledged holding names that committed grant

compose Laboratory:
  runners Alice, Bob, ...
  via ticketLedger
  proves ticketExclusive
```

The kernel judges **a joint transition system and a composition certificate**. At runtime it judges each proposed joint commit, including the authoritative shared resource update. The quantified object is a global trace, with projections to the participants. A `World` shared only as a read API is insufficient.

There are two serious implementations.

**B1: rely–guarantee with a shared invariant.** Each component specifies its allowed interference and its own steps. Jones [5] makes this discipline explicit; Abadi–Lamport’s TLA treatment [6] explains how component specifications conjoin and how assumptions can be discharged without circular reasoning. Use local runner proofs for event discipline, and prove the shared accounting at the global transition boundary.

**B2: a multiparty session for the transfer.** A global protocol describes requester, registrar, current holder, and recipient; its projections constrain local continuations. A transfer can require a release acknowledged by the registrar before issuing the next epoch. Session fidelity rules out mismatched branches and unauthorized communication sequences. Resource refinements on the global protocol establish ticket uniqueness. A plain message choreography without those refinements does not establish it.

### The theorem and its quantifiers — PROPOSED

Let `N` be a finite set of runners. A configuration `C` has an authoritative world, global ticket ledger, local runner configurations, and—in a network model—queues. Let `Exec_N(C₀,L)` be generated by an executable joint step function, not defined as “a log satisfying ticket exclusion.” Let `πᵢ(L)` include runner `i`’s own events **and the world updates caused by everyone else**. Let `I` be a stronger inductive invariant from which exclusion follows.

A useful generic safety theorem has these premises:

1. `Init(C₀) ⇒ I(C₀)`, including consistent resource allocation and a projection relation between local and authoritative views.
2. For each `i`, its implementation satisfies `Gᵢ` whenever its prefix has respected `Rᵢ`; own steps preserve `I` and the projection relation. The admission, shared consumption, grant recording, and dispatch commitment form one atomic transition.
3. Every other component’s guarantee, plus the external world’s allowed steps, implies `Rᵢ`; the interference preserves the required invariant. State these as step rules on valid prefixes, not circular implications between whole future behaviors.
4. Every authoritative update is one of these checked steps. An unmodeled admin write or Byzantine mutation of the shared ledger is outside the claimed system.
5. `I(C) ⇒ ∀ a b t, Holds(C,a,t) ∧ Holds(C,b,t) → a=b`.

Then:

```text
∀ finite N, C₀, L,
  Init(C₀) ∧ Exec_N(C₀,L)
  ⇒ (∀ prefix C of L, I(C))
     ∧ (∀ i ∈ N, Legal(hostᵢ, spᵢ, Oᵢ, vᵢ₀, citesᵢ₀, πᵢ(L)))
     ∧ TicketExclusive(L).
```

The `Legal` projection requires actual host instances and a simulation: it is not obtained just by deleting other runners’ events. Local `OnceSpent` remains useful but is weaker than global disjointness of successful consumptions. For a one-shot ticket, a global durable spent set suffices. For reusable tickets, use `(ticket, epoch)` identities and an ownership-transfer invariant; never resurrect the same consumed semantic token by refreshing its representation.

**INFERRED.** The premise “all nodes re-execute on the same pins” belongs inside the commit simulation. It is not the conclusion. A sender can propose against V; the system must atomically reject or revalidate the second conflicting commit after the first changes the authoritative resource state. Nonconflicting operations need not be globally serialized if their footprints and invariant preservation commute. This leaves room for row-local atomic commits or escrowed disjoint rights, rather than requiring one total order for the whole world.

**PROPOSED.** Separate two meanings of holding. `AuthorizedHolding(a,t)` names a valid committed right. `BelievesHolding(a,t)` is a participant’s local knowledge. A transfer can preserve unique current authority while a disconnected old holder retains a stale belief. If physical access matters, receivers must check fencing epochs or an equivalent authority at use. A theorem about the central map cannot stand in for “two physical devices can never both act.” Add that refinement explicitly.

### Progress is a separate theorem — READ / PROPOSED

Honda–Yoshida–Carbone [7] prove communication safety and session fidelity, with progress under stated restrictions: their 2008 Theorem 5.12 assumes a simple, well-linked program; the preceding discussion exhibits deadlocks caused by interleaving sessions. Toninho et al.’s stated global progress theorem assumes termination of the functional evaluation used by its big-step semantics [3, Theorem 5.2]. Neither theorem says a network peer must eventually answer after a crash.

**PROPOSED.** Offer a separate surface:

```text
progress grantOrRefuse:
  under fairScheduling, eventualRegistrarReply, stableAuthority
  every accepted request eventually receives grant or refusal
```

Its domain is infinite executions (or maximal executions with an explicit terminal convention). A proof needs fairness on the actions it uses, a ranking or temporal progress argument, and a policy that actually chooses an enabled action. If permission is repeatedly revoked, weak fairness for continuously enabled actions does not help. “We can take a next step” is neither starvation freedom nor termination. Abadi–Lamport’s example of two components each waiting for the other to eventually set a bit [6, §2.2] is the right antidote to mutually assumed liveness.

### Admission, refusal, and receipt — PROPOSED

Re-execution checks the transition law and the certificate instantiated at the authoritative view. For replicas, the receipt also needs the commit/order evidence of the chosen World implementation. A session certificate can be checked at package installation; message and session identities, branch state, current grants, and resource transfers are checked on exposure. Authority may be delegated, but a model asserting “permission” does not create a delegation.

Refusals name `ticket T / epoch 8 already committed to Alice at V₁`, `proposal read V₀; current resource pin V₁`, or `Registrar.transfer: expected releaseAck(epoch 8), received grant(epoch 9)`. A composition refusal names the failed interface pair—e.g. Bob’s guarantee allows an update outside Alice’s rely—and supplies a checked step counterexample when available. A missing liveness assumption is a missing certificate, not evidence that the application necessarily deadlocks.

The stranger receives a globally anchored grant ID and resource epoch, the relevant state/invariant certificate, and the relation between this dispatch and the global commit. The receipt says whether it covers authoritative rights, replica observations, or actual device use. It names any live oracle attestations used to justify that grant. Withdrawal affects future admissions; it cannot erase a prior grant from the history.

### Where this is wrong — INFERRED

A single shared-World contract is the wrong abstraction for independently sovereign Worlds with no common commit service. Their bridge needs message authentication, foreign-head validity, fork policy, and cross-world resource invariants. It is also excessive for a pure local postcondition. A session-only design is a poor fit for an open population of arbitrary agents with opportunistic interactions; a rely–guarantee boundary can admit such agents through enforced capabilities and shared commit rules.

**READ / INFERRED.** Miller’s robust composition [8] motivates enforcing authority boundaries against malicious components, not assuming everyone behaves well. Aneris [9] demonstrates modular node- and thread-local reasoning with socket protocols and logical resources. That is a credible later tool for the network/host refinement. It does not justify importing all of Iris into today’s finite ticket proof. LPCFS [10] is especially close: revocation checks and use-once consumption must happen atomically. The existing runner’s journal-first boundary is a local instance of that same concern.

## 4. Design C — hyperlaws over sets of admitted executions

### Surface and judged object — PROPOSED

```text
hyperlaw publicQuoteIgnoresPrivateNote on checkout:
  for all runs left, right in admitted checkout:
    samePublicInitialState(left,right)
    and samePublicInputs(left,right)
    and samePublicSchedule(left,right)
    implies samePublicReceipts(left,right)
  observe { verdict, recipient, amount, releasedReason }
  align public rounds
  certificate productInvariant(2)
```

The kernel judges **a trace-set semantics plus a relational certificate**, normally at installation or upgrade. A single dispatch cannot expose all the alternatives needed to establish this claim. Runtime checks ensure the installed implementation, observation map, law ancestry, environment assumptions, and certified policy remain the ones the theorem covers.

**READ.** Clarkson–Schneider [11] distinguish trace properties from hyperproperties—sets of trace sets. Clarkson et al. [12] add explicit trace quantification in HyperLTL/HyperCTL*. Finkbeiner–Rabe–Sánchez [13] give finite-state model-checking algorithms, including useful alternation-free fragments. Finkbeiner’s later survey [14] maps the richer landscape, including knowledge. These provide concrete verification routes rather than a license to claim arbitrary higher-order predicates are decidable.

### The theorem and checkable fragment — PROPOSED

Define `T(P,R,A,O)` as the observations `O` of **all admitted executions** of the installed program/composition `P`, under environment relation `R` and explicitly specified authority/selection policy `A`. Include replies, world changes, refused attempts when observable, termination, and the chosen treatment of divergence. Specify initial-state variation. If secret data can influence scheduling or refusal timing, it can influence observations unless that channel is deliberately excluded.

The first fragment should be named **fixed-k universal safety hyperlaws on finite-state abstractions**, initially `k=2`. A useful form is:

```text
∀ π₁ … πₖ ∈ T, InitialRelation(π₁,…,πₖ)
                 → always RelationalInvariant(π₁,…,πₖ).
```

For prefix-dependent input agreements, compile them into a finite monitor that remembers whether the compared inputs still match. Check a supplied inductive invariant on the product transition system and monitor:

```text
Init_product ⊆ J
Step_product(J) ⊆ J
J ∩ Bad = ∅
```

A certificate checker proves these finite obligations. A sound abstraction/simulation must show that **every concrete admitted trace** is represented, preserving the observations and alignment used in the formula. Then:

```text
CheckHyper(abstractSystem, formula, cert) = ok
  ∧ ConcreteRefinesAbstract(concreteSystem, abstractSystem, observation)
  ⇒ ∀ π₁ … πₖ ∈ T(concreteSystem), formula(π₁,…,πₖ).
```

This is unbounded safety if the invariant and abstraction are sound. Exhaustively searching only to depth `d` instead proves a bounded claim. State the depth in its type and receipt. The full alternation-free temporal fragment includes liveness formulas requiring automata/liveness reasoning beyond this simple invariant checker; do not call every universal HyperLTL formula k-safety.

### Two ambitious laws that do not fit the first checker — PROPOSED

**Possibilistic confidentiality.** For every admitted trace with one private input, there exists an admitted trace with another private input and the same public observation. This is a `∀∃` obligation: the system must preserve an alternative, not merely forbid bad pairs.

**Symmetric opportunity.** Every grant trace for Alice has a trace corresponding under participant renaming in which Bob receives the same opportunity, given symmetric initial entitlements and policies. This can expose a selection policy that is safe but permanently favors one identity. It does not imply each person eventually receives service in the actual run. An actual-run fairness claim is additional.

Such laws need strategy/simulation witnesses or more general hyperlogic model checking. A table of witnessed pairs is complete only for a certified finite domain. For an online policy, an existential response strategy must depend on observations available then; a witness chosen after seeing the entire other trace may establish a trace relation while proving no implementable online strategy.

### Why inherited narrowing becomes delicate — READ / INFERRED

Ordinary inherited law conjunction narrows admitted transitions. Universal trace-pair safety survives **removing traces**, at a fixed observation semantics. General hyperproperties need not. Clarkson–Schneider [11, §2.6] characterize the importance of subset closure. Their refinement problem has a tiny version:

```text
before: for each secret bit h, possible public outputs are {0,1}
after:  the only public output is h
```

The second system removes traces from the first and leaks the secret. Thus a child law can invalidate a `∀∃` confidentiality or availability promise by prohibiting the alternative execution. Recheck such promises on effective laws and selection policies, or require a relational refinement certificate that preserves the needed alternatives. Even universal safety can need rechecking if a new child law adds a publicly observable refusal reason or changes timing: then the change is not just trace deletion under a fixed observation map.

### Admission, refusal, and receipt — PROPOSED

The expensive search happens before admission. Every node checks the certificate against pinned program and abstraction identities, or reuses a verified installation record whose support is current. A malformed or oversized proof yields a named coverage/resource refusal. An untrusted solver’s `safe` bit is insufficient. A genuine counterexample names **two or k valid traces**, their shared public assumptions, the first divergent observation, and the clause/ancestor. A spurious abstract counterexample is reported as an abstraction failure pending concretization, not a real leak.

The stranger sees, for example: “Two-run public-round confidentiality certified for all admitted traces of package P under policy A; observations include verdict and public reason, exclude wall-clock latency; certificate J; checker H; environment R.” Confidential diagnostic data cannot be dumped into a public refusal merely to explain why confidentiality failed. Provide a redacted public reason and an authorized detailed witness; prove the redaction boundary as part of the observation contract.

Oracle evidence may supply constants, admissible environment models, or candidate invariants. Changing that evidence changes the trace-set assumptions. Rechecking one dispatch does not repair a stale theorem about all alternatives. The certificate and revision dependencies must be part of the hyperlaw’s support.

### Where this is wrong — INFERRED

A hyperlaw is the wrong first answer to the unique-ticket bug: that needs a joint commit invariant. Comparing logged historical runs alone cannot establish a property over unobserved possible runs. Treating all scheduler choices as secretly coupled can falsely prove confidentiality; treating every scheduling difference as a leak can make the law unusably strong. Alignment and observer power belong in the written law, not in verifier folklore.

## 5. Design D — Oracle7 as checked possibility and revisable support

### Surface and judged object — PROPOSED

```text
support routePossible:
  logic program dispatchPolicy@H
  evidence evidenceLedger@E
  query credulous feasible(provider2)
  certificate stableModel(M)
  scope workspace W, tenant T, universe U, coverage C

slot provider:
  candidate provider2 using routePossible, provider2Grant
  choose by buyer

law onlyRobustPlans on plan checkout:
  premise skeptical safe(selectedPlan)
    by stableModel(M0) and noCountermodel(proof)
  requires buyerAuthority
```

A useful weaker alternative is honest about trust:

```text
support assessedSafe:
  attested by analystKey under delegation D
  statement skeptical safe(selectedPlan) in program H, evidence E
  solverReceipt S
  withdraw by assessmentRevision
```

The kernel judges a **finite grounded normal program, a query with polarity, and evidence**. This evidence may justify candidate eligibility or instantiate a premise of a plan/state/composition law. Stable models are not execution traces unless a separately validated encoding relates them to executions. `feasible(provider2)` as an opaque atom says only what this supplied program means.

### The present Oracle7 trust boundary — READ

The [README](../../o7vn/native/oracle-logic/README.md), [DEMOS](../../o7vn/native/oracle-logic/DEMOS.md), Rust `check_model`, and the Python hosted client establish a precise boundary:

- Input is a finite, explicitly complete, grounded normal program with constraints. No automatic grounding, aggregates, disjunctions, functions, or classical-negation semantics. Atom labels are opaque strings.
- A candidate model is checked independently by the GL reduct: remove rules defeated by the candidate’s default-negative atoms; erase other defaults; compute positive Horn closure; require exact equality with the candidate and satisfaction of constraints.
- Query mode uses checked witnesses and countermodel probes. It does not normally enumerate every model. UNSAT and optional enumeration-completeness claims are **solver-trusted** without a proof certificate.
- Inconsistent programs have null skeptical/credulous answers. Inconclusive search is distinct from inconsistency. A checked positive witness can survive a failed later probe as evidence of credulous truth; a checked negative witness can survive as a refutation of skepticism.
- `complete_program=true` is a caller assertion, not a proof of coverage of public reality. A tenant/snapshot label is not a semantic identity.
- The hosted `program_identity` hashes numeric ASP text, omitting labels, query, and scope. `request_identity` covers the validated request. Neither alone authenticates the source evidence or proves the intended domain-to-program encoding.

The README and DEMOS have earlier status paragraphs followed by newer hosting receipts; I use them for the semantic/trust contract, not as a fresh qualification of a deployed service. I did not launch clingo or the service for this study.

### The theorem and its quantifiers — PROPOSED

For an explicitly finite normal program `P`, let `SM(P)` be its stable models and `CheckModel(P,M)` a proved Boolean checker. The useful first theorem is:

```text
CheckModel(P,M) = true ↔ M ∈ SM(P).
```

The implementation proof must cover well-formed atom indices, constraints, duplicates, and termination of closure. Search remains untrusted. This yields a deliberately asymmetric certificate vocabulary:

| Claim | Sufficient independently checkable evidence |
|---|---|
| Consistent | One stable model |
| Credulous `q` | One stable model containing `q` |
| Not skeptical `q` | One stable model omitting `q` |
| Skeptical `q`, with Oracle7’s nonvacuous convention | A stable model of `P`, plus proof there is no stable model of `P ∪ { :- q. }` |
| Not credulous `q` in a consistent program | A stable model of `P`, plus proof there is no stable model of `P ∪ { :- not q. }` |
| Inconsistent | A checked inconsistency proof for `P` |
| Complete enumeration | All listed models checked, plus independently checked coverage of all candidates or an equivalent proof that no unlisted model exists |

The first probe constraint keeps only models omitting `q`; the second keeps only models containing it. Constraints filter models without supplying new support. The base stable model prevents an inconsistent program from granting universal permission by vacuity.

**READ / INFERRED.** Lifschitz [15] explains why completion alone is inadequate in the presence of unsupported cycles. Elkan [16] connects nonmonotonic TMS behavior to stable-model reasoning. Alviano et al.’s ASP-DRUPE [17] supplies a concrete proof-format direction for inconsistency, with a soundness/completeness theorem and a wasp implementation for normal programs. It is not evidence that Oracle7’s current clingo path emits those proofs. A SAT route needs a certified stable-model encoding—completion plus the required loop/unfounded-set treatment, or another proved translation—and a checked UNSAT proof. A SAT certificate for the wrong encoding certifies the wrong question.

**PROPOSED.** There are three honest deployment choices:

1. **Witness-only kernel support.** Accept checked stable models for existential claims and counterexamples. This has the smallest trust boundary and is immediately useful for proposing alternatives.
2. **Certified universal support.** Add exhaustive checker-controlled enumeration for deliberately tiny atom universes, or proof-producing countermodel exclusion. The atom cap bounds the cost of the former, not the semantics of an arbitrary larger problem.
3. **Named attestation.** A delegated principal signs a solver-dependent assessment. Every node verifies the same statement, signer, scope, and current support. The theorem concludes that an authorized, still-live assessment was relied on; it does not conclude mathematical skepticism without that trust premise.

An attestation must be immutable data at admission. A timeout from independently re-running remote solver search cannot become a node-local choice about whether the same write is valid. Resource grades for deterministic certificate checking belong to the protocol, like the meaning/procedure split in METATHEORY. Search budgets belong to the proposing assistant.

### “Inside a law” must preserve the effect boundary — PROPOSED

A law may invoke the **pure certificate checker** on request data. It must not contact Oracle7 while deciding admission. The producer first yields a query plan, receives the response, and proposes a write or filling containing its evidence envelope. Re-execution then checks that envelope. Otherwise admission itself has an effect whose authority, failure behavior, and shared view need another admission, recreating the problem recursively.

For an immutable program, a stable-model certificate remains mathematically valid forever. Its relevance to the current World is defeasible. Keep these separate:

```text
HistoricalTruth: CheckModel(P@H, M) = true
CurrentUse:      policy H is current, evidence E is current,
                 coverage C is authorized, assessment not withdrawn
```

`HistoricalTruth` need not be recomputed after an unrelated cell update. `CurrentUse` is checked at selection and again at dispatch through cited supports. A support can be represented by a cell whose pinned value commits to the entire evidence envelope, fitting `World.holds_congr`; authenticated materialization links its subdependencies to that cell.

### Revision and withdrawal — READ / PROPOSED

**READ.** DEMOS’ revision layer associates facts with named evidence tokens. Withdrawing `camera/bird` leaves `keeper/bird` intact. Revisions draft and replace atomically; token IDs are not reused. Every query resubmits the active program. The exploratory builder’s `rule()`/`atom()` mutations can change a program without changing its topic/counter snapshot label. Conditional explanations list fired rules and absent defaults for one interpretation; they are not stable-model certificates and do not prove universal answers.

**PROPOSED.** Promote the revision layer as a *support producer*, with these exact additions:

- Seal policy construction or content-address **every** policy, atom-universe, evidence, and scope change. Commit to both semantic program identity and the labels/provenance used in the explanation. Use immutable evidence IDs and a revision parent; do not key support on the current demo snapshot string.
- An admitted revision names the withdrawn token and publishes a new program/evidence identity. It invalidates the old answer’s *current-use* support. Recompute or re-certify the query; preserve the old model as a historical witness.
- Track negative dependencies as well as positive ones. Adding a previously absent defeater can invalidate a conclusion even though every displayed positive support remains. Initially make the full sealed program/evidence snapshot a dependency. Optimize to smaller dependency slices only with a locality theorem covering defaults, constraints, and atom-universe changes.
- Before exposure, a changed support causes `unsupported` and may permit a new filling of an unentered hole. After exposure, preserve the in-flight call, spent token, and established obligation. A new assessment can trigger a separate compensating plan if authorized; it does not rewrite history or silently free the ticket.

**READ / INFERRED.** Doyle’s TMS [18] provides reasons and withdrawal; de Kleer’s ATMS [19] retains alternative assumption environments. They suggest a good user model: “this proposal was supported in these environments; this named observation defeated it.” They do not justify unioning mutually inconsistent stable models. Green–Karvounarakis–Tannen [20] give provenance semirings for positive query derivations; Grädel–Tannen [21] treat negation with richer provenance. Neither licenses Boolean antichain eligibility as a complete stable-model solver. The [Just report](../lean/docs/REPORT-JUST-20261031.md) already found no construction advantage from replacing the slot with a single polynomial algebra. Keep provenance for explanation, ordered refusals as ordered data, and stable-model checking as its own semantic operation.

### The receipt, and what refusal names — PROPOSED

A usable evidence envelope contains:

```text
law/slot/ancestor identity; selected candidate and body hash;
program, atom-label mapping, full request and evidence identities;
tenant, World view, coverage authority, query and polarity;
certificate kind and checker version; witness or proof bytes/hash;
conditional explanation with source and default IDs;
current-use support names; decision authority and revision;
trust mode: checked witness | checked universal proof | named attestation.
```

The stranger can distinguish “provider2 occurs in one checked alternative,” “every stable model of this finite program is safe, with model coverage proved,” and “the authorized analyst currently attests safety.” Model coverage does not prove coverage of the external world. A model is not permission and does not choose the slot. The user’s existing policy-independent `SelectionSound`, current admission, and commitment-conservation contracts remain in force.

Refusals should say `model M: atom permit unsupported in reduct at program H`, `query safe: universal claim lacks countermodel-exclusion certificate`, `assessment E7 withdrawn by revision E8: scanner/compromise`, `scope tenant mismatch`, or `checker budget uncovered`. For inconsistency, name the checked conflict proof or explicitly say that only a solver attestation is available. A minimal unsatisfiable core or a minimal repair requires its own verification/optimization claim; do not call an arbitrary explanation minimal.

### Where this is wrong — INFERRED

ASP is the wrong authority for unobserved public facts, physical truth, or an unbounded liveness theorem without an encoding. A credulous “safe” model is the wrong guard when another stable model makes the same action unsafe. Skepticism over a badly translated, incomplete, or biased model is still a badly founded conclusion. Revocable assessments are useful precisely because those premises can be wrong; naming that trust is stronger engineering than hiding it in a `true` field.

## 6. Hybrid intelligence: model, propose, discriminate, commit

**PROPOSED.** The compelling hybrid system is an assistant that can keep several interpretations alive and design an action that is justified under the right quantifiers. Oracle7 provides exact combinatorial reasoning about an explicit finite model. Humans and language models supply observations, hypotheses, candidate encodings, goals, and explanations. The kernel checks the admitted claim about that model and enforces who can rely on it. None of these roles has to impersonate the others.

A useful workflow is:

1. A person or assistant proposes a finite program and a materialization of observations, with named sources. Unknown external approval is represented as unknown evidence, not inferred from default absence.
2. Oracle7 finds mutually incompatible but individually checked alternatives. The UI shows them as alternatives, not a single blended world.
3. A planner proposes a plan and its mode of robustness. The chooser approves/selects through the slot’s policy and authority rules; the solver’s arbitrary first model has no special authority.
4. When alternatives disagree about safety, the assistant can propose an information-gathering operation with a typed reply and explicit cost/authority. Its continuation branches on the new evidence; revision rebuilds the answer’s supports.
5. The runner admits the selected action at the current view, commits its resource use, and retains the historical evidence. Subsequent corrections can block future exposures and initiate repair without pretending the past did not occur.

### Quantifier discipline — INFERRED / PROPOSED

These are different contracts:

```text
∃ M ∈ SM(P), ∃ run: Safe(run)                   a possible favorable story
∃ plan, ∀ M ∈ SM(P), ∀ allowed replies: Safe    a robust fixed plan
∃ causal policy, ∀ M, ∀ replies: Safe          an adaptive robust plan
∀ M, ∃ plan: Safe                              a plan if the world were known
```

The last does not give the second or third when the world is hidden. Similarly, `∀ reply ∃ filling` does not imply a single filling chosen before the reply. Nano’s Coin example already puts this distinction in the hole-naming discipline. An ASP planner with time-indexed action atoms must encode nonanticipation; otherwise it can select a “plan” using facts learned only later.

A skeptical formula can serve as a small epistemic modality: `K_E φ` means `φ` holds in every model compatible with evidence E, provided there is at least one model. It means **knowledge relative to the declared model class and observation relation**, not omniscient truth. Hyperlogic supplies a richer language for indistinguishable histories [12,14]. A language model’s confidence score is neither a probability measure over stable models nor a certificate of `K_E φ`.

**PROPOSED.** A later probabilistic extension could attach an independently specified measure over environments and an observation/likelihood model, then certify bounds on expected cost or failure probability. Stable models themselves have no canonical probabilities; counting returned witnesses is especially invalid when query mode does not enumerate models. “If we intervened with action A” additionally requires a causal transition model. Logical consistency of `A ∧ outcome` alone is not a causal counterfactual. I would not add probability or causal syntax to the first implementation: the four-way distinction among feasibility, robustness, permission, and choice is already substantial new capability.

**INFERRED.** This permits a productive division of labor: creative agents propose many explanations; exact search exposes disagreement; a small checker establishes what follows; a living support ledger makes correction normal; an irreversible boundary records what was actually done. The opportunity is not a wiser Boolean gate. It is a system that can say what it thinks might happen, what survives every declared alternative, and exactly which new observation would change its recommendation.

### A concrete meeting of the four designs — PROPOSED

Suppose a sealed dispatch model has two alternatives: in `M₁`, provider1 can honor the booking; in `M₂`, provider2 can. Each model supports exactly one feasible provider. A query can certify that either provider is *credulously* feasible and that *some* provider is feasible in every model. Those facts do not certify that one provider is feasible in every model. Choosing the first returned model would silently change `∀ M ∃ provider` into `∃ provider ∀ M`.

Instead the assistant offers `measureCapacity; chooseFromReply; commit`. The plan contract permits the measurement and bounds commitment to one ticket. The model of the measurement must say which replies are possible in each world; if replies faithfully distinguish `M₁` and `M₂`, a causal continuation can choose the feasible provider in both. If the sensor can answer `unknown`, the continuation must include a safe wait/refusal branch. If it can lie arbitrarily, the robust-success theorem disappears even though prefix safety remains. The query has helped discover an experiment, not magically supplied its reliability premise.

The shared-World contract prevents two assistants from spending the ticket while their measurements overlap. The hyperlaw can require that the public receipt reveal the selected provider but not an unrelated private note; its observation map explicitly treats the provider choice as permitted disclosure. A revoked sensor calibration token withdraws the measurement's current-use support before commitment. If commitment is already in flight, the correction cannot replace it with the other provider. The receipt now explains, in one place, the alternative models, the measurement assumption, the selected branch, the global ticket commit, and the later correction.

This suggests a useful additional surface, `law contingentSuccess under measurementContract`, with a proof of a causal strategy rather than a chosen favorable trace. It is beyond the first envelope checker, but it gives the research a destination: executable, inspectable *conditional commitments* whose informational and resource assumptions remain named.

## 7. Solver support without moving search into consensus

**PROPOSED.** Reuse the meaning/procedure/budget separation already demanded by METATHEORY. A total bounded checker returns a verdict plus attributable coverage/resource status. A semantic theorem is fuel-free. The producer can try elaboration, SMT, ASP, automata, a human proof, or an LLM-generated invariant; the receiver checks a fixed artifact.

| Obligation | Producer-side tool | Receiver checks | Refusal must distinguish |
|---|---|---|---|
| Finite plan envelope | Structural elaboration / tree traversal | Derivation covering all declared branches | Violating branch vs unsupported syntax |
| Arithmetic/state invariant | SMT or abstract interpretation | Reconstructible proof, checked invariant implications, or reflected decision procedure | Counterexample vs solver unknown |
| Shared-World exclusion | Rely–guarantee proof, finite exploration | Component contracts, shared-step invariant, simulation | Bad joint step vs absent host refinement |
| Session fidelity | Projection and endpoint checker | Coherence, endpoint compliance, resource refinements | Protocol mismatch vs external nonresponse |
| Fixed-k safety hyperlaw | Product model checking / relational invariant synthesis | Product invariant and observation-preserving abstraction | Concrete trace tuple vs spurious abstraction witness |
| ASP possibility | Oracle7/clingo | GL reduct model check | Unstable witness vs no witness found yet |
| ASP necessity | Countermodel search + proof-producing backend | Base model and inconsistency proof, or exhaustive finite coverage | Refuted vs unproved vs inconsistent scope |
| Named assessment | Human/agent plus any solver | Signature, delegation, immutable statement, live revision support | Withdrawn authority vs mathematical refutation |

**READ / INFERRED.** Verus [22] is instructive about the *surface*: executable code, unrestricted specifications, and linear ghost proof state need different modes. Its reported architecture sends verification conditions to Z3 and trusts aspects of the Rust checker; it is not itself the small per-node certificate replay scheme proposed here. Copy the useful separation of modes, not an unexamined trust claim. A proof-carrying authorization discipline, exemplified by LPCFS [10] and the access-control calculus [23], makes the speaker, delegation, and resource consumption explicit. In particular, `analyst says φ`, `φ`, and `analyst may authorize action` are three different propositions.

**PROPOSED.** Maintain a small registry of judgment domains and certificate formats. Each registration has a versioned semantics, a deterministic checker, a checker-soundness theorem, a cost/coverage contract, and a receipt schema. This can be a library pattern before it becomes language machinery. It avoids both a single monolithic solver and an unconstrained “arbitrary plugin says yes” escape hatch. Existing state laws remain one domain. A kernel need not understand the search method that produced a proof.

**INFERRED.** Search failure must not masquerade as “nothing admissible.” A bounded Oracle enumeration, a failed SMT search, or a checker depth limit establishes only the corresponding bounded/unfinished outcome. Conversely, a valid certificate need not be rejected because the producer’s search used heuristics or a language model. Soundness depends on the checked artifact and its linkage to the actual program, not on the ingenuity of its producer.

## 8. Which design is strongest; which should be built first?

**PROPOSED.** There is no total ranking by usefulness. Their semantic targets are different:

| Design | Strongest new capability | Smallest credible entry point | Principal cost |
|---|---|---|---|
| A: plan contracts | State what every continuation may establish | Surface for `HasProt`/`Fills`, plus one finite prefix monitor | Representation and coverage of all replies |
| B: composition | State what all participants can jointly do | Shared ticket commit and projection theorem | Actual authority/atomicity and host refinement |
| C: hyperlaws | Compare possible executions and observer knowledge | Two-run universal safety with a product invariant | Trace-set semantics, alignment, policy/refinement sensitivity |
| D: oracle evidence | Use defeasible alternatives without trusting search | Stable-model witness support with full snapshot dependency | Coverage, encoding correctness, negative dependencies |

**PROPOSED.** **C is strongest expressively** when its trace universe includes the joint system: hyperproperties include ordinary trace properties and more. That does not mean the proposed finite checker is strongest, or that a set of traces captures branching/causal knowledge without additional structure. **B is the strongest immediate semantic improvement**: it makes an actual multi-runner promise from enforceable shared steps. **D is the most distinctive user capability**: evidence-backed alternative plans and named correction. **A is the simplest surface extension** because the core already has most of its judgment.

Build in this order:

1. **B’s one-ticket composition experiment**, with A’s existing envelope judgment as a client where useful. Settle exactly what the World commit boundary must promise and how existing `Legal` projections are recovered.
2. **A’s envelope surface and certified installation bridge.** Carry the law name and checked plan identity through the emitted-plan adapter and dispatch receipt. Include in-flight obligations and honest uncovered results. This should compose with the active LawFinish/SlotRun work, not duplicate it.
3. **D’s witness-only support.** Prove the finite normal-program model checker and bind evidence identities/revisions into `DecisionsHeld`. Allow named solver assessments only under an explicit attestation policy. Add skeptical certificates when there is a real producer/checker pair.
4. **C’s two-run safety fragment**, starting with public receipt noninterference—including refusal disclosure. It exercises every layer’s observation discipline and shows whether “laws about alternatives” are more than decorative specifications.

A route that starts with C can make a beautiful verifier for a model whose commits still race. A route that starts with D can make an impressive assistant whose authorization depends on an unproved universal answer. The ordering above lets the more ambitious capabilities inherit a concrete execution foundation.

## 9. One Lean experiment, one day, that could refute the recommendation

**PROPOSED.** Run this in an isolated experiment after the active lanes settle; it is not performed or landed by this study. Use the project’s designated build host/resource limits and warm artifacts. Import the existing runner, rather than reproducing a toy `Legal` predicate.

**Question:** Can two real runner instances be lifted into a shared atomic ticket host so that the global theorem both recovers their existing `Legal` logs and proves exclusion, with the atomicity premise doing observable work?

**Morning: obtain the counterexample.** Instantiate two identical single-call `Open` objects, distinct runner IDs, one semantic ticket, and a constant view with the ticket live. Each dispatches a grant to its own member. Prove each local log `Legal` using `reachable_legal`. Prove their naive combined exposure history has two grants. No concurrency machinery is needed to expose the gap: two sequential calls with independent spent masks suffice.

**Afternoon: add one shared transition wrapper.** The global configuration contains the shared spent set, committed grants, and the two existing runner configurations. Its dispatch arm:

1. brings the relevant local host view into the authoritative shared view;
2. rechecks operation and decision supports and global token availability;
3. atomically records consumption, the grant, and the runner’s in-flight event;
4. only then exposes the operation.

Project each global commit to the local runner’s own event plus appropriate world-update events; other participants observe world updates. A successful own dispatch may project to dispatch followed by the shared-world update. Prove that this expansion preserves the simulation relation and satisfies the instantiated `host.allowed`. Do not assume a joint `Legal` predicate containing the desired conclusion.

Targets:

```text
local_legal_does_not_imply_global_once
joint_reachable_projects_legal
joint_reachable_ticket_exclusive
loser_refused_names_winner_and_epoch
```

Quantify the safety result over arbitrary finite accepted event sequences, including world updates that claim the ticket is live again, a lost reply, and abandonment. The raw world may revive its live flag; it may not erase the wrapper’s durable shared spent set. Show both orderings: Alice can win with Bob refused, and Bob can win with Alice refused. This avoids proving exclusion by refusing all grants.

**Mutation teeth.** Replace the shared mask with each runner’s local mask: both grants must become possible and exclusion fail. Make abandonment erase shared spending: the lost-reply scenario must break exclusion. Omit propagation of another runner’s world update: the projection/authority coupling should fail. The ordinary `Legal` theorem need not fail on the first mutation—that is the point of the experiment.

**Pass criterion.** The proof consumes existing runner lemmas, exposes a short commit/simulation interface, and names the second grant’s refusal. It establishes a semantic theorem over the existing runner plus an abstract shared host; a later host implementation still owes durable-commit and network refinement.

**Failure criterion.** If the only proof assumes global once-spending, if the wrapper replaces rather than instantiates the runner, or if projections cannot be made `Legal` without falsifying their dispatch views, the proposed composition interface is not yet real. Record which state or event attribution is missing. If the wrapper is simple but the host’s actual commit boundary cannot implement it, move the next work to that boundary. Do not bury the gap in a universal `World` axiom or declare success from a two-element owner datatype alone.

**INFERRED.** This experiment has more decision value than a day spent proving a fresh generic theorem `I(initial) ∧ preserves(I) ⇒ always I`. That induction is unsurprising. The difficult question is whether the local runner’s authoritative view, global consumption, and exposed effect can be connected without assuming the result.

## 10. Small computations performed for this study

**RAN.** I downloaded nine primary-source PDFs found through Kagi and extracted `.txt` siblings in `~/paperbin`: the three hyperproperty/HyperLTL papers plus Finkbeiner’s survey, Jones, Kozen, ASP-DRUPE, Verus, and Aneris. Initial Python requests failed because the default interpreter lacked a CA bundle and `requests`; standard-library HTTPS with `/etc/ssl/cert.pem` succeeded, without disabling certificate validation. No paywall access was needed. No full build, Lean check, clingo run, or hosted Oracle7 qualification was performed.

**RAN.** With bytecode writes disabled, I loaded the existing pure Python `stable` checker from `o7vn/tools/usage/hosted_reasoning.py` and compared it against an independent subset-minimal-model check of each reduct. Six three-atom fixtures × eight interpretations = **48 agreeing checks**:

| Program, atom IDs 0/1/2 | Stable models |
|---|---|
| `0 :- not 1; 1 :- not 0` | `{0}`, `{1}` |
| `0 :- 1; 1 :- 0` | `{}` |
| `0; 2 :- 0, not 1` | `{0,2}` |
| previous program plus fact `1` | `{0,1}` |
| `2 :- 0, not 1` with no supporting fact | `{}` |
| fact `0` plus constraint `:- 0` | no stable model |

The first fixture demonstrates why a valid positive witness is insufficient for skepticism and why unioning alternatives is invalid. The cycle fixture rejects self-support. The revision fixtures distinguish withdrawal of a conclusion from inconsistency. This is a small check of the existing client function and the examples, **not** a proof or a test run of the Rust provider.

**RAN.** An abstract ticket simulation admitted `[Alice, Bob]` under two independent local spent masks at the same live view. A shared atomic spent bit admitted at most one grant across all **121** sequences of length 0–4 over `{acquire Alice, acquire Bob, revive world flag}`. This establishes only the tiny model, not Objective Bend’s composition theorem.

**RAN.** Exhaustive Boolean enumeration confirmed `∀ reply ∃ constant answer` but refuted `∃ constant answer ∀ reply`. A four-trace output set `{(h,o) | h,o∈{0,1}}` has equal possible outputs for both secrets; its subset `{(0,0),(1,1)}` does not. These are finite counterexamples to quantifier interchange and unrestricted hyperproperty preservation under trace deletion.

**PROPOSED.** The following compact reproducer captures the semantic probes; it uses no service or subprocess:

```python
import importlib.util
from itertools import product

spec = importlib.util.spec_from_file_location(
    'o7_client', '/Users/ember/dev/o7vn/tools/usage/hosted_reasoning.py')
client = importlib.util.module_from_spec(spec)
spec.loader.exec_module(client)  # run with PYTHONDONTWRITEBYTECODE=1

def subsets(n):
    return [{i for i in range(n) if m >> i & 1} for m in range(1 << n)]

def rule(h, positive=(), negative=()):
    return dict(head=h, positive=list(positive), negative=list(negative))

def independent(rules, candidate):
    reduct = [r for r in rules if not set(r['negative']) & candidate]
    def model(s):
        return all(not set(r['positive']) <= s or
                   (r['head'] is not None and r['head'] in s) for r in reduct)
    return model(candidate) and not any(
        s < candidate and model(s) for s in subsets(3))

programs = [
    [rule(0, negative=[1]), rule(1, negative=[0])],
    [rule(0, [1]), rule(1, [0])],
    [rule(0), rule(2, [0], [1])],
    [rule(0), rule(1), rule(2, [0], [1])],
    [rule(2, [0], [1])],
    [rule(0), rule(None, [0])],
]
for rules in programs:
    args = dict(atoms=['a', 'b', 'q'], rules=rules)
    for m in subsets(3):
        assert client.stable(args, m) == independent(rules, m)
    print([sorted(m) for m in subsets(3) if client.stable(args, m)])

local = [False, False]
grants = []
for i in (0, 1):
    if not local[i]:
        local[i] = True
        grants.append(i)
assert grants == [0, 1]

count = 0
for n in range(5):
    for events in product(('A', 'B', 'revive'), repeat=n):
        spent, live, grants = False, True, []
        for e in events:
            if e == 'revive':
                live = True
            elif live and not spent:
                spent = True
                grants.append(e)
        assert len(grants) <= 1
        count += 1
assert count == 121
assert all(any(c == b for c in (0, 1)) for b in (0, 1))
assert not any(all(c == b for b in (0, 1)) for c in (0, 1))
full = {(h, o) for h in (0, 1) for o in (0, 1)}
refined = {(0, 0), (1, 1)}
def same_possible(ts):
    return {o for h, o in ts if h == 0} == {o for h, o in ts if h == 1}
assert refined <= full and same_possible(full) and not same_possible(refined)
```

## 11. Decisions this study would put in front of Ember and Claude

**PROPOSED.** Adopt the four judgment domains as a research architecture; start with the shared-World experiment. Preserve the existing state-law type rather than adding a continuation argument to every law immediately. Put plan contracts in the protocol/installation adapter, composition certificates at the World boundary, and hypercontracts over a precisely named admitted-trace semantics. Let the surfaces share names, provenance, receipts, and inheritance infrastructure without pretending their quantifiers are interchangeable.

**PROPOSED.** Use Oracle7 first to certify *possible alternatives*. Require independent universal certificates for theorem-level skeptical premises. Where the point is to trust an analyst or a service, make that a named attestation with explicit delegation and withdrawal. A trustworthy system should be able to say both “this follows” and “this is the judgment we currently authorize,” without conflating them.

**INFERRED.** The long-term design can be both more ambitious and simpler than four separate feature stacks: one evidence lifecycle, several small semantic checkers, one execution commitment boundary. A plan is inspectable before it runs; its justification remains inspectable after it runs; revision changes what may happen next while preserving what happened. That is a plausible language of laws about effects, rather than an extra assertion syntax around ordinary effect execution.

## 12. Reading map

**READ.** The following are sources inspected for the specific claims above, not claims that every page or all cited literature was surveyed. Downloaded items have PDF and text siblings in `/Users/ember/paperbin`; existing local texts were read without altering their files. Repository reports were treated as reports, with definition checks where noted.

1. **Xia et al., “Interaction Trees: Representing Recursive and Impure Programs in Coq,” POPL 2020.** Introduction and representation/equivalence discussion. [Paper](https://arxiv.org/abs/1906.00046); local `xia2020-interaction-trees.txt`. Supplies the tree/handler distinction and coinductive divergence boundary.
2. **Kozen, “Kleene Algebra with Tests.”** Introduction and PDL/relational semantics. [Author PDF](https://www.cs.cornell.edu/~kozen/Papers/kat.pdf); downloaded as `kozen1997-kleene-algebra-with-tests.{pdf,txt}` (the author copy has later publication boilerplate). Supplies the algebraic partial-correctness route, not a liveness theorem.
3. **Toninho, Caires, Pfenning, “Higher-Order Processes, Functions, and Sessions: A Monadic Integration,” ESOP 2013.** §§1–2 and Theorems 5.1–5.2. Local [text](/Users/ember/paperbin/toninho2013-higher-order-processes-monadic.txt). First-class open computations and the precise progress assumption.
4. **Wood and Atkey, “A Linear Algebra Approach to Linear Metatheory,” EPTCS 353.** Introduction and usage/substitution account. Local [text](/Users/ember/paperbin/wood-atkey2022-linear-algebra-approach-linear-metatheory.txt). Usage algebra, distinct from Boolean support provenance.
5. **Jones, “Tentative Steps Toward a Development Method for Interfering Programs,” TOPLAS 1983.** §§3.1–3.2, especially compatibility and dynamic-invariant obligations. [Paper PDF](https://ilyasergey.net/CS6213/_static/05-owicki/rg.pdf); downloaded `jones1983-tentative-steps-interfering-programs.{pdf,txt}`.
6. **Abadi and Lamport, “Conjoining Specifications,” TOPLAS 1995**, §§2.2, 3, 5; and **“The Existence of Refinement Mappings,” 1991**, abstract/introduction on behavior refinement and auxiliary variables. Local [composition text](/Users/ember/paperbin/abadi-lamport-conjoining-specifications-toplas1995.txt), [refinement text](/Users/ember/paperbin/abadi-lamport1991-existence-of-refinement-mappings.txt). The former supplies TLA composition and the circular-liveness counterexample; the latter motivates an explicit projection/refinement rather than equality of internal states.
7. **Honda, Yoshida, Carbone, “Multiparty Asynchronous Session Types,” POPL 2008.** §5, particularly Definitions 5.7–5.9 and Theorem 5.12. Local [text](/Users/ember/paperbin/honda-yoshida-carbone2008-multiparty-asynchronous-session-types.txt). Coherence, fidelity, and progress with restrictions. This study does not transplant the theorem to crash failures.
8. **Miller, “Robust Composition,” dissertation, 2006.** Introduction and authority/reference-graph account. Local [text](/Users/ember/paperbin/miller2006-robust-composition-thesis.txt). Composition among potentially malicious components and partial-failure boundaries.
9. **Krogh-Jespersen et al., “Aneris: A Mechanised Logic for Modular Reasoning about Distributed Systems,” ESOP 2020.** Introduction and modular/socket-protocol account. [Project PDF](https://iris-project.org/pdfs/2020-esop-aneris-final.pdf); downloaded `krogh-jespersen2020-aneris.{pdf,txt}`. A later route to node-local host/network refinement.
10. **Morgenstern, Garg, Pfenning, “A Proof-Carrying File System with Revocable and Use-Once Certificates,” 2011.** Introduction and implementation/trust architecture. Local [text](/Users/ember/paperbin/morgenstern2011-lpcfs.txt). Particularly relevant to atomic revocation checking and certificate consumption; LPCFS offlines proof verification through a trusted verifier issuing capabilities, so it is not identical to every node replaying a proof.
11. **Clarkson and Schneider, “Hyperproperties,” JCS 2010.** §§1–3, subset closure, k-safety, and self-composition Theorem 2. [Author PDF](https://www.cs.cornell.edu/fbs/publications/Hyperproperties.pdf); downloaded `clarkson-schneider2010-hyperproperties.{pdf,txt}`.
12. **Clarkson et al., “Temporal Logics for Hyperproperties,” POST 2014.** Introduction and quantifier/observation examples. [Paper](https://arxiv.org/abs/1401.4492); downloaded `clarkson2014-temporal-logics-hyperproperties.{pdf,txt}`.
13. **Finkbeiner, Rabe, Sánchez, “Algorithms for Model Checking HyperLTL and HyperCTL*,” CAV 2015.** Introduction and alternation-free construction/complexity discussion. [Author PDF](https://software.imdea.org/~cesar/papers/finkbeiner15algorithms.pdf); downloaded `finkbeiner-rabe-sanchez2015-model-checking-hyperltl.{pdf,txt}`.
14. **Finkbeiner, “Model Checking Algorithms for Hyperproperties,” 2021.** Abstract and overview of self-composition, quantification, and knowledge. [Paper](https://arxiv.org/abs/2107.11841); downloaded `finkbeiner2021-model-checking-algorithms-hyperproperties.{pdf,txt}`. The first proposed checker deliberately uses less than the surveyed logics.
15. **Lifschitz, “Thirteen Definitions of a Stable Model,” 2008.** Introduction and completion/reduct account. [Author PDF](https://www.cs.utexas.edu/~vl/papers/thirteen.pdf); local `lifschitz2008-thirteen-definitions-stable-model.txt`.
16. **Elkan, “A Rational Reconstruction of Nonmonotonic Truth Maintenance Systems,” AI 1990.** Introduction and grounding characterization. Local [text](/Users/ember/paperbin/elkan1990-rational-reconstruction-nonmonotonic-tms.txt).
17. **Alviano et al., “Inconsistency Proofs for ASP: The ASP-DRUPE Format,” TPLP 2019.** Abstract, §3 Theorem 1, §4 implementation. [Paper](https://arxiv.org/abs/1907.10389); downloaded `alviano2019-asp-drupe-inconsistency-proofs.{pdf,txt}`. A proof-format lead, not a qualified Oracle7 capability.
18. **Doyle, “A Truth Maintenance System,” AI 1979.** Abstract and reason-maintenance architecture. Local [text](/Users/ember/paperbin/doyle1979-truth-maintenance-system.txt).
19. **de Kleer, “An Assumption-based TMS,” AI 1986.** §§1–1.1. Local [text](/Users/ember/paperbin/dekleer1986-assumption-based-tms.txt). Explicit alternative assumption environments; absence of belief distinguished from negative belief.
20. **Green, Karvounarakis, Tannen, “Provenance Semirings,” PODS 2007.** Abstract/introduction and scope of positive query provenance. Local [text](/Users/ember/paperbin/green-karvounarakis-tannen-provenance-semirings-pods2007.txt).
21. **Grädel and Tannen, “Semiring Provenance for First-Order Model Checking,” 2017/2018 version.** Abstract/introduction on dual indeterminates and negation. [Paper](https://arxiv.org/abs/1712.01980); local `gradel-tannen-semiring-provenance-first-order-model-checking-1712.01980.txt`.
22. **Lattuada et al., “Verus: Verifying Rust Programs using Linear Ghost Types,” extended version, 2023.** Introduction, modes, VC/Z3 and trusted-borrow-checker discussion. [Paper](https://arxiv.org/abs/2303.05491); downloaded `lattuada2023-verus-linear-ghost-types.{pdf,txt}`. The ghost-state/specification surface is the relevant precedent, not a claim of proof replay in Objective Bend.
23. **Abadi, Burrows, Lampson, Plotkin, “A Calculus for Access Control in Distributed Systems,” TOPLAS 1993.** Introduction on authentication, authorization, principals, and delegation. Local [text](/Users/ember/paperbin/abadi-burrows-lampson-plotkin1993-calculus-access-control-distributed-systems.txt).

**READ / INFERRED — one additional important contrast.** de Alfaro and Henzinger, **“Interface Automata,” 2001**, abstract and introduction, local [text](/Users/ember/paperbin/dealfaro2001-interface-automata.txt), use optimistic compatibility—some environment can make components work—and alternating refinement—weakening input assumptions, strengthening output guarantees. This is an excellent source for a negotiation UI that finds a compatible environment. It is not the same as robust safety against every admitted environment. Keep the chosen quantifier in the contract and receipt.

**PROPOSED — scope choice.** Cardelli’s mobile-computation work was a search lead, not a premise of this study. The useful “laws as types” precedents here are the contextual monad, session contracts, ghost specifications, and proof-carrying authorization. A general mobile-code calculus would add less to the present design than making these four judgment domains precise.
