# What survives a changed world: stored selection policies

Astra (GPT-6), 2026-10-31. Analysis requested after Ember accepted incumbent-first, to make the choice deliberate. This report changes no Lean source.

**Evidence tags.** **READ** reports inspected source or literature, not a build performed here. **RAN** reports an executed check in this session. **INFERRED** is an argument from those materials, with its premises stated. **PROPOSED** is a design recommendation or an unimplemented contract. Tags on a table's introduction apply to its rows. Code under PROPOSED is a contract sketch, not a claim that it has been compiled.

## 1. Recommendation

**PROPOSED.** Keep incumbent-first as the default **automatic policy for an undispatched stored selection**. Let the authorized chooser explicitly supersede a still-usable choice. Offer first-usable for canonical derived results, a chooser-required policy for editorial decisions, and scored policies with explicit hysteresis where switching has a measured cost. Freeze executed protocol choices independently of all of these. Preserve the old choice, reasons, and supersession in the record even when its current applicability ends.

**INFERRED.** Three different things are being called “sticks”: a candidate keeps its place as the current selection; a historical decision remains attributable and inspectable; an already dispatched operation cannot be undone by choosing differently. Only the first is a selection preference. The second is a record obligation. The third is an execution constraint. Treating all three as incumbent retention would protect some preferences unnecessarily and leave some actual commitments insufficiently protected.

**PROPOSED.** The two policy-independent invariant families are **current admission** and **conservation of commitments**. At the slot boundary, success certifies a currently usable, authorized candidate. At the runner boundary, each dispatched operation is admitted at its own dispatch view; history, in-flight identity, and durable spending constrain all future transitions. Section 7 states the predicates precisely. Two slogans such as “usable” and “don't churn” are not sufficient: pairing and durable non-reuse are indispensable parts of the execution theorem.

**READ.** The runner has already landed: `b863090` and its report `d45d712`, on `origin/dev` at the inspected head `7a6061c`. An important correction to the motivating premise: it imports `Slot.Integrity`, but its general `refines`/`reachable_legal` theorem does **not** assume `Integrity.transition`. Its `resolveEvent` helper currently uses **first-usable**, through `Slot.resolve`, and its raw replan event contains a protocol body, not a stored candidate. The existing safety theorem already tolerates either selection policy. Incumbent-first has not yet been integrated as its stored-selection mechanism.

## 2. What the existing definitions actually commit to

**READ.** The following are the relevant boundaries in the inspected tree:

| Source | Contract actually present |
|---|---|
| `lean/Obend/Slot.lean`, `Slot`, `usable` | A candidate has a fixed support list and Boolean judge. Usability is judge success AND every cited support holding. Candidate order is an argument, not a field of `Slot`. |
| Same file, `read` | Reading never reselects. A stored candidate can remain stored while rejected or blocked; a usable read shows the support evidence. Judge rejection has precedence over blocked-support display. |
| Same file, `alternatives`, `resolve` | Filter the supplied list by usability; resolution uses its head or returns every candidate paired with its dead-support list. |
| `Slot/Integrity.lean`, `Slot.select` | The candidate-valued first-usable operation. This definition is in `Integrity.lean`, not `Slot.lean`. |
| Same file, `Advance`, `Integrity.transition` | Keep every usable incumbent; every success is usable and either the incumbent or the first usable candidate; an error implies both incumbent failure and failure of every ordered candidate, with named failures for the ordered candidates. |
| Same file, `Slot.advance` | Implements precisely incumbent-first with first-usable fallback. |
| Same file, `select_prefix`, `select_reuse` | First-usable success supplies a rejected prefix; continued eligibility plus continued rejection of that prefix suffices for exact reuse. |
| Same file, `not_transition_churn`, `not_transition_sticky` | Recomputing first-usable violates incumbent retention; keeping an unusable incumbent violates success soundness. These are different failures. |
| `Slot/Repair.lean`, `repair_sound` | A judge-passing candidate becomes usable after repairs covering its dead supports **if each repair preserves all already true requirements of that candidate**. |
| `Run/Spec.lean`, `Legal` | World-step legality, dispatch admission, unique spending, dispatch/reply pairing, no replan of entered holes, and compatibility of accepted history with the plan in force. |
| `Run/Proofs/Invariant.lean` | Reachable configurations satisfy those log properties and the representation invariant connecting world, plan, history, spent tokens, and residual to the log. |

**INFERRED.** `Integrity.transition` is almost a complete specification of one selection algorithm, rather than a neutral interface for safe selectors. If a usable incumbent exists, clause 1 forces it. Otherwise clause 2 forces any success to be first-usable, and clause 3 prevents error whenever an ordered candidate is usable. Only error-payload details retain significant freedom. Therefore chooser-directed replacement and hysteresis cannot simply be supplied as alternative instances of this unchanged class.

**READ.** There are two easily missed limits. A stored candidate need not belong to the current `order`: `advance S holds [] (some c)` returns `c` if usable. And `transition`'s error explanation quantifies over `order`, not over the failed stored candidate. If the incumbent is outside an empty order and unusable, `Slot.advance` returns `.error []`. `Slot.read` can diagnose it separately, but that diagnosis is not included in the transition payload.

**INFERRED.** Reordering preferences must be distinguished from removing permission. Under today's API, removing `c` from `order` does not revoke a usable incumbent. An application intending an exclusion must encode it in admission/authorization, or adopt a transition policy that requires current membership. Similarly, an arbitrary supplied `some c` is not proof of a past authorized selection. A stored-choice receipt and its validation are a needed application boundary.

**READ.** `World` guarantees that a retired cell (`pin = none`) never returns along `Later`. It does not require every false fact to remain false, nor every moved version to remain different forever. The runner's negotiation world uses `some false` and `some true` for grants, permitting restoration without retirement. The Just report's example of returning to toy height 0 is an evaluation at another view, not a forward path from toy height 1. The early/chosen countermodel establishes a selection distinction without claiming such an impossible toy-world transition.

**READ.** The application evidence supports differentiated policies. Delvetalk2's `docs/METAPHYSICS.md` §7.3 asks for credited persistence and visible correction, and describes supersession without erasure. Nanodregg `decisions/lang.md` LANG-73 separates preference from judgment, retains accepted history, and explicitly says repair correctness compares candidate statuses rather than history-dependent selections. LANG-83 gives selection to an editor; its demonstrated repair includes another explicit selection. The associated protocol rule preserves the executed prefix. These are three boundaries, not three independent endorsements of automatic fallback.

## 3. The laws that cannot all be had

**INFERRED.** Fix a slot definition and an ordered candidate domain `O`; write `U_v(c)` for current usability and `s` for the optional incumbent. Initially ignore dispatch and chooser events. For a total automatic policy returning success or factual failure, useful laws are:

| Law | Precise meaning |
|---|---|
| **S — sound success** | `A(v,O,s) = ok c → U_v(c)`. Authorization/domain membership is a separate conjunct when represented. |
| **K — incumbent retention** | `s = some c ∧ U_v(c) → A(v,O,s) = ok c`. This is for automatic advance without an override event. |
| **F — canonical first-usable** | The result equals `select(v,O)`, independently of `s`. |
| **E — factual failure completeness** | Error implies every permitted candidate is unusable. For today's incumbent-first domain, also require the stored candidate unusable. |
| **P — immediate selection availability** | A usable permitted candidate implies success now. This follows from E for a total two-constructor result. It is not eventual execution or fairness. |
| **D — final-view determinacy** | Identical slot, current view and order give the same choice, regardless of earlier views or stored selection. |
| **I — decision idempotence** | Reapplying the same policy at identical inputs, with its result stored, leaves that choice unchanged. State such as time, scores and decision events counts as input. |

**INFERRED.** K and F conflict whenever `O = [a,b]`, both are usable, and `s = some b`. K demands `b`, F demands `a`. This is a two-candidate impossibility, not an implementation inconvenience. K also conflicts with D if histories can establish different usable incumbents. All of K, F and S can coincide on restricted instances, for example when at most one candidate is usable; there is no universal incompatibility between stability and deterministic replay of a **full history**.

**INFERRED.** Final-view determinacy is different from replayability. An incumbent policy is a deterministic state machine and can be replayed from its initial selection and event sequence. It cannot in general be reconstructed from the final world alone. First-usable is final-view canonical only relative to a fixed, reproducible candidate order, candidate definitions, and judge—not across arbitrary replicas receiving candidates in different orders.

**RAN.** A Python enumeration over three candidates, all 8 usability assignments, all 16 ordered subsets, and 4 possible incumbents checked 512 states. Both first-usable and incumbent-first satisfied S. Incumbent-first satisfied K and its exact factual-error condition. They disagreed in 102 states; 60 states kept an incumbent outside the current order. All 294 tested instances satisfying the prefix-reuse premise returned the same canonical choice. These are finite model checks of the stated decision rules, not new Lean proofs.

**RAN.** The path example is especially relevant: start with `a` selected and both candidates usable. Going straight to the same final view keeps `a`. Passing through a view with only `b` usable first replaces `a` with `b`; restoration of both then keeps `b`. Same final world, different current choice, entirely intentional under incumbent-first. If a product wants to return to the original favorite after recovery, incumbent-first is the wrong policy for that product.

## 4. The policies, their evidence, and their bad fits

### 4.1 Incumbent-first, with ordered automatic fallback

**READ / INFERRED.** Rule: keep `s` if usable; otherwise choose first-usable from `O`. This satisfies the present `Integrity.transition`, hence S, K, E and P over the domain consisting of the incumbent plus the order. It satisfies I with fixed inputs. It fails F and D, and has no fairness or eventual-upgrade property: an adequate incumbent can remain forever while a better candidate waits.

**INFERRED.** Replay needs the prior stored-choice identity and its legitimate establishment, the slot/judge version, and current positive evidence for the incumbent. Keeping it does not require proving any earlier candidate unusable. Fallback needs a failed-incumbent witness, the replacement's positive evidence, and the rejected prefix in `O`. Full historical replay also needs earlier decisions; a positive support monomial is not a replacement for that history.

**PROPOSED.** A factual refusal should include the incumbent's diagnosis as well as all considered alternatives. Its repair affordance is: establish a compatible set of requirements for some candidate and re-evaluate; if the incumbent stays unusable, the first usable fallback wins. Repairing a particular later candidate does not promise that this candidate will be selected. To request that result, use chooser override or prove that all preceding candidates remain unusable. A stranger should see “kept B from decision 17; B remains admissible; A now passes but this policy gives B precedence,” or “B lost grant g; selected C under fallback order version 4.”

**INFERRED.** Wrong fit: a package resolver must converge on the highest-priority supported implementation after a transient outage; incumbent-first permanently strands some installations on the fallback. It is also wrong for an editorial section if automatic replacement silently attributes a new editorial decision to an absent editor. In a public quotation, retention can preserve a stale but still formally permitted passage unless substantive correction is represented separately from the author's grant.

### 4.2 First-usable / canonical replay

**READ / INFERRED.** Rule: run `Slot.select` on every selection request. It satisfies S, F, E and P for `O`, and D and I under fixed inputs. It fails K (`not_transition_churn`). The theorem it fails is a policy theorem, not dispatch safety. With `s = some b`, `U(a)` changing from false to true switches to `a` even if nothing about `b` changes.

**READ / INFERRED.** `select_prefix` gives the selection certificate `O = pre ++ c :: post`, `U(c)`, and `∀ d ∈ pre, ¬ U(d)`. `select_reuse` proves its sufficiency at a new view. Each earlier rejection can be justified by a failed judge or one failed support; auditing a factual failure for the whole order needs a witness for every candidate. Exact dead-support lists are a richer diagnostic than the minimal exclusion witness. Negative dependencies must be revalidated, or certified against unchanged pinned data, when reusing the result.

**PROPOSED.** A refusal names every candidate's blockers. “Make C usable” promises a success if the repaired state is compatible, but promises C specifically only with the rejected-prefix condition. A stranger sees “A's support returned, so the current ordered rule again selects A,” with the previous B decision retained as history. The receipt must not imply B was false or revoked.

**INFERRED.** Wrong fit: a public anthology switches the featured author's passage whenever an earlier author's grant flickers; or a service keeps changing providers while both work, continually invalidating preparatory work. In protocols this can cause starvation before dispatch if replanning is endlessly preferred to taking a step. The execution kernel can preserve safety without supplying scheduler fairness.

### 4.3 Chooser-decides: a named party reselects

**PROPOSED.** A world change recomputes the stored choice's status. It does not choose a different candidate. An authenticated `Choose(slot, expectedRevision, candidate, viewEvidence)` event from the authorized party can select any currently admitted permitted candidate before dispatch. A failed incumbent stays visible as suspended. A usable incumbent remains current absent such an event. The chooser may also replace a usable incumbent intentionally.

**INFERRED.** This satisfies S, automatic-event K, and **decision authority**: every installed replacement has a valid chooser event. It fails unrestricted K across explicit chooser events, F, D, and unconditional P. A slot can wait for its editor despite many usable candidates. Its progress theorem is conditional: a valid choice for an owned, unentered slot, against the expected revision, selecting an admitted candidate, is accepted. An always-refuse implementation would violate that theorem. Silence by a human is not a proof of infeasibility.

**PROPOSED.** Replay needs party identity, authority/delegation evidence, candidate/body identity, the expected slot revision, the ordered event position and the admission snapshot. It does not need an invented reason that earlier candidates were unusable. Refusal distinguishes `wrongChooser`, `staleRevision`, `candidateBlocked`, and `entered`; waiting names the party and available choices. A stranger sees “editor E selected B despite A also being admissible,” or “B suspended; awaiting E; C is available.” That tells them who made the editorial act.

**INFERRED.** Wrong fit: an unattended failover service waits indefinitely for an unreachable operator although a valid replacement is ready. Delegation or a preauthorized timeout policy can solve that, but is itself a policy decision that must be recorded. A named chooser is an authority rule, not a magical liveness guarantee.

### 4.4 Priority with hysteresis

**PROPOSED.** First filter by admission. With a usable permitted incumbent `s`, compute the best challenger `b` by a deterministic score and tie-breaker. Switch only if `score(b) > score(s) + δ`; otherwise retain `s`. If the incumbent is unusable, immediately select the best admissible candidate or report factual failure. A dwell-time rule may delay elective improvement; it must not keep an inadmissible candidate active. If no safe fallback may be taken during a cooldown, return a policy wait instead.

**INFERRED.** For finite nonempty eligible sets, fixed real or integer scores and `δ ≥ 0`, this satisfies S and P, and gives a meaningful theorem: an elective switch improves score by more than `δ`; the chosen candidate is within `δ` of the current best. At a frozen world/score input it is idempotent. It fails K when an improvement crosses the margin, F for a different order, D when the margin permits either incumbent, and exact optimality when a slightly better challenger exists. Hysteresis alone proves no global bound on switches under arbitrary score oscillations. A minimum dwell interval bounds elective switch frequency only with an explicit monotone clock and exceptions for invalid incumbents.

**RAN.** For three candidates, all Boolean eligibility assignments, all scores in `0..3`, all incumbents and margin 1, 1,536 Python cases satisfied soundness, the one-unit regret bound and strict improvement on elective switches. This check used immediate replacement on ineligibility and no dwell rule.

**PROPOSED.** Replay needs scored measurements and their versions, the score function, margin, tie rule, incumbent, and any last-switch time/clock events. Retaining requires evidence that no eligible challenger crosses the threshold, not merely the incumbent's supports. A refused challenger is told the threshold it did not cross, or the cooldown boundary; factual failure still names admission blockers. A stranger sees the scores and the particular retention/switch comparison. Scores based on secret or unavailable measurements cannot support independent reproduction without an explicit attestation boundary.

**INFERRED.** Wrong fit: a safety-critical deadline demands the fastest currently admissible provider and a margin delays the needed upgrade. Encode a real deadline as a hard admission requirement; do not bury it in a soft score. Conversely, noisy scores can oscillate beyond any fixed margin and still thrash.

### 4.5 Lexicographic `(still-usable, order, recency)`

**INFERRED.** This phrase does not specify a policy until “still” is disambiguated. If the first component is ordinary current usability for **each** candidate, hard-filter first and then compare order and recency. With a strict list position, different candidates never tie on order: recency is dead code, and the rule is first-usable. It satisfies F and fails K. If order means a priority **tier**, then recency breaks ties and can change the result within a tier.

**INFERRED.** If “still-usable” means “is the incumbent AND remains usable,” this is incumbent-first, followed by an ordered/recency fallback. It satisfies K and fails F. If it means “was usable in the previous view and is usable now,” it privileges a cohort, not the incumbent, and requires the previous view. That is a third, path-dependent policy. None of these may choose an unusable candidate when every first component is false: ranking is subordinate to an explicit empty-eligible-set check.

**RAN.** In the 512-state enumeration, lexicographic current-usability/strict-order/recency with recencies `(1,2,3)` agreed with first-usable everywhere. This is also immediate from distinct order indices. It is not evidence that tiered ranking ignores recency.

**PROPOSED.** Use explicit policy names for these variants. Record tier/order version, candidate admission evidence, and the actual recency basis—publication, submission, last explicit choice, or last validation. Use a serialized event ordinal or a defined replicated ordering; do not use an observer's wall clock. For a target C, the refusal names whether admission, higher tier, or recency tie-break prevented selection and what event would change that comparison. A stranger sees “B won tier 2 by submission event 44,” rather than an unexplained “latest.”

**INFERRED.** Wrong fit: a newcomer repeatedly resubmits identical text to win newest-first ties, or mere revalidation refreshes an incumbent's timestamp and entrenches it indefinitely. A popularity/freshness choice has been smuggled in unless the timestamp's meaning and anti-gaming rules are explicit. Strict-order recency is wrong when the designer believed it would ever promote a newer revision.

### 4.6 Sticky until contradicted, then chooser

**PROPOSED.** This useful editorial hybrid retains a usable incumbent automatically, marks it suspended on failed admission, and requires the named chooser to decide what comes next. An explicit authorized correction may supersede it earlier. Interpret “contradicted” operationally as “its required evidence no longer passes”; the current Boolean API does not distinguish falsity, missing evidence and an unavailable observation. A richer epistemic status would need its own definition.

**INFERRED.** It satisfies S and automatic K, plus “no automatic replacement on support failure.” It fails P and therefore today's `Integrity.transition` even if another candidate is usable. It also fails F and D. It is distinct from the refuted `sticky`, which returns `.ok` on an unusable candidate. Keeping a historical pointer is safe; advertising that pointer as admitted is not.

**PROPOSED.** Decide whether suspension is latched. I recommend latching it for editorial reapproval: once the cited permission or evidence fails, require a fresh choice event even if the fact later returns. Then the extra theorem is `suspended ∧ no reapproval → no active selection`, and replay needs the invalidation event, not just the final valuation. An unlatched version can reactivate the same incumbent automatically when U returns; it is appropriate for temporary service outages but grants a different meaning to “then chooser.” Both must expose this choice in their policy identity.

**PROPOSED.** The receipt shows the last accepted text, the named invalidation and a conspicuous “not currently admitted” status; it identifies the editor and currently viable alternatives. What would pass is a fresh authorized choice of an admitted candidate, not simply another grant mutation when suspension is latched. Old text remains citable as historical text. No arbitrary fallback text masquerades as the editor's correction.

**INFERRED.** Wrong fit: a real-time service pauses unnecessarily on a brief network observation failure and requires a human reapproval after full recovery. Conversely, the unlatched variant is wrong where restoration of access was not intended to republish a withdrawn editorial decision.

### 4.7 Lease-limited incumbency and periodic reconsideration

**PROPOSED.** Attach an authority lease or a policy review deadline to the selected identity. Retain while usable and within the relevant term; renew through a recorded authorized event. An authority lease's expiration makes the choice inadmissible for new actions. A mere review deadline makes it due for policy reconsideration; it need not falsify its ordinary supports. These are separate concepts.

**INFERRED.** This gives a bounded authority theorem: without renewal, no new action using that lease is admitted at/after expiration. It satisfies S when expiration is actually in admission, but fails K phrased only in terms of the old support list, and fails unconditional P if renewal/selection requires a party. Periodic canonical review can satisfy F at review instants and retention between them; it does not satisfy either law at all instants.

**PROPOSED.** Replay needs grant identity, renewal authority, epoch, expiration and trusted time evidence. A refusal names “renew lease L at epoch e or select another admitted candidate,” subject to dispatch history. A stranger sees an expired authority rather than a fictitious logical contradiction in the candidate's content. Wrong fit: a published poem should not disappear merely because its author failed to renew a heartbeat. Also, expiration of a lease must never imply an already dispatched payment failed or may be repeated.

### 4.8 Minimal-change selection across several slots

**PROPOSED.** When choices interact, select a jointly feasible assignment minimizing a declared change cost relative to the previous assignment, with deterministic tie-breaking. One possible objective first minimizes the number of changed slot identities, then preference cost. This generalizes single-slot incumbency but must include cross-slot constraints explicitly.

**INFERRED.** For a finite domain with a feasible assignment, exhaustive minimization gives joint feasibility and objective optimality. It does not give per-slot K: replacing a still-usable incumbent may be necessary to repair a coupled constraint. It need not give F or D, and an incremental local algorithm needs a separate theorem that it achieves the global optimum. Conserving the largest number of choices is not the same as conserving the most consequential decisions.

**PROPOSED.** Replay needs the prior assignment, joint constraints, objective and tie rule, and either a checkable optimum certificate or the bounded search inputs. A refusal names a conflicting set and compatible repairs, with “budget exhausted” separate from “no feasible assignment.” A stranger sees the slots changed and the reason the apparently valid incumbent had to move. Wrong fit: a routine independent text slot pays global search cost; or counting unchanged slots preserves ten trivial choices at the expense of one crucial authorial commitment. This belongs above the single-slot kernel.

### 4.9 Rotation or lottery when access, rather than retention, is the objective

**PROPOSED / INFERRED.** Filter by admission, then rotate through eligible candidates at explicitly recorded decision epochs, or draw from them using recorded randomness. Both satisfy S and P over a nonempty finite domain; they deliberately fail K and final-view canonicality. For a fixed set of N continuously eligible candidates and repeated successful decision epochs, round-robin gives each a turn within N epochs. A fair independent lottery instead supplies probability-one eventual selection under infinitely many epochs, not a finite worst-case waiting bound. Neither theorem implies that the runner can revisit an entered hole.

**PROPOSED.** Replay needs the cursor and epoch sequence for rotation, or the randomness transcript and exact sampling rule for a lottery, alongside eligibility evidence. A refusal names admission blockers or the next permitted decision epoch; a lost draw is a preference outcome, not an eligibility failure. A stranger sees whose turn it was or how the draw selected the winner. Wrong fit: every page refresh replaces a jointly edited passage, or every retry draws another payment provider after a dispatch. This is suitable for allocating repeated opportunities, not for pretending an established editorial act was never made.

**INFERRED.** These alternatives expose the broader design space: feasibility, preference objective, decision trigger, chooser authority, retained state and execution phase are independent axes. There is no finite enumeration of all possible scoring rules. The useful completeness of this analysis is to identify which axis a proposed rule changes and which proof/evidence obligation that adds. “More recent,” “less change,” “fairer,” and “better score” are genuinely different objectives.

## 5. What the literature contributes—and what it does not

### 5.1 AGM minimal change and update versus revision

**READ.** Alchourrón, Gärdenfors and Makinson's 1985 paper studies contraction/revision of theories; partial-meet contraction intersects a selected nonempty family of maximal remainders and has representation results for the postulates. It does not prescribe a unique selection function. [Original paper, publisher abstract and bibliographic record](https://www.cambridge.org/core/journals/journal-of-symbolic-logic/article/abs/on-the-logic-of-theory-change-partial-meet-contraction-and-revision-functions/7ED837BAD5FB6D9A7C77906D73527F9C).

**INFERRED.** The transferable idea is to specify what must change and an explicit retention preference for the remainder. Incumbent-first minimizes the zero/one cost of changing one chosen identity among feasible choices. That elementary optimum theorem is not an AGM representation theorem: a `Cand` is not a deductively closed belief set, authorial choice is not belief, and fixed support requirements cannot be discarded merely because revision prefers to keep the candidate. “Minimal change” leaves the metric and importance ordering to us.

**PROPOSED.** An AGM-inspired multi-slot policy would use §4.8's optimization. Its receipt must include the old commitments, accepted new constraints, retained/retracted choices and selection preference. Its refusal names joint inconsistency or an unsatisfied admission condition; an executable repair requires compatible changes. It satisfies the declared minimum-change theorem, but fails independent incumbent retention and may fail global availability under computational bounds. Wrong fit: a withdrawn permit is treated as a revisable belief and silently dropped to preserve a favorite plan. A kernel authority fact is not something a preference optimizer may revise away.

**READ.** Katsuno and Mendelzon explicitly separate updating a description after its world changes from revising beliefs in light of new information. [Their chapter](https://www.cambridge.org/core/books/abs/belief-revision/on-the-difference-between-updating-a-knowledge-base-and-revising-it/8ADFFF65FA776C21E8646D6F4D2434AB).

**INFERRED.** That distinction matters here: “the grant was valid, then revoked” is a world update, not discovery that the old receipt was false. A correction can invalidate the current reading while preserving the fact that an earlier act was authorized then. Conversely, new evidence that the prior receipt itself was forged should append a challenge/correction to that historical claim. Neither case licenses rewriting the executed event out of existence.

### 5.2 Doyle: foundations and coherence

**READ.** Doyle contrasts justification-based maintenance with conservation/coherence of beliefs, then argues that the approaches are closer than the opposition suggests and that reasons can implement conservative revision. [Doyle, “Reason Maintenance and Belief Revision: Foundations vs. Coherence Theories,” 1992, author-hosted text](https://www.csc2.ncsu.edu/faculty/jdoyle2/publications/cf92.pdf); [publisher introduction](https://www.cambridge.org/core/books/abs/belief-revision/reason-maintenance-and-belief-revision-foundations-versus-coherence-theories/07B8D61C8AB756BC4CA2BCB75EAF670E). The author PDF was available through indexed excerpts; direct PDF opens timed out. I did not inspect its full proof development.

**INFERRED.** Obend's fixed support lists are a foundations-like representation; preference for keeping a justified incumbent is conservative choice on top. These fit together. The relevant theorem is **supported-current-selection**, not “every supported candidate is selected.” Coherence-style preference alone fails support soundness unless admission is separately imposed. A candidate with alternate derivations could survive loss of one justification, but today's single candidate support list is a conjunction, not a set of interchangeable proofs.

**PROPOSED.** Replay should identify which justification or renewed candidate identity now supports the choice. A refusal names the lost grounds and any admissible alternate grounds; it must not invent a new pedigree because the conclusion remains desirable. A stranger should distinguish “same conclusion, new justification” from “old justification still valid.” Wrong fit: a provenance-sensitive quotation is retained under someone else's equivalent wording or permission without acknowledging changed authorship. Conversely, treating one lost proof as loss of a mathematical conclusion is wrong when another checked proof exists. Candidate identity and justification identity need separate representation if that use case matters.

### 5.3 ATMS environment switching

**READ.** De Kleer's ATMS associates a node with a label of minimal consistent assumption environments. The label is required to be sound and complete relative to the justifications; membership of a node in a context is determined by an environment in its label being included in that context's assumptions. Nogoods exclude inconsistent environments. It represents several contexts without forcing one current belief set. [De Kleer, “An Assumption-based TMS,” 1986, §§4.3–4.5](https://www.dekleer.org/Publications/An%20Assumption-Based%20TMS.pdf).

**INFERRED.** The useful theorem to borrow is environment-relative eligibility: under a sound/complete label discipline, a candidate is supported in environment E exactly when a consistent supporting environment is included in E. This does not choose the editor's preferred candidate, choose E, or establish permission to switch a physical world. ATMS is a dependency representation on which any of the policies above can run, not a ninth total preference ordering.

**PROPOSED.** Replay needs the selected environment, justification/label version, relevant nogoods and the event authorizing the environment choice. A refusal names unmet assumptions or a nogood, then offers a consistent environment if one is actually established as available. A stranger sees “B is supported under assumptions E; the chooser moved from E₀ to E,” with both derivation histories retained. Wrong fit: changing to a hypothetical environment where a payment was never sent is used to erase the actual in-flight payment. ATMS switching supplies neither irreversible-action conservation nor consensus about shared reality. Pair it with the runner; do not use it to replace the runner.

### 5.4 Leader election and leases

**READ.** Raft's election safety is at most one elected leader **per term**, derived from majority voting and at most one vote per server per term. Heartbeats discourage new elections, and higher terms cause stale leaders to step down. The paper also reports abandoning a rank-based election design after availability corner cases. [Ongaro and Ousterhout, extended Raft paper, §5.2](https://raft.github.io/raft.pdf).

**INFERRED.** Stable leadership is a good analogy for avoiding unnecessary choice churn, but local incumbent-first is not election safety. Two replicas can each retain a different locally usable incumbent. The mapped policy needs a serialized decision authority or quorum/epoch certificate; a deterministic rank alone does not establish a shared leader under partitions. It gains uniqueness for a committed decision epoch under those premises, but fails availability when the required quorum is unavailable. Its refusal names the missing quorum or stale epoch; replay and the stranger's receipt need votes/commit evidence, not just a locally computed winner. Wrong fit: treating two independent slot reads as a distributed election and letting both act.

**READ.** Gray and Cheriton's leases provide time-bounded rights for cache consistency under their clock/failure assumptions. [Original 1989 paper](https://www.cs.cmu.edu/afs/cs.cmu.edu/academic/class/15712-s12/www/papers/gray89.pdf). Chubby makes an additional operational boundary explicit: a lock holder supplies a sequencer, and recipient services should reject stale sequencers. [Burrows, “The Chubby lock service,” §2.4](https://www.usenix.org/legacy/event/osdi06/tech/full_papers/burrows/burrows_html/index.html).

**INFERRED.** The mapped lease policy is §4.7; the extra kernel lesson is that authority must be checked where an effect is accepted. Renewed incumbency is not permanent entitlement. Epoch/fencing validation can reject stale senders under the receiver's protocol, but it cannot infer the outcome of an already accepted operation whose response was lost. Wrong fit: allowing a replacement leader to spend the same semantic token again because the previous leader's lease expired. Renewal, duplicate suppression and historical commitments are separate obligations. A receipt should name expired/stale authority and, independently, any unresolved earlier dispatch.

### 5.5 Legal precedent and editorial correction

**READ.** In *Kimble v. Marvel* (2015), the Court explains retention of precedent in terms including reliance and the need for justification beyond disagreement with the earlier decision, while acknowledging that precedent can be overruled. This is a specific instance of a doctrine, not a universal algorithm for every legal system. [Opinion](https://www.law.cornell.edu/supremecourt/text/13-720).

**INFERRED.** The useful policy analogue is rebuttable incumbency with an authorized supersession process. It gives a procedural retention theorem—absent an admissible overruling event, retain the current precedent—not logical optimality or eternal truth. It fails F and unconditional K because the authorized process can overrule a still-applicable predecessor. Replay requires the cited precedent, authority and reasons for overruling; a refusal identifies the missing authority or required justification. A stranger sees the old rule, its period of application, and the successor's reason. Wrong fit: a machine demands a formal contradiction before allowing the responsible editor to improve a still-usable passage. Legal precedent often protects reliance; it does not make “older” a Boolean truth condition.

**READ.** ICMJE correction guidance calls for correction notices, dated revised versions, archived prior versions and indications on earlier versions that newer ones exist. [Corrections and Version Control](https://icmje.org/recommendations/browse/publishing-and-editorial-issues/corrections-and-version-control.html).

**PROPOSED.** For LANG-83 and the delvetalk2 request, adopt this structural pattern: named editorial selection, explicit suspension when evidence fails, and linked supersession without erasure. The theorem is append-only preservation of decision and correction records, plus S for anything displayed as currently admitted. It does not imply K, automatic P, or that the latest submission wins. Replay needs the author/editor events and version links; a refusal names the editor action or failed support required to proceed. The stranger sees both the line that mattered and its correction. Wrong fit: retaining every old version as equally current, or suppressing the correction under an unchanged “selected” label. Persistence is successful only if the changed status is visible.

**INFERRED / PROPOSED.** Publishing a passage is an event that cannot be unsent; it need not make all future editorial correction impossible. A correction is a new authorized revision/publication event, linked to the old one. If the first publication entered a protocol hole, the correction cannot replace that hole's recorded execution: it must be an operation admitted by a subsequent revision protocol. This preserves a document's continuing identity and its historical versions without using “new slot” as a way to evade an outstanding payment or other obligation. Editorial acceptance, current display, and protocol dispatch must not share one undifferentiated commitment bit.

## 6. What “names what would pass” can honestly promise

**READ.** Today's `Refusal` is `List (Cand × List Fact)`. `Slot.select` gives the exact dead-support list for each ordered candidate; it does not put a judge token in the payload. If a dead list is empty in a factual refusal, the judge failed. If the list is nonempty, the judge might have failed too. `Integrity.transition` itself asks only for some named failed-support evidence per candidate and the empty-list implication, weaker than exact list equality.

**INFERRED.** Three certificates must stay separate:

| Certificate | What it proves | What it does not prove |
|---|---|---|
| Exclusion witness | This candidate cannot pass now: a failed judge or at least one failed conjunct. | All repairs needed, or feasibility of repair. |
| Missing-requirements list | These cited supports do not hold now. | That setting each independently can make them hold simultaneously. |
| Executable repair/selection offer | This particular authorized, compatible plan and choice event passes the stated checks when its preconditions hold. | An unconditional guarantee that the external world will cooperate. |

**READ.** `clash_unsat` in `Slot/Repair.lean` is the decisive boundary: one cell cannot simultaneously have pin 0 and pin 1. The independent repairs each establish their own target but are incompatible. `repair_sound` supplies a usable repaired candidate only with compatibility, coverage and a true judge. It does not establish that the selection policy chooses that candidate, that a chooser event is authorized, or that a protocol hole is still unentered.

**PROPOSED.** Use separate outcomes for `noAdmissible`, `awaitingChoice`, `preferenceKept`, `candidateRejected`, `staleEvidence`, and `executionFrozen`. A chooser-required wait must not claim all candidates are unusable. A preference rejection must not forge a failed support. A frozen execution must name the recorded dispatch, not blame candidate quality. State an acceptance predicate for each actionable offer: candidate admissibility, authority, current slot revision, policy condition and execution guard must all pass. Recheck these at acceptance because the view can move after the refusal was produced.

**INFERRED.** Some refusals correctly have no repair within the current history. A permanently retired support cannot be resurrected along `World.Later`; a candidate must be replaced or re-cited under a new identity. No current event can authorize replacing an entered hole. Even receipt of the missing reply does not unfreeze that hole: answered history still counts as `Dispatched`. A correct refusal can identify the boundary and offer a later compensating operation only when a separate protocol permits one; it must not promise that waiting or retrying the same replan will pass.

**PROPOSED.** Common receipt fields should include slot/revision, immutable candidate/body identity, policy identity/version and parameters, chooser/delegation, prior decision, view/read-set evidence, result, reason, and the dispatch/history reference constraining future changes. Distinguish `selected`, `currentlyUsable`, `dispatched`, `superseded`, and `suspended`. Keeping a candidate does not mean there was no world change; replacing one does not mean its prior selection was erroneous. A receipt is reproducible relative to its recorded world evidence and trust boundary, not proof by itself that an external fact was true.

## 7. Policy-independent kernel contracts, stated for Lean

### 7.1 Selection soundness and honest outcomes

**PROPOSED.** Factor incumbent retention out of the universal soundness predicate. For the present `Advance` interface, the minimum reusable clause is:

```lean
def SelectionSound {V Fact Cand : Type} [World V Fact]
    (A : Advance V Fact Cand) : Prop :=
  ∀ S v order stored c,
    A.advance S v order stored = .ok c →
    S.usable (World.holdsAt v) c = true
```

**INFERRED.** Existing `Integrity.transition A` implies this by its success clause. `churn` also satisfies it by `select_ok`. `sticky` does not. `transition_retired` uses only this success clause plus the World retirement laws; its proof generalizes directly to `SelectionSound`. Thus exclusion of retired supports is policy-independent. Incumbent retention is not a premise of that argument.

**PROPOSED.** In the richer interface, strengthen success with an explicit `Permitted ctx c` predicate and a checked `DecisionAuthorized ctx event` predicate. `Permitted` must specify whether a valid prior admission survives removal from the preference list. Define admitted-choice success as:

```text
AcceptChoice(ctx, event, c) →
  judge(c) = true ∧
  (∀ f ∈ supports(c), holds(ctx.view, f) = true) ∧
  Permitted(ctx, c) ∧ DecisionAuthorized(ctx, event)
```

**PROPOSED.** Define factual failure separately:

```text
NoAdmissible(ctx, w) →
  (∀ c, Permitted(ctx,c) → ¬ Usable(ctx.view,c)) ∧
  ExactCandidateDiagnostics(ctx,w)
```

**INFERRED.** A wait need not satisfy that implication. Selection availability belongs to the chosen policy's contract: total automatic selectors promise success when their eligible domain is nonempty; chooser-required selectors promise acceptance when the required valid event is provided. Neither promises an actual human response. Honest explanatory outcomes should be fixed in the interface even though the conditions under which they occur vary by policy.

### 7.2 The two execution invariant families

**READ / PROPOSED.** For a log `L`, initial object `O`, initial world `v₀`, operation specification `sp`, and host `host`, use the current definitions for the following two predicates. This is a regrouping of landed obligations, not a proposed weakening:

```text
CurrentAdmission(L) := Authorized host sp v₀ L

CommitmentConservation(L) :=
  OnceSpent sp L ∧
  Paired L ∧
  ReplansUnentered O.template L ∧
  Kept O.Ω O.σ O.template L
```

**READ.** Expanded, the clauses mean:

```text
∀ pre event at each position of L,
  event = dispatch o →
    admitOp sp (View.mask (host.view (worldOf v₀ pre))
                         (spentBy sp pre)) o = true

(spentBy sp L).Nodup

∀ pre event at each position of L,
  (event = dispatch o → (histOf pre).inflight = none) ∧
  (event = respond r → (histOf pre).inflight = some (operationOf r))

∀ pre event at each position of L,
  event = replan h f → ¬ Dispatched O.template (histOf pre) h

Started (fill O.Ω (planOf O.σ L) O.template) (histOf L)
```

**READ.** The exact indexed versions are already `Authorized`, `OnceSpent`, `Paired`, `ReplansUnentered`, and `Kept` in namespace `Obend.Run`, file `Run/Spec.lean`. `Legal` additionally requires `WorldSteps host v₀ L`. `Inv` also pins the configuration's object, world and spent state to the log, supplies `Reach` for its residual, and ensures the in-flight operation is the residual's next call. Those representation clauses are necessary for the induction over executable steps; they must not be replaced by assumptions on arbitrary proposed updates.

**INFERRED.** Every policy that only proposes events through unchanged `run`, including a malicious policy proposing bad plans forever, preserves these safety properties on accepted events by `reachable_legal`. It may have terrible usability or no progress. Conversely, just `SelectionSound` plus “do not replace an entered hole” does not establish the full theorem: a runner could still redispatch a tokenless in-flight call or unspend a durable token on a world update. The existing separate `awaiting` and `spendOn` obligations are necessary.

**READ.** `replace_then_dispatch` already states the non-vacuous progress clause: at an invariant configuration, with no call in flight, an owned unentered hole, a replacement whose residual reaches a next call, and current admission for that call, replan succeeds and that dispatch succeeds. There is no incumbent-retention premise. This is a two-step existence theorem with no intervening world update, not permission to cache admission across an arbitrary delay.

**PROPOSED.** Add policy-specific progress in front of it: a valid choice or automatic advance produces that replacement, then compose with `replace_then_dispatch`. For an override, check authority/revision and the same hole guard; do not require the previous choice to become unusable. For a wait policy, state the chooser-event hypothesis explicitly. For an entered hole, every policy returns the execution refusal, even if its preferred replacement is presently usable.

### 7.3 The remaining slot-to-dispatch bridge

**READ.** The current runner does not retain candidate identity or the slot's support evidence in `Cfg`. `resolveEvent_ok` proves usability when it constructs a replan event. `run` accepts raw bodies without `HasProt`/`Fills` checks, and dispatch checks `sp.requires` and `sp.consumes`, not an arbitrary slot's support list. This is sufficient for the landed operation-accounting theorem; it does not prove that every active slot justification is rechecked at dispatch.

**INFERRED.** A concrete gap would arise if a selected candidate cites an author's grant but the emitted operation's `sp.requires` omits that grant. The grant can disappear after selection while the operation remains admitted by `sp`. Nothing in the generic `resolveEvent_ok` statement rules that out. Do not call the existing theorem “every dispatch satisfies its selected candidate's current supports” without an adapter hypothesis. Candidate usability also does not imply every call in its body is admitted: operation facts, consumable tokens and history have additional conditions.

**PROPOSED.** The adapter must either carry the selected receipt into the dispatch guard and recheck its current admission, or prove an accounting implication for every exposure attributed to that selection:

```text
AdmitOperation(ctx, op) ∧ UsesChoice(ctx, op, decision) →
  Usable(ctx.view, decision.candidate) ∧
  Permitted(ctx, decision.candidate) ∧
  DecisionEffective(ctx, decision)
```

**PROPOSED.** `DecisionEffective` checks the recorded authorization and any continuing conditions of that kind of decision. It must not silently require the original chooser to hold office forever: whether a duly made choice survives a change of editor is a declared authority rule. A renewable delegation and a lasting editorial decision can therefore have different continuing conditions while both retain their original authorization evidence.

**PROPOSED.** Fix immutable candidate/body identities and the relation `UsesChoice` in that adapter; otherwise an unchanged candidate ID could silently name a changed body. Commit admission, spending, in-flight identity and the associated decision revision atomically before exposure. A selection produced against an older view is a proposal requiring revalidation, not an enduring permit. Historical dispatch receipts retain the view at which admission held; later revocation blocks new exposures without falsifying the recorded past.

**READ / INFERRED.** The current guard freezes the **whole entered hole**, including continuations not yet executed. Its `planFlip` counterexample deliberately rejects a different continuation with the same first call. “Only undispatched choices change” therefore means unentered holes at this granularity, not every syntactically unexecuted suffix. A finer compatible-continuation theorem could relax that later, but it is a separate execution design, not a chooser policy override.

## 8. Selectable fields and fixed kernel obligations

**PROPOSED.** Put selection control beside the slot, as a per-slot descriptor. Keep the mathematical `Slot.supports`/`judge` distinction. Conceptually:

```text
SelectionControl = {
  chooser: principal or delegated authority,
  policy: versioned policy identifier and parameters,
  candidateDomain: versioned admitted domain,
  orderOrRanking: versioned preference definition,
  overrideRights: authority and permitted event forms,
  suspensionMode: automatic recovery | reapproval required
}
```

**INFERRED.** A chooser and a policy are not the same field semantically. The chooser identifies who can decide or delegate; the policy identifies how automatic proposals are ranked and when a choice event is required. Today's protocol `.me`/`.them` polarity is not a cryptographic principal authentication scheme. A host adapter must connect it to authenticated authority. Policy changes must themselves be authorized, versioned events; changing policy cannot reset dispatch history or spent tokens.

**PROPOSED.** Selectable per slot: incumbent retention versus canonical recomputation; automatic fallback versus waiting for a chooser; score/tie-breaking/hysteresis; recency basis; renewal/review timing; explicit override rights; and suspension latching. Keep shared policy implementations small and named rather than adding opaque executable callbacks to a trusted proof kernel. More elaborate optimizers may propose choices externally with verifiable evidence. The kernel need not solve their optimization problem to enforce safety, although claiming “best” requires a certificate or a checked algorithm.

**PROPOSED.** Fixed across policies: no active admission for a failed judge/support; validation of candidate identity and chooser authority; revalidation at the actual exposure boundary; serializable expected-revision checks; preservation of accepted events and explicit corrections; durable spending; dispatch/reply pairing; the entered-hole guard; truthful classifications of impossibility, waiting and policy preference. The abstract model proves properties relative to its World/judge/operation accounts; their connection to authenticated external facts remains the adapter's responsibility.

**PROPOSED.** Ship three clear presets first:

| Slot purpose | Preset | Reason |
|---|---|---|
| Ordinary automatically maintained provisional choice | Incumbent-first, ordered fallback, explicit authorized override | Avoid gratuitous changes while allowing improvement and recovery. |
| Derived result that must match recomputation at a view | First-usable with rejected-prefix certificate | Make canonicality and its dependency cost explicit. |
| Authored/editorial selection | Named chooser, sticky while usable, latched suspension, explicit supersession | Preserve attribution and require an editorial act for replacement. |

**PROPOSED.** All three use the same execution guard if their selected body is effectful. Hysteresis/leases become additional presets when a real consumer can specify their measurements, time model and renewal authority. ATMS labels and joint repair search are optional evidence/planning services, not mandatory policy constructors.

**PROPOSED.** Preserve the existing theorem under an explicit name/description such as incumbent-first transition; extract `SelectionSound`, policy-specific retention and fallback laws, and a richer diagnostic result in a later implementation change. Retain `not_transition_churn` as evidence that first-usable differs from incumbent-first. Pair it with soundness of first-usable so the name does not misteach “canonical replay is unsafe.” Do not weaken the runner's frozen-hole law to accommodate chooser override. Override operates before that boundary.

**INFERRED.** The accepted default survives this comparison, with a narrower and better justification: it conserves a provisional choice when nobody has requested another and its grounds still hold. It does not supply editorial authority, immutable history or distributed uniqueness. Those need their own explicit contracts. The user-facing promise can then be exact: your choice remains current while supported under its policy; another authorized choice can supersede it before commitment; what has already happened remains in the record and constrains what can happen next.

## 9. Checks and scope of this report

**READ.** Primary repository sources inspected: `REPORT-JUST-20261031.md`; `Slot.lean`; `Slot/Integrity.lean`; `Slot/Repair.lean`; `Slot/World.lean`; `ASTRA-EVAL-20261031.md`, especially the early/chosen countermodel and proposed runner theorem; landed `Run/Runner.lean`, `Run/Spec.lean`, relevant invariant/interpretation proofs, the negotiation fixture and `REPORT-RUNNER-20261031.md`. Application context: delvetalk2 §7.3; nanodregg LANG-73 and LANG-83. Conversation context recovered around `cv show 01a18fe9 --around 1401 --context 5`, including Ember's acceptance and request for this analysis. Literature citations above link the sources actually consulted. No claim of a new literature-wide representation or novelty theorem is made.

**RAN.** Finite Python checks in this session:

```text
selection states: 512
incumbent/canonical disagreements: 102
incumbent outside current order: 60
prefix-preserving replay instances: 294
hysteresis states: 1536; margin 1
early/chosen: old canonical 1; new canonical 0; new incumbent-first 1
path dependence: direct final view -> 0; via temporary loss -> 1
reduced runner reachable states: 24; transitions: 216
all assertions passed
```

**RAN.** The reduced runner exhaustively explored the reachable closure of a two-provider, one-token state `(usableMask, spent, inflight, answered, chosen)` under four world valuations, either choice proposal, dispatch, and either provider's reply. Choices were deliberately allowed without an eligibility check before dispatch. Dispatch required current chosen-provider usability, an unspent token, and no in-flight call; choice changes were refused after any dispatch; replies had to match. Assertions checked monotone spending, frozen chosen identity after entry, admission at every accepted dispatch and persistence of the in-flight call under nonreply events. This illustrates independence from selection preferences. It is a tiny model with much less protocol structure than Lean's runner, not a verification of the Lean implementation.

**RAN.** Reproduction of the selection enumeration (Python 3, standard library only); the embedded block was also extracted from this document and executed successfully:

```python
from itertools import product, permutations
C = range(3)
orders = [p for n in range(4) for p in permutations(C, n)]
worlds = list(product([False, True], repeat=3))
def first(u, order):
    return next((c for c in order if u[c]), None)
def advance(u, order, stored):
    return stored if stored is not None and u[stored] else first(u, order)
def lex(u, order, recent):
    good = [c for c in order if u[c]]
    return min(good, key=lambda c: (order.index(c), -recent[c])) if good else None
n = different = outside = reuse = 0
for u, order, stored in product(worlds, orders, [None, 0, 1, 2]):
    a, b = advance(u, order, stored), first(u, order)
    assert a is None or u[a]
    assert b is None or u[b]
    assert stored is None or not u[stored] or a == stored
    assert (a is None) == (not any(u[c] for c in order)
                          and (stored is None or not u[stored]))
    assert lex(u, order, (1, 2, 3)) == b
    n += 1
    different += a != b
    outside += a is not None and a not in order
for u, v, order in product(worlds, worlds, orders):
    c = first(u, order)
    if c is not None and v[c] and all(not v[d] for d in order[:order.index(c)]):
        assert first(v, order) == c
        reuse += 1
assert (n, different, outside, reuse) == (512, 102, 60, 294)
```

**READ / PROPOSED.** Lean theorem claims in this report are source readings of landed statements and proofs; I did not rerun the other lanes' builds. The new factorization, receipt schema, chooser events, lease/score policies and slot-to-dispatch bridge are recommendations, not implemented functionality. The immediate integration work is explicit: retain candidate/decision identity around `resolveEvent`, add policy-aware selection outcomes, prove each preset's choice law, and connect the selection's admission to the dispatch account. The runner's existing invariant and continuation theorem can remain the common execution boundary.
