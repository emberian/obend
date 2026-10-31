# Plan

Revised 2026-11-01. The destination is `AMBITION.md`; the design is `DESIGN.md`; what is proved is
`METATHEORY.md`; decisions and who took them are `review/DECISIONS-20261031.md`. This file is the
order of work, as workstreams with a deliverable, a gate and a status. A workstream is done when its
gate holds on `dev`, its report is in `lean/docs/`, and the twin it replaced is gone.

## How we work

A lane is one agent in its own warm worktree (a finished lane's worktree, fast-forwarded), briefed by
a one-page file under `lean/docs/LANE-*-BRIEF-*.md` or `review/*-BRIEF-*.md` that names the sources,
the ground truth, the deliverable and the gate; it commits named files on `dev`, rebases before
pushing, and ends with a report in the lane-report style (what landed, decisions with critique and
meta-critique, what is not proved). Studies land in `review/` or `astra/`; outside reads (Kimi,
Gemini, Astra) are commissioned at checkpoints (`checkpoint-*` tags). No spikes as foundations: an
experiment is built as the module it tests or deleted. No per-theorem axiom lists; the census in
the build is the check. One stranger-usable artifact stays ahead of every platform.

## Workstreams

| # | workstream | deliverable | gate | depends on | deliverable status / gate status |
|---|---|---|---|---|---|
| 1 | **Judge and Receipt** | `Obend/Judge.lean` (class, `Format`, five instances, one foreign format with a bad-certificate tooth), `Obend/Receipt.lean` (the type, per-support trust, dial, `holdsOfPin`), `obend verify RECEIPT` | a receipt exported by one run checks in a consumer with no producer state; the foreign format decodes a real solver's output | Fold | in progress |
| 2 | **Quote** | per `review/QUOTE-ORIENTATION-20261101.md` §3–§4, §8: lane 1 is T1–T6, T8, T14 (`Core/Code.lean`, `Equiv/Quote.lean`: `quote`/`unquote`/`address`, `Code Ψ A θ`, `import`, `Mirror`, `≈q`, the ladder, `rewrite_sound_below`, versioned encoding, `holeInCode`); lane 2 is T7 after the linear/affine split; lane 3 is T10–T12 with the cost lane; `splice` as a turn and `RewriteJudge` follow | the ladder's teeth; `import` refuses an escaped index, a foreign encoding and a hole by name; a rewrite certificate checks | 1, 13 | **lane 1 done** (`REPORT-QUOTE1-20261101.md`: T1–T6, T8, T14, versioned encoding, `holeInCode`; `mix_assoc` holds at ≈r, it is `compose` that fails); lane 2 (T7) next; lane 3: quoting terms that mention names not yet declared (fresh kinds, a stranger's future names) via Nanevski's names-and-necessity, which the orientation's "held closed terms" rule does not cover; queued: rename `BEquiv` to ≈r |
| 3 | **Kinds and Intention** | the nominal kind cell (every instance tagged, the kind's law an ancestor, dispatch by kind), one `Intention` module re-basing package parents and cites, C4 `linearize` rewritten structurally and proved | two kinds with equal fields distinguished by a protocol call; `resolve`/`recite`/`renew` one repair; monotonicity and local precedence proved | 1 | deliverable done (`REPORT-KINDS-20261101.md`: kind cell, Intention with three instances, C4 proved); **gate open**: dispatch distinguishes kinds, general checking still erases the distinction; the end-to-end identity contract is C1 |
| 4 | **Cost** | `≈c` (clairvoyant call-by-value over Core4) with `mix_assoc` constants, the improvement judge | an optimization's charge difference is a theorem | Equiv | deliverable done (`REPORT-COST-20261101.md`: `mix_assoc_cost` within a factor of 8, Faré's tests costed, the improvement judge); **gate open**: the tick correspondence was refuted for H&H's semantics (`ticks_not_within_cv`), so the cost foundation for the runtime is contract C4, not done |
| 5 | **Leaf** | the emitter (acyclic defs, dispatcher with fuel, represented machine), the refinement against BendTT's `Eval` through the runner's adapter, the toolchain decision, the specialization slot | a Bend user's package is an ancestor of a kind; an emitted book's run is `Legal`; moving a cited pin selects the machine candidate | 2, 4 | not started |
| 6 | **Runner remainder** | durable commit and recovery, the ledger as a fold member (projection as the generic theorem), consensus time as a ledger fact, World fork and stitch, holes in emitted plans | restart with two competing clients cannot double-spend; a fork's write to a shared token is refused `notMine` | Fold, Shared | deliverable done (`REPORT-RUNNER2-20261101.md`); **gate partly open**: `exposed_once` holds in a model with atomic appends and no peer dedup; the stitch rechecks only the token; a checked view is self-consistent with a producer-supplied root, not membership in an authoritative history (contract C3) |
| 7 | **Laws over domains** | `law L on plan P` (envelope and monitor), `world law for W`, `hyperlaw` with the product-invariant judge, attestation supports with revision | the negotiation's plan contract refuses `commit` before `reserve`; a two-run receipt-noninterference law checks at install | 1, 6 | not started |
| 8 | **The first platform: metadata-driven business software** | kinds for catalog, document, register, report; `balanced`/`conserved`/`monotone` laws; posting as a turn; period closing as a version law; reports as judged folds with non-omission receipts; forms as view methods; offline drafts through fork and stitch; one purchase-to-payment app on the shared World | a stranger opens a vault with a ledger kind, posts from a second machine offline, reconnects, sees a balance refusal name its clause, prints a report an auditor recomputes | 3, 6 | not started |
| 9 | **Widgets and the inspector** | `View` as `Data` with typed bindings, events as plans, affordances as the judge's would-pass, a remote widget as a byte cite with an attenuated live reference, one inspector over the same objects | a revoked grant removes exactly the affordances citing it | 8 | not started |
| 10 | **Automation** | the producer protocol and isolation, exact algebra and SAT/PB adapters, one certified encoding from a real obligation, the problem DAG and portfolio, a `ProofSession` page | each accepted subgoal composes back to the original judgment; unknown is never negation | 1 | not started |
| 13 | **Linear separates from affine** | exact discharge of `linear` binders enforced in `PartialTyping`/`Bidirectional` (`Quantity.fits` promoted from the teeth to the rule), the coercion quantity table re-derived, cohorts unchanged | a `linear` binder used zero times is refused by name; the η-wrapper matrix changes exactly where the orientation predicts | none | deliverable done (`REPORT-LINEAR-20261101.md`); **gate restated**: exact checked usage at binders, branch agreement, transfer restrictions; no eventual-consumption theorem for aggregates, and the singleton projection is refused too; the ownership contract is C2 |
| 11 | **Build speed** | `@[expose]` confined to what reduction needs, the large proof files split, two build tiers, the warm worktree pool, a kernel-evaluable type graph | a leaf proof edit under 10 s; a `Check` edit stopping within twenty modules; a clean build under two minutes | none | deliverable done (`REPORT-BUILD-20261101.md`); **gate open**: private proof edit 5 s met; clean build under two minutes and `Check` edit within twenty modules not met, awaiting the expose pass |
| 12 | **Contracts** | receipts as proofs at the one-bit position of the dial, replicated settlement | after 6 and 1; the charters say not yet | 1, 6 | deferred |

## Decisions pending

The four contracts C1–C4 in `review/DECISIONS-20261031.md` (identity across kinds, code and
upgrades; ownership across aggregates and staging; receipt meaning and authoritative history;
runtime cost and optimization claims), each with its recommendation and owner. Decision rights from
here (Astra §8): a lane decides proof structure, representation and scoped restrictions and reports
them; the integrator decides cross-lane interfaces, sequence and build policy under standing
approval; Ember decides what users mean by durable choices and identity across upgrades, the first
product priorities, and externally promised trust and failure behaviour, from a reviewable proposal
with real alternatives. An outside read is commissioned while a lane builds, before any new
semantics is promoted into a relied-on boundary.

The next integration's first row: a package upgrade changes a kind law; an offline document retains
old typed code; stitching rechecks current authority and schema; a stranger verifies the resulting
report and can distinguish a historical fact from a current one.
