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

| # | workstream | deliverable | gate | depends on | status |
|---|---|---|---|---|---|
| 1 | **Judge and Receipt** | `Obend/Judge.lean` (class, `Format`, five instances, one foreign format with a bad-certificate tooth), `Obend/Receipt.lean` (the type, per-support trust, dial, `holdsOfPin`), `obend verify RECEIPT` | a receipt exported by one run checks in a consumer with no producer state; the foreign format decodes a real solver's output | Fold | in progress |
| 2 | **Quote** | orientation (`review/QUOTE-ORIENTATION-20261101.md`), then `Obend/Code` as typed represented syntax with checked import and splice, the observer ladder with `rewrite_sound_below`, mirrors, `RewriteJudge`; promotion into `Term` only with erasure and preservation theorems | the ladder's teeth (`mix_assoc` holds under `≈b`, fails under `≈r` and `≈q`); a rewrite certificate from a real rewriter checks | 1 | orientation in progress |
| 3 | **Kinds and Intention** | the nominal kind cell (every instance tagged, the kind's law an ancestor, dispatch by kind), one `Intention` module re-basing package parents and cites, C4 `linearize` rewritten structurally and proved | two kinds with equal fields distinguished by a protocol call; `resolve`/`recite`/`renew` one repair; monotonicity and local precedence proved | 1 | decided, not started |
| 4 | **Cost** | `≈c` (clairvoyant call-by-value over Core4) with `mix_assoc` constants, ticks-within-a-constant of CV cost on the machine, the improvement judge | an optimization's charge difference is a theorem | Equiv | not started |
| 5 | **Leaf** | the emitter (acyclic defs, dispatcher with fuel, represented machine), the refinement against BendTT's `Eval` through the runner's adapter, the toolchain decision, the specialization slot | a Bend user's package is an ancestor of a kind; an emitted book's run is `Legal`; moving a cited pin selects the machine candidate | 2, 4 | not started |
| 6 | **Runner remainder** | durable commit and recovery, the ledger as a fold member (projection as the generic theorem), consensus time as a ledger fact, World fork and stitch, holes in emitted plans | restart with two competing clients cannot double-spend; a fork's write to a shared token is refused `notMine` | Fold, Shared | not started |
| 7 | **Laws over domains** | `law L on plan P` (envelope and monitor), `world law for W`, `hyperlaw` with the product-invariant judge, attestation supports with revision | the negotiation's plan contract refuses `commit` before `reserve`; a two-run receipt-noninterference law checks at install | 1, 6 | not started |
| 8 | **The first platform: metadata-driven business software** | kinds for catalog, document, register, report; `balanced`/`conserved`/`monotone` laws; posting as a turn; period closing as a version law; reports as judged folds with non-omission receipts; forms as view methods; offline drafts through fork and stitch; one purchase-to-payment app on the shared World | a stranger opens a vault with a ledger kind, posts from a second machine offline, reconnects, sees a balance refusal name its clause, prints a report an auditor recomputes | 3, 6 | not started |
| 9 | **Widgets and the inspector** | `View` as `Data` with typed bindings, events as plans, affordances as the judge's would-pass, a remote widget as a byte cite with an attenuated live reference, one inspector over the same objects | a revoked grant removes exactly the affordances citing it | 8 | not started |
| 10 | **Automation** | the producer protocol and isolation, exact algebra and SAT/PB adapters, one certified encoding from a real obligation, the problem DAG and portfolio, a `ProofSession` page | each accepted subgoal composes back to the original judgment; unknown is never negation | 1 | not started |
| 11 | **Build speed** | `@[expose]` confined to what reduction needs, the large proof files split, two build tiers, the warm worktree pool, a kernel-evaluable type graph | a leaf proof edit under 10 s; a `Check` edit stopping within twenty modules; a clean build under two minutes | none | partly done |
| 12 | **Contracts** | receipts as proofs at the one-bit position of the dial, replicated settlement | after 6 and 1; the charters say not yet | 1, 6 | deferred |

## Decisions pending

Should the shared ledger's view commit pins (a Merkle map per view), so a World-transition receipt's
openings check against a root and the view becomes `checked` rather than the host's word? It fixes
what `dated : View` is; cost: a commitment scheme in `Run/Shared` and an opening proof per read.
Recommended yes, as part of workstream 6.

Nominal kinds: decided yes (3). `quote` into `Term`: decided yes, gated on the orientation (2). The
leaf toolchain (vendor `bendtt.lean` at 4.34 or wait): open (5). Sum versus max for branch uses in
`PartialTyping`: open, recorded in `review/ARGON-RESPONSE-20261030.md`.
