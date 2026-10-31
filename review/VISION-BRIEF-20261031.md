# Vision brief: the symbolic core of what comes after

Ember, 2026-10-31: "imagine briefly that we were building what would someday be the symbolic core of
the successor of Mathematica, and that using this language we would layer on staged reflective
metaprogramming in a way Amal Ahmed and the whole Harvard metareflection lab would nod their heads at,
and integrated with a runtime/compilation environment so trim but powerful that it makes GraalVM
weep; able to operate with and upon and synthesize many subsystems including theorem provers or
specialist computational tools and logics. Suppose it were also used to express smart contracts in a
platform replacing Mina, hybrid desktop/cloud SaaS in a platform replacing 1C, distributed widgets,
things like that. How would we want to approach the problem, from where we're at? especially
considering we want as powerful automation as the laws of computer science permit (this does mean a
lot of solver diversity)." Two scholars answer this independently, a Claude (this brief) and an
Astra (the same brief); Ember and Claude evaluate both. This is a study: read as much as you like,
fetch any reference into `~/paperbin` (Kagi key in `~/dev/allgame/.env`, request shape in
`~/dev/allgame/claude_resident/tools/web_tools.py`; `~/.annas-key` and `$ANNAS_SECRET_KEY` for
paywalled papers, the site's API wants an MD5), land nothing in `lean/`, be ambitious.

## Where we are

`/Users/ember/dev/obend`, tag `checkpoint-20261031b`. Read `README.md`, `THESIS.md`, `DESIGN.md`,
`METATHEORY.md`, `review/DECISIONS-20261031.md`, `review/GENERALIZATION-20261031.md` (the audited
fold, the judgment class, intentions as slots, the receipt type, laws over declared domains), the
studies it rests on (`review/GENERATED-20261031.md`, `astra/ASTRA-EFFECT-LAWS-20261031.md`,
`review/ALGEBRAIC-SUBTYPING-20261031.md`, `review/EQUIV-PLAN-20261031.md`), and the lane reports in
`lean/docs/REPORT-*.md` for what is actually proved: a lazy object calculus with a mechanized
metatheory, a bidirectional checker complete on a stated fragment with equi-recursive agreement, laws
judged by re-executing a machine probe and inheriting across packages, a slot theory of deferred
decisions with withdrawable supports, a guarded runner with `refines` and a shared-World composition
layer (`Run/Shared.lean`, `joint_reachable_ticket_exclusive`), documents with pushout merge and
cites, cross-package extension with intentions as slots, and `obend open` on a markdown vault. The
kernel admits by re-execution; a stranger checks a certificate; every refusal names what failed.

## The previous ambitions, which you must read

breadstuffs is the first whole system, read-only at `/Users/ember/dev/breadstuffs`. Its vision and
its platform are in `docs/deos/` (250 files; start with `docs/what-is-deos.html`, `docs/vision/`,
`docs/deos/APPS-AS-CELLS.md`, `CELL-HOSTED-VIEWTREE.md`, `COCKPIT-UX.md`, `CROSS-DEVICE-FIRMAMENT.md`,
`BRANCH-AND-STITCH-PROTOCOL.md`, `CONSENSUS-TIME-AND-RECEIPT-IDENTITY.md`, `COMPUTRON-POLICY.md`,
`AGENT-CONFINEMENT-REDTEAM.md`, `CONDITIONAL-VAULT.md`, `DARK-AMM-PRIVATE-RECEIPT.md`, and whatever
the index names on GUI, events, widgets, cross-device, cloud, contracts), its metatheory in
`metatheory/docs/` (53 files; start with `DREGG-CALCULUS.md`, `CELL-PROGRAM-LANGUAGE.md`,
`FLOW-COMPOSITION-ALGEBRA.md`, `GUARDED-HOLES-METATHEORY.md`, `FRONTIERS-BEYOND-DEOS.md`,
`POLIS.md`, `POLIS-HYPERPROPERTY-FRONTIER.md`, `POLIS-METATHEORY-QUESTIONS.md`, `LOGIC-COMPILER-ASSESSMENT.md`,
`AXIOM-HYGIENE.md`, `APPS-RECENSUS-DEOS-ERA.md`, `DISCARD-CANDIDATES.md`) and
`metatheory/CONSTRUCTIVE-KNOWLEDGE.md`. Also `docs/DREGGNET-CLOUD-OFFERINGS.md`, `docs/RECEIPT-CONTRACT.md`,
`docs/COMMUNITY-BRIEF-CLOUD-FORGE-APPS.md`. Say what deos got right that obend has not yet taken, what
it got wrong that obend should not repeat, and which of its frontiers (`FRONTIERS-BEYOND-DEOS`,
`POLIS-*`) are the ones this vision reaches.

## The question

From where we are, how do we approach building that: (1) the symbolic core, what Mathematica's
successor needs that a term rewriter and a notebook do not have, and whether Core4 with reflection,
laws and slots is the right kernel for symbolic computation over heterogeneous subsystems or needs a
different object at its center; (2) staged reflective metaprogramming done right, in the lineage the
Harvard metareflection lab stands in (Ahmed's logical relations for multi-language and gradual
systems, Nanevski's contextual modal types which the slot already uses, MetaML/MetaOCaml staging, the
reflective towers from 3-Lisp through Amin–Rompf's collapsing towers, Rompf's LMS, Lean's own
elaborator-as-metaprogram), and what the typed, law-abiding reflection obend has (`reflect`,
`metadata`, the observer table) must grow into; (3) a runtime and compilation environment with one
intermediate language that specializes, stages and partially evaluates across the whole tower (what
Truffle/Graal does by partial evaluation of interpreters, what a lazy call-by-need machine with
checkpoints already gives, where Bend's leaves and affine compilation fit, what a trim design looks
like that is nevertheless more powerful); (4) automation as powerful as the laws of computer science
permit: solver diversity as a first-class design (SMT, ASP, SAT with proofs, ILP, CAS, model
checkers, HOL/Lean/Isabelle provers, proof search like waterfall, LLM-proposed invariants) under the
one discipline the design already has, that the kernel checks certificates and never trusts search;
what a certificate format registry looks like, what the trust boundary of each solver is, what
"as powerful as the laws permit" means concretely (what is decidable, semi-decidable, and only
attestable), and how the system synthesizes and operates upon other systems; (5) the platforms: smart
contracts replacing Mina (a receipt is a proof; the shared-World layer is the chain; what the
verifiable-computation story must be and what breadstuffs' circuit lineage already settled), hybrid
desktop/cloud business software replacing 1C (metadata-driven applications, forms, reports,
accounting registers as objects with laws, offline-first with merge, the 1C lesson of a platform
that non-programmers configure), distributed widgets and the GUI/event story deos had (cells, view
trees, the cockpit); (6) the order: from the checkpoint, what is built first and why, which existing
modules carry the weight and which must be replaced, and where the risk of building on the wrong
foundation is highest.

Write `/Users/ember/dev/obend/review/VISION-CLAUDE-20261031.md` (Claude) or
`/Users/ember/dev/obend/astra/ASTRA-VISION-20261031.md` (Astra): precise enough that a lane could be
briefed from any section, with claims tagged READ, INFERRED, PROPOSED, and references by name with
the paperbin filename where fetched. Commit the file alone on `dev` with `git -c commit.gpgsign=false
commit -F -` (trailer `Co-Authored-By: Claude Fable 5.1 <noreply@anthropic.com>` for Claude, `Astra
(GPT-6) via codex <noreply@openai.com>` for Astra), rebase before pushing; a proof-engineering lane
is live under `lean/`, touch nothing there. Ember's safety paragraph, verbatim: "Never kill by
pattern. No `pkill -f <anything>`, no `pkill -x <bare word>`, no `killall`, no `kill -u`. A process
you started is stopped by the PID in its PID file, and only that. Every detached job writes one
(`nohup ... & echo $! > job.pid`). No PID file, no kill: tell me instead." When a disk is low: stop
writing to it, tell Ember, wait. Reply with the commit hash, your one-sentence answer to (1), and the
first thing you would build.
