# Scholar brief: analyses of obend worlds relative to partial setups

Ember, 2026-11-01: "interesting, relevant analyses of obend worlds relative to (partial) setups ...
maybe that's a stretch." Make it not a stretch. A *world* here is the kernel's history: cells with
pins and versions, slots with candidates and supports, members with grants, packages with
intentions, laws in force, a ledger of commits (`lean/Obend/Slot/World.lean`, `Run/Shared.lean`,
`Run/Fork.lean`, `Spec/Ecosystem.lean`, `Vault/Store.lean`). A *partial setup* is a world
described incompletely: some pins unknown, some members' grants unresolved, a package's parent
version open, a law not yet amended, a fork not yet stitched, a solver's answer pending. The slot
theory already treats unknowns as candidates with supports; the audited fold (`Fold.lean`) already
makes every admission a function of the pins it reads (`step_of_pins`); the runner's `Legal` is a
trace predicate; the Merkle view commits what is known. This is a study for Ember and Claude to
evaluate; it lands nothing in `lean/`.

The question. What analyses of a world are worth having, stated so a kernel can compute them and a
stranger can check the answer: (1) **Reachability and safety under partial knowledge.** Given what
is pinned and what is open, which states can the world reach; can a member ever double-spend; can a
law be amended by someone without the grant; is a slot's candidate ever selectable; is a package's
diamond resolvable without conflict. These are model-checking questions over the audited fold with
open pins as parameters: say what the state space is, where it is finite (protocol automata, kind
lattices, C4 lists) and where it is not (Core4 terms), and what abstraction gives a finite one
(the slot's support lattice; the quantifier shapes `∃M ∃run`, `∃plan ∀M ∀r`, `∃policy`, `∀M ∃plan`
from `astra/ASTRA-EFFECT-LAWS-20261101.md` §6). (2) **Dependency and impact.** The journal already
computes, for a change to a theorem, the exact set of theorems affected; the same analysis over a
world: if this pin moves, which candidates go `blocked`, which receipts go stale, which pages'
cites go behind, which laws' verdicts could change (`review/GENERATED-20261031.md` on `read_congr` as
distributed knowledge); as a static analysis of a world before the change is made. (3) **Repair
synthesis.** Given a blocked slot, which minimal set of supports would make it usable (the
`Repair.Compatible` condition, retired into `REPORT-JUST`, is the soundness side; the synthesis side
is a search a solver can do and the kernel can check); given a stale package turn, which re-pins
restore it; given a conflict, which selections resolve every section. (4) **Epistemic and
provenance questions.** Who could know this fact at this view (distributed knowledge over
pin-holders); what is the minimal receipt that convinces a stranger (the disclosure dial made
exact); what did a member rely on that has since moved; whose attestation does this verdict rest on.
(5) **Counterfactual and what-if.** Were this law amended, which past writes would have been
refused (replay the fold with the new law: it is a fold, so this is computable); were this member's
grant revoked, which admitted dispatches lose their citation; were the fork stitched now, which rows
conflict. (6) **Hybrid: the analysis as a judged subsystem.** Each of these is a producer (a model
checker, a solver, a replay) whose answer is a certificate (a path, a witness, a core, a replayed
fold) checked by a `Judge` instance, so the kernel never trusts the analyzer. Say which analyses
have certificates that are cheap to check, which need the fold replayed (and are therefore as
expensive as the history), and which are only attestable.

Read `DESIGN.md` §3–§4, `review/GENERALIZATION-20261031.md`, `review/GENERATED-20261031.md` §3,
`astra/ASTRA-EFFECT-LAWS-20261101.md` §3–§6, `astra/ASTRA-SELECTION-20261031.md` §7,
`lean/docs/REPORT-RUNNER2-20261101.md`, `REPORT-JOURNAL-20261030.md`, `REPORT-KINDS-20261101.md`, and
the code named above. Literature to fetch into `~/paperbin` (Kagi; `~/.annas-key`): model checking
of parameterized and partially specified systems (Clarke, Grumberg, Peled; partial Kripke structures
and 3-valued model checking, Bruns–Godefroid, Huth–Jagadeesan–Schmidt); abstract interpretation of
protocols; incremental and demanded analysis (Stein et al. is in paperbin); provenance semirings
for why/why-not (Green–Tannen in paperbin); repair and synthesis via MaxSAT/ASP; epistemic model
checking (MCMAS, Lomuscio); what-if query processing in databases (hypothetical queries, Balmin);
Datalog-based program analysis (Doop, Soufflé) since a world is relational and the Scry MCP already
offers Datalog over corpora.

Write `/Users/ember/dev/obend/review/WORLD-ANALYSIS-20261101.md`: the analyses ranked by value to the
first platform (a business ledger with members, laws and offline forks) and by cheapness of
certificate; for each, the formal statement over the existing structures, the producer, the
certificate, the `Judge` instance it would be, and the first query a stranger would type (`obend
analyze …`); the design of `Obend/Analysis/` with its first three theorems; and what is a stretch
and why. Tag claims READ, INFERRED, PROPOSED. Commit alone on `dev` with `git -c
commit.gpgsign=false commit -F -` and trailer `Co-Authored-By: Claude Fable 5.1 <noreply@anthropic.com>`,
rebase before pushing; two Lean lanes are live, touch nothing under `lean/`. Ember: "Never kill by
pattern. No `pkill -f <anything>`, no `pkill -x <bare word>`, no `killall`, no `kill -u`. A process you
started is stopped by the PID in its PID file, and only that. Every detached job writes one
(`nohup ... & echo $! > job.pid`). No PID file, no kill: tell me instead." When a disk is low: stop
writing to it, tell Ember, wait. Reply with the commit hash, the analysis you would build first, and
the first `obend analyze` query.
