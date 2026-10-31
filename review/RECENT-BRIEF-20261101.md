# Scholar brief: the recent literature (2022 and later) on everything this project touches

Ember, 2026-11-01: our reading lists are anchored in 1987–2013. This study finds what has moved
since 2022, so our designs are checked against the present state of each field rather than the
classics. It lands nothing in `lean/`.

Method. For each topic below, search for work from 2022 to 2026 (Kagi, key in `~/dev/allgame/.env`,
request shape in `~/dev/allgame/claude_resident/tools/web_tools.py`; arXiv listings for cs.PL, cs.LO,
cs.CR, cs.DC; POPL/ICFP/OOPSLA/PLDI/LICS/CAV/CSF/CCS/OSDI/SOSP 2023–2026 proceedings; the
`semantic-scholar` MCP if it connects; `~/.annas-key` for paywalled papers). Pull each paper that
bears into `~/paperbin` as `author-year-short-title.pdf` with a `.txt` sibling; read at least its
introduction and the theorem or construction that matters; and write, per paper, one sentence on
what it changed relative to the classic we cite and one sentence on what it means for our design,
naming the file in `lean/Obend` or the contract in `review/DECISIONS-20261031.md` it bears on.

Topics, with the classic we cite and the question the recent work should answer:

1. Staging and quotation under a type theory (we cite Davies–Pfenning, Nanevski, Kovács 2022, Tan–Wei
   2026): typed quotation with pattern matching and hygiene, two-level type theories in practice,
   verified staged compilers, quotation under effects and linearity.
2. Linear, graded and quantitative types (McBride, Atkey, Wood–Atkey): graded modal types in
   practice, linearity with effects and aggregates (the `⊗`/`&` elimination question, C2), ownership
   types in Rust-adjacent formalizations (Aeneas, RustBelt successors, Verus), resource-aware
   session types.
3. Bidirectional and algebraic typing (Dunfield–Krishnaswami, Dolan, Parreaux): completeness
   results since 2022, MLstruct successors, equi-recursive subtyping decision procedures, nominal
   plus structural hybrids.
4. Program logics for lazy and effectful languages, and cost (Iris, Moran–Sands, Hackett–Hutton):
   Iris-based logics for laziness or coinduction, time-credit and cost logics 2022+, clairvoyant
   call-by-need follow-ups, verified cost semantics.
5. Interaction trees, choice trees, effect handlers (Xia 2020): CTrees, formal reasoning about
   effect handlers, mechanized refinement of effectful programs.
6. Verified distributed systems and ledgers (Abadi–Lamport, TLA+): Verus/Iron systems, verified
   consensus and CRDT work 2022+, authenticated data structures with proofs, receipts and
   verifiable logs, "verifiable computation without a chain".
7. Proof-carrying data, folding and incremental verification (we hold a zk shelf): Nova successors,
   accumulation schemes, lookup arguments, verified SNARK formalization 2023+, and any work on
   certificate formats a kernel re-checks (LRAT/VeriPB successors, proof-carrying SMT).
8. Truth maintenance, belief revision, three-valued and partial model checking (de Kleer, Doyle,
   Bruns–Godefroid): anything since 2022 on justification-based reasoning, provenance semirings in
   systems, incremental Datalog, partial Kripke structures.
9. Object calculi, mixins and open recursion (Cook, Bracha, Faré): recent work on mixin
   composition, trait linearization, "objects as fixed points" in dependently typed settings, open
   recursion in Scala 3 / Koka / Flix, and anything citing Rideau.
10. Local-first, CRDTs, documents with provenance (Shapiro, Kleppmann): 2022+ work on
    intention-preserving merge, patch theory implementations, byte-level transclusion, verified
    collaborative editing.
11. Mechanized metatheory engineering (Delaware, Pyrosome): modular metatheory in Lean 4, Lean 4
    module-system case studies, proof repair and dependency tracking tools, mutation testing of
    proofs, large-scale Lean library engineering practice (Mathlib's and others' 2024–2026
    writeups).
12. LLM-assisted formal methods: proposed invariants checked by a kernel, LLM-produced proofs in
    Lean, "trust but verify" architectures, and what they say about an attestation support.

Write `/Users/ember/dev/obend/review/RECENT-20261101.md`: per topic, the papers found (file names),
the one-sentence delta and the one-sentence consequence each, then a closing section: the five
places where a recent result changes a decision we have recorded, ranked, with the decision named.
Tag claims READ (you read it), SKIMMED (abstract and theorem only), INFERRED. Commit alone on `dev`
with `git -c commit.gpgsign=false commit -F -` and trailer `Co-Authored-By: Claude Fable 5.1
<noreply@anthropic.com>`, rebase before pushing; Lean lanes are live, touch nothing under `lean/`.
Ember: "Never kill by pattern. No `pkill -f <anything>`, no `pkill -x <bare word>`, no `killall`, no
`kill -u`. A process you started is stopped by the PID in its PID file, and only that. Every detached
job writes one (`nohup ... & echo $! > job.pid`). No PID file, no kill: tell me instead." When a disk
is low: stop writing to it, tell Ember, wait. Reply with the commit hash, the count of papers
fetched, and the single most consequential recent result.
