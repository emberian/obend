# Analyses of a world under a partial setup

Claude (Fable 5.1), 2026-11-01, on `review/WORLD-ANALYSIS-BRIEF-20261101.md`, for Ember. A study;
nothing lands in `lean/`. Read in full: `DESIGN.md`, `review/GENERALIZATION-20261031.md`,
`review/GENERATED-20261031.md` §2.4 and §3, `astra/ASTRA-EFFECT-LAWS-20261031.md` §3–§7,
`astra/ASTRA-SELECTION-20261031.md` §6–§7, `lean/docs/REPORT-RUNNER2-20261101.md`,
`REPORT-JOURNAL-20261030.md`, `REPORT-KINDS-20261101.md`, `REPORT-JUST-20261031.md` §3 (the
`Repair` record), and the modules `Slot.lean`, `Slot/World.lean`, `Fold.lean`, `Judge/Class.lean`,
`Intention.lean`, `Run/Spec.lean`, `Run/Shared.lean`, `Run/Fork.lean`, `Spec/Ecosystem.lean`,
`Receipt.lean` (declarations), `Vault/Store.lean` (header), the docstrings of `Law/Fold.lean`,
`Run/Fold.lean`, `Run/LawJudge.lean`, `Vault/Law.lean`, `Kind.lean`, `Judge/Instances.lean`,
`Run/Proofs/Shared.lean`, and `Journal/Journal.lean`'s two theorems. Tags: **READ** (in the tree or
a paper read today), **INFERRED** (follows from what was read, not stated there), **PROPOSED** (a
design). Literature fetched into `~/paperbin` today is listed in §8 with what could and could not be
extracted.

## 0. The one definition everything else is an instance of

**READ.** A world is `World V Fact` (`Slot/World.lean`): views `V`, `pin : V → Cell → Option Pin`,
and `holdsOfPin : Cell → Option Pin → Fact → Bool`, so that `holdsAt v f` is *computed* from the
pin of `cell f` (`holds_pin` is `rfl`) and `holds_congr` is a congruence, not a law. An admission
(`Fold.lean`) judges each row from the accumulator and the facts it `reads`, and `step_of_pins` says
two worlds agreeing on the pins of a row's reads give the row the same verdict. A receipt is the
accumulator's roots plus the openings of those reads (`receipt_sufficient`, `Receipt.recheck`).

**PROPOSED.** A *partial setup* is a view with some pins unknown:

```lean
/-- what an analyst knows of a view: a cell's pin, or `none`: unknown -/
abbrev Setup (V : Type) [World V Fact] := World.Cell V → Option (Option (World.Pin V))

/-- the views the setup describes: every known pin agrees -/
def ext (σ : Setup V) : V → Prop := fun v => ∀ c p, σ c = some p → World.pin v c = p
```

Every "partial" condition the brief names is one `Setup` (INFERRED, each from the module named):

| condition | the unknown cells | source of the unknown |
|---|---|---|
| a pin not yet committed | cells the next commits may move | the future (`Ledger.commit`, `tick`) |
| a member's grant unresolved | the member's grant cell | `Member.grants` not yet read |
| a package parent's version open | the owner's record line (`RecordLine`) | `Ecosystem.resolve` not run |
| a law not yet amended | the law cell (its digest) | the relaw write pending |
| a fork not yet stitched | every cell main moved since `Fork.epoch` | `Fork` sees no ledger record |
| a solver's answer pending | the cell whose pinned value commits to the evidence envelope (Astra D) | the producer |
| a stranger behind the dial | the cells whose openings the receipt withholds (`Dial.cited`) | disclosure policy |

The kernel is never in a partial setup: `pin v c` is total. Partiality is the *analyst's* condition,
the question asked before the view exists or by someone not shown all of it. That is why none of
this touches the kernel and why all of it must be judged by it (§6).

**The three readings of an unknown pin** (INFERRED; the literature in §8):

1. *Three-valued* (Bruns–Godefroid 1999; Kleene strong logic): a fact is `true | false | ⊥`; a
   slot's read is `usable | blocked d | open (d, u)` where `d` are the supports known dead and `u`
   those unknown.
2. *Set of completions* (Bruns–Godefroid 2000, "generalized model checking"): a claim is
   *necessary* (true at every `v ∈ ext σ`), *possible* (at some), or neither. Their theorem that
   three-valued checking reduces to two two-valued checks on the *optimistic* and *pessimistic*
   completions is, for a slot, the statement that `Slot.usable` is monotone in `holds`: set every
   unknown support true and false respectively, and the two reads bracket every completion. Their
   warning that the three-valued `⊥` can be an artefact when no more-complete structure makes the
   formula true is, for obend, exactly the gap between "no known dead support" and "some reachable
   view makes every support hold": the latter is reachability (§2.4), the expensive question.
3. *Symbolic* (Green–Karvounarakis–Tannen 2007): the verdict as a polynomial over the atoms
   `pin c = p`. For one row this is exact and finite because `reads acc r` is a finite list, so the
   verdict is a function of finitely many openings (`receipt_sufficient`); the provenance of a
   verdict is the set of openings it was computed from, and *why-not* (Chapman–Jagadish 2009) is
   the refusal's named dead supports, which `read_blocked_exact` already makes exact.

The slot's **support lattice** is the finite abstraction the brief asks for: for a candidate `c`
with `n` supports the state is the pair `(D, U)` of dead and unknown supports, `2^n × 2^n` at most,
and `(∅, ∅)` is usable, `D ≠ ∅` is blocked whatever `U`, `D = ∅, U ≠ ∅` is open. Everything in
§2 reads off this lattice or folds it along rows.

## 1. The analyses, ranked

Ranking by value to the first platform (a business ledger: members with grants, laws in force,
offline forks that must stitch) and by cheapness of the certificate a stranger checks. Cost classes
(the brief's (6)):

- **C1, cheap**: checked from the roots and finitely many openings; the cost is the row's `reads`
  (what `obend verify` already does).
- **C2, replay**: the certificate is a fold replayed from a root over a slice of the history; as
  expensive as the slice. With chained view roots (REPORT-RUNNER2's open decision, recommended
  there) a slice is checkable from a recent head, so C2 is bounded by the slice, not the history.
- **C3, attestable**: a universal claim over an unbounded domain (every future, every Core4 input),
  or a minimality claim whose search is not enumerated; the kernel records who said so.

| rank | analysis | question of the first platform | producer | certificate | cost | build |
|---|---|---|---|---|---|---|
| 1 | **Impact** (§2.1) | if this pin moves, what goes blocked, stale, behind, unjudged | the `reads` index (a Datalog closure) | the dependents with the opening each rests on | C1 | first |
| 2 | **Dry stitch and counterfactual replay** (§2.2) | were the fork stitched now, which rows conflict; were this law in force, which past writes refuse; were this grant revoked, which dispatches lose their citation | `Fork.replay` without `settle`; `Admission.run` under a substituted law | the conflict list, each a refusal with openings; the first divergence | C2 | second (one CLI verb over existing functions) |
| 3 | **Repair** (§2.3) | which re-pins unblock this candidate / restore this turn / resolve every section | MaxSAT or ASP over the support lattice | the plan, applied in a scratch fork, with the usable read at its end | C1 per step; minimality C3 | third |
| 4 | **Reachability and safety under partial knowledge** (§2.4) | can this candidate ever be selectable; is double-spend excluded; can a law be amended without the grant | finite enumeration where finite; invariant synthesis | a path, or a permanent dead support, or an inductive invariant over a finite row alphabet | C2 (path), C1 (permanent), C1 per row (invariant) | fourth |
| 5 | **Epistemic and provenance** (§2.5) | who could know this verdict; the minimal receipt; what a member relied on that moved; whose attestation it rests on | the three-valued fold over subsets of openings | an opening subset under which the verdict is decided; `Receipt.overall` | C1 | with 1 and 5 |

Why this order (INFERRED): Impact builds the one index (`reads : row → cells`) that replay, repair
and the epistemic questions all consume, and the journal has already built and proved that index
once for theorems (`Journal.slot`, `verdict_unaffected_iff`, `mem_closure_iff`). The dry stitch is
already implemented as a pure function (`Fork.replay`, `stitch_accounts`, `stitch_atomic`); it only
lacks a verb that does not `settle`. Repair's soundness theorem exists at `4753f62`. Reachability is
the one whose honest answer is often "attestable" and whose finite cases are already theorems.

## 2. Each analysis

### 2.1 Impact: the dependents of a cell

**READ.** The journal (`REPORT-JOURNAL` §1, §8) is this analysis for the Lean tree: cells are
declarations, pins are `(name, meaning)` hashes, a theorem is a candidate whose supports are the
closure of what its statement and proof cite, and `verdict_unaffected_iff` says the verdict is
`Slot.read`'s reading and nothing else; `mem_closure_iff` proves the closure exact. Over a world the
same construction has these candidates and supports (each an existing structure):

| dependent | its supports (`Fact`s naming cells) | goes |
|---|---|---|
| a slot's stored candidate `c` | `S.supports c` | `blocked`, naming the dead ones (`read_blocked_exact`) |
| a package turn `Turn` | each `Pin.supports` (the record line) | `stale pin` (`Ecosystem.admit`, `stale_iff_blocked`) |
| a cite in a page | the cite's identity or byte support | behind (`cite_stale_iff_blocked`, `following_cite_behind`) |
| an instance's kind pin | "the registry names version `v` of `K`" | refused by name (`effective_refuses_stale`) |
| an issued receipt | `R.pins : List (Cell × Option Pin)` | no longer current (`dated` names a past root) |
| a dispatch's decision | `citesOf cs₀ pre j h` | `DecisionsHeld` was at its view; a *new* dispatch would not be |
| a law's verdict on a write | the facts the machine probe read (`Run/LawJudge`: `LawFact`, the height; `Law/Fold`: `HeightIs`) | could change: the row must be re-judged |

**PROPOSED, the statement.** For a setup `σ` and a cell `c`, let `σ \ c` be `σ` with `c` unknown.
A dependent `x` is *affected by `c`* when its three-valued read under `σ \ c` is `open`:

```lean
def affected (S : Slot Fact Cand) (σ : Setup V) (c : World.Cell V) (x : Cand) : Prop :=
  ∃ u, read3 S (σ.forget c) x = .open [] u ∧ u ≠ []
```

and the *syntactic* dependents are `{x | ∃ f ∈ S.supports x, cell f = c}`. Two theorems
(§5, T2): `affected → syntactic` (the index is complete: by `holds_pin`, a read that cannot depend
on `c`'s pin is decided), and `syntactic ∧ no known dead support → affected` (the index is exact up
to known-blocked candidates, which are blocked whatever `c` does). For a fold rather than a slot,
`step_of_pins` is the same statement row by row: a row that does not read `c` is unaffected, and the
rows after it are affected only through the accumulator, which the fold threads; so the dependents
of a cell in a history are the rows that read it plus every row after the first affected one whose
reads include the accumulator's rest (for `Legal`: the spent tokens and the history; for the law
fold: the current value). That tail is why impact over a history is C2 in the worst case (a moved
pin early in a log can change every later verdict) and C1 for the common question (which *current*
candidates, turns, cites and receipts cite this cell).

**Producer.** The index is one relation `reads(x, c)` and `affected` is a closure over it: Datalog
(Bravenboer–Smaragdakis 2009 and Jordan–Scholz–Subotić 2016 are the evidence that whole analyses are
best *written* as Datalog and *run* by a synthesized engine). The engine is the producer; the kernel
checks the derivation (a Datalog proof tree is a why-provenance tree, linear to check). READ: the
Scry MCP's `datalog` tool is "bounded recursive graph walks as a JSON program of named id sets";
over an exported world (the journal's JSONL shape) it is one such producer. INFERRED: do not put a
Datalog engine in the kernel; the journal's `closureBy` with `mem_closure_iff` is the checked walk
and it is enough.

**Certificate and judge.** `ImpactCert := List (Dependent × Fact × Option Pin)`: each dependent with
the support naming `c` and `c`'s pin at `σ`. `check` re-reads each (`read3`); `Meaning`: every
listed dependent is affected, and (completeness clause) every dependent in the index that reads `c`
is listed or known-blocked. `sound` from T2; `complete` on the fragment "the index was built from
this world's `reads`"; `refutes` the clause "names a dependent that does not read `c`".

**First query.**

```
obend analyze impact commons/record@^2 --world .obend
  blocked   section Garden#3 candidate 2    support record(commons/record,^2)@pin 7 = 2.1.0
  stale     turn Garden@2026-11-01          pin intention commons/record ^2 @7 2.1.0
  behind    page Notes#cite 4               byte cite of commons/record/README@7
  rejudge   law Garden.budget on write #41  read record(commons/record,^2)@7
  current   receipt 0x3f…                   pins [(commons/record ^2, some 7)]
```

Each line is a refusal-shaped receipt (the dependent, the dead-to-be support, the opening) and
`obend verify` checks it by `read_blocked_exact`.

### 2.2 Dry stitch and counterfactual replay

**READ.** `Fork.replay step main F.escalated` returns the tentative state and the conflicts; `settle`
keeps main unless the conflicts are empty; `stitch_accounts` says every escalated row is accepted or
returned as a conflict with its refusal, `stitch_atomic` that the stitch is all or nothing, and
`stitch_double_spend` that a ticket main granted while the fork was offline is a conflict naming the
winner and the epoch. The law judge over a log is a fold whose world component is the consensus
height (`Law/Fold.lean`), and the runner's `Legal` is a fold (`Run/Fold.lean`).

**PROPOSED.** Three analyses, one function each, all existing:

1. *Dry stitch*: `(replay (jstep …) main.1 F.escalated).2`, computed and not settled. The
   certificate is the conflict list; each conflict is a refusal (`JRefusal.taken t winner epoch`,
   or a runner's own clause) and carries the openings the refusing step read; a stranger with main's
   root and the fork's escalated rows replays it (C2 over the fork's rows, not main's history).
   The analysis's value is that `stitch_accounts` makes it *complete*: nothing is dropped, so an
   empty answer is a theorem that the stitch would settle.
2. *Law amendment*: replay the law fold with `L'` for `L` from the root at which `L'` would be
   installed. `Meaning`: the list of rows at which the two folds first disagree, each with the
   clause `L'` refuses by. T3 (§5) is the statement that the first divergence is a row `L'`
   refuses and `L` admitted, or conversely, and that before it the two folds agree
   (`step_of_reads` at equal openings). Under the narrowing discipline (`package_never_widens`) a
   child law can only add refusals, so the divergence list is the exact set of past writes the
   amendment would have refused, *up to the first one*: after it the counterfactual history is a
   different history (the refused write never happened), and the replay must say so rather than
   continue as if it had. This is Balmin–Papadimitriou–Papakonstantinou's hypothetical query
   discipline (a what-if is a query over a hypothetically updated state, evaluated by pushing the
   update through the view definition); for a fold the "view" is the accumulator and the push is
   the replay.
3. *Grant revocation*: set the grant's fact false in the setup and read every dispatch's
   `citesOf cs₀ pre j h` (`DecisionsHeld`): the dispatches whose decision cited it are the ones that
   would not be admitted *again*; the ones already exposed keep their obligation (`AfterAbandon`,
   the ledger's durability). The analysis must say both halves; Astra D's "withdrawal affects future
   admissions; it cannot erase a prior grant from the history" is the rule and `DecisionsHeld`
   dated at the dispatch view is why.

**Judge.** `ReplayCert := { root; rows : List Row; verdicts : List (Outcome Clause) }`; `check`
re-runs the fold from `root` and compares; `Meaning`: the verdicts are the fold's. `complete`
everywhere (the fold is total); `refutes` on a verdict mismatch. Cost C2.

**First query.** `obend analyze stitch FORK --dry` (prints the conflicts, settles nothing);
`obend analyze replay --law Garden/_kind.md@new --from 0x…` (prints the first divergence and the
rows refused before the history would have changed).

### 2.3 Repair synthesis

**READ.** `Slot/Repair.lean` at `4753f62` (retired, recorded in `REPORT-JUST` §3): a `Repair` is an
audited step `act` with `establishes : holdsAt (act v) fact = true`; `Compatible r S c` is "every
requirement of `c` that holds at `v` still holds at `act v`"; `repair_sound`: a plan of compatible
repairs covering every dead support of a judge-passing candidate ends at a later view where the
candidate is usable. `clash_unsat`/`clash_refused`: one cell cannot hold pin 0 and pin 1, and
`Compatible` is what refuses the naive plan. `Intention.renew` is the one repair of a stale pin
(`renew_repairs`), and `Ecosystem.admit` says `stale pin`, `refused r`, or `diverged`.
ASTRA-SELECTION §6: three certificates must stay separate (exclusion witness, missing-requirements
list, executable repair offer), and "do not call an arbitrary explanation minimal".

**PROPOSED, the statement.** For a blocked candidate `c` at `v` with dead supports `D`:

```lean
structure Plan (V) := (steps : List (Repair V))
def Repairs (S) (v : V) (c : Cand) (P : Plan V) : Prop :=
  S.usable (holdsAt (applyPlan P v)) c = true
```

The *search* is the producer's: the supports of `c` are soft clauses to satisfy, the cells' version
laws (`ver_step`: forward only; `retired_step`: tombstones terminal) and the candidate's other
requirements are hard clauses, and a minimum-cardinality plan is a partial-MaxSAT answer
(Jose–Majumdar 2011: the CoMSS, "a set of soft clauses of minimum cardinality whose removal would
make Φ satisfiable", here the set of supports that cannot be jointly established) or an ASP
optimization (clingo, in paperbin; Meliou–Gatterbauer–Suciu's *how-to queries*, "how to change the
data to achieve this condition at bounded cost", are this problem in the database vocabulary and
they say so: "the adoption of SAT or MaxSAT solvers as general purpose tools"). The *check* is the
kernel's and it is a fork: apply the plan to a `Fork.at L d` (a scratch view that holds no shared
token and whose effects cannot leak), read the slot there, and settle nothing. `repair_sound` is
the judge's `sound`; `Compatible` is checked per step by re-reading the candidate's other supports
after it (C1 per step).

The three instances the brief names:

- *blocked slot* → the plan above; the certificate is the plan with the usable read at its end.
- *stale package turn* → `renew` each stale pin, then `admit`; the certificate is the new `Turn`;
  `diverged` is an honest outcome (the record grew a parent) whose repair is a new closure, not a
  re-pin. Which re-pins: exactly `t.pins.filter (!·.current v)`, by `stale_iff_blocked`; no search.
- *merge conflict* → each conflicted section is a slot with two candidates (`mergePage_pushout`);
  a resolution is one selection per section such that the page's laws admit the merged page
  (`Vault.Law.judge`, `judge_admits`). The product over sections is a CSP the producer solves; the
  certificate is the selection list and the kernel's check is `selectPatch` then `judge`.

**Judge.** `RepairCert := Plan × Reading`; `check` applies the plan in a scratch fork and reads;
`Meaning`: `Repairs S v c P`; `complete` on the fragment "every dead support is local
(`compatible_of_local`)", where the plan is the dead supports' own repairs in any order;
`refutes`: a step that is not `Compatible` (names the requirement it kills). Minimality is a
separate object: `Minimal P` is `complete` only when the domain of alternative plans is finite and
enumerated by the checker; otherwise it is the solver's attestation (C3), and the receipt says
`attested solver@rev`.

**First query.** `obend analyze repair Garden#3 --candidate 2` → `plan: renew commons/record@^2
(7 → 8); then usable, evidence [(record …@8 = 2.2.0, true)]`, or `no plan within 3 steps: support
(bells, 0x9a…) is a retired cell (blocked_forever)`.

### 2.4 Reachability and safety under partial knowledge

The brief's four questions have four different shapes; the honest analysis says which.

**(a) Can this member ever double-spend?** READ: it is a theorem, not an analysis:
`joint_reachable_ticket_exclusive` and `joint_once` at every reachable joint configuration,
`stitch_exclusive` across every stitch, `exposed_once` across crashes. INFERRED: what remains is a
*census*: every consuming operation of the deployment has `sp.consumes o = some t` and every
exposure goes through `jrun` (Astra B's premise 4: "an unmodeled admin write … is outside the
claimed system"). `obend analyze safe double-spend` lists the operations and the one path by which
each reaches the ledger; the certificate is that list and the theorem's name; C1.

**(b) Can a law be amended by someone without the grant?** READ: `Vault.Store.commit` refuses a
change of a law line by anyone but the owner or a member granted `relaw`; `select_needs_grant` is
the same shape for selection; `legal_law_admitted` for the runner. Under a partial setup (the
member's grants unknown) the three-valued read says `open` and names the grant cell the answer
depends on; that is the answer. C1.

**(c) Is this candidate ever selectable?** This is generalized model checking: does some `v' ∈ ext σ`
reachable from `v` make `S.usable (holdsAt v') c = true`. INFERRED, the three answers and their
certificates:

- *No, permanently*: a support of `c` names a retired cell (`blocked_forever`), or is pinned at a
  version the cell has left (`stale_blocked_forever`, or the collision disjunct). Certificate: the
  support and the pin; C1. This is the pessimistic completion's verdict and it is final.
- *Yes, by this path*: a list of rows from `v` to `v'` accepted by the admission, with the usable
  read at `v'`. Certificate: the path; C2 (replay). The quantifier shape is `∃M ∃run`
  (`Shape.existsRun`).
- *Unknown*: no known dead support and no path found within depth `d`. The honest verdict is
  `uncovered` at grade `d` (`Judge.Verdict.uncovered`, `mono` in the grade); never "unreachable".

Where the state space is finite the third answer disappears: the open pins range over finite
domains for protocol automata (`Prot S Hole A i` over a finite `Sig`), kind precedence (`KindCell`
parents, C4 over a finite kind set), package closures (`close` over a finite `View.releases`), the
ledger's grant structure (a finite `Tok`), and the `.obend` law fragment (comparisons of natural
fields, `monotone`, `writeOnce`: quantifier-free linear arithmetic, decidable). It does not
disappear for Core4 laws in general (`lawOf` emits any closed term; the machine decides one input
in bounded ticks, never all inputs) nor for the version order (`Ver` is a chain without an upper
bound). The abstraction that makes a finite space is the support lattice of §0: the analysis runs
over `(D, U)` states, with a pin move's effect on `(D, U)` as the transition, and a completion is
realizable only by a cell whose `holdsOfPin` admits the needed pin, which is where the optimistic
answer can be an artefact (Bruns–Godefroid 2000's point) and must be reported as `open`, not `yes`.

**(d) Is the diamond resolvable?** READ: `close` decides it at a view (`incompatible` names the two
routes). Under a partial view (a record line open) enumerate the finite candidate lines, run
`close` for each, report the set that resolves. Certificate: the `Turn` per resolving line, checked
by `admit`; C1 per line.

**Quantifier shapes** (Astra §6 and `Receipt.Shape`), as certificates:

| shape | certificate | checked by |
|---|---|---|
| `∃M ∃run` | one path | replay (C2) |
| `∃plan ∀M ∀r` | one plan and an inductive invariant preserved by every completion's rows | per-row check over the finite row alphabet (C1 per row); over an infinite alphabet, attestable |
| `∃policy ∀M ∀r` | a policy (a function of observations) and the same invariant on the product | as above, with non-anticipation checked by the plan's hole discipline (`ReplansUnentered`) |
| `∀M ∃plan` | a table of plans, one per completion | complete only for an enumerated finite completion set; otherwise C3 |

The product-invariant check is Astra C's `Init ⊆ J, Step(J) ⊆ J, J ∩ Bad = ∅` over the audited
fold; the invariant is the producer's (SMT, abstract interpretation, a person) and the kernel checks
the three inclusions row by row. Stein–Chang–Sridharan's demanded abstract interpretation is the
right producer discipline for keeping such an invariant live under edits ("program edits,
client-issued queries, and evaluation of abstract semantics are all treated uniformly"; demanded
results equal the batch results), which is also what the journal's incremental export wants to
become; it is a producer, not a judge.

**First query.** `obend analyze reach Garden#3 --candidate 2 --depth 4` → `permanent: support
(bells, 0x9a…) retired at view 0x…` or `path: [world 0x…, dispatch renew …]` or
`uncovered at depth 4; open supports: [record(commons/record,^2)]`.

### 2.5 Epistemic and provenance

**READ.** `read_congr` is distributed knowledge over the holders of the pins a candidate's supports
name (GENERATED §3.2, "the definition unfolded"); `Receipt.pins` lists those cells; `Receipt.overall`
and `ceiling` compute whose attestation a receipt rests on and refuse a `checked` claim no check
stands behind; the dial is `full | cited | bit` with `dial_invariant` and `accepts_cited_sound`;
`recheck_covers` requires the openings to cover every read.

**INFERRED.** Four questions, each a computation already latent:

- *Who could know this verdict at this view?* The group `G = cells (reads acc r)`'s holders; it is
  `pinsOf v (reads acc r)` (`Receipt.pinsOf`). No search. C1.
- *What is the minimal receipt that convinces a stranger?* A subset `O' ⊆ openings` such that the
  three-valued verdict of the row with every opening outside `O'` unknown is decided. By
  `receipt_sufficient` applied to each completion of the unknown openings, a decided three-valued
  verdict is the verdict at every world agreeing with `O'`, so the stranger needs `O'` only. That is
  the disclosure dial made exact: `cited` today is "all reads"; the minimal position is "a prime
  implicant of the verdict over the reads". Finding one is a search (the producer's); checking it is
  `2^|openings \ O'|` re-runs of the step at the unknown completions, which is cheap when the
  withheld set is small and is the brief's price for confidentiality (Astra C's redaction boundary,
  proved rather than asserted). The check needs no change to `Receipt`: it is a function
  `decided3 : Admission → Acc → Row → List (Fact × Option Bool) → Bool` with its theorem.
- *What did a member rely on that has since moved?* Impact (§2.1) over the member's dispatch
  receipts: the `pins` entries whose pin at the current view differs. C1.
- *Whose attestation does this verdict rest on?* `Receipt.overall`, after `ceiling` against what
  the verifier ran. Already built; the analysis is to run it over a history and report the
  attested principals and revisions a verdict transitively rests on (a receipt's `prev` chain plus
  the attested supports of each). C1 per receipt.

Where epistemic *model checking* (MCMAS: interpreted systems, CTLK over OBDDs; MCK: the
observational, clock and perfect-recall interpretations) would add something: only when there is
more than one knower with a protocol between them, that is, the shared-World layer (several runners,
Halpern–Moses's shared step). Then "runner `i` knows the ticket is granted" under the *observational*
interpretation is "every joint configuration indistinguishable to `i` (same projection) has the
grant", and `joint_coupled` (every runner's world is the ledger) makes the ledger's record the
observation, so the question reduces to a predicate on the record: C1. Under *perfect recall* the
indistinguishability is over logs, which is the frame GENERATED §3.4 proposed
(`exclusion_not_local`). Neither needs an epistemic model checker in the kernel: the worlds are
finite records and the certificate is the set of indistinguishable records with the predicate
checked on each.

**First query.** `obend analyze knows RECEIPT.json --minimal` → `openings needed: 2 of 5
[(height, 41), (record(commons/record,^2)@7, true)]; decided: ok`.

## 3. The state space, stated once

**READ / INFERRED.** The configuration of the first platform is a joint configuration `JCfg`: the
ledger's record (`raw : W`, `spent`, `grants`, `height`) and each runner's controlled configuration
(its log, plan, history, stored selections). The raw world of the vault is a `Store` (pages'
histories, members' grants, the turn). Views are records; pins are version states (`Ver`) read as
digests (`pinOf`); the step relation is `jrun`.

| component | domain | finite? | analysis over it |
|---|---|---|---|
| a cell's pin | `Option Pin`, a digest of `Ver` | the *reachable* pins are a chain (`ver_step`), unbounded above | the support lattice abstracts it to known/dead/unknown |
| a slot | candidates × supports | finite | exact |
| a protocol | `Prot S Hole A i` | finite for a finite `Sig`; holes bounded by `interp`'s depth | exact up to the depth, stated in the receipt |
| kinds, C4 | `KindCell` parents, precedence lists | finite | exact (`linearize` is proved) |
| packages | `View.releases`, record lines | finite per view | exact (`close`) |
| tokens | `Tok`, `spent`, `grants` | finite | exact; exclusion is a theorem |
| `.obend` laws | comparisons of natural fields | ℕ^k, decidable fragment | exact by decision procedure (a judge to register) |
| Core4 laws | closed terms, run by the machine | one input in bounded ticks; all inputs undecidable | enumerative on finite pin domains; else attestable |
| the version order | `Ver`, `Past` | unbounded | the future is never enumerated; claims about it are invariants or attestations |

The one abstraction the brief asks for is therefore not new: it is the slot's `(D, U)` lattice for
reads, the fold's openings vector for rows, and the ledger's `spent` set for tokens. Each is finite
per question, and each is what the existing theorems are already stated over.

## 4. The analysis as a judged subsystem

**READ.** `Judge Obj Cert` has `check : Nat → Obj → Cert → Verdict`, `sound`, `refuted` on refuting
clauses, `complete` on a `Fragment`, `mono` in the grade; a `Format` registers a judge on bytes with
a trust base, a regime (`decidable | semidecidable | attestable`) and a planted bad certificate
without which it cannot be registered (`trivial_unregistrable`).

**PROPOSED.** Every analysis of §2 is one `Format` in `Judge.registry`, and the analyzer (the
Datalog walk, the solver, the replay, the enumeration) is never in the kernel. Which cost class each
certificate falls in, and its regime:

| analysis | certificate | regime | trust base | the planted bad certificate |
|---|---|---|---|---|
| impact | dependents with openings | decidable | kernel | a dependent that does not read the cell |
| dry stitch, replay | rows and verdicts from a root | decidable | compiled (the fold runs as code) | a verdict the fold does not give |
| repair | a plan and the final read | decidable; minimality attestable | compiled | the clash plan (`clash_naive`) |
| reach: permanent | a retired or stale support | decidable | kernel | a support of a live cell |
| reach: path | a path | decidable | compiled | a path with a refused row |
| reach: invariant | `J` with the three inclusions | decidable over a finite row alphabet; else semidecidable | compiled | `J := True` (fails `J ∩ Bad = ∅`) |
| minimal receipt | an opening subset | decidable | kernel | the empty subset on a row that reads something |
| attestation chain | principals and revisions | decidable (it is a projection) | kernel | a principal the chain does not name |

The two that are *only attestable* in general: minimality (of a repair, of a receipt) beyond an
enumerated domain, and any universal claim over Core4 laws or the unbounded future. The receipt
says `attested solver@rev` and the theorem concludes that a live, authorized assessment was relied
on (Astra D's third mode), never that the claim holds.

## 5. `Obend/Analysis/` and its first three theorems

**PROPOSED.** A library beside the kernel; imports `Obend.Slot.World`, `Obend.Fold`,
`Obend.Receipt`, `Obend.Intention`, `Obend.Run.Fork`; nothing in `Obend/` imports it.

```
Obend/Analysis/Setup.lean    Setup, ext, Three, holds3, read3, Reading3, forget; T1
Obend/Analysis/Impact.lean   the reads index over slots, intentions, receipts, dispatch cites; T2
Obend/Analysis/Replay.lean   counterfactual fold, first divergence, dry stitch; T3
Obend/Analysis/Repair.lean   Slot/Repair.lean restored from 4753f62 as an analysis, check in a fork
Obend/Analysis/Reach.lean    permanent / path / invariant certificates
Obend/Analysis/Know.lean     holders, decided3, minimal openings, attestation chain
Obend/Analysis/Format.lean   the Formats above, registered
Obend/Analysis/Cli.lean      obend analyze …
```

`Setup.lean`:

```lean
inductive Three | t | f | u  deriving DecidableEq, Repr

/-- a fact under a setup: computed from the pin when known (`holdsOfPin`), unknown otherwise -/
def holds3 (σ : Setup V) (f : Fact) : Three :=
  match σ (World.cell f) with
  | some p => if World.holdsOfPin (World.cell f) p f then .t else .f
  | none => .u

inductive Reading3 (Fact Cand : Type)
  | empty | rejected (c : Cand)
  | usable (c : Cand) (evidence : List (Fact × Bool))
  | blocked (c : Cand) (dead : List Fact)              -- known dead, whatever the unknowns
  | open (c : Cand) (dead unknown : List Fact)         -- dead = [] : could go either way

def read3 (S : Slot Fact Cand) (σ : Setup V) : Option Cand → Reading3 Fact Cand
```

with `read3` the obvious case split on `(S.supports c).filter (holds3 σ · = .f)` and
`… = .u`.

**T1, the bracket** (`read3_sound`): the three-valued read is sound against every completion.

```lean
theorem read3_usable (S) (σ : Setup V) (c : Cand) (ev) (h : read3 S σ (some c) = .usable c ev) :
    ∀ v, ext σ v → S.read (holdsAt v) (some c) = .usable c (S.evidence (holdsAt v) c)

theorem read3_blocked (S) (σ : Setup V) (c : Cand) (d) (h : read3 S σ (some c) = .blocked c d) :
    ∀ v, ext σ v → ∃ d', S.read (holdsAt v) (some c) = .blocked c d' ∧ d ⊆ d'
```

Proof: for `f` with `σ (cell f) = some p`, `ext σ v` gives `pin v (cell f) = p`, so
`holdsAt v f = holdsOfPin (cell f) p f` by `holds_pin`; a usable three-valued read has every support
known true, so `dead_eq_nil_iff` and `read_of_usable`; a blocked one has `d` known false, so
`mem_dead_iff` puts each in `S.dead (holdsAt v) c`. Twenty lines, from `holds_pin` alone. Tooth:
mutate `holds3` to return `.t` on unknown; `read3_usable` fails at the returning world
(`World.Returning`).

**T2, the index is complete and exact up to known blocks** (`affected_reads`,
`reads_affected`):

```lean
theorem affected_reads (S) (σ : Setup V) (c : World.Cell V) (x : Cand)
    (h : ∃ d u, read3 S (σ.forget c) (some x) = .open x d u ∧
                 read3 S σ (some x) ≠ .open x d u) :
    ∃ f ∈ S.supports x, World.cell f = c

theorem reads_affected (S) (σ : Setup V) (c : World.Cell V) (x : Cand) (hj : S.judge x = true)
    (hf : ∃ f ∈ S.supports x, World.cell f = c) (hd : ∀ f ∈ S.supports x, holds3 σ f ≠ .f) :
    ∃ u, read3 S (σ.forget c) (some x) = .open x [] u ∧ u ≠ []
```

Proof: `forget c` changes `holds3` only on facts whose cell is `c` (one `simp` on `Setup.forget`);
if none of `x`'s supports names `c` the two reads are equal, contradicting `h`; conversely with no
known dead support and one support naming `c`, that support is `.u` under `forget`, so the read is
`.open x [] u` with it in `u`. The fold form is `step_of_pins` with `hp` discharged by the index,
stated as `impact_fold`: a row none of whose reads names `c` has the same verdict at any world
differing from the accumulator's only at `c`.

**T3, the first divergence of a counterfactual replay** (`replay_divergence`): for two admissions
`A A'` over the same rows, world, rest and `reads`, differing only in `step` (the law), and a root
`a`:

```lean
theorem replay_divergence (A A' : Admission W Rest Row Fact Clause)
    (hr : A.reads = A'.reads) (hl : A.look = A'.look) (a : W × Rest) (rows : List Row) :
    (∀ pre, pre <+: rows → A.run a pre = A'.run a pre) ∨
    ∃ pre r post b, rows = pre ++ r :: post ∧ A.run a pre = .ok b ∧ A'.run a pre = .ok b ∧
      A.step b r ≠ A'.step b r
```

Proof: induction on `rows` with the accumulator; `foldlM_cons`; the first row at which the steps
disagree is the witness, and before it the folds are equal by the inductive hypothesis. Corollary
(`amend_refuses`): when `A'` only refuses more (`∀ b r x, A'.step b r = .ok x → A.step b r = .ok x`,
the narrowing discipline), the divergence is a row `A'` refuses that `A` admitted, and the replay
reports it with `A'`'s clause and the openings of `A.reads b r`. The dry stitch's theorem is
`stitch_accounts` and needs nothing new; `Replay.lean` only exposes `replay` without `settle`.

Three, as the brief asks. The fourth that matters is `decided3_sound` for the minimal receipt
(`Know.lean`): a decided three-valued step at a subset of openings is the step's verdict at every
completion, by `receipt_sufficient` once per completion of the withheld openings.

## 6. What the kernel must not do, and what this costs

**INFERRED.** Nothing in `Obend/` changes. `Slot/Repair.lean` comes back under `Analysis/`, not
`Slot/` (the Just report retired it because nothing in the kernel consumed it; an analysis
consumes it). The `.obend` law fragment's decision procedure is a new `Format` and belongs with
the analyses, not in `Law/`. The CLI gains one verb with sub-verbs. The census gains the
`Analysis` modules' constants under their own cohort so the kernel's count is unchanged.

The kernel never calls an analyzer: a law may not consult the impact index or a solver while judging
(Astra D, "inside a law must preserve the effect boundary"); an analysis result enters the world
only as a candidate's support whose cell pins the certificate (Astra D's "a cell whose pinned value
commits to the entire evidence envelope"), so a stale analysis is a stale support, by name.

## 7. What is a stretch, and why

- **Generalized model checking over Core4 laws.** A law is any closed term; "is there a completion
  under which this write is admitted" is the machine's halting on all inputs. Honest only on the
  `.obend` fragment or an enumerated finite pin domain; elsewhere `uncovered` at a depth, or an
  attestation. The brief's "where it is not (Core4 terms)" is right and the abstraction does not
  rescue it: the support lattice abstracts *facts*, not the law's computation on them.
- **`∀M ∃plan` completeness.** A table of plans is complete only for an enumerated completion set
  (Astra C's "a table of witnessed pairs is complete only for a certified finite domain"); for the
  version order's unbounded future there is no such set. Report the table's domain in the receipt.
- **Minimality.** A minimal repair or minimal receipt is the solver's claim unless the checker
  enumerated the alternatives; call it `attested` (Astra D: "do not call an arbitrary explanation
  minimal"). The exact-up-to-known-blocks impact set (T2) is the one minimality that is a theorem.
- **Who could know, beyond pin-holders.** The frame's agents are cells; a member's knowledge is the
  pins it holds *and* the receipts it has been shown, and the second is the dial, a policy. "Could
  know" is therefore a lower bound (pins) and an upper bound (pins plus every receipt issued to it);
  the gap is not a theorem to prove but a disclosure to record.
- **Liveness.** "Will the fork stitch cleanly if it waits" depends on other members' futures;
  Astra B's progress is a separate contract with fairness premises. The dry stitch answers "now";
  nothing answers "ever".
- **Probabilities over completions.** Refused, as Astra §6 refuses them: completions have no
  canonical measure, and counting returned witnesses is invalid when the producer does not
  enumerate.
- **Abstract interpretation of protocols as a kernel analysis.** The protocol-verification
  abstractions (pattern-based secrecy abstractions, Verimag's Hermes line; not fetched today, cited
  from memory) over-approximate the intruder's knowledge; obend's protocols are typed holes with a
  checked envelope (`HasProt`), so the question they answer is the hyperlaw question (Astra C), a
  product invariant, and belongs to that design, not to this study's five.
- **Epistemic model checking.** MCMAS and MCK are the right tools for interpreted systems with
  several agents and a protocol; obend's one-ledger platform reduces knowledge to a predicate on the
  record (§2.5), and the perfect-recall frame over logs is GENERATED §3.5's unbuilt thirty lines.
  Building an epistemic model checker into the kernel would be the "organizing account of a
  single-writer kernel" GENERATED §3.4 already refused.
- **Datalog in the kernel.** The right notation for the index, the wrong thing to trust: the
  derivation is the certificate, the walk is `closureBy`, the engine (Soufflé, Scry) is a producer.

## 8. Literature

In `~/paperbin` before today, read for this study: Stein–Chang–Sridharan 2021 (demanded abstract
interpretation; §2.4), Green–Karvounarakis–Tannen 2007 (provenance semirings; §0), Halpern–Moses
1990 (§2.5), Alviano et al. 2019 and Gebser et al. 2014 (ASP proofs and clingo; §2.3). Fetched today
(READ where text extracted):

| file | used for | extracted |
|---|---|---|
| `bruns-godefroid2000-generalized-model-checking-partial-state-spaces` | §0: optimistic/pessimistic completions reduce 3-valued checking to two 2-valued checks; `⊥` can be an artefact; generalized semantics asks for a completion | yes |
| `balmin-papadimitriou-papakonstantinou2000-hypothetical-queries-olap` | §2.2: what-if as a query over a hypothetically updated state | PDF present; text extraction garbled (font encoding); cited from memory |
| `jose-majumdar2011-cause-clue-clauses-error-localization-maxsat` | §2.3: partial MaxSAT, the CoMSS as the minimal set to drop | yes |
| `chapman-jagadish2009-why-not` | §0: why-not as the "picky manipulation" that excluded the unpicked item | yes |
| `meliou-gatterbauer-suciu2011-reverse-data-management` | §2.3: how-to queries, SAT/MaxSAT as the general tool | yes |
| `lomuscio-qu-raimondi2009-mcmas-model-checker-multi-agent-systems` | §2.5, §7: interpreted systems, CTLK, OBDDs | yes |
| `gammie-vandermeyden2004-mck-model-checking-knowledge` | §2.5: observational, clock, perfect-recall interpretations | yes |
| `emerson-namjoshi1995-reasoning-about-rings` | §2.4: cutoffs for parameterized rings (the finite-instance reduction) | PDF present; text extraction garbled; cited from memory |
| `bravenboer-smaragdakis2009-doop-strictly-declarative-points-to`, `jordan-scholz-subotic2016-souffle-synthesis-of-program-analyzers` | §2.1: whole analyses written in Datalog, run by a synthesized engine | yes |

Not fetched (paywalled or blocked today; cited from memory, so INFERRED where used):
Bruns–Godefroid 1999 (CONCUR; the partial Kripke structure and completeness preorder, restated in
the 2000 paper's §3 which was read), Huth–Jagadeesan–Schmidt 2001 (modal transition systems:
may/must transitions and refinement, the transition-side analogue of the support lattice),
Clarke–Grumberg–Peled (the book), Bozga–Lakhnech–Périn 2003 (pattern-based secrecy abstraction).

## 9. Decisions for Ember

1. **Build Impact first** (`Setup.lean` + `Impact.lean`, T1 and T2), because its index is what the
   other four consume and the journal has already proved the construction once.
2. **Restore `Slot/Repair.lean` from `4753f62` under `Analysis/`**, not `Slot/`: its theorem is the
   repair judge's `sound`, and the check is a scratch fork.
3. **Chain the view roots** (REPORT-RUNNER2's open decision): every C2 certificate here is a slice
   from a root, and a chained root is what lets a stranger start the slice at a recent head.
4. **The minimal receipt changes no type**: `decided3` is a function beside `recheck`, and the dial
   gains a fourth position only in the CLI.
