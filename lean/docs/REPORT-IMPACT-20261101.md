# Report: lane Impact (2026-11-01)

Brief: `lean/docs/LANE-IMPACT-BRIEF-20261101.md`; design: `review/WORLD-ANALYSIS-20261101.md` §2.1,
§2.2, §5, corrected by `review/GEMINI-CHECKPOINT-20261101b.md` §3 before the first line (a partial
cell is its domain of admissible pins, not a support list).

## What landed

| item | where | state |
|---|---|---|
| (1) `Setup`, `holds3`, `read3`, T1 | `Obend/Analysis/Setup.lean` | proved; tooth |
| (2) the reads index, `affected`, T2 | `Obend/Analysis/Impact.lean` | proved; tooth |
| (3) the analysis as a judge, a planted bad certificate | `Impact.lean` (`impactJudge`), `Obend/Analysis/Format.lean` (`impact@1`) | proved |
| (4) `obend analyze impact` on a vault and a workspace, the test, the mutation tooth | `Obend/Analysis/{Worlds,Cli}.lean`, `Main`, `tests/analysis/run-impact.py` | 32/32 |
| (5) `obend analyze replay` | `Obend/Analysis/Replay.lean`, `Cli.lean` | done, with T3 proved |

Nothing in `Obend/` outside `Analysis/` imports it except `Main` (the verbs) and the census. No
sorry, no axiom; the census covers the six new modules. No former theorem was touched.

## What is proved

**Setup** (`Setup.lean`). A `Setup V` is, per cell, a `range` (a finite list of pins, or `none`:
any) and `known` supports with their values; a cell's `domain` is its range less the pins that
disagree with a known support of it; `ext σ v` says every cell's pin at `v` is admissible.
`holds3 : Fact → Three` (`known b | open | uncovered | contradiction`):

- `holds3_sound`: `.known b` is `b` at every completion; `holds3_contradiction`: a contradictory
  cell has no completion;
- `holds3_exact`, `holds3_open_iff`: on a finitely ranged cell, `.known b` iff the domain is
  non-empty and every admissible pin gives `b`; `.open` iff two admissible pins disagree. On an
  unbounded cell a fact is decided only when it is itself known (both ways: contradiction);
  otherwise `.uncovered`, which is where a Core4 law's verdict over every pin lands;
- the degenerate instances: `ofMap` (the three-valued map, `holds3_ofMap_some/none`, `ext_ofMap`:
  its completions are the views agreeing with every known pin, the design's `ext`), `ofView`
  (`holds3_ofView`, `ext_ofView`);
- `move`/`forget`: `holds3_move_ne` (no other cell's reading changes), `holds3_move_one`,
  `holds3_forget`.

`read3` reads a slot under a setup: `usable | blocked dead | excluded supports | undecided unknown |
contradiction f | rejected | empty`. `excluded` is Gemini's same-cell case: no support is known
dead, yet every admissible pin of one finitely ranged cell kills one of the candidate's supports on
it (Kleene's per-fact reading calls it open). **T1 `read3_sound`**: at every completion the
two-valued `Slot.read` is the one the three-valued read covers (usable with the same evidence;
blocked naming at least the known-dead supports, or one of the excluding cell's; a contradiction has
no completion). `read3_usable`, `read3_blocked`, `read3_contradiction` are its cases.

**Impact** (`Impact.lean`). T2: `read3_congr`; **`affected_reads`** (a candidate whose read changes
when a cell is re-ranged has a support naming the cell: the index is complete); **`reads_affected`**
(a judged candidate reading the forgotten cell, its other supports known true, reads `undecided`
naming it: exact up to known blocks). For folds: `foldIndex` (every row the fold reaches with
`Admission.reads` at its accumulator), `impact_row` (a row not reading the moved cell keeps its
verdict, from `step_of_reads`), `impact_prefix` (the fold before the first indexed row reading it is
unaffected).

A concrete move is a `Question` (base view, dependents `Dep` with kind/name/judge/reads, cell, new
pin). `moved_holds`: every view holding the new pin and the base elsewhere reads `movedHolds`;
`holds3_moved`, `ext_moved` tie the move to `Setup` (`(ofView base).move cell [pin]`). `affected`
lists each dependent that changes with the opening it rests on (the support naming the cell and its
value at the new pin). `Meaning q ls`: every line holds, read off `holdsOfPin` and the base
(`LineHolds`), and every dependent that changes (`Changes`: a row reading the moved cell whose pin
moved, or a judged candidate whose usability differs) has a line. **`affected_exact`**: the
producer's list has that meaning. **`line_blocked`**: a `blocked` line's dependent reads blocked at
every view holding the new pin, its dead list being exactly the supports that fail (by
`read_blocked_exact`) and naming the line's support; `line_restored`; **`unlisted_unchanged`**: under
any accepted list, an unlisted judged candidate's usability at every moved view is the base's.

`impactJudge : Judge (Question V) (List (Line Fact))`: `check_sound`, `check_complete`; complete on
every question (the producer's list), monotone (grade-free), never refutes (a bad list says nothing
of the move).

**Format** (`Format.lean`). The exported table (`TView`, `TFact`: each support lists the pins at
which it holds) is a `World` (`tableWorld`), so every theorem above is about the exported question.
`impact@1`: decidable, compiled trust; `bad_refused` (a line resting on a support of another cell:
`doesNotRead`). `embed_behind`: the honest prediction for a following embed whose page moved.
**Tooth `drop_read_misses`**: an index that drops a dependent's last read predicts nothing for that
embed, and the checker refuses it as `missing`. Also `#tooth affected_exact by mutation indexReads`
and `#tooth read3_sound by mutation Setup.holds3` (every support `.known true`).

**Replay** (`Replay.lean`). **T3 `replay_divergence`**: two admissions over the same rows from the
same root give the same fold, or there is a first row their steps judge differently at an
accumulator both reached. `amend_refuses`: when the amended admission only refuses more, that row is
one it refuses.

## The worlds and the verbs

`obend analyze impact CELL@PIN --world PATH [--turn TURN.json] [--out RECEIPT.json]`:

- a **vault**: a cell is a page, a pin its history (`vN`); the move is a version (`N`), `retired`,
  or a file the owner would write (`ownerWrite`, the write `obend open` makes; a refused write is a
  `note:` and moves nothing). Dependents: every cite of every page's current version (`behind` is
  the cite intention's blocked read) and every page's law row (reads the page and its kinds' pages).
- a **workspace**: a cell is a record line `NAME^MAJOR`, a pin `P names V` / `P retired`; the move is
  `P:V`, `P:retired`, or another workspace file's line. Dependents of the turn (or of the entry's
  closure): the turn (`stale`), its intention pins (`blocked`), the closure's law (`rejudge`).
- `CELL@?` forgets the cell and prints `read3` under the forgetting setup (`open`, or `known-dead`
  when another support already blocks it).

The list is checked by `impact@1` before it is printed; `--out` writes `{kind: impact, object,
certificate}`, which `obend verify` re-checks through `Format.checkBytes` with no producer state.

`obend analyze replay PAGE@FILE --world DIR`: every write of every page PAGE's laws judge, re-judged
by `Vault.commit` under the laws in force and with PAGE amended; the first write judged differently,
per page, with both verdicts.

`tests/analysis/run-impact.py` (32 checks): the owner's write of a new Beta predicts Alpha's embed
`behind` and Beta's law row `rejudge`, nothing for the identity link or the untouched block quote;
`obend status` after the write agrees cite by cite. Rolling Beta back to v1 predicts the embed
`restored`; writing the old text back agrees. On `three-package`, re-pinning `ext/left^1` and moving
`commons/counter^1` each predict the turn `stale` resting on that line; `obend admit` at the moved
records names the same line. A move to the pin already named predicts nothing; `admit` admits.
Receipts verify; flipped opening → `wrong-opening`; dropped line → `missing`; a line on a support
the dependent does not read → `does-not-read`. The tooth: `--tooth drop-read` predicts nothing for
Alpha's embed, which the re-judgment shows behind; the checker and `verify` refuse it `missing`.
Replay: a journal kind's `new.words <= 20` amended to `<= 10` makes Mon's second write (12 words)
diverge; a vault with the amended kind in force from the start, given the same writes, refuses that
write with the same words.

## Builds

On dregg-build2 (`~/obend/impact-wt2`, a worktree of `~/obend/repo`) at `7e0f4fe`, rebased on `dfc26d6`: tier 1
`lake build` green, `lake build obend` green; `tests/analysis/run-impact.py` 32/32,
`run-receipts.py` 31/31, `run-logic.py` 20/20, `run-workspace.py` 30/30 (the `verify` dispatch now
passes through `Analysis.Cli.verifyOr`). Tier 2 (`lake build Obend.Census Teeth`): green; the census reports 38089 constants, none on sorryAx or a declared axiom (27 on native_decide, none of them new). A first tier-2 run on the pre-`05beecd` base hung in `CheckTeeth`; it was left running (its PID file names a wrapper shell, not `lake`) in `~/obend/impact-wt`.

## Limits

- The exporters' faithfulness is by construction, not a theorem: `Worlds.lean` computes each listed
  pin with the native read (`Obend.Doc.holds`, `Ecosystem.holds`), and the table is exact on the
  pins the question names. A verifier of a receipt checks the table's arithmetic, not that the
  table is the world's (see the decision).
- The vault's pin label `vN` names a history by its length: exact for the moves offered (a prefix
  of the current history, or it extended by a write); two replicas' different histories of one
  length would collide, which is `World.Collides` in label form.
- Section candidates of a conflicted page are not yet dependents of the vault export (cites and law
  rows are). Receipts are dependents generically (`Kind.receipt`: a receipt's pins as "this cell
  holds this pin" supports) but neither CLI world indexes stored receipts yet.
- Law rows are `rejudge`, not exact: whether the verdict actually changes is replay's question.
- Replay re-judges each write as the owner's at the write's version; a law reading the author or
  the turn is replayed with those values, not the historical ones (the store does not record them).

## The decision for Ember

An impact receipt is checked against the table it carries. Should it also name the world's root
(the digest of `.obend/world.json`, or of the workspace's records and releases), so that `obend
verify --world PATH` re-exports the question from the world and refuses a receipt whose table is not
the world's? That makes the exporter's faithfulness a checked support rather than the producer's
word, and it is the same move as chaining the view roots (`WORLD-ANALYSIS` §9.3): a receipt dated by
a root a stranger can open.
