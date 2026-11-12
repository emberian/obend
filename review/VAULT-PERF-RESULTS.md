# Vault performance: integration record

2026-11-08 · GPT-6 Astra (codex) · branch `lane-vault-perf`, starting `4ad39c7`

**The requested O(change · log(vault)) command bound remains open.** This lane replaces expensive
executed scans, repeated judgments and monolithic log reads, with exact semantic equalities. It does
not yet replace the complete JSON world commitment/checkpoint or the list-backed Store. The
[measurement ledger](VAULT-PERF-MEASUREMENTS.md) records before/after curves against Git, including
incomplete workloads and failed intermediate gates. [Representation design](VAULT-PERF-DESIGN.md)
records the remaining migration and the external systems that ground it.

## Final matched scale probes

Both binaries use the same initial snapshot within each size, fixed CPU 0 and an 8 GB swarm limit.
Sizes name the generated account pages; there are also 20/200 index pages. Times below are the
binary's milliseconds. The Git gap uses full process wall time divided by the paired Git
status/add/commit time on the same markdown tree. These are observed samples on a shared host,
not isolated causal estimates for individual optimizations.

| Account pages | Command | `4ad39c7` ms | Final build5 ms | Final read bytes | Final wrote bytes | Wall / Git |
|---:|---|---:|---:|---:|---:|---:|
| 2,000 | One-page edit | 1,589 | 1,346 | 1,774,309 | 1,548,515 | 45.5× |
| 2,000 | Following unchanged open | 840 | 908 | 1,774,817 | 1,548,406 | 160.5× |
| 20,000 | One-page edit | 121,410 | 9,636 | 17,557,453 | 15,588,501 | 64.7× |
| 20,000 | Following unchanged open | 19,404 | 8,431 | 17,557,967 | 15,588,387 | 84.6× |

All these samples replay zero records. The 20k edit's judging phase falls from 97,500 to 1,408 ms,
but ten times the pages still produces about ten times the IO for one edit. Reading and writing
the entire checkpoint remains an unavoidable linear cost in this implementation. The initial
candidate access also measures the one-time legacy-log migration; the rows above follow it.
Git persists markdown without performing the vault's judgments or recording refusals.

The measurement ledger contains the exact wall/Git values, burst curves, original and final binary
hashes, completed and pending histories, resumed-run qualifications, and commands/logs.

## What the executable now uses

* A checksummed generation selector and byte-addressed 64 KiB log segments. Normal checkpoint
  recovery reads the anchor/suffix window, rather than the complete retained receipt log. Boundary
  rollover clears an orphan before publishing it. Readers, forks and compaction use the same vault
  lock; recovery memo keys include the selected generation, not only logical length.
* Balanced, ordered lookup buckets shared across query batches, preserving first-match and duplicate
  behavior. Admission batches retain a certified name tree and update it after each page update,
  rather than rebuilding it or rescanning for every subsequent write. Incoming law checks walk graph structure only for indexed citation candidates. A single
  judgment shares a deferred data footprint, and checks its explicit writes before demanding pins.
* Shared name/history indices for open construction/replay, file matching, diagnostics and views;
  unchanged name lists avoid the deletion/rename search. Dangling resolution skips graph traversal
  when no atom can be unresolved.
* Structural keys and an Array tail worker for distinct form checks; accepted results are reused
  without replacing the checker with a disk flag. The overlap diagnostic uses its proved zero result.
* One exact-input process-local checkpoint decode memo. Authentication precedes decoding; a cache
  hit uses native ByteArray equality. Cold decoding, encoding, hashing and checkpoint bytes remain.
* Strict cost coverage: a missing baseline or changed command sequence fails. SWARM's retention
  scenario now actually performs the refused write instead of accepting shell missing-file errors.
  WORKSHOP has a complete current-command baseline rather than 13 silently excluded steps.

The original definitions remain as semantic specifications for `@[csimp]` equalities. The compiler
uses the proved replacements; these are not selectable parallel implementations. Legacy monolithic
log support exists only for reading/migration. An append migrates a legacy log once; older binaries
cannot read the new segmented selector. Logical record bytes and receipt checks remain unchanged.
Full-log audit/retention operations remain explicit.

## General theorem statements

These declarations are quoted verbatim from the implementation; their proof bodies are in the linked
modules. Index declarations use the module's lawful ordering/equality assumptions. None is a finite
fixture or an axiom. The storage statements refine the actual pure byte assembler/parser; they do
not claim a universal theorem about operating-system crash or fsync behavior. As documented
in `Cli.lean`, writes flush without fsync: these gates cover process interruption, not power-loss
durability.

[Index.lean](../lean/Obend/Vault/Index.lean)

```lean
theorem bucket_ofList (key : α → κ) (xs : List α) (k : κ) :
    bucket (ofList key xs) k = xs.filter (fun x => key x == k)
```

[Index.lean](../lean/Obend/Vault/Index.lean)

```lean
theorem first_ofList (key : α → κ) (xs : List α) (k : κ) :
    first (ofList key xs) k = xs.find? (fun x => key x == k)
```

[Store.lean](../lean/Obend/Vault/Store.lean)

```lean
theorem entryLinkIndex_eq_scan (es : List Entry) (id : PageId) :
    Index.bucket (entryLinkIndex es) id = es.filter (fun e => citesPage e.graph id)
```

[Store.lean](../lean/Obend/Vault/Store.lean)

```lean
theorem Prepared.queryContext_store (pr : Prepared) (es res : List Entry)
    (over : List (String × Obend.Core.Data.Data)) :
    (pr.queryContext es res over).store = pr.worldAt es res over
```

[Store.lean](../lean/Obend/Vault/Store.lean)

```lean
@[csimp] theorem pinsAt_eq_indexed : @pinsAt = @pinsAtIndexed
```

[Store.lean](../lean/Obend/Vault/Store.lean)

```lean
@[csimp] theorem judgePrepared_eq_filtered : @judgePrepared = @judgePreparedFiltered
```

[Store.lean](../lean/Obend/Vault/Store.lean)

```lean
@[csimp] theorem judgeAll_eq_indexed : @judgeAll = @judgeAllIndexed
```

[Store.lean](../lean/Obend/Vault/Store.lean)

```lean
@[csimp] theorem forgetMissing_eq_fast : @forgetMissing = @forgetMissingFast
```

[Store.lean](../lean/Obend/Vault/Store.lean)

```lean
@[csimp] theorem fixDangling_eq_fast : @fixDangling = @fixDanglingFast
```

[Store.lean](../lean/Obend/Vault/Store.lean)

```lean
@[csimp] theorem settle_eq_indexed : @settle = @settleIndexed
```

[SegmentLog.lean](../lean/Obend/Vault/SegmentLog.lean)

```lean
theorem assemble_range (bs : Bytes) (start stop : Nat) (nonempty : start < stop) :
    (assemble (((split capacity (by decide) bs).drop (start / capacity)).take
      ((stop - 1) / capacity + 1 - start / capacity) |>.map
        (fun b => (⟨b.toArray⟩ : ByteArray))) (start % capacity) (stop - start)).data.toList =
      (bs.drop start).take (stop - start)
```

[SegmentLog.lean](../lean/Obend/Vault/SegmentLog.lean)

```lean
theorem holds_window {W : Type} (Hb : Bytes → Bytes) (dec : Bytes → Option W)
    (ck : Checkpoint) (bs : Bytes) (offset : Nat) (ha : offset ≤ ck.start)
    (hb : ck.start ≤ ck.stop) :
    (localCheckpoint ck offset).holds Hb dec (bs.drop offset) = ck.holds Hb dec bs
```

[SegmentLog.lean](../lean/Obend/Vault/SegmentLog.lean)

```lean
theorem parse_window (Hb : Bytes → Bytes) (prev : Nat) (bs : Bytes) (offset : Nat)
    (window : ByteArray) (h : window.data.toList = bs.drop offset) :
    parseFrom Hb prev (bs.drop offset) =
      ((parseFromAt Hb prev window 0).1,
        bs.drop (offset + (parseFromAt Hb prev window 0).2.1),
        (parseFromAt Hb prev window 0).2.2)
```

[DecodeCache.lean](../lean/Obend/Vault/DecodeCache.lean)

```lean
theorem read_eq {W : Type} (decode : Bytes → Option W) (cached : Option (Entry decode))
    (bytes : Bytes) : (read decode cached bytes).result = decode bytes
```

[DecodeCache.lean](../lean/Obend/Vault/DecodeCache.lean)

```lean
theorem holdsAt_bind {W : Type} (Hb : Bytes → Bytes) (decode : Bytes → Option W)
    (ck : Checkpoint) (bytes : ByteArray) :
    Obend.Vault.LogBytes.holdsAt Hb decode ck bytes =
      (Obend.Vault.LogBytes.holdsAt Hb some ck bytes).bind decode
```

[FormCheckCache.lean](../lean/Obend/Vault/FormCheckCache.lean)

```lean
@[csimp] theorem Form.checksAt_eq_cached : @Form.checksAt = @Form.checksAtCached
```

[FormCheckCache.lean](../lean/Obend/Vault/FormCheckCache.lean)

```lean
@[csimp] theorem classify_eq_cached : @classify = @classifyCached
```

[Index.lean](../lean/Obend/Vault/Index.lean)

```lean
theorem First.replace_eq_rebuild {key : α → κ} {xs : List α} (ctx : First key xs) (value : α) (q : κ) :
    (ctx.replace value).find q = (First.build key (replaceKey key value xs)).find q
```

[Store.lean](../lean/Obend/Vault/Store.lean)

```lean
theorem admitWritesWithIndex_eq (H : Hash) (res : List Entry) (s : Store)
    (pending : List Write) (refused : List RefusedWrite) (index : Index.First Page.name s.pages) :
    admitWritesWithIndex H res s index pending refused = admitWrites H res s pending refused
```

## Verification and outstanding work

The integrated hbox build uses:

```sh
cd /othersys/home/hbox/obend-vaultperf-build/lean
SWARM_MEM_MAX=16G LEAN_NUM_THREADS=4 swarm-build lake build obend
```

`integrated-build3.log/.exit` and `integrated-build4.log/.exit` are successful. Build 4's frozen binary
SHA-256 is `fff4533f76509b1bd89e732c041506ac300f59066ece73f754c873b8468d044f`.
Build 5 adds the maintained admission index (`e5b4604`), passes the same build gate, and freezes
SHA-256 `0726bb5c6cf8e6c92e3ea8c557e3bfa129dac77a52b4e88a2db744f92195b098`.

The selected theorem axiom audit runs `SWARM_MEM_MAX=2G swarm-build lake env lean
../VaultPerfAxioms.lean` from that build's `lean/`. It prints axioms of the maintained index,
admission refinement, query context, filtered judgment, segment assembler/window/parser,
decode reuse, form checks/classification and indexed status report. `vault-perf-axioms.log/.exit`
is green: only Lean's standard `propext`, `Classical.choice`, `Quot.sound` (or none), with no
`sorryAx`, custom axiom or native-decision dependency. The exact declarations checked are retained
in `../VaultPerfAxioms.lean`; this was a scoped audit, not an unfiltered package census.
Local harness gate: `python3 lean/tests/vault/cost_harness.py` passes fifteen tests;
`git diff --check` passes.

All remote paths below are on hbox; later gates and measurements are in the measurement ledger.

Final storage gates use `/othersys/home/hbox/obend-vaultperf-storage-tests/gates5.sh`, with recorded
PID, log and exit files (`gates5.exit` = 0). They exercise `tests/vault/Segments.lean`, `log_lock.py`,
CRASH and RETAIN; CRASH includes every one of 232 byte cuts. Segments reads only 133 physical bytes
for the final nine-byte logical window of a 196,625-byte stream (selector plus active block);
the lock test observes `locks_lock_inode_wait` before the reader is released.

CRASH and RETAIN both pass functional recording and fresh independent strict comparison, with
every step compared. CRASH's comparison totals 9,602 ms; RETAIN's 209 ms. Baseline and comparison
rows are `COST5.baseline.tsv` and `COST5.compare.tsv` in that directory. Build 4's original-baseline
timing failure remains in `gates4.exit`/`crash4.log`: step 12 was 103 → 411 ms with identical bytes
and replay. Focused reproductions with checked preconditions measured 224 and 84 ms, both passing
without changing that baseline; variation was in the full-audit log read, while merge was 23/26 ms.
Evidence is `crash-focused4.{py,log,exit}`. The final recording was made in the later quiet window,
then independently compared; the earlier red was not relabeled a pass.

Before/after walkthroughs run the named docs only, using `swarm-build python3 tests/vault/walkthrough.py
--doc tests/vault/NAME.md --work DIR`; record passes add `--cost-baseline`, followed by independent
strict comparisons. Forms/workshop logs live in `.../obend-vaultperf-measure/final-checks5/`;
WALKTHROUGH/TRANSPORT/REASONS/SWARM logs live at `.../obend-vaultperf-measure/*-after5-*.log`.
The scale commands, exact binary hashes, same-tree Git commands and fixture/resume validation
are recorded in the measurement ledger and each run's `run.json`.

All eight named documents pass independent final cost comparisons: WALKTHROUGH, FORMS, WORKSHOP,
SWARM, TRANSPORT, REASONS, CRASH and RETAIN. Every WORKSHOP step has matching current commands;
there are no silently excluded steps. `COST.baseline.tsv` merges only those documents' recorded
rows, retaining the unrelated ledger/decisions baselines. The merge checks each corresponding
independent measurement table with the actual comparator (`/tmp/merge_vaultperf_costs.py`, output
`/tmp/vaultperf-baseline-merge.log`).

SWARM uses the explicit `--cost-samples 3` mode added in `502c514`: three complete fresh recording
fixtures followed by three independent fresh comparison fixtures, with every functional check
required. Per-step time is the median; bytes, replay and checkpoint costs are the maximum. The
thresholds are unchanged. Both batches pass, and all raw transcripts/costs remain in
`.../obend-vaultperf-measure/swarm5-{record,compare}-samples/`; summary logs are
`SWARM-after5-samples-{record,compare}.log/.exit`. The earlier single-sample red is retained.
Neither the 2 GB cap nor mixed core classes explained its variability in the focused probes;
this report makes no causal claim that changing either fixed a regression. The fixed final
sampling protocol and its affinity are recorded in the measurement ledger.

Remaining requirements are concrete, not permission barriers:

1. Replace list-backed Store access with a certified read/write algebra and maintained persistent
   name/id/backlink indices. Current batch indices are reconstructed after process startup; they are
   not a disk index maintained by every turn.
2. Produce an ordered page-edit trace covering every Store mutation, including wakeups, rename,
   deletion, settle, merge and restore. Use it to update persistent authenticated paths. A Merkle
   tree rebuilt from a whole World per turn would not solve the problem.
3. Separate the versioned receipt commitment from snapshot encoding, preserving v1 receipts and
   explicitly migrating to authenticated objects. A fresh command must demand only the objects its
   read algebra requires. Merges still load the other complete world, and retained-anchor membership
   can read the other complete log; those need root comparison and an authenticated receipt index.
   Do not silently reinterpret old JSON commitments as roots.
4. Carry certified judgment/render dependencies across turns. A prior `seen` string is not evidence
   of a current view: arbitrary decoded stores and refused pending writes make that shortcut false.
5. Provide a trustworthy filesystem change source (with an explicit overflow/rescan path) or change
   the edit protocol. Discovering arbitrary unannounced edits without examining files cannot be
   sublinear. Widely shared law changes also legitimately affect many judgments.
6. Complete the requested 10,000-record curves at both sizes. Current matched short-history probes
   refute the desired bound; a projected multi-day baseline is not a completed measurement.

The remaining work is tracked here so integration does not mistake the measured improvement for
completion of the architecture migration.
