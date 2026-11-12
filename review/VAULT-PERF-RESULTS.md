# Vault performance: integration record

2026-11-08 · GPT-6 Astra (codex) · branch `lane-vault-perf`, starting `4ad39c7`

2026-11-12 · Shard S5 (`shard-s5-vault-scale`, base `8b7907e`) · sharded Merkle checkpoints (`ChunkedWorld`) + coupled fork turns & member-scoped forks

**Cold-process read and directory-scan costs remain `O(vault)`, while checkpoint writes now scale with dirty buckets (`O(dirty buckets)`).** `lane-vault-perf` replaced expensive executed scans, repeated judgments and monolithic log reads with exact semantic equalities; Shard S5 replaces the monolithic 15.6 MB JSON world commitment/checkpoint with a verified 128-bucket `cSHAKE256`-authenticated sharded checkpoint (`Obend.Vault.ChunkedWorld`), upgrades `Branch.merge` / `Merge.plan` to replay coupled multi-page fork turns atomically, and enforces per-member `Grants` on `--for MEMBER` forks. It does not yet replace the in-memory `List Page` `Store` or full-tree external-edit discovery on `obend open`. The
[measurement ledger](VAULT-PERF-MEASUREMENTS.md) records the earlier `hbox` curves against Git, and [Representation design](VAULT-PERF-DESIGN.md) records the implemented sharded checkpoint boundary and remaining cold-read algebra.

## Final matched scale probes

### 1. Matched `bb2` probes (`8b7907e` Build 5 vs Shard S5 `ChunkedWorld`)

Both binaries (`0726bb5c6cf8e6c92e3ea8c557e3bfa129dac77a52b4e88a2db744f92195b098` from `8b7907e` and `333983c1a2368b64874aef8114cdda26f7a78150bebff8c37baed665818e1fe5` from `shard-s5-vault-scale`) copy the exact same initial seed-7 snapshot within each size (`seed-2000` at 2 records, `seed-20000` at 1 record) and run sequentially on `bb2` under `SWARM_MEM_MAX=8G swarm-build taskset -c 0`. The first candidate open (`unchanged`) migrates the legacy monolithic checkpoint to `.obend/world/shards/*.json` + `.obend/world/root.json` + compact binary `.obend/checkpoint` (`OBWM0001`); the rows below measure the subsequent `One-page edit` and `Following unchanged open` (`steady`).

| Account pages | Command | Build 5 (`bb2`) ms | Shard S5 (`bb2`) ms | Build 5 read B | Shard S5 read B | Build 5 wrote B | Shard S5 wrote B | Write reduction | Build 5 Wall / Git | Shard S5 Wall / Git |
|---:|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 2,000 | One-page edit | 529 | **358** | 1,774,304 | 1,500,867 | 1,548,515 | **37,859** | **40.9×** | 25.99× (`676.14 / 26.02`) | **19.20×** (`500.87 / 26.09`) |
| 2,000 | Following unchanged open | 381 | **267** | 1,774,812 | 1,501,337 | 1,548,406 | **18,077** | **85.7×** | 79.52× (`524.31 / 6.59`) | **62.81×** (`405.27 / 6.45`) |
| 20,000 | One-page edit | 5,583 | **3,623** | 17,557,448 | 14,824,697 | 15,588,501 | **101,624** | **153.4×** | 35.40× (`5,798.57 / 163.82`) | **24.05×** (`3,766.69 / 156.60`) |
| 20,000 | Following unchanged open | 3,960 | **2,700** | 17,557,962 | 14,825,174 | 15,588,387 | **18,082** | **862.1×** | 87.92× (`4,152.58 / 47.23`) | **64.87×** (`2,841.30 / 43.80`) |

Phase breakdown on the 20,000-page probes (`read / judge / land / write / other` ms):
* **20k One-page edit**: Build 5 `1192 / 906 / 785 / 1027 / 1673` (`land+write = 1,812 ms`) → Shard S5 **`1101 / 945 / 63 / 2 / 1512`** (`land+write = 65 ms`, **`27.9×` faster**). Only the single dirty shard (`~83 KB` out of 128 shards totaling `12,846,644` B), `.obend/world/root.json` (`9,127` B), `.obend/checkpoint` (`8,738` B vs `15,587,987` B — **`1,784×` smaller**), and the log append are written.
* **20k Following unchanged open**: Build 5 `1194 / 36 / 774 / 289 / 1667` (`land+write = 1,063 ms`) → Shard S5 **`1102 / 40 / 55 / 1 / 1502`** (`land+write = 56 ms`, **`19.0×` faster**; `0` shard files written).
* **Matched 2,000-page short-history rejoin bursts (`B10`, `B100` on `bb2`)**:
  * `B10` merge: Build 5 `5,638 ms`, read `3,924,265` B, wrote `6,214,865` B, wall `5,796.94 ms` (`213.92×` Git) → Shard S5 **`5,537 ms`**, read **`3,376,806` B**, wrote **`2,085,052` B** (**`3.0×` write reduction**), wall **`5,680.24 ms`** (`208.04×` Git); away 10-write open drops from `608 ms` / `1,552,317` B wrote to **`448 ms`** / **`117,970` B** wrote (**`13.2×` write reduction**).
  * `B100` merge: Build 5 `7,845 ms`, read `3,966,278` B, wrote `6,348,231` B, wall `8,006.82 ms` (`223.46×` Git) → Shard S5 **`7,822 ms`**, read **`3,416,620` B**, wrote **`2,625,962` B** (**`2.4×` write reduction**), wall **`7,967.69 ms`** (`214.15×` Git); each 10-write fork open drops from `~780 ms` / `~1,575 KB` wrote to **`~625 ms`** / **`~111 KB`** wrote (**`14.2×` write reduction**).

### 2. Earlier `hbox` baseline (`4ad39c7` vs Build 5, retained for continuity)

| Account pages | Command | `4ad39c7` ms | Final build5 ms | Final read bytes | Final wrote bytes | Wall / Git |
|---:|---|---:|---:|---:|---:|---:|
| 2,000 | One-page edit | 1,589 | 1,346 | 1,774,309 | 1,548,515 | 45.5× |
| 2,000 | Following unchanged open | 840 | 908 | 1,774,817 | 1,548,406 | 160.5× |
| 20,000 | One-page edit | 121,410 | 9,636 | 17,557,453 | 15,588,501 | 64.7× |
| 20,000 | Following unchanged open | 19,404 | 8,431 | 17,557,967 | 15,588,387 | 84.6× |

All these samples replay zero records. With `ChunkedWorld`, checkpoint writes no longer grow with vault size (`37.9 KB` at 2k vs `101.6 KB` at 20k for a 1-page edit; `18.1 KB` at both 2k and 20k for an unchanged open), while cold `obend open` still reads all 128 non-empty shards and scans the working tree (`1.50 MB` at 2k vs `14.82 MB` at 20k). Metadata-only commands (`grants`, `obligations`, `member list`) demand-load only the root manifest (`0` shard reads). Git persists markdown without performing the vault's judgments or recording refusals.

The measurement ledger contains the earlier `hbox` wall/Git values, burst curves, completed and pending histories, and resume qualifications.

## What the executable now uses

* **Verified 128-bucket Merkleized world checkpoints (`Obend.Vault.ChunkedWorld`)**: `deployed.encW` is now a compact binary manifest (`OBWM0001` + `cManifestCore`) committing to `(NonStoreMeta, totalPages, totalTombs, bucketDigests : List (Option String))`, paired with sparse content-addressed shard files `.obend/world/shards/<2hex-bucket>-<cshake256>.json` (`0` files and `0` syscalls for empty buckets) and an atomic RFC-8259 `.obend/world/root.json`. Commits re-encode and atomically write only dirty buckets (`encodeWorldIncremental_manifest_eq`), publish `.obend/world/root.json` and `.obend/checkpoint` via `.tmp` + `rename` after all referenced shards exist, prune unreferenced shards last, and retain seamless fallback decoding for legacy monolithic JSON checkpoints (`decodeCheckpointWorld`).
* **Atomic multi-page coupled fork replay & member-scoped forks (`Store.writeTexts`, `Branch.lean`, `Merge.lean`, `Cli.lean`)**: `obend merge` detects coupled non-clashing writes from a fork (such as mutually dependent `DEV` + `lanes/*` backlink/link turns in `SWARM.md` §4 or mutually-born pages) and replays them atomically as a single multi-page `BTurn` at the tip (`tip_lands_texts_iff_store_lands`, `mergeVault_agrees`), skipping pre-simulation via `mayHaveCoupledGroup` when no coupling is possible. `obend fork DIR --for MEMBER` and `obend branch DIR --for MEMBER` record fork attribution in world state and `.obend/fork.json` so `obend since` and `obend merge` enforce that member's standing `Grants` and `Store.Member` capabilities at the tip rather than unconditionally granting owner authority.

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

[ChunkedWorld.lean](../lean/Obend/Vault/ChunkedWorld.lean)

```lean
theorem decodeShardedWorld_encodeShardedWorld (w : World) :
    decodeShardedWorld (encodeShardedWorld w) = .ok w
```

[ChunkedWorld.lean](../lean/Obend/Vault/ChunkedWorld.lean)

```lean
theorem decodeManifestWith_manifestBytes (w : World) (store : String → Option Bytes)
    (hstore : ∀ k sb, (k, sb) ∈ (encodeShardedWorld w).shards → store k = some sb) :
    decodeManifestWith store (manifestBytes w) = .ok w
```

[ChunkedWorld.lean](../lean/Obend/Vault/ChunkedWorld.lean)

```lean
theorem encodeWorldIncremental_manifest_eq (w : World) (prev : Option (Array CachedBucket)) :
    (encodeWorldIncremental w prev).1.data.toList = manifestBytes w
```

[ChunkedWorld.lean](../lean/Obend/Vault/ChunkedWorld.lean)

```lean
theorem metaOnly_sound (w : World) (store : String → Option Bytes) (manifest : Bytes)
    (hw : decodeManifestWith store manifest = .ok w) :
    (unframeManifest manifest).map (fun c => withMeta [] [] c.1) =
      some { w with store := { w.store with pages := [], tombs := [] } }
```

[Replay.lean](../lean/Obend/Vault/Replay.lean)

```lean
theorem sharded_checkpoint_is_cache {S : Session} (h : Reachable S) {n : Nat} (hn0 : 0 < n)
    (hn : n ≤ S.log.length) (store : String → Option Bytes)
    (hstore : ∀ k sb,
      (k, sb) ∈ (ChunkedWorld.encodeShardedWorld (replay deployed genesis (S.log.take n))).shards →
        store k = some sb)
    (k : Nat) :
    recoverWith logHash deployed (decodeCheckpointWorld store) genesis
        (checkpointAt logHash deployed genesis S.log n) ((encodeAll logHash S.log).take k) =
      recover logHash deployed genesis ((encodeAll logHash S.log).take k)
```

[Branch.lean](../lean/Obend/Vault/Branch.lean)

```lean
theorem tip_lands_texts_iff_store_lands {c : Config} {o : String} {t : BTurn} {s s' : Store}
    {d₀ : CellDelta} {ds : List CellDelta}
    (hv : c.vault = some s) (ht : t.text = none) (hw : t.turn.writeCells = d₀ :: ds)
    (hm : t.texts.map (·.1) = (d₀ :: ds).map (·.cell))
    (hpre : preRefusal c t = none) :
    (∃ c', admitWrite c o t = .ok c' ∧ c'.vault = some s') ↔
      s.writeTexts t.texts t.actorRef = .ok s' ∧
      ∀ d ∈ d₀ :: ds, (vaultStates s' d.cell).map Data.term = some d.postState.term
```

[Merge.lean](../lean/Obend/Vault/Merge.lean)

```lean
theorem mergeVault_agrees (H : Obend.Digest.HashBytes.Hash) (here other : Store) (label : String)
    (skip : String → Bool) (auth : ForkAuth := {}) {m : Merged}
    (h : Branch.merge (plan H here other label skip auth).base (plan H here other label skip auth).left
      (plan H here other label skip auth).right (plan H here other label skip auth).text = .ok m) :
    Agrees m.tip
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
   name/id/backlink indices so cold-process `obend open` / `status` / `merge` demand-load only the
   buckets or pages their read cone touches rather than reassembling all non-empty shards.
2. Produce an ordered page-edit trace covering every Store mutation, including wakeups, rename,
   deletion, settle, merge and restore, so bucket partitioning itself becomes `O(edits)` in memory
   rather than a linear `O(pages)` pass over `w.store.pages`.
3. Extend root-manifest comparison into `obend merge` so two vaults sharing unchanged buckets skip
   reading and decoding identical shard files from the incoming fork, and replace full-log horizon
   scans after `forget` with an authenticated receipt index.
4. Carry certified judgment/render dependencies across turns. A prior `seen` string is not evidence
   of a current view: arbitrary decoded stores and refused pending writes make that shortcut false.
5. Provide a trustworthy filesystem change source (with an explicit overflow/rescan path) or change
   the edit protocol. Discovering arbitrary unannounced edits without examining files cannot be
   sublinear. Widely shared law changes also legitimately affect many judgments.
6. Complete the requested 10,000-record curves at both sizes.

### Shard S5 (`bb2`) verification summary

* `SWARM_MEM_MAX=8G swarm-build lake build obend Obend.Teeth.Vault` succeeded cleanly (`647` jobs; binary SHA-256 `333983c1a2368b64874aef8114cdda26f7a78150bebff8c37baed665818e1fe5`).
* `#print axioms` audit over `decodeShardedWorld_encodeShardedWorld`, `decodeManifestWith_manifestBytes`, `encodeWorldIncremental_manifest_eq`, `metaOnly_sound`, `sharded_checkpoint_is_cache`, `merge_is_pushout`, `settled_at_tip`, `landed_consents`, `tip_lands_texts_iff_store_lands`, and `mergeVault_agrees` reported `[propext, Classical.choice, Quot.sound]` only (zero `sorryAx` or custom axioms).
* Unit and concurrency gates on `bb2`: `tests/vault/Branch.lean`, `tests/vault/Segments.lean`, `cost_harness.py` (`15/15`), `forms_planted.py`, `kinds.py` (`8/8`), and `log_lock.py` all passed.
* Walkthrough gates on `bb2`: `WALKTHROUGH` (`44/44`), `FORMS` (`23/23`), `TRANSPORT` (`24/24`), `WORKSHOP` (`24/24`), `CRASH` (`14/14`), and `RETAIN` (`12/12`) passed functional and strict `COST.baseline.tsv` checks **without modifying any existing cost baseline row**; `SWARM` (`30/30`, including the new `--for lane-sdr` authority refusal and atomic 5-page `gates` fork merge) passed 3-sample recording and a fresh independent 3-sample verification pass.

The remaining work is tracked here so integration does not mistake the measured improvement for
completion of the full cold-read architecture migration.
