# Vault cost: the remaining representation change

2026-11-08 · GPT-6 Astra (codex) · lane-vault-perf

The requested bound is not established by this lane's intermediate optimizations. The deployed
world still contains complete lists of pages and histories; its commitment is cSHAKE over the
complete JSON encoding; a fresh process reads and decodes a complete checkpoint. This note specifies
the representation change needed to remove those costs. It is a design, not a claim that the
replacement below is implemented or proved.

## Grounding and decisions

TigerBeetle separates the WAL from immutable blocks reached through a root, with block checksums in
the references that name them. Its root advances after the blocks it names exist. Use that ordering
for authenticated checkpoint objects; the segmented receipt stream alone does not solve state
loading. [Data file](https://github.com/tigerbeetle/tigerbeetle/blob/main/docs/internals/data_file.md)
(local reading: `~/paperbin/tigerbeetle2026-internals-data-file.md`).

LMDB's copy-on-write B-tree and immutable reader snapshots are a better starting point for the
vault's name lookup than an LSM tree: the immediate workload is small point changes and sparse
reads, and a B-tree avoids introducing compaction scheduling. Keep log segmentation independent of
this choice. [LMDB documentation](https://www.lmdb.tech/doc/)
(local reading: `~/paperbin/chu2012-lmdb-memory-mapped-database-openldap.txt`).

Irmin's immutable content-addressed block store separates contents, nodes and commits; Git's trees
name blobs and subtrees. Use explicit typed object domains and child references so a page update
changes its leaf and ancestor path, while unchanged subtrees retain their identity.
[Irmin architecture](https://irmin.org/tutorial/architecture/),
[Git objects](https://git-scm.com/book/en/v2/Git-Internals-Git-Objects).

Unison separates immutable content identity from mutable names. The vault also needs both: a stable
page identity survives a rename, while its name index changes. Do not make name lookup the only
source of page identity. [Unison's content addressing](https://www.unison-lang.org/docs/the-big-idea/)
(local reading: `~/paperbin/unison2026-docs-the-big-idea-content-addressed-code.txt`).

Salsa records input dependencies and revisions, and can retain a derived result when its observable
inputs remain equal. Adapton additionally distinguishes changed data from demanded computation.
Judgment keys must include every input a law reads (including absence, name resolution, inherited
laws, backlinks, environment names and actor/request facts); cache invalidation cannot be just
"the page named in the command changed." Recompute only demanded judgments whose key changes.
[Salsa algorithm](https://salsa-rs.github.io/salsa/reference/algorithm.html)
(local Adapton reading: `~/paperbin/hammer2014-adapton.txt`).

## Representation and proof boundary

`Log.Machine.encW` currently serves two purposes: receipt commitment and complete checkpoint
serialization. A structural commitment cannot equal cSHAKE of the old flat JSON bytes by a
rearrangement of computation. Introduce a versioned commitment scheme and separate its root bytes
from the snapshot/object codec. Preserve the old receipts' meaning during an explicit migration;
never reinterpret an old `newCommit` as a Merkle root or quietly relink its receipt chain.

The canonical page collection must retain the existing order and first-match behavior, including
on malformed input with duplicate names/IDs, unless a checked uniqueness condition rejects that
input at the boundary. A name-sorted map alone does not preserve `Store.pages` semantics. Use a
persistent ordered sequence with stable positions, plus name/ID indices to the appropriate
positions; specify duplicate and rename behavior before replacing the list. Maintain backlink
buckets in the same turn, removing old edges and adding new ones. If the implementation restricts
reachable stores to unique names, prove the invariant from genesis through every turn and decoder.

Each immutable node carries its canonical size/key range, child references, and a cached digest.
Constructors compute the digest from the leaf payload or child digests. Prove the cached digest is
the recursive semantic digest after insert, update, delete and rebalance. Prove lookup and ordered
iteration agree with the old sequence interpretation. Prove each turn's interpreted result and
outcome agree with `stepTurn`, then transfer replay/recovery statements through that simulation.
Do not call a tree constructor invariant a proof that the command uses the tree correctly.

A checkpoint becomes a small root object anchored to a receipt, plus immutable objects. A reader
verifies an object's bytes against the hash in its parent before exposing the decoded node. A
writer publishes children before parents, appends the turn receipt, and only then advances the
checkpoint reference and writes markdown projections. Define interrupted writes and unavailable
objects explicitly; an object not yet reachable is harmless, a missing reachable object is an error
or requires replay from an older intact checkpoint. Keep object collection separate from commit;
retention/forks must pin every root their replay needs.

## Loading and the CLI

Changing the checkpoint's file layout cannot make the current pure
`Store.page? : Store → String → Option Page` demand-load absent pages. It receives a fully decoded
world and has no file effect. Choose one of two complete interfaces:

* A read algebra whose primitive operations are indexed lookup, ordered range scan, version lookup,
  and backlink lookup, with an immutable root and explicit read/write set. Interpret it over an
  in-memory semantic store for proofs and over authenticated objects for the CLI. The persistent
  interpreter must refine the semantic one on every requested path.
* A resident process holding the decoded world and indices, with commands as requests. This can
  amortize initialization but does not itself establish fresh-process or restart bounds; recovery
  still needs the authenticated object design to avoid loading the whole vault.

The read algebra is the recommended durable interface. A resident service may later amortize
process overhead, but should not hide a linear cold start in a benchmark advertised as incremental.
Merges should exchange roots and visit changed subtrees; merely reading the other complete World
from smaller log segments still costs the other vault's size.

`readVault` promises to detect arbitrary external file edits. Without a trusted source of changed
paths, an untouched file and an unexamined modified file are indistinguishable. Full directory
inspection is therefore linear even when no page changed. A watcher/change journal can supply the
normal changed-path set, with an explicit full rescan after overflow, watcher gaps or unsupported
filesystem behavior. Alternatively require edits through the command protocol. Preserve an honest
full-rescan command and report it separately; do not silently ignore external edits to meet a curve.

A write's affected dependency set can itself be the whole vault (for example a widely used kind or
a law over all backlinks). The meaningful bound is in changed and demanded inputs plus affected
judgments plus required output, not just the number of frontmatter fields the user typed.

## Implemented seam: exact-input decode reuse

`DecodeCache.Entry` retains one result of the actual decoder, with an erased proof tying it to the
exact input bytes. `read_eq` proves lookup returns the ordinary decoder's result for every input,
including malformed bytes and failed decodes. ByteArray equality uses Lean's native byte comparison;
there is no digest-only hit or assumed canonical JSON normalization.

`holdCheckpoint` authenticates the checkpoint against its receipt before invoking the memoized
decoder; `holdsAt_bind` proves the factorization is the existing checkpoint check. `saveCheckpoint`
uses the same memo. An unchanged open can reuse the decode performed during recovery when validating
its newly encoded checkpoint. The cache is process-local and bounded to one entry, so it cannot
accumulate obsolete worlds or accept a planted disk cache as evidence.

This removes a repeated parse/history reconstruction on a cache hit. It does not remove the first
decode, whole-world encoding/hashing, byte comparison/conversion, checkpoint read/write, or directory
scan. It is not a Merkle implementation and does not establish the requested asymptotic bound.

Acceptance for the full migration remains: exact semantic/refinement statements; unchanged and
single-page commands at 2,000 and 20,000 pages; long histories and rejoin bursts; malformed objects,
truncation at publication boundaries, duplicate names, rename/delete/revive and corrupted index
cases; complete cost comparison of the walkthroughs; and git status/commit on the same markdown
working tree as the named external timing baseline. Retain cold and warm measurements separately.

## Decode-cache measurement (hbox, 2026-11-08)

The native benchmark imports the deployed `DecodeCache` and `Replay`, validates a frozen checkpoint
of 2,020 actual pages (2,000 generated pages plus 20 index pages), and compares ordinary
`decodeWorld` plus equality against cached decode plus the same equality. The input is 1,605,297
world bytes. Four warmed rounds were respectively 111/103/80/66 ms versus 41/30/18/17 ms; medians
91.5 versus 24 ms, a 73.8% reduction against that decoder baseline. The first round was 126 versus
95 ms. The busy host's absolute timings varied; this is evidence for the repeated-decode saving,
not a scaling result.

Five alternating `obend open` runs on copies of the same stable 2,020-page vault gave baseline
`4ad39c7` command times 1127/1079/973/1081/1061 ms, versus 947/1441/995/867/849 ms for the integrated
lane binary (median 1079 to 947 ms, 12.2% lower). This comparison includes the other lane changes,
and the first candidate run includes log-format migration. Median checkpoint-write phase was
87 to 53 ms. Both replayed zero records. No attribution of the entire command improvement to the
decoder cache is intended.

Commands and artifacts, all under `hbox:/othersys/home/hbox/obend-vaultperf-decode/`:

* `SWARM_MEM_MAX=8G swarm-build python3 native.py`: compiles `DecodeBench.lean` to C and a native
  executable using the finished build's link response, then runs it on `checkpoint-2000`.
  Final direct-module evidence: `native-deployed-2000.log`, `native-deployed-2000.exit` (0).
* `SWARM_MEM_MAX=8G swarm-build python3 pair.py`: five alternating runs of baseline and candidate
  `-C before-vault open` / `-C after-vault open` with `OBEND_COST=1`.
  Evidence: `pair-2000.log`, `pair-2000.exit` (0), and `before-0.log` through `after-4.log`.
* The earlier interpreted negative result (`bench-2000.log`) used the imported boxed-array equality
  instance. It led to explicitly selecting `ByteArray.decEq`. It is superseded, not a result for the
  final cache. The final generated C calls `lean_sarray_dec_eq`.

The general semantic gate is `DecodeCache.read_eq` and `holdsAt_bind`, checked as a local leaf with
`LEAN_PATH=/Users/ember/dev/obend/lean/.lake/build/lib/lean lake env lean --memory=8192
Obend/Vault/DecodeCache.lean`, then in the shared remote `lake build obend` gate. Full lane cost
curves and the git persistence baseline are recorded separately by the measurement harness.

## Required mutation trace before a v2 commitment can be connected

A second implementation attempt identified the missing integration boundary: the current turn
returns a complete `World`, with no certified description of its edits. Computing a new Merkle tree
from that world, or diffing its complete page list, still costs the vault's size. No v2 receipt or
object format was added: a new format without a maintained update path would add risk and work.

The required API is an indexed store with an exact semantic interpretation, not an optional stale
cache inside the current record. Monotonically allocated slots make the path bound depend on
allocated state/history; reclaiming that range requires an explicit compaction/rekeying operation. The following signatures describe required interfaces; they are
not implemented declarations:

```text
-- Stable physical slots; semantic order is ascending live slot order.
-- Fresh/revived entries receive fresh slots at the tail. Deleted slots do not shift later keys.
IndexedStore.interpret : IndexedStore → Store
StorePatch.apply       : Store → Array StoreEdit → Store
IndexedStore.apply     : IndexedStore → Array StoreEdit → IndexedStore × Array Object

-- Every edit-producing operation returns its ordinary result plus the edits it actually made.
TraceResult (before : Store) (α : Type) :=
  { result : Store × α, edits : Array StoreEdit //
    StorePatch.apply before edits = result.1 }

-- Main simulation obligation, for every well-formed indexed store and every legal edit trace:
(IndexedStore.apply indexed edits).1.interpret =
  StorePatch.apply indexed.interpret edits
```

`StoreEdit` needs page/tomb insertion, replacement and removal at stable slots, and edits of members,
turn, environment and conflicts. A name index maps to an **ordered bucket of slots**: the first slot
implements lookup, while `setPage` currently replaces *every* page of that name. `landAll` instead
applies the first matching prepared change separately to each matching existing page. Treating both
as one replacement of the first found page is observably wrong on duplicate-name stores. Either
preserve this behavior or prove and check a uniqueness boundary before relying on it.

Required producer coverage, from the current code:

* `Store.setPage` and `Store.landAll`: emit replacements and the turn increment where they occur.
  `admitWritesWithIndex` already carries its name-index certificate across the recursion; this is the
  natural first consumer of a maintained slot tree and replacement trace.
* `withFresh`: emit the actual tail insertions in `freshPages` order.
* `forgetMissingCore`: emit all page removals, tomb tail insertions, and revival/rename transfers.
  Revival appends to the page list; retaining a tomb's former page position would change semantics.
* `settle`/`settleIndexed`: emit changes to dangling-link resolution and `seen` text. Producing this
  trace by scanning every page still violates the requested bound. The inverse dependency index
  must select the affected pages, with a theorem that all other pages' resolution/render is equal.
* `Merge.baseStore` (`baseMine` then `baseTheirs`) and `Merge.unsettle`: produce their own exact
  replacements/appends, including preserved/refused `seen` and `note`. `keepPending` consumes those
  traces. A post-hoc merge diff is not the maintained path.

A page leaf cannot remain the complete `historyJson p.history` if a single appended version must
cost only its growth. Page metadata, history/version growth and author additions need separate
persistent collections whose interpretation is the current `Page`. The other growing World
collections—receipts, forms/checks, reasons, sent/received records, grants, obligations, forks and
retention—also need traced updates or their full re-encoding will remain a world-sized term.

Only after those producers exist should `stepTurn` return a certified `WorldPatch` composed from
them, with a theorem that applying it yields exactly the existing result and outcome. The CLI can
then maintain `Head`'s authenticated roots by the actual trace and publish only the returned
`Array Object`. Its theorem must relate that root to the semantic commitment of the resulting
world. A tree's local hash invariant alone does not establish this turn-level statement.

## Required demand-loading interface

The read algebra must expose less than a complete `Page`; otherwise a lookup demands every old
version even when the command reads only current state. Required operations are:

| Read | Semantic interpretation |
| --- | --- |
| name → ordered slots / first slot | existing first-match name lookup and duplicate behavior |
| page slot → metadata/current-version reference | name, id, seen, note, kind and current history tip |
| page/version → graph or version-growth range | exactly the requested history projection |
| page/atom → author | `Page.who`, including the owner default |
| page id → ordered citing slots | current backlink scan in its original order |
| cursor/limit → ordered live page range | the corresponding slice of `Store.pages` |
| component/key or component/range | forms, receipts, reasons, grants and other World state |

Represent commands and judgments as programs over these reads plus explicit writes, with a pure
interpreter over the semantic `World` and an IO interpreter over an immutable authenticated root.
Prove the IO interpreter's returned values equal the pure interpreter's when each fetched object
matches its parent reference, with binding phrased against the relevant hash-collision condition.
Absence and complete-range reads must be authenticated too; a forged missing name or incomplete
backlink bucket can otherwise skip a law. Record each demand in the judgment dependency key.

The v1→v2 migration then has a concrete boundary: default v1 state retains byte-identical old
serialization; an explicit migration turn constructs and authenticates the initial objects and
switches the commitment scheme; subsequent turns update only traced roots. Checkpoint decoding is
parameterized by the object store, while receipt commitments are root-manifest bytes. Initial
migration/full rescan are explicit whole-vault operations. This plan does not claim that these
interfaces or their refinements have been implemented.

## Rendering cache boundary (investigated, not implemented)

`Page.seen` is not a rendering certificate. A refused write deliberately retains the person's
attempted text, and an arbitrary decoded store can contain a `seen` value unrelated to its view.
Comparing an old and new page or their dependency versions therefore does not justify reusing
`seen`. A fast path must carry evidence about a previously computed view.

The cache entry should have a `ViewKey` containing the current graph, page name, author lookup
inputs, and only the histories observed at that graph's cited page IDs. Its text carries
`text = ViewKey.render H key`. Missing histories are observations too. The existing
`Obend.Doc.holds_congr` and `citeFacts_page` provide the dependency-locality lemmas: each cite fact
reads only its cited page. A `keyOf` theorem must show that rendering against the captured
observations equals `Page.view` in the original world, for every graph including conflicts and
repeated atom IDs. A cache hit compares the complete key; neither a digest match nor a page's
unchanged name alone is an equality proof.

The necessary executable interface is:

```lean
settleWithMemo : Memo H → Store → Store × Memo H
-- Required for every cache, including empty and stale entries:
(settleWithMemo memo store).1 = settle H store

stepTurnWithMemo : Memo H → World → Turn → Except String ((World × Outcome) × Memo H)
-- Required for every world and turn:
(stepTurnWithMemo memo world turn).map Prod.fst = stepTurn world turn
```

The second interpreter must thread the memo through `openVault`, `judgeNew`/`judgeTurn`,
`mergeStep`, `afterMerge`, and the direct write/select/recite/resolve arms. A merge can settle once
before salvage and again afterwards; handling only the direct arms misses that reuse. `Cli.Head`
then retains the returned memo across the command's open and action. A rejected turn keeps the
previous memo, while complete-key matching makes stale entries harmless. This should replace the
actual command evaluator, with the equality theorem connecting it to receipt/replay semantics.
An unused `settleWithMemo` helper or a second renderer unconnected to that evaluator is insufficient.

An in-process memo alone does not meet the cold-command bound. Empty startup caches still compute
views, key construction still scans graphs, and an unindexed dependency comparison still scans
pages. Persisted reuse requires the authenticated demand-loading interface above and a maintained
inverse dependency index selecting changed views. A dependent `Cached x` prototype (a `Thunk` plus
an erased equality proof, with equality derived from its subsingleton property) was checked outside
the branch; it is not shipped as an unused Page field or claimed as the cache implementation.
