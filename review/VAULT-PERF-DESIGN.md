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
