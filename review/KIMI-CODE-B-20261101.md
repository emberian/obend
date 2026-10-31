# KIMI CODE B 20261101

## Correctness

- [READ] `Judge/Class.lean:24-28` says the planted bad certificate is refused at every grade, but `Judge/Class.lean:192-197` requires refusal only at `badGrade` and `Judge/Class.lean:224-229` derives refusal only above that grade.
- [INFERRED] `Judge/Lrat.lean:488-506` supplies a concrete counterexample to the broader wording because its one-step planted certificate is `uncovered` at grade zero under `Judge/Lrat.lean:132-138`.
- [READ] `Judge/Class.lean:231-234` calls a format nontrivial after showing only that one fixed object-certificate pair is not accepted above one grade.
- [READ] The module summary at `Receipt.lean:19-22` omits the non-move hypothesis that `receipt_sufficient` actually requires at `Receipt.lean:206-210`.
- [READ] `Receipt.lean:218-229` never compares `N.rowDigest r` with `R.row`, so `recheck` can accept a receipt whose row digest names a different row whenever the checked verdict and roots agree.
- [READ] `Receipt.lean:218-229` also ignores `law`, `pins`, `dated`, `proofs`, `quantifier`, `trust`, and `prev`, so its name and the broader receipt narrative cover more fields than its result authenticates.
- [READ] `Receipt.lean:180-196` accepts `quantifier` and `trust` as unrestricted arguments, and no theorem in the reviewed files relates either field to the fold or to evidence.
- [INFERRED] A receipt can therefore carry `planForAll`, `policyForAll`, or an attested support without any checked justification for that claim.
- [READ] The disclosure documentation at `Receipt.lean:461-462` says the cited stranger reads openings, but `accepts .cited` at `Receipt.lean:455-459` reads only `R.verdict.isOk` and performs no opening check.
- [READ] `dial_invariant` at `Receipt.lean:463-479` proves equality with the receipt's own verdict bit, not independent validation by the cited stranger described above it.
- [READ] `chained` at `Receipt.lean:405-409` checks only predecessor digest links, so the phrase “verified chain” at `Receipt.lean:415-418` does not include verification of any receipt's evidence.
- [READ] `Run/Fork.lean:69-77` uses the `shared` predicate for minting but not for deferral, and `.defer` accepts every token absent from `F.own`.
- [INFERRED] A token with `shared t = false` can consequently be escalated and committed to the main ledger by `Run/Fork.lean:127-132`, contrary to the shared-token row description at `Run/Fork.lean:53-54`.
- [READ] `Run/Fork.lean:72` permits repeated minting of the same non-shared token because it never checks membership in `F.own`.
- [READ] `Fork.epoch` is recorded at `Run/Fork.lean:67` but ignored by `stitch` at `Run/Fork.lean:146-149`, so the executable door does not check any relationship between the fork's origin and the supplied main record.
- [READ] `stitch_union_comm` at `Run/Fork.lean:169-172` proves only extensional membership equivalence, not equality of the merged lists or equality of multiplicities.
- [READ] `union` at `Run/Fork.lean:143` removes elements already in `xs` but preserves duplicates within `ys`, so its implementation is not list-level set union.
- [READ] `stitch_accounts` at `Run/Fork.lean:194-212` quantifies over membership by value rather than occurrences, so duplicate escalated rows are not individually accounted for by the theorem statement.
- [READ] `Run/Shared.lean:245-250` silently retains the old runner configuration whenever propagation of a world event fails.
- [INFERRED] The callers at `Run/Shared.lean:270-298` can still return an accepted joint transition after such a failure, leaving a runner stale despite the documentation saying every runner observes the new record.
- [READ] The exclusion and once-spending guarantees summarized at `Run/Shared.lean:40-43` require empty initial spent and grant lists in `Run/Proofs/Shared.lean:569-571`, although that precondition is absent from the summary.
- [READ] The restart guarantees summarized at `Run/Durable.lean:23-37` likewise require empty initial ledger lists for `journal_once` and `exposed_once` at `Run/Proofs/Durable.lean:239-258`.
- [READ] `Run/Durable.lean:106-109` permits exposure while memory is lost, which is consistent with the outbox model but means exposure does not establish that the current memory has recovered.
- [READ] `Vault/Store.lean:793-801` never checks `1 ≤ k`, and natural-number subtraction makes `k = 0` select index zero through `(sections G)[k - 1]?`.
- [INFERRED] Section zero therefore aliases section one instead of receiving the “no section” refusal implied by the one-based interface.
- [READ] `Vault/Store.lean:314-321` computes `newLaws` but selects `oldLaws` whenever the law lines are unchanged.
- [INFERRED] Changing only the `kind:` frontmatter can change `kindChain` without changing `lawLines`, so such a write is judged under the old kind's laws and does not require the `relaw` adoption branch.
- [INFERRED] `openEntries` at `Vault/Store.lean:389-396` advertises every changed file as its forthcoming draft before any write is judged, so a successful page can cite a version whose target write is later refused at `Vault/Store.lean:492-499`.
- [READ] The `same` branch at `Vault/Store.lean:349-353` preserves `p.note`, while `remarkPage` at `Vault/Store.lean:444-448` refuses to redraw a page with a note, contrary to the branch comment saying the view is redrawn.
- [READ] `Judge/Lrat.lean:115-118` returns success immediately on deriving the empty clause and never inspects the remaining steps, so acceptance does not mean the entire supplied certificate was checked.
- [READ] `Judge/Lrat.lean:98` classifies every nonpositive hint as `ratHint`, although `Judge/Lrat.lean:78-79` describes that refusal as a negative RAT hint and zero is not negative.

## Performance

- [INFERRED] `Receipt/Merkle.lean:45-49` performs linear length, take, and drop work at every level of a balanced recursion, giving `root` O(n log n) list processing rather than a linear array-based tree build.
- [INFERRED] `path` at `Receipt/Merkle.lean:52-57` recomputes the complete root of the sibling subtree at every level, so constructing one opening repeats O(n log n) tree work.
- [READ] `Commit.opening` at `Receipt/Merkle.lean:273-274` rebuilds `C.values` and a fresh path for every requested key.
- [INFERRED] `Naming.ofReading` at `Receipt.lean:340-347` consequently repeats full Merkle-tree work for every fact read, making receipt issuance scale roughly as the number of reads times O(n log n), in addition to rebuilding the dated root.
- [READ] `Judge/Lrat.lean:88-105` uses linear association-list lookup and repeated linear `contains` checks inside clause filtering for every propagation hint.
- [INFERRED] A long LRAT run therefore has growing per-hint cost in both the database and the accumulated assignment, which will dominate checking on large proofs.
- [READ] Model validation at `Judge/Lrat.lean:139-144` calls `lits.contains (-l)` for every literal, giving an O(m²) consistency pass before clause scanning.
- [READ] `Run/Durable.lean:104` appends with `s.journal ++ [ev]`, and `Run/Durable.lean:108` does the same for the outbox, making long sequences of submissions and exposures quadratic in list copying.
- [INFERRED] `pending` at `Run/Durable.lean:140-145` adds another quadratic pass because it performs list indexing and outbox membership for every journal position.
- [READ] Every mutable fork log is extended by append at `Run/Fork.lean:71-77`, so a fork built one row at a time repeatedly copies its entire history.
- [READ] `union` at `Run/Fork.lean:143` performs a linear membership test in `xs` for every element of `ys`.
- [READ] `Page.current` at `Vault/Store.lean:72` takes the last element of a list, while `commit` at `Vault/Store.lean:309-333` appends each accepted version with `p.history ++ [G']`.
- [INFERRED] Repeated writes therefore copy the whole version history and make history growth quadratic.
- [READ] `openEntries`, `openVault`, and `writesFor` at `Vault/Store.lean:391-396`, `Vault/Store.lean:492-499`, and `Vault/Store.lean:375-377` perform association-list lookups by page name inside maps over pages.
- [INFERRED] Opening a vault with distinct page names therefore has quadratic page-name lookup behavior before graph and rendering costs are counted.
- [INFERRED] `Judge/Class.lean:204-208` evaluates both decoders for the paired match, so an object-decoding failure does not avoid certificate decoding.

## Engineering

- [READ] `Run/Shared.lean:45`, `Run/Fork.lean:26`, and `Run/Durable.lean:39` publicly import proof modules into executable interface modules, coupling downstream builds and APIs to the proof layer.
- [INFERRED] `Run/Fork.lean:26` appears to need `Run.Proofs.Shared` for the generic list lemma used at `Run/Fork.lean:255`, which belongs in a utility module rather than behind a full proof import.
- [INFERRED] `Run/Durable.lean:39` has no definitions that use a theorem from `Run.Proofs.Shared`, so its sibling proof module is the more appropriate place for that dependency.
- [READ] `Ledger.Durable` at `Run/Shared.lean:104-111` merely repackages the two durability fields already present in `Ledger`, adding a second vocabulary for the same proposition.
- [READ] `JRefusal.taken` at `Run/Shared.lean:235-236` duplicates `LClause.taken`, and `jrun` can expose the same ledger refusal either as `.taken` or as `.ledger (.taken …)` through `Run/Shared.lean:277-284`.
- [READ] `setCfg` at `Run/Shared.lean:252-255` duplicates the nondependent case of `dupd` at `Fold.lean:85-93`.
- [READ] The text-resolution branch of `danglingOf` at `Vault/Store.lean:402-410` is duplicated inside `reciteOf` at `Vault/Store.lean:866-871`.
- [READ] `postOf` at `Receipt.lean:198-202` duplicates the post-root computation embedded in `issue` at `Receipt.lean:183-186` instead of providing the single definition used by both.
- [INFERRED] The blanket exposure at `Run/Durable.lean:40` is unnecessary for its sibling proofs because `Run/Proofs/Durable.lean:8-9` already uses `import all`, so ordinary consumers need not receive every definition body for that proof style.
- [READ] `Run/Shared.lean:12` names `joint_height_mono`, but the sibling theorem is `jrun_height_mono` at `Run/Proofs/Shared.lean:537-565`.
- [READ] `Judge/Lrat.lean:471-474` scans and tokenizes the complete certificate to select a decoder and then scans it again in the selected decoder.
- [READ] `Receipt.lean:349-354` places a generic list `filterMap` lemma in the receipt namespace, although it has no receipt-specific content.

## The ten changes I would make first

1. [INFERRED] Change `Vault/Store.lean:315-321` so a changed `kindChain` is judged against `newLaws`, or require the authorized adoption branch whenever the kind lineage changes.
2. [INFERRED] Add an explicit `1 ≤ k` guard before the lookup at `Vault/Store.lean:798` so section zero cannot alias section one.
3. [INFERRED] Make the `.defer` branch at `Run/Fork.lean:77` require `shared t = true` and return a specific refusal for a token outside both the fork and the shared ledger.
4. [INFERRED] Change `propagate` at `Run/Shared.lean:245-250` to return `Except` and make `jrun` refuse the joint transition when any required runner observation fails.
5. [INFERRED] Add `N.rowDigest r == R.row` to `recheck` at `Receipt.lean:218-229` and extend `recheck_sound` so the accepted receipt is tied to the row being replayed.
6. [INFERRED] Replace the cited case of `accepts` at `Receipt.lean:455-479` with actual receipt and opening validation, or narrow the documentation and theorem to a verdict-bit comparison only.
7. [INFERRED] Introduce a reusable tree or path-building artifact around `Receipt/Merkle.lean:45-65` and `Receipt/Merkle.lean:273-274` so one dated view is built once and all receipt openings share its sibling roots.
8. [INFERRED] Refine the association-list database and linear assignment representation at `Judge/Lrat.lean:88-105` to indexed structures while retaining the current lists as the proof model.
9. [INFERRED] Replace journal and outbox append/index representations at `Run/Durable.lean:97-145` with arrays plus an indexed exposure set, and prove refinement to the existing list model.
10. [INFERRED] Reverse the proof-layer imports at `Run/Shared.lean:45`, `Run/Fork.lean:26`, and `Run/Durable.lean:39`, moving generic lemmas and proof-only dependencies into their proper modules.
