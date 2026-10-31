# REPORT 2026-10-31 — the law fragment compiled to laws; wikilinks become identity cites

Lane LawDoc (Claude Opus 5.5), acting on `LANE-LAWDOC-BRIEF-20261031.md`. I worked in my own worktree
on branch `lane-lawdoc`, rebased on `origin/dev`, and pushed to `dev` after each step. Tags as in the trees:
**MEASURED** (a command run here, output read), **READ** (a file opened), **INFERRED** (my
reasoning). The trees under `~/dev` other than `obend` were only read (minidregg's
`Compiler/ObjectiveBendLaw.lean`, for `packageLaw`).

## 1. What landed (commits on `dev`)

| commit | what |
|---|---|
| `88e77dc` | `Obend.Law.Syntax`: `reqTy` gains the kernel facts the fragment reads (`caller`, `height`, `subject`, `turn`; `optNatTy`), `requestAt`; `request` keeps its signature. `Obend.Law.Proofs.Typing` (+ legacy leaf `TypingTeeth`). `Obend.Spec.LawCompile`, `Obend.Spec.Proofs.LawCompile` (+ legacy leaf `LawCompileTeeth`). `FrontEnd.Lowering.lawTerms`. `tests/law/Package.lean`. |
| `6b7c99b` | `Obend.Doc.Graph` (`Span`), `Section` (identity cites, rule (b)), `Render` (embeds, block references), new `Obend.Doc.Backlinks`; the two-page vault gets an embed and a block reference. |
| `344d7f6` | this report. |
| (this commit) | Ember's ruling on §5, (b) and (c): an adoption is judged with old = new, a relaw of a package law is refused naming the package; teeth for both; report updated. |

**MEASURED:** `LEAN_NUM_THREADS=2 lake build` green, 192 jobs, after the rebase on `origin/dev`.
`python3 tests/run-obend-source.py`: probes 30/30, tutorial 71/71, preview cohort 161 items, 0
failures (the cohorts are unchanged; the one stale pin it prints, `Structured-neverFinishing-no-partial-value`,
is the cohort's own). `lake env lean tests/law/Package.lean`: 83/83 `ok`. `lake env lean
tests/doc/RoundTrip.lean`: 25/25 `ok`. Every theorem in the new Law/Spec proof modules is pinned by
`#assert_axioms` to the standard three. The Doc theorems print `propext, Classical.choice, Quot.sound`
at most. No `sorry`, no `axiom`, no `native_decide`. Every `#tooth` reports a rejected stored proof.

## 2. The theorems

**Typing** (`Obend/Law/Proofs/Typing.lean`, closing the Law lane's "Not done" item). `ChecksAt law S`
means `checkAgainst ⟨law, noAnn, {}⟩ [] (lawTy S) = .ok _`. That is the bidirectional checker itself, with NO
annotations. A lemma for each term form reads the checker's own `elaborate`:
`syn_bound`, `syn_get`, `chk_lam`, `chk_case` (arms covering a closed row in order), `chk_inject`,
`chk_ifBool`, `chk_bin`, `chk_unit`. The skeleton is `lawOf6_checks`: for a canonical, shareable `S`, a law
checks if its six clauses check at `verdictTy` in `clauseCtx S P`. Then, for every such `S` that has the
fields a generator reads at the types it reads them, `ownerSigns_checks`, `allowlist_checks`,
`bounded_checks`, `windowed_checks`, `machine_checks` and `quorum_checks`, plus the checked
generators (`machine_ok_checks`, `quorum_ok_checks`, …). The teeth: four concrete instances, and the checker
refusing `bounded` at a field the state lacks or at a non-law type. The mutations
(`occasionRow`, `reqTy`, `proposalTy`, `stateTy`) are in the legacy leaf.

**Compile** (`Obend/Spec/LawCompile.lean`, proofs `Obend/Spec/Proofs/LawCompile.lean`).
`compile S name e` is `lawOf6` with an arm for each occasion, built from the Law combinators (`guard`, `andT`,
`anyOf`, `eqNat`, …). `Fits S e d` says the state is a record whose fields `e` reads fit `S`. On fitting
states:
- `cond_eval`: at any clause depth, the compiled condition evaluates to `.boolean (e.denote facts old n)`.
  It is proved by building the evaluation, case by case over the fragment.
- `compile_change` / `compile_birth` / `compile_adopt`: the law evaluates to `verdictOf name (denote …)`.
  A write or invoke uses the old state, a birth uses `none`, and an adoption uses `some new` (old = new).
- `compile_relaw`: a relaw of a package law evaluates to `refused (relawRefusal pkg)`, naming the package.
  `compile_retire`: a retirement gives `ok`.
- `compile_admits_*`, `compile_refuses_*` for change, birth and adopt: `Admits ↔ denote = true` and
  `Refuses … name ↔ denote = false`. Also `compile_refuses_relaw` and `compile_admits_retire`.
- `compile_checks`: for every canonical shareable `S` and every `e`, `ChecksAt (compile S name e) S`.
  `compilePackage_checks` gives the same for a whole package.

The teeth are decided in the kernel: a tally law admits a write and refuses two by name; at a birth,
`monotone` refuses and `writeOnce` admits; a negative constant, an absent subject and a missing field
are decided statically; a retirement is admitted; the kernel's own `run` agrees; the law is typed.
`adopt_teeth`: `monotone(total)` with no old state is false, so judged as a first write it refused every
adoption; judged as the identity write it admits the adoption of `total = 5`, and the tally's bound still
refuses an adoption over `total = 2000`. `relaw_teeth`: a relaw of the tally is refused with
`package law of Tally: changed by a package upgrade, not a relaw` and is not admitted. The mutations
(`scalarRead`; `clause` for birth; `compile` with a first-write adoption; `compile` with an admitted relaw;
`optNatTy`) are in the leaf, each rejected.

**Wiring.** `Lowering.lawTerms l S = compilePackage S l.laws`. A package's `law NAME: EXPR` lines,
already parsed into the lowering a capture loads, become the Law terms a kernel installs on an object
whose declared state type is `S`. The package is named by its source entry. `tests/law/Package.lean` lowers
a three-law package through `FrontEnd.lower`. It checks each term at `lawTy Tally`, and runs each law by the
reference step on six writes, two fact sets, births and adoptions. Every verdict equals `denote`, both
verdicts occur for every law, every relaw is refused naming `Tally.seed`, and a law outside the fragment
still refuses at lowering (119/119 `ok`).

**Doc** (`Obend/Doc/{Graph,Section,Render,Backlinks}.lean`). `Cite.span : Span` (`identity | page |
block b | bytes r`) replaces `range`. An identity cite rests on `present page`. A byte cite rests on
`verifies`, and, if it is following, also on `current`, which is now rule (b): the bytes at its span are the same at the
source's current version. Theorems:
- These keep their statements: `section_alternatives`, `conflict_is_section`, `pinned_cite_stays`,
  `renderAt_fresh`.
- `following_cite_behind` gains `hchg`: the quoted bytes changed.
- `recite_holds` gains that the span is quoted at the current version (a deleted block cannot be re-cited).
- New theorems: `identity_cite_stays`, `following_cite_stays`, `quoted_stays`, `present_stays`.
- Backlinks: `mem_backlinks` (the index is authentic: an entry is in it iff the world stores that live cite
  there), `post_correct` (dropping a page's entries and adding its new version's gives the new world's
  index), and `usable_unmoved` (when `q` moves, a run of another page that does not cite `q` is exactly as
  usable as before: the backlinks are all a move must re-judge).

The vault test, run against the deployed hash:
- Beta appending a line puts only the embed behind. The identity links and the block reference stay current.
- Rewriting Beta's marked line puts the block reference behind.
- Re-citing the embed restores it.
- The index maintained after Alpha drops its embed equals the recomputed one.

## 3. Decisions (each with a critique and a meta-critique)

**D1. The request carries the kernel's facts.** The fragment reads `request.subject/caller/height/turn`.
Law's `reqTy` had nano's vocabulary (`agent`, `principal`, the window), which cannot express them. So
`reqTy` gains the four facts as fields, in label order, with the subject and caller as `optNatTy`.
*Critique:* two vocabularies now sit side by side in one request: `principal`/`agent` labels, and
`subject`/`caller` naturals. *Meta-critique:* unifying them is a kernel-identity decision, not a
law-compiler one. I kept both and changed no Law theorem: `request` fills the new fields with `none`/`0`.

**D2. The compile is indexed by the declared state type `S`.** A field reads as a natural or as a
boolean (0/1) according to `S`, and a field `S` lacks reads as absent, statically. *Critique:* the
Spec front end knows no declared state type, so `lawTerms` takes `S` from the installer and the
captured package holds `LawExpr`s, not terms. *Meta-critique:* Core4 has no runtime type test, so
an `S`-free compile would fault on booleans or lie about absent fields. `S` really is an input.

**D3. Occasions** (§5, decided). A write and an invoke are judged with the old state, a birth with none, an
adoption as the identity write of the state the law is added over (old = new), and a retirement is admitted.
A relaw of a package law is refused, naming the package. Why: a package law is part of the pinned program the
receiver re-executes byte for byte, so the path to change it is a package upgrade (the carry), not a relaw.
Relaw remains the path for object-level laws, and the metarule (a law must admit its own amendment) is met
for package laws by the upgrade path, not by relaw.

**D4. Spans, not an optional range.** The brief said "range optional". A block reference addressed by
byte offset would fall behind whenever text is inserted above it, which is rule (b) at its worst. So
`Span.block b` re-finds the block by its marker in each version, and `Span.page` is the whole page:
a `(0, len)` range would not notice an appended line. *Critique:* this is more than "optional".
*Meta-critique:* `bytes r` keeps the literal reading available, and every theorem is over all four spans.

**D5. Mutation teeth for the typing and meaning theorems live in legacy leaves.** A `#tooth` re-checks
every proof downstream of the mutation, the checker's included, and a `module` cannot see those bodies,
even with `import all` on two modules (MEASURED). The Doc teeth stay inline.

## 4. Not done

- `keeps` typing: its invariant is an arbitrary closed term, and an unannotated closed lambda does not
  synthesize. `windowedLaw`/`quorumLaw` are typed for a scalar `T` only (`eqAt` is scalar equality).
- The compile is not tied to the minidregg kernel's `Pred` (`compile_sound` there). This tree has no `Pred`.
- Block embeds (`![[P#^b]]`) read as `!` plus a block reference. Heading links (`[[P#H]]`) are identity cites.
- `post_correct` is membership equality, not list equality: the maintained index appends.

## 5. The one decision for Ember (decided)

**What a package law says at an adoption and a relaw.** The first build judged an adoption as a first
write, so `monotone(F)` refused every adoption, and it admitted a relaw, so any authority that could relaw
could remove a package law. Ember chose (b) and (c): an adoption is judged with `old = new`, so the law's
invariant parts still bite and `monotone` holds; and a relaw of a package law is refused, naming the
package, because a package law is part of the pinned program the receiver re-executes byte for byte, and
it changes by a package upgrade (the carry). Relaw stays the path for object-level laws; for package laws
the metarule (a law must admit its own amendment) is met by the upgrade path.
