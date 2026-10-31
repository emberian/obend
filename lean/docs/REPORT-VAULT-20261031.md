# Report: `obend open` (lane Vault, Claude Opus, 2026-10-31)

Placed by the root session from the lane's closing report; the harness refused the lane the write.
Commits `1d7ae02` (the library and CLI) and `1bc0118` (the executed walkthrough), full build green
at 213 jobs, Mini's cohorts unchanged, 11 `#tooth` mutations rejected, census clean.

## What landed

`Obend/Vault/{Page,Law,Store,Json,Cli,Teeth}.lean`, `tests/vault/WALKTHROUGH.md` and
`walkthrough.py` (22 steps, passing).

- **`obend open DIR`** reads every `.md` as a page and keeps the world in `DIR/.obend/world.json`:
  every version of every page, cites with byte commitments, line authorship, members and grants. It
  writes pages back, reports what changed and which cites are behind, and leaves the text alone; a
  second open prints `nothing changed`.
- **Edits and merges.** A changed file is a write turned into a patch against the current version;
  `obend merge OTHER_DIR` merges each page by the pushout; a conflict is a readable block in the file
  (`<<<<<<< section 1 · candidate 1 (owner) · keep it: obend select Gamma 1 1`) settled by
  `obend select` or by hand.
- **Laws.** A `law NAME: EXPR` frontmatter line, and each folder's `_kind.md` laws, compiled by
  `Spec/LawCompile` and judged on every write; a refusal names the law, says when it came from a
  kind, and says what would pass (`refused by its law short: new.words <= 20 does not hold; words =
  20 would pass (this write has words = 27)`).
- **Members.** `obend member add NAME --grant VERB:PATTERN` (post, select, write, relaw); a member's
  post never overwrites, each changed line becomes a section with "as it is" and "as proposed";
  selecting without the grant is refused.

## Proved

`open_idem` (open, write, open again changes neither store nor files, any hash), `mem_writes`
(a file is written only where it differs, only with that text), `judge_admits`/`judge_refuses`
(admission agrees with the law language's own meaning; a named refusal is a listed law that does
not hold), `mergePage_pushout`, `select_keeps`, `select_needs_grant`, `post_needs_grant`.
Not proved: that an edit's patch renders back to exactly the saved file (both test vaults
round-trip byte for byte).

## Decisions

D1 (revised in `9304fc2`) files hold the text and carry behind-marks (`![[Beta]]{behind}`, `[[Beta#^id]]{behind}`, `{unverified}`, `{missing}`) that the reader strips exactly before reading, so a mark is never an edit (`dropMark_mark`, `stripToks_mark`, two teeth); a hand-deleted mark writes no version and is redrawn at the next open. D2 a refused write leaves the file as
typed and records the refusal. D3 changes widened to whole lines. D4 line and page ids are content
and name hashes, so identical edits merge cleanly. D5 a member's post deletes nothing. D6 the opener
is caller 0; changing a law needs the opener or a `relaw` grant. D7 cite version numbers are not
stable across copies. Deviations: one library commit rather than four (one write path); the teeth
file is a non-module leaf.

## Limitations

Line-granular conflicts; 32-bit name hashes (a collision refuses, never merges wrongly; a rename is
a new page); a cite made on a diverged copy reads unverified until `obend recite`. Dangling links resolve on open once the target exists (`9304fc2`). Not done: merging members
across copies, members paying for writes, recreating deleted files.

## Decision (taken by Claude under standing approval, 10-31; built in `9304fc2`)

Where a page shows it is behind: (b) marks written into the file (`![[Beta]]{behind}`) that the
reader strips exactly, so the round trip stays a theorem and you see it where you read. Alternatives
were (a) report only, (c) a marked copy under `.obend/view/`. Reversal cost: the mark writer and
stripper, no theorem shape.
