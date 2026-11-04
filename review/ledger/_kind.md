---
environment: ../lean/.lake/build/census/environment.txt
law appendOnly per ##: new.deletions == 0
law cited per ##: new.unresolvedInserted == 0
---
# The decisions ledger's kind

`DECISIONS-20261031.md` names this kind (`kind: ledger`); `obend open` in `review/` keeps the
world beside it (`.obend/world.json`) and judges every write of the ledger by the laws above, which
say what its preamble requires and the law fragment can say (2026-11-04):

- Appended to, never rewritten: `appendOnly per ##`, judged at every `## ` section (a decision is
  a table row inside one). A write deletes or rewrites no line of a section; it adds lines, anywhere
  in it. A refusal names the section and the number of lines the write removed.
- Every theorem a decision names is one the environment has: `cited per ##`. The lines a write adds
  to a section cite no backticked name that `environment:` lacks: the census's list of the library's
  constants, `lean/.lake/build/census/environment.txt`, written by `lake build Obend.Census` (tier 2,
  the whole tree) or `cd lean && lake env lean tests/decisions/Environment.lean` (the tier-1
  library). A refusal names the names. The names already in the ledger are history and are not
  judged again; `obend status DECISIONS-20261031` lists the ones the environment lacks today.
- Dated, decided by Ember, the integrator or a lane, and claiming Ember only when Ember posted it:
  not sayable for this file. A section carries many decisions and a decision row carries no field
  the reader knows (per-row fields are a question for Ember in the ledger, 2026-11-04);
  `lean/tests/decisions/WALKTHROUGH.md` says all three for a vault with one decision per page.

To add a decision, from `review/`:

    obend post DECISIONS-20261031 ROW.md --into "Taken by lanes under standing approval, 2026-11-04"

where `ROW.md` holds the table row and the quoted text is the section's heading; `--append` puts
the lines at the end of the file instead. The owner's post is the owner's write of the page,
judged: admitted, the file is rendered with the row; refused, the file is untouched and the refusal
names the section, the law, and the line or name that would pass. The whole of it, run and checked:
`lean/tests/decisions/LEDGER.md`.
