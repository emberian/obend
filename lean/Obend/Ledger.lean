module
/-
# Obend.Ledger — the first platform: a business ledger in a vault

`PLAN.md` workstream 8; `AMBITION.md` (platforms); `review/VISION-CLAUDE-20261031.md` §7.2;
`astra/ASTRA-VISION-20261031.md` §6.1–6.2. Catalogs, documents and registers are vault kinds with
laws; posting is a row of the register's audited fold, with its receipt; period closing is the
fold's world move, monotone; a correction is a reversing posting; a report is a judged fold whose
receipt says nothing of its period was left out; offline postings come back through the one door,
`Obend.Run.Fork.stitch`, re-judged by the register.

* `Obend.Ledger.Register` — postings, the register as an `Obend.Fold.Admission`, its theorems
  (append-only, monotone closing, balanced and conserved, posted once, reversal cancels, templates
  proved once, the stitch refuses a double posting and leaves main as it was).
* `Obend.Ledger.Vault` — the register's law is its kind page's, judged by the vault's judge.
* `Obend.Ledger.Json` — the journal, the register's root, origins.
* `Obend.Ledger.Report` — the trial balance (`Obend.Analysis.Coverage`), `trial-balance@1`, posting
  receipts.
* `Obend.Ledger.Cli` — `obend ledger`, `obend report trial-balance`, the stitch in `obend merge`,
  `obend verify` of ledger receipts.

The acceptance test is `lean/tests/ledger/WALKTHROUGH.md`, executed by `lean/tests/ledger/walkthrough.py`.
-/
public import Obend.Ledger.Register
public import Obend.Ledger.Vault
public import Obend.Ledger.Json
public import Obend.Ledger.Report
public import Obend.Ledger.Cli
