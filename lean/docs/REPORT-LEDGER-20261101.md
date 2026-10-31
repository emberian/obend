# Report: lane Ledger (2026-11-01)

Brief: `lean/docs/LANE-LEDGER-BRIEF-20261101.md`. Gate (`PLAN.md` workstream 8): a stranger opens a
vault with a ledger kind, posts from a second machine offline, reconnects, sees a balance refusal
name its clause, corrects it, and prints a report an auditor recomputes. The gate is the walkthrough
`lean/tests/ledger/WALKTHROUGH.md`, run by `python3 tests/ledger/walkthrough.py` (24 steps, every
refusal's text shown, exit codes checked).

## 1. What landed

| item | where | state |
|---|---|---|
| (1) kinds: `Account` (`accounts/_kind.md`, a catalog law), `Document` (invoices, payments, bills, outlays: a `_kind.md` whose posting TEMPLATE is lines `- debit [[accounts/X]] FIELD`), `Register` (`register/_kind.md`: `balanced`, `solvent`, `sealed`), `Report` (the trial balance) | vault pages in the walkthrough; `Obend/Ledger/Register.lean`, `Vault.lean` | proved (§2) |
| (2) posting as an admitted row with its receipt; closing as the fold's monotone world move; correction as a reversing posting | `Register.lean` (`register : Obend.Fold.Admission`), `Report.lean` (`postingReceipt` = `Obend.Receipt.issue`) | proved |
| (3) the offline story: `obend merge` replays the other replica's new rows through this register by `Obend.Run.Fork.stitch`, atomically; a double posting and an overdraft refused by name | `Cli.lean` (`merge`), `Register.lean` (`stitch_twice_refused`) | walkthrough §6 |
| (4) `obend report trial-balance P [--out]`, `obend verify` of trial-balance and posting receipts, `obend analyze impact` on a posting | `Report.lean` (`trial-balance@1`), `Cli.lean`, `Main.lean` | walkthrough §7–8 |
| (5) the walkthrough, executed by a script | `lean/tests/ledger/` (the vault's runner, reused) | 24/24 |
| the missing kernel theorem: non-omission | `Obend/Analysis/Coverage.lean` | proved, two teeth |

Commits `a6b51f4..` on `lane-ledger` (range in the reply). New modules: `Obend.Analysis.Coverage`,
`Obend.Ledger{,.Register,.Vault,.Json,.Report,.Cli}`, all `module`s, all in the census and the tier 1
globs. Kernel edits: `Obend/Run/Fork.lean` gains two theorems (`stitch_conflicts`,
`replay_conflicts`: a conflict found on every replay state where an invariant holds is returned);
nothing else in the kernel changed. One vault edit outside the kernel: `Obend.Vault.suggest` also
tries the values of the other fields a law reads (so `a <= b` refused suggests `a = b`'s value; the
vault walkthrough and `run-impact.py` are unchanged, 26/26 and 32/32). No former theorem changed.
No sorry, no axiom; the only trust beyond the kernel is none (`decide +kernel` for the concrete
teeth).

## 2. What is proved

**The register** (`Obend.Ledger.Register`). A posting has lines `(account, debit, credit)`, a
document, a period, the origin of the posting it reverses, and its own ORIGIN (its identity across
replicas). The register is an audited fold whose world is the closed-through period and whose rest
is the postings. A posting row reads one fact (`isOpen period`) and is refused, in this order, by
`closedPeriod`, `again` (the register has this origin), `law name text` (the register kind's law,
a parameter that sees the register before the posting), `postedTwice doc first`, and for a reversal
`notLive`/`notInverse`. The register numbers each admitted posting (`P-NNNN`), so a fork's postings
renumber when stitched. The fold's laws (`keeps_world`, `step_of_reads`, `observe_ok`) are proved,
so `Obend.Fold.receipt_sufficient` and `Obend.Receipt.recheck_*` apply as they do to every admission.

- `register_append_only`: a run only appends postings (correction is not an edit).
- `register_monotone`, `closed_refused`, `closed_forever`: the closed-through period never
  decreases; a posting into a period at or before it is refused `closedPeriod period`, at that state
  and every state a run reaches from it (a closed period never reopens: the version law).
- `reach_lawful`, `reach_balanced`, `conserved`: every posting of a register reached from empty
  passed the kind's law at the register before it; when that law implies balance, every posting is
  balanced and the register's total debits are its total credits. `net_conserved`: a balanced
  posting's account nets sum to zero over any list of distinct accounts naming its lines.
- `reach_once` (posted once): a reachable register has distinct origins, every reversal names one
  of its postings, and at most one LIVE posting per document; `twice_refused` names the live one.
- `reversal_cancels`, `inverse_debits`, `inverse_credits`: a posting and its reversal net to zero on
  every account.
- `template_balanced` (proved once for every document): a template whose debit fields are a
  rearrangement of its credit fields makes only balanced postings.
- `stitch_twice_refused`: main has a live posting of `d`; a fork that reversed nothing posted `d`
  too; at the stitch the fork's posting is a conflict (returned with its clause) and main's register
  is as it was (`stitch_atomic`).
- Totals: `get_bump`, `get_addPosting`, `get_addAll` (an account's totals are the sums of the
  postings' lines on it).

**The vault's law is the register's** (`Obend.Ledger.Vault`). `kindLaw lin` judges a posting by the
register kind's law lines with the vault's `judge`, on the posting's state: its `debits`, `credits`,
`movements`, `period`, `version` (0), and for every account the register has moved, `NAME_debits`,
`NAME_credits` after the posting (`accountMeasures`). `kindLaw_holds` (every law holds of that state
by the fragment's meaning, from `judge_admits`), `kindLaw_balanced` (a kind carrying
`new.debits == new.credits` under any name admits only balanced postings), `vault_conserved` (so a
vault's register is conserved because its kind page says so).

**Non-omission** (`Obend.Analysis.Coverage`, the theorem the kernel lacked). A report over rows is a
selection, a key and an addition; its run is a left fold. A book is rows and their root. The judge
recomputes the fold and the root and refuses by `omitted k`, `extra k`, `order`, `total`, `root`
(last, so omissions are named without hashing; `root` is a refutation). `run_keys`, `run_total`,
`covers`, `only_selected`, `check_sound`, `check_complete`, `check_root_refutes`, **`check_covers`**
(an accepted report names every selected row of its book, no other, and its total is theirs),
`check_binds` (of every list with the book's root, when the root binds), `coverJudge`. Teeth:
`#tooth check_covers by mutation Report.run` (a fold that drops the last row: the stored proof is
rejected), `drop_last_refused` (a concrete report missing a row is refused `omitted`, naming it),
`other_rows_refuted`.

**The trial balance** (`Obend.Ledger.Report`). `tb P` is a coverage report (postings of period `P`,
keyed by number, added into per-account totals). `tb_totals` (each account's totals are the period's
postings' sums on it), **`trial_balance_covers`** (an accepted trial balance names every posting of
the period in its book and its totals are theirs), `trial_balance_binds`. `trial-balance@1`
(`tbFormat`: decidable, compiled; the planted bad certificate leaves out `P-0003`,
`tb_bad_refused`). Posting receipts: `naming` (roots are `postingsRoot`, the digest of the
postings), `postingReceipt` (`Receipt.issue` of the row), `posting_receipt_checks` (the stranger's
`recheck` accepts every honest one).

Tooth on the register: `#tooth step_once by mutation Reg.liveOf := fun _ _ => none` (the proof that
posting once is kept is rejected).

## 3. The stranger's path (the walkthrough)

§1 the chart, four document kinds, the register kind; §2 an invoice posted, its page (it embeds the
document, so a later edit of the document leaves the posting behind by name), its receipt verified
with no books; §3 a supplier's bill refused **by `register/_kind: balanced`, naming the clause and
what would pass** (the template forgot the tax), the kind corrected, posted; §4 a second posting of
the invoice refused `posted-once` naming `P-0001`, the invoice edited, the posting page's edit
refused by `sealed`, the reversal and the repost; §5 period 11 closed, a late payment refused
`closed-period` naming the period, posted into 12; closing back is a no-op ("closing never goes
back"); §6 the laptop copy posts offline, the desk posts meanwhile, `obend merge ../laptop` is
refused whole: **the laptop's outlay by `register/_kind: solvent` (`Cash_credits = 650 would pass
(this write has Cash_credits = 700)`: each side's cash was fine alone)** and its invoice by
`posted-once`; the owner drops both (`--drop`), the laptop's payment is stitched and renumbered,
the outlay corrected to what cash allows and posted; §7 the trial balances of 12 and 11, the
auditor's `obend verify tb-12.json --root $(obend ledger root)`, a report missing `P-0007` refused
`omitted`, a stitched posting's receipt re-checked; §8 `obend analyze impact register/P-0002@retired`
lists the trial balance's link to it going behind, checked by `impact@1`.

## 4. Decisions, with critique

**D1. The posting is a row of the register's audited fold, with `Receipt.issue`'s receipt; it is not
dispatched through `Obend.Run.Runner`.** The brief says "a turn through the runner". The runner's
machinery (protocol, holes, in-flight calls) has nothing to say of a posting, which is one judged
write; the register as an `Admission` is the instance the fold's and receipt's theorems were built
for, and the stitch is `Run.Fork.stitch`'s generic door. Critique: the durability story is weaker
than `Run.Durable`'s: `ledger.json` is rewritten whole, and a crash between writing a receipt and
saving the journal leaves an orphan receipt and page (the journal stays authoritative). Meta: the
right next step is the register as a member of the shared-World ledger fold (`Run.Shared`), which
would give the runner's `refines` and the durable host for free; it is a lane, not a patch.

**D2. The register's law sees the register.** `Law := Reg → Posting → Option …` so that a balance
law (`solvent`) is a law of the kind page, judged at the stitch against main's state, which is what
makes an offline overdraft a refusal by name. Critique: account fields are named by the account
page's short name (`Cash`), so two accounts with one short name in different folders share fields
(the first wins); and laws reading page-only measures (`words`, `bytes`) read 0 at the ledger and
the page's value at the vault's own birth check of the posting page.

**D3. The stitch is atomic, with the owner's `--drop`.** As the brief and `stitch_atomic` require:
one refused row and nothing of the other register is taken; every refusal is printed with its
clause. Documents still merge as pages (drafts merge, postings escalate: Astra §6.2). Critique: a
large offline batch with one conflict needs one `--drop` per conflict; a per-row "accept what
passes, keep the rest as drafts" door would be friendlier and is not what was asked.

**D4. Cross-replica identity is the origin** (digest of the content and of the origin before it
where it was made); numbers are the receiving register's, given at commit. A row already here (by
origin) is not replayed, so merging twice is idempotent. Consequence: two replicas that post the
same document with the same lines on the same history make ONE row, taken once, without a refusal.
This is §6's decision.

## 5. What is not proved

- The CLI's merge decides by `Run.Fork.stitch` and then commits by replaying the same `step` per row
  (for each row's receipt); their agreement is by construction, not a theorem.
- Root binding is under a collision-freedom hypothesis (`check_binds`, `trial_balance_binds`), as
  `Receipt.chain_binds`.
- The solvency law's meaning is proved on the posting's state (`kindLaw_holds`); the statement
  "a reachable register's cash credits never exceed its cash debits" over the register's totals is
  not stated (it needs the short-name lookup lemmas of D2).
- Not built from row 8: forms as view methods, a purchase-to-payment app on the shared World,
  posting through `Run.Durable`. The laptop does not pull: after a stitch the desk's register is
  authoritative and the laptop is re-copied.

Tier 1 green on the Mac and on hbox; tier 2 on hbox: see §7.

## 6. The decision for Ember

**What is a posting's identity across machines?** (contract C1's territory.)
- A (built): content plus the history it was made on. Identical postings made on one history are one
  posting; merging is idempotent; numbers are the receiving register's.
- B: replica plus local number. Every offline posting is distinct; the same posting made twice is
  refused `posted-once` at the stitch and must be dropped by hand. Needs a replica id that a copy
  does not inherit (a copy made with `cp -R` would otherwise share it).
- C: the document alone, one posting per document version, with reversal bumping a version.
  Simplest to explain; loses the order of history.
Recommendation A: it makes the merge idempotent and the "same" posting the same without a rule, and
a person still sees every differing double posting refused by name.

## 7. Builds

