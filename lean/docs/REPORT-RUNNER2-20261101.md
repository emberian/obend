# Lane Runner-2: the ledger as a fold member, the committed view, consensus time, durable commit, fork and stitch (Claude Opus, 2026-11-01)

Placed by the root from the lane's closing report. Commits `950b932`, `74f45ec`, `5644522`,
`f2546f8`, `af5d0a6`. End build 465 jobs; census 34,654 constants, 27 on compiler trust; cohorts
unchanged; receipts 22/22 (5 new); the law package test with `request.height`.

1. **Ledger as a fold member** (`ledgerAdmission`: commit, raw move, abandon, observe; a spent
   token refused `taken` naming winner and epoch). `jrun` is the ledger and every runner as one
   family; `jreachable_fold`; `joint_reachable_projects_legal` is `project_moves_run` applied;
   durability is a `Ledger` field; the erasing-ledger tooth is on `ledgerAbandon_durable`.
2. **The committed view** (`Receipt/Merkle.lean`, positional Merkle map over cSHAKE):
   `opens_complete`, `opens_binds` (collision as a disjunct), `lengthHash_opens_lie` as the pole;
   `dated` is the root with one opening per read; `dated_verdict`, `issue_checks`,
   `member_receipt_dated_verdict`; the negotiation receipt's view is `checked`; `obend verify`
   re-checks openings; a consistent lie is refused only by the dated root.
3. **Consensus time**: a `Submission` may claim a height, `sealAt` builds the request at the
   ledger's height; `seal_future`, `write_future_refused`, `seal_claim_irrelevant`; `LawFact.current`;
   surface `ledger.height`, `request.height` refused; `jrun_height_mono`, `joint_consensus`.
4. **Durable commit and recovery**: durable journal and outbox, volatile memory; linearization at
   the journal append; `durable_refines`, `recover_restores`, `exposure_journaled`, `expose_once`,
   `journal_once`, `exposed_once` (two exposed effects consuming one token are one, across crashes);
   fixture with a crash between two buyers; tooth: a recovery that forgets the journal.
5. **Fork and stitch** (`Run/Fork.lean`): `notMine`; monotone rows union; bounded rows escalate
   through the ledger's step (`stitch_is_commit`); `stitch_accounts`; `stitch_double_spend`.

Restructured: durability hypothesis gone from joint theorems; no sync event before dispatch;
`JRefusal.ledger c`; `Receipt.issue` without `dated`; `requestAt` takes a `Consensus`;
`lawAdmission` through the seal; two old teeth replaced by `ledgerAbandon_durable`'s.

Not done: projection still borrows each runner's reachability for acceptance and `Kept`; the
stitch re-checks only the token; atomic appends assumed, no peer dedup; `Law.Std.rate` and the
vault's height still request-carried; teeth at fixtures.

## Decision for Ember
Should the ledger's view roots chain (hash chain or MMR committing the previous root and height)?
Receipts check against `dated`, but nothing shows `dated` is the ledger's root at that height.
Chaining lets a stranger check from one recent head, at one more opening per receipt and an
accumulator in `Run/Shared`; the alternative is a host or quorum signature, `attested` again.
Recommended chaining, as the input to workstream 12.
